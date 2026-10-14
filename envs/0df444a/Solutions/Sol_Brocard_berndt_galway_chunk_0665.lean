-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0665
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:00:33.20556+00:00
-- url     : https://prove2.me/submissions/9d6ca2fd-ba1a-4503-bd5e-b4d808e4d083

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 119424460 ≤ n < 119604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 119425710 1250 119424460 119424479
    0x70510080c030106080c0403060e1c031112040c03140a0605090105160807020715180905010b070312020f04090b1e010e010525060905190c030b04030234 67
    0x50140c850071036194556407070800b08590b10600641107070440c003000c010020004041d4440c2d21110030b000409000740c41d4a4001c8814880c6442e54682d05040c03c1c0390950030f0188014088842e00440303030021608945860030020250032454000034000d00c17048014071102c00002a400521500c40e400501190b0360341082d082c00e81d00240c3d00c82e4411a52460040c0c0124011040240d0010140c41101c00380c03940c50000200f0f10314203927060b40c013141c40189140110fa401e40d250034050040a0800d10055141088007440351150141c041d080cc04141003518032407aa580445142906c0390708082e40721900d450f000d80081440340c800601c115010300640e0b011540c031a4001d1140001615012028210540103480c0380e4400c0a11054060381c0800240740e0f50000c54400f070303420340a400000b8504459140c0146421440d00418580400082011000580d14144002941d0b40076429444a484510703003030f860b22101003290481184035509a007465680b142498513420002030411041a0b5504e0205 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 119426960 1250 119425710 119425727
    0x70b040b0301050d050c090f100504110409020304020111010509010c094104050c0705060106050c0d050d0e0a0f1b0305100b120708010204060806060f0d1517070510 72
    0x30a0080001d00040015260600c403010b000c6004800303444560030380e9800956140b00444800e804030502c00300740600e04002501c0d000c0601000c6d20704112010b405401c50080d4012032048040b02a00000020116403044142074201128207000380620b0400601d01c0b40030b0700810206800043c056580040c0c2105051041e0324450150355a86440e100400d20b800b070505d404071203c4050041c0c8511017a403545842c884c0d40d00c00c090300110141c5425481c51306600704841a030000c42001020301c0328100c510000700b074441007641d0500300b8a607103200918400c000351064206d82300180c0114149a420703c402103540749002440b816400580b494049080c4210b144140005051076100360210308400110741e01ca8a003080340140302c488019400e84d6198130b003102e20780101c0e126940220301040402d0700916541e41149088907458140903d05204076001c0c060348140f018055241e207045c1d64800c0c4000700080143ca8064607517928070180601480d9100740c01d02c901801a03649c60029400340b4480c2400c3e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 119428210 1250 119426960 119426969
    0x3050a0c080601030b060c030406050405030f150f060d060e0303250c030302070204150b19020705090f1009020c010605013c140d05240a09020a090f08030c070b04 71
    0x1181e14545803500114000c0c03840814035504044c003046030702019041000504000d044e240c0d203aa560710b05040c20315090001d000f20a121a521001070340741640309270590307140d0040d00c142d0109000d50b107010005410b40c8113a40054207551400c065002d07000800f00047d8461501c1f20300e071490500c0e46004203c07034551001e10100c0003510004031940024030a800910203540010004907446240100b008145215544a00f0250000040d152202c00c2d89094421403c8000c0c00503000d402e1800020401c103083c011f200b00381080301c610016200341860091003014201c2018110345500a802116000700f80d103001d068007140b0302c0400c0c02c08a50480d000403043d43d0a014002e022a14841280c0c0c0d41c44581181510600c10100c0700f0728900031003c0b019081400c1d000b41c0215135824042c01030800f560042000c0011820300080d60807039500c070b00f42c134142101d16034080140c0e1600f80d018100c0d41d40c4c480d0b402103a5209003c5d0720014900f80c0000141100404950540e6156940c1d103c1d40600c6115a118 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 119429460 1250 119428210 119428217
    0x1407030519050c091303120e0303040210030e0703082205100e01050c0a0c0311090402030d0f030e03030406090506010e01140103021804020c0f0c03030901080a090f020303070b060103050a0c 83
    0x410440040240000502580c41101224000d02c3c82200103110720a00300d07060555092140c01720014545e0291069110f01113500e400c011881ea90a039494492000a0020740038441d403004254102d0310a03400401c102e40d455058030003c90b180c0c500304041c1e90102d003a80c144840c2120284882c0c034240d80c1844201c0e1002000308420203880c0c4400e854030300341c480b102810b104092007180c548010601c43c003c0329070300c5600300505d014103514180f09001040440c060040038004200070068400040c0c1004116050511074038032800014102c0240c110300d1241c80d010b0002006000c01c0148507048a1155489541035552903030300c40496078110709092190700920090b40c080422254002ea00801c14000c0300540e122904d461800400c0907a030040190040b6948681c10700784407882e041c003084888010850207907180c14044c2d00020f0140c0700242000040c03d503100e0320002080221104210b8083c0e01605503a184d920608060102d2841222490b0101e420007000414010a82c802d0510490140c0c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 119430710 1250 119429460 119429473
    0xa09021905092205100c0212040605120a1b0201020c060906070909051f03050307050c0609010527100f03050105030a02010c06050703060810060f120803061309060501090914070305 79
    0x41e09009407140c00710140c01005101c0b40b8900c00325005002144032000c45040100310800c40c0180280707000904840c230740181c1814401400781e1980201140d000f001d40907608155071311038418840080900058201d40c4825040444803203a40640140019024a0041c0e851940d13805042030307202c0c1d108403080000110540e00500c003001752a40841c0d0440b5204000c6aa100c0854000704d0541117660001e56450740302041700005c0000400c40000c0111080d5103803800c1043e028006061800387c805210f9400c070a0041108008880007105007000c0700c000d00da42d482d20311103000a00003035104100c1c5000a414240042800d0a00103604030719280c1c10780d6076070b140c50003644909005100203400d200415807210030000b203403002006103200144842ca80081c1061516142e1001c1c0c0e9644c1d480798600800505604000c5480d500a4a5204030244e400d64100e00394041410014502400c0090060740740000100b08070400e85e000c40c411500c59035107407507022001848035950b00e2091000030460b50001c7e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 119431960 1250 119430710 119430721
    0xf06060905040e0309240702040903050919061b0f020d0606030c32031606030e010f0b03030703140d05130303111206041113090203070f0c03050910050d050a0902190509 74
    0xd00c1000d01448621446c2030400c0019800134044d610054410740008501040e03102c1c0601e01100ca0300004494455030420a5280680290425501d05285c10035010845840000e0003c012441c0301c40c0e40d802401b084065450386040801445035000270703211480c1c03154000c101c481c10803171101381c0030a904803641c041c00c2c18601d903240b402d402c4442c030f02d8060050000d814000c00640c203906014000c81c0d03e020600b1124201002d003103900c40301b140c9614500b490591b1703503244c402000310b5404036014a85200d0044408002441c0740c400c241401030f01604d007100300040040c500d00a00b00d00e82c4a41d03824408801c04070822320050080300009240d580c880c0000c170710280ba1540c0924806170b400c8036014202240140240d8041d1519440f040340b86800000f0000040d602c0340c003500c6813100c1818005142043c3e51001800c42c0100100b050142484001303401f0103070301a80c20b56028541c01d04060110b0720740054480d01030440507004900824251201b01c4124082024050075600d000d003840a041d55030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 119433210 1250 119431960 119431999
    0x32104030206010506090a21050f01091a0901110c010606020c06071109090f030d060e0f010b0a03050705090a03030309050106090b0609010e040b10170109090312020901030f06060905040e0309 84
    0x2c01c08551000180d90b0010311102c1903d540ca03213003000c2c160223021410300e03410300c0e60501e494035202c60b80340d9141002030400580488140c082c01904c884c0300c020545c1e80c1c0b510307907401484c40040380c291307251012030034030b5881c101500003030b003500e082c1e40c02d8442c4451404140325660082d20f0000b40300d44417900000603103003014141a070340030001038125851025040e0410b800e541c0442101c9007001d4656805110681c0c65032001c5400110ba00540c00056261141e15030450107041605810181c40e03002140089224005442460301d00428580c3d525035240b170301030014078056400301d80c503508054001958030302c5840b420600c5c0714043c01d45443c0c0b20322900110b1b6889010b03e00c03181d00c0ba84d540018001d40e11140f4403804145110340784c090000d07080100e8840320707500582c0a070404078103010110000a03440905582e0311610b444c809030310fa540e1140140c0160802c0032440203064503148000403060382c45148042110780c1a50104500e06694a801c0c0e00c912402c5c17910381d040078490400c10640d016 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 119434460 1250 119433210 119433217
    0x1501030b010903020402181504030b22020307091d01050105060a0f020a1a0402090c0702010c0b070e0d060204050a050a05030c01180f0e06010e01020a020d080a0309080309032104030206010506 84
    0x4051400382120b98890780081d08982092003404011001000701c1d4000d42171140407034064005418503682070505d540d880340e80d03084004004505c0040911520480c1a004094452089500070f0580c0c10990702c9104bd04014805801d001400041c1c40041c24940b00061280034140d64000e0401490101c4000d000d464a450381c010b090211701c19842c014001c0780700e00c2d40d1000d620400144441150070607004102e124080a0415140c800c0c041040100503a08035066649103644480c0318001c9640e4202c040e5210000d0140003030704800d041c4a2002040090340c010300c1510011035428210b00d8640090001c0581c0600866825601150680d0b880b50b00807000b00040e0141c0521b179005a0751900403240fa5550f1650000e82110381c0c1d603052015568100e5500c06035003000780300811b04a9a00e80000d00c07487c1c2c8514000e00841000240c6100540c80703600700905040c0c121104030b6503030400c00f4483d07076030341e02c00081c841650058810300070038410b8903000507004540540c01080d1507420507040040c0741e403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 119435710 1250 119434460 119434481
    0xa0507030b0a0b13080102041509050924060d0504121b0314090a12050d03050a0203090c010e060c01180b0c040f06030506061201290901050d02250803090d08150103 72
    0x21004d01c2c00040b80c040c240014006840e1640c0c044d110341e000c0c01c4000d080240903820180c45551103034104940e0800c10301031100c0011810b109406401c2106010450510900c40d401031040c1c100310412003408405115103401380e80541e5804207000f01204405028403034184014005190f0031821100f402c020340203080801da001305228003043e920202c080011450303c0e01110030360410340b034400545405204c0c03103520900d00e5405518500c1d25a28441d1220401008107048c4001c0004507032481e20307030209440e40031b941c800082154560079005105800c51012003201e03031405440002c0e0101032600103a07404c4507107906442176003500700350080c2d002e400001c200701d4000318140b05c90f0103600300c1e89510a00070600b2850300d000c0c1a000401c0003000d030f00b98880352811316004014a01250b640501221940380c50400016200d4202000000d240d9892905540c92800310b0600d13081440f4515005600800d00b520448082d075000b004240c80341c000448450300b012100f81c5d54202c481d40030f500b20100c0813 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 119436960 1250 119435710 119435737
    0x3030f030a060b0c100515060403030c0c0302060d060305061f1a0c0610090e0c0a050118030b0702010c0f03060503070e071e02070602011a0a0b0c070308040308030a0507030b0a0b 78
    0x39449000c07803152600585005011617125111406503010b0a1152a802820710302c1510008444e07480450203600c990f202c001d00b0002640d60003c02c5c03202c414500800740da0b000f084150390300207400b03000740681200e0100f912075010f0b11020500c04040c034030a0420500e03c8114100303030a4500901821016001a2101c45407131041001c0030b0858001c0c000588501c4006005e14401402e1048a104440802007601c905510140c10009540e0383d11000100700c4009181402e922241001d442c203500301640e1000308942280070a0007411034040d0030030050881c19a81d54225141d140804500fa100301d4441e260b00754000c04c5081c0305440c60030f94901e9001e81c440c00c0c500c0c01480001d0451040780e103520f8072000160010350b41400b003241d0a000c1d104100b0014000b81040c07910100009440f801103114082140000240c2d0a10503042442040001d540249040b45c50740c0d03617810300715031360742c02111050714041c98800003c28a034080d100d40235001d41c01501303d00802c1d0810160300c100781d0201e001414034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 119438210 1250 119436960 119436971
    0x60702090103061e020a0207260a14030702060705300306040216120806010f020f03040b0a0905090901021312050a0f06061205070503070b04150c0c0909080712050903030f030a 77
    0x145110f0000301001c1c21650f000b0501c00e03142011980c1032100086a25007154084c89188503411000181e02b1800341d00501003600f4000302c1c1032010314500c107040380250801c10101d0b5020a100c40400c4c0c00b22042c0d01c08503050220403101c200c681c48103d0790385070b08480010a0000c40c1103820140c0c00b424040c503000681d900400b901d51103101d040034906030300c08000ba141e00100105540c0c40001d05808002c2360000b060b00c0c0c101000300b1030310307801a805000705124020444262041c8a0903164005290142015100341041c1e00b0050103980701c1e00707115440000c0b25a0020780042c0000d6402180d0350400d024025114444d40c40030401d5a0045064801d1600d0320404a41006e5a01d500001c0e14420030040100601e04402e242c00e107500f55201d0101c50000340010408036010380c2103454004180e01d482950702c0100d203031407a51064103811041056150021b40e00800949800410085020354900300191115803022a1180704044650350103070018003004040000441c051500b10401210102d01c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 119439460 1250 119438210 119438261
    0x60503130b0a0203060f0f01020c1905060c0601080d1b06020a1205070306050306090d0e010503040312060f05010e04110a0507050709050f0f0a0902152505070503070506070209010306 80
    0x4189000741c4201028640c00405d0040354a41030b103c00511010903034282c2840800c001c0080d413030380c81c1104c15a014200f8485041e40324058001c220b0040d00300145a1916031844207060759031008240a00c8a45200311103135800c102c3e0142d44d0f0450001c46005070103540c00015503404010303400c80b40d034000900c160000d40c3c000e107a441c1c4c01068424140e59030001062490310041600d054405810509079030080081c904516500426150b000202802d1080d683c4d10f0780e24045440909509108a046180600c003040d107814103c40002103480c00d130b80d62440329950340c080108031f07488249403c4903007404000101d6020300440c0a000c105000c0c0b4141c2e900259a02006000d50380b044030216050507901d0100a0101d00d00d10b40c20b9008900b092042081e42130982c00b084640c2c10f14028481d800e00041a41100c96605080c80d51110003024100c1c0c254030518a001070360384015000301d910030b01400401048d10f00b4508103a564075030f0000d10913140ca91854441600030800150b07a5080c00d9a400320290 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 119440710 1250 119439460 119439473
    0x2c0a02090a021b0a080c0706090b03070c0203120d060501140c06220218040b0f01030803070c0f0f0c26060a02070201020c190807050a08100c020124030c0608090706050313 75
    0x8001e136004401080d51003540d511600d04050b800e800410622100c13040a00070101500c054070b9000d221802c2c8100f82001c0c60000900e80411210005600c1c00d00240714002180e154000000f1070300d007030700c03904010b000301304580146001344140701c1f81e15400309000401c030389003940c1c0d10003410260101038110140d0517000320360240700041d080700c441c41d100c00c20f103c00c01c4504444690b122a400b5500c0c400c55056a07980300300b5101c081c01c0d4201f00103006a1301001d102c261f210411907550302201294038510185008418800c0ca4071445c94000307404d2806007107120081d032000c2c06544465014107070a07950128403500075003107030301300f81e0440c440c0380300c404000d03100d01c031211010001e0200504115450f0010030703450010541c1002e40a808005020849904001051103400304000d4011462030301030b0340200d005012061780e41c40e50000061480c48030425000c080d0041c0c9002e4420004256103401d800c1d41c5887c030985001030640d00c00003080003058480e1000e1904416030340905e803c1541d0f0342d202c02c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 119441960 1250 119440710 119440723
    0x23032113030b010f09020c030307081b0307030914060919050f010606020304091b0f1b061a091006080705071104091103060604060303141303062c0a02090a021b 70
    0x71a100b01e0b040e00144000f0644075241c40050034011419841d040519101c0713526408094809400d2010010101c1d036560003401c421601040c0c030450b0f2945034900203000074080c0005400560f020440081170410800d03020420310310580310080148401c20426180b14020010908260340324040c4100340213843c1405c4c052040102226030080d921a07041a0410040310705d42142101c2e60704e148101c03043c1181e0807407182d600e10711a50824005840c514407500074a004400300c01400036250100c0d40f41c2403580d401d14400d80d404107444648440d511032140c200002058003038040440d030864009801244a10002d0039014030640780f01c000700842001240a40300d001d00d08981d004c80120607080541400c01c05958000703011282070014a14540b40a8801e2400030380081c502c03036000515040e1301c01c010b840780780215400201000440301c8034484546888a50316150303072041036580d00c099543c01c0014480c40290b00107080380c0e11500d07008500c0d0700a6101003403841e001c840000038180c2403801072144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 119443210 1250 119441960 119441963
    0x601120512070f2f010e04020c060403031d030c070506030c120f1623090102030c0a11040506090f07030f0603020d061b02070311121f062303211303 65
    0x2c00c0400c1e1402c0c07402e40e070b03110041c2c4d00000d102e80769158075065030000340d81c612a200c8400e0a1500001020102060282c0308200308401c03d4800d10b000d010406070305a004188101000001c0503d10b1540189075440c4d10034942c00303805591215900348020b02c1d001e0010742e00010321400c124034290043c070b14100e0351141211304030085c91a64040100002032010070031074000b5149000c1000c031042e00341e14140f40c281d014001c0364481000c11101c45a034003c10803103028400100499000e4500342c90681000c91144021900490504000c52041e04101310311034000e0b240340d81c0302036480da18020101c0c02405040d040c02503807610b6000020168032103091448d100c83c01100c0c00300b0601e8980c44201200011000b064046500c420801c00210301d1440321200300b8135007228400d4414001c44c902d14501302840c2d4244800d982c40ea410810700d400164400c104031030f01c1c10076070302d420380108810b18200c0d2850901ca64060708032694008200d2140340e4028904a80039402c6030900410040405056040e42c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 119444460 1250 119443210 119443223
    0xa020304030311030f0f191d010f060803180303040308120a06270e0102090a3201091202030106180f0b09090a03050a050403020d060626060112051207 66
    0x51000381035043c040e500d8125581e004840ca10f041c24a04010303041d01c0200504140c21b000c0300820083c0304a40706003003800700c4100e002d000003001c90b280d00081802c0d40310700e03007001c5d803a08848001e84000343c091035044800340b002450406807a40180403803c5040401d003641400308200100001d4100d0029184240048440d0040781ca44141c640b42121300a400048400792410500d03d07000e2040305400e0a03110030f5050205912900c0000c840c0a80920f40209601010b003807008911280c280300141d0114110302103103042070011030043c41040c01c00455250001c0e001c544c0174004695800f140361500c501c040c000041e00d80c2d5484081a16002c80360050038415294603072225160040d0080c0c0e02c0a036401c42d004041424603100190b51110f4074500103080c04004603d28030114003550a8900454016025034501c82607407406d00010001d5001c2c0c0340050210340c05608401102241d03050110301003074000c000030b03400c019040c8954141e0030000c1720540f080381103076190000d48101406d0558030a00c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 119445710 1250 119444460 119444467
    0x5070e0106080603010519020918150108070f0206040204020f12010902190207081b0102070810050a11070309050f062b1d0d0c03121b020c010203090d0b07170a02 71
    0x1900402040c0b0180045200b0380c1850144840520400d807001d01501562800596582ca1100030407640c0700d03140742202c404030300d040c00c012139001c142d4030310400c41a0036660300a10f03564003c400d40341c0750050481d142c0140e000100140050606600810001207605030b03450901e000c00418240d0281c00341c00c05000b080c1c000c1004c2c012043d040074140e105a03014006400181d0038401165034541d030171800b2102ca030304120039410890340240004400fa00340362080c0e54190004648110103030106644944200e498034000405040c00142038900f0254159500c140003403821080080801c5842191948200c0c00c0292900d0200140d054441008400491041c2c0c0c404015880048801422000d15403114000040b031054401144040c098001c0c0d0410140302a000c1c142124005038000520481520300070425041945d05043c10700d40ea2890b600302c894203a03040004903240d014640c07115800030300030180880050b000340802e80c1e0144080c9003602e29055001032807000e0300810759088140a9002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 119446960 1250 119445710 119445719
    0x40806090f01060b0c030304170f0309010b031c08071d031b03060105060f1608040b030906040203060709180b13060f0614120103110f030102130f150206060607050a05070e01 76
    0x20702440c001010f05800032400c0850710901c0303e1b120f1200402c000c24003001c101c115402c06801400756001d80c00002d0350141c031f80c81d100401600a000194110b4420f00c149a952461070a50706480e203020119a03a4008250f01c44020940311040000c00c51a500d0007400b020554546040102e5800012420280400c40300301905150402e05d068000c10b001d0001009a00c0c0f43c84204021a00a00440d40040802990030f0070008114062504034104514000003400625000090081c0c0620300032070070b549443d2681082070b00c00000511a90307200e1403c0703091105c107200790340c2d02c40c8005035805020b194901251400b50802c41c1c040b604030441103205c4140500075140c1c0214909003007074140c9101842c01c10302c1d45a00d11808814800100217050005511501d80c650114503152801c0180083d034072508014840e0003502418012804541145c00700014101268404d002032501c03641c028018644494007800341542c0904420b0380c0030310039441181b001500070072146d0010420032030a4056075041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 119448210 1250 119446960 119446963
    0x90806070f0909060e040f0c03051f0b0102070303080c07060b031c0906050703120c120f0b010e030a0804030f020105040305060109020a0306081b010e040b031c080711071406040806090f 81
    0x2660032034880146044014400c80100c0385d5101d800070b400c0240070003003240924042c3e554000c50340009080f4003a072402070082180b01601a28003008552042c0034000c2510012aa03d10140c0b00c00b40014500201003488034203900c0c0101119801365401240040c15040030a1810461020900c00304804016101c0c101c0d81c0241800041c10040c603011740342207802d8400500401085401c000e48550b01d0210039100c2c0e000e404040d03e048803030541802440385c6892007000500c40144400d001c928810701ea210140340200c3d00a10301903000c3c3c6054101811500c1c7c0310000c400c20103017207050040c1000040042001005002d00a00e50a000580c3c2c4418181008003950311a07885006180d00c030b00000303c3c842000396050014000c081c60650a03080414001401070140044100d4050081415882c50262000380c0341c800c3d103407641c541070002e8499180c11102008100605050341e00a0035050003c40c06056621a240300d0050003142425119000c241c1000800d8809040e25804040c2c0b20b19840c40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 119449460 1250 119448210 119448227
    0x60f04030821070c0302060a1a040c1101050703022b090b04060603120915210603060e06150604030f0303022511092202030109060903081b0a0903020f01090806070f 72
    0x49103004d04414200790b80296070340001071f103294180360700d813010b655292035002548c184c030000090052115080040c00604a0413111050304e80035401c2400085500c0d010b40229010725103003d030f10345080c0d42c62903024941d2103010503800807001d03228030010010600800c1b18138001e901410b000150f15156140c080c02c140020b9414100384000e0400402419075000a00084c08042d810709441e1900601618044416a429039030348544c0703003400102c140f041070b0f8040c600d103500344402c86000361600d2092603000b414003080d01d039000b9000c000500015000390048800c2911034100581082444210f03410448402d4820381180c40110b01590240039207482126002001990300020600348607030642c90709541000d07210180412200000110b44096108642e03050300981c04020201c81440d000309050400d5070041c440c03000b0020488400c000311411107140c00b00c0c5407501c00300c443c030355070038450481d003410302441c14000c030700c030b4000b03654581400901d201e440c050b079480e030031440c1d51200070700481e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 119450710 1250 119449460 119449471
    0xf15090105010f03111e1f0305010504061518050a240e0a1e03170c0f07060203090f01120903030c140405090612120f07060608010b0906060f04030821 66
    0x941410003040485d4011004500d20501a5016900c25404081d40f2103050003000c6103070303005404001045055998000f502156144607501030055980e99003c00c42a9070050059280304409a2002a8010b000701d080041c5030781d07002d55000d00d8656840c00100e41d0030050b4001809140074400007000c005074203072040b080b4101410704240e805148004504880d400d07001c5c498070020139410f8184148111308840005560203280204075441c0c4465a01050708a260201c0c0315108104000c6048040819101b051f256294025820f00b0715070801c00440088110b105c03414003681c417403900c040010a0240c40f002500a44000c0b482c0400c91400901e6502110594100d12205110034001c90380e810b1216504003078200c0300910b0444411070403d0038040e10440d1000d844000250901400916001400400d0b000b80010009103940380380560a850300000101e6028085000090451801d030000d0312121f40114046810192283e81d0744d00c0c103500c65103016003058035a464844648448a2166074484c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 119451960 1250 119450710 119450729
    0x801240603021303080c070503010e0d0206090a05100c0306080312010f060e1f1704030809060618061002010b060d0f0b0d050709020a030207060518100b0307170f1509010501 76
    0x41018043d12890a0310340802010200002000c842c0c8840c10080d440c050480100204103071399220b01c1c07181d60350041c0303066400075004250008501c0003010800d0401580c02c040070b004144000d40e24100101440201c05052581d5402c0120b80050108003134005542844c40300d17101e55041c4035501d951007116034481c20130070180307102081c5691507a555001c4404074640302000800403014068940c81158102f00d80c00b0070400b0100014140e005d000103009003a07090a50341c41d40c940b0170074003c003641409818490800c078800840c0e06418613920344100c0c3c4c222031000065815440700018143c3c2d100801c1801025110520400c080740300c0c3c803403c2d0b202d5404450f441442440b0360385150700c540c42e600c0fa200400d98080b400801c0a80203404507140f030b50303000008215600c3c183d6210710001108488500f40b070721442c000a44012087d02c02d94840d503400600412a8501e070411104056141c005440c0045c05038011070300e080c10b020400b801148020302d8400300e5610b0300742241401c40750141c0c001240c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 119453210 1250 119451960 119451967
    0xd1a0f0105060a1b050111120103140d0c1e15060810060602191a0103140f2a04110301090905160501090b070f020d060510090506030c040504030207080124060302 71
    0x1e1030740000e144651903042404c007900c07081c01401c2013401000c01000340708507158005041c0c40c11040b9001c1e040d044e0382c440c0c40d0101e80c080ca0407182644d9600640b002c2000f2400003400580817803c0080700300c0164003104150344994116039507604081c034076013405d88000c6480d1710051204690038040d0410211018804101c00c03031800c0740c001d56561043c000c48811000e20034500041c40340003859108040c17615180700c045135950b40380c165014131000124801074024500404210714000c90485100300d40803801c8100744c40e002d151005004507075138107543e006540b2281c000100345680301540c028000c441001841c22078030f0500b18200001420121402d0300020420311050380c00c440d250050b500070310441619405240b40038030300c07115081806948404030a940d04100b21050708814030805a0903a000400359403480d2400541e44203a07001641a0402c20014050b403c20368012a031240c007d10444151a170740f180d1060854480c0008041000310f420380c40c030516542c00d034104c00100498a8114603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 119454460 1250 119453210 119453227
    0x91203060a2105160302010e0405160503091906140108070605041202040905030c0604022106060d03020705150703081506180105041a0702031504020117060d1a0f010506 74
    0x30785850354024040c51079080c03030140054154070710302c00d030281d5405030440f00c1000138004a4440f2104520040b03002400300b0707201c1c800505150050314043e85070081240d101c2c1e4080319090f00c113030304001c00c120034a02c1030060340c0040503010001c0841e1b55000b600d0004c0c03030516601001400d00e005030401e06045c0c6c40840700b004456404011202211404c1d0b4500780a81c0b118400a0080d01010a000d0007520002c90082c04442d40800e900703016a1007140c0d25103d800542c60462865800034400040c0c6030031050000780d0605008411035003243c441d2043d0f030655600d46000443c1d0b995001a400b008100c0403c0b15410542c1008055411403240058004051401c0000500d103118440c0d00162081001020750410390051041c0d6000e040d02001420000c0c510200520300c0d038200b607100740e20901ca010080c810160100c641075004540607900c11481d140035104c041c4c0e4121000d0620758001c6150783c0c1c0100401e1180f042034800100240c0081c1030390a0202d00c401001c081a0406480b42c0404c201620 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 119455710 1250 119454460 119454469
    0x6050111070614040504061404050108010c020d051602040204060503070e0607020d020d1505070e04232205010903050901030c03050702100e070f09140702011406120a14010509120306 80
    0x100b1200b2500e4019441000c030b4a560009000e6a8403964026040000c0030032030090130300704000141e0043d01c04002030f03a0f88a420a013661082c03c4000050f800c1241c40b046160302c03620040103004880d00d101d481500307440d400700d012a4401d6101000042c008030912041a5028910f001099411900203040a01ba0740008015100188009103d02c0480308102c04200e424840e480400b131072401c2c1003006150110000d0600845480710610682c5003404c41504601190002c0702e0740f101110711594030355200743c4c0b11403036120322813492980c1c0f000a1400d800043c4090003415595446030384c440d80c452503004009029a505081d6003010b05061004100350385500080d90030100200240100b03d1a91420744182401d145805c160b49018407186e000c503485800307030000724110140b140003403001e9a0710402242210740342c071100c4000740300c3c00c400301ea000c1c94440741e10b1844201200c02d0f180f50b04150313502e114000304110640c02460b5101c00400c01c148400b40020125828100703095403070740c0390200004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 119456960 1250 119455710 119455723
    0x30e03070c05150414041d0a030e120303010f0e100306020c0a03030e0a1505060105130e061206070503040f061e090203010c0c03020a060f110406020f1c020c0d030318140106050111 79
    0x14046c1342e40d99480e82c201180c105070141000c43d500103646c2102031a0400500002640610b28061011805010600c89000089a040f104c0c46940c20f0941c0f400d15440e841c017008041c10000c5a2010b8100102c08034050f0310040c0041e0038030b90002c002d0440c892070054142c0365039541120301500700d100c1d5200441c00307104400b002c46d00c19520000f015500c090042c0c03500d001d0a0000c2480d41780400000c140c840701c0150080c012300f422204600007034040b0051130742e1100b0031280ba0000507001d2021500180c280f1383c0e01c254081c410900440d02450140e440d40309502c0e44070840a850780c40d600003e0a41c00d080c864108207890a140c0440f0180268602a65800320520000e18540d07440d107150074515410b5200003c4010b1030081d0070740d038607a900f40080d40c6030305506008005028400c81030720744403d803410782504d03010607130040c0420800c020300300001c0505400c8140c0c00d06841d14049080c0c0402c2e00e00340382c5074038440c0030071004076441d100125007100c0d0150441c03410b001c0300ba841843e0859000628 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 119458210 1250 119456960 119456999
    0xc09070906020c04090804170a060510030f0b13120c0c05090105030a020904050c03031605060f010f03080703020c03070f0305010f1a090703110313020117010b19030e03070c051504 79
    0x4201c42d4940d246c40d07482e5120b40d6110f1b149010024051a2280001150050f0141d0280130240040c0e11640504100001584002440810703549840400a011126160b40c00091555400a841e0060301e85c40001440c045503900052601c100300d004204003a0400305c040c1c081a20b40c0b414960619001ca540c50052180c041d10404240c00080c0801c2010810f5a00000002d0140e036261123003e81e0101807881011000c0b9031500401c80040c0d0030500c50b50f10241260515590102460b1440e03d072008980d01c028801e0741140545510144191020080c25004040f142080c2000910b10709104d4212000030110000045c1401545c8c17a0a1213602e07461400b82d0002c4a101c14940c4480307600390020050307600e032806154004805c20801070280000e507410700c0e000382c07503100100d030031441c1c0483d111100b40030b0382c40382001c05c0c448440400401e140c1401090030b9401c002561250320002d052460b0003040c0201c40700c00d001c45081c0000d0a00c88158000c1007a0f40702a54105400c0007810560170340071810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 119459460 1250 119458210 119458219
    0x807080a0e03040b07030503010e010905060a1203050d06080d030e030f04050616150902090a090f0b070c08030405030408010b0d1a10240f050708070b07020a02030303090c09070906020c 81
    0x30707080d050090040707a006200c080c2200b030f40d40c111440c1c0030341290003d1013840080401c0710000500d1072054010f00d0312030000201142506803c003219000d880a002070180c04000c010302c14241140d8583c8a4a8041c0652000500a82c0c0f01d07240010240d40300d0281410316900705014036203409000001342c4060700e004542461f00c80c00140748a80042c91115005407101c0600c480c03d082854290f8000036150b8003c1c1d50b142000d5030740803110815a04c128900800070110078090f40003103580c0d440c0c215001a45403070102915070941c0c6910105400559013034505030000102000364035401d2084e0701c08071200703880039201c3e50901c0d11490403070100900f01c06172a514101c00500c84810075808600a450031701181d600071101031008080509179a42408086103070388806140480c003550689200c150721800261a0403495542c5d96800507000d012502580f213041d0425005a809101961045a0030001014000d0481c410406903c00242910f424401602c0c41401b0380b960200302a9041242a80c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 119460710 1250 119459460 119459471
    0x807050f0303070504060f080402010e010c08090406080c040b0306010e0705070303110a02010902010f082208070b2410051206031e0c150c0705010f110102030f01150807080a 76
    0x9226041a021054161030380c0000020402c1c000d8000c406041555040d40e41c0310030303e8a21010503a080c001c1aa00a0301040e24143c07110304030743c81145004045803180c00010709060a00c40810169170154200c10040c0e0004042010300e810140314401103a58200c00a0415500d042072a00400402602807401c0142c00289601814000c1e080303240e1200c4d64084a41d0344e00b404000090003040181d038101d00083c0f0441d030485686204410b01030250140340020654410200004440781100040c11540d86a092080102003041c03c0a06442515100c4605410400c900c02c0e602e410015941c0c0d4502c51f11481700322040c1d060348241610020704001d0400e0071592100c1d00020b1402c0fa4007440c64196401c07186000c00102004103070814541c0b0141d032214070040007100510030602990719880340c50781c00078400700505c1d84100ca6509081c0300310709140400100b9440100c2c266401120b01c58180320840004018410341c0b1034681020482915242c29039003800d50000300b080a02170641207030b103610341 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 119461960 1250 119460710 119460713
    0x605180903070c0b120714030a020c0111041e060203040b03040204050411120319030b030a120c080705150601021c180b041805070c050319030e06040303090506070e0a030807 76
    0x2081118010b641010031080001d035070340402050340e4818001001001c413014041003400b4020b0002c104022044807065040d6600c0149100083d000108482099900c901d01540e44401d05c1004001600c0c03040851500c42101e003400e140240010380c0301104552041004000c5410145c0980e030b0415030444001c0b450761210b0410100552013010f025030320005003030010b61341e0716000005200c801e041c0d5843c400e02201c440d40650032a1004840c95425400c40c1071200c2c00180f600c0d140d000e49901a0420703036000c114984480d28540c000900444041c1d1050b5142c801020704079602135400f07a404d20080c81211031904100c6151060b43c1c02e42412300010340508800c42d000303001e02d4800b90460900154645640da040d0100000c0c0002108401900c1d00c004a4010307841840c1c07042d003981c1c008000318070b80480182c124130010071040303034441059038518855080c980d007409111702490180d54080364503052424814180400503080740180300c85e841004040791101c44e1060200c07504119850b1701c0d000c0a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 119463210 1250 119461960 119461963
    0xf0b0f07151e0b280b0d1b0201060f090203010605071b090f14130b1504150305010203061504050a120807020904050a0507060201230a110a09050108060406051809 71
    0x49080b0321614807054407005906100310751040309a01030454910100c0028076415030005603007603590b14030804051205000000e8194000c0485004030350001900e140e80312198103c1d4042c0e001a000180d4440700200203c18010140340060124542d0440c07442d49001d40190640c81803001c024a00d01d251704524203142c05100c4550010203c241c014481c0036a640d40000c02051020710301d154400406010408061042a0440c48913600003110400c41d2900c04181310801c07010b640301d50303009840c2c03030345211411181d0349004003c620034030000d612801c0032020001c4602d410300d50035454503400d2000f0050340d502c40034124100c5201a840300400701180c1003002c0b5921807044080d41100711541072208100001441301c003514040c000f52440281c584100324280d40c241c1014007810441086e07140103112a882045412201d0743c640018500e0707900300701e01031582080f60703100085020051f0801103540c0100d14541d201908440410039603082000085050070900040121841b440e400242072180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 119464460 1250 119463210 119463221
    0xf010c061503020310050106020a021908031306031a010210020f07060207080307021203040201080402090601020a120206010611030c0a060507050409060f1403010e12030c04030803010801060f0b0f0715 88
    0x100094240201c40007551207000704031080c03004034024450100d070310010310140d12441b810f0310115406001c40700d800b6001c01c180720282d14405502490042d40004420b03800700300074090300d13540e0511500728600c1c005002d401c544500e5101600720b000f85008440680c0e000c5010b00007545602c200585500c020300f0b03210168014907100502c028400940e4200740280c020240d4445e185a5084070404034141000803650302050320000d01180d0520045030051030040c1c58607a0008062040714642001c5d91910300d0251581d408240241e003040b001401005d40c00200c020402c1c81c28802585000640110682e54150440307024041903961000302da542031080702290010110600140030b0729440b08612031984000c1d119001043c829081c040300d1906040c0103c1c1000760b2010041d081c5480c600e01c42110950000f060b45500d0070040001100042000340594044c0903210000200b99042c04101a040104ca07001001d005406001c84040420100c04443c801c0d5070104400302c60210b4169200007504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 119465710 1250 119464460 119464463
    0xf030608011a01031d0a0f0605060109030f020d060e1f061a0315061309020a03150b0306090901020c01020c071403121909090903030c030f060501020307030e0604080a050f070b09010e0f010c 83
    0x20f80c00400050000742d521f1024524010302080041391a400c00540d81d10581d48001001d00404004080c00351620280710883c15000d003d01281007042c85407901d0a089607078102100b408492240c41c4804041841003001400d0000c08001901c0c282248004003400018020418042c3c1482042a2500c404c8140d881642101c00c4c820400f074bc642400401a4004440320000a49401c41c842070160354581290103c5446420031840e580703421041c000d5400f0010000541d56408015058414409100804020340c000015060303981c10301000e000d40c12118648107200340c0c400c64014403c04c2d14902196007170080006040009603024401b961101c40584c03024010310720b080021020325815401507001c42d12503540412044800708400d5048810500030b15005034024882c0900003030180c003601808140003410281081c0ea01d9910601d0104e44210844058102e00460014018104011009050708080460504400200080c20194111000c1d1320a10f07240d00303103501076400b03801c0505455 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 119466960 1250 119465710 119465713
    0x1e04090804030b0405210f0309010908030c09030c0f01020c09040311010f0509190309050d0f080c1507020304080a03080a0f0f0213060207080c040b06190f030608011a01031d 76
    0x107a0381ea040409103044103ca0580d558029007403641460803400c3c0030212034071051148181012400c4503251000c0d0002441901c10790f44c1c901d00c800100f901000994400c1a0760110302d0394501030901418101380f0f42c2c0e610746008050010110354542e8000c00c0d18640c0341c10a49002c01c26541d1811700302c401d00389078109600c45510385041c858161480c4d0700420301c90403110b000c41e0500c8203545c07a0b15410506c5036030003600050580d5800d200c1d43c80e040525264081c010380e010700c440d051544a12450b03a03c50b42e900e20340ca50260368504032842c0c080c24030303903170100c810300265051030f14128203d80c9525111000508214210f000101d03810010313402100c1920088104010351014401900c00960082240c3e01f803060a15400103001840001d040701500e4256015003032103c101d07030500002d041310b100c2035540000d00340040480e100b1100c280c03640307243c80ca44e1440b405030064030010b41241d850b81c022980503410702d0024031038032103400c4869030782c40c20a10300025060345240040117200b180700d681720000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 119468210 1250 119466960 119466967
    0x3011d040201020a1b061b020108040308060303040f0e0912071104020a030e01020a08060901080a0528021e0405012c060604090e03070524010909030203090a120b0609061e040908 78
    0xc60f45c88103070a1080d03072200e850f0114042560200c0c852141ca8080c8001c0c00100141d0018000034402c141c619088040030302102e007010b4407045160320030050358000c40c00d100c004c0010440419800c00c0420300e020004c5040e54540402900c07134911100c000e80c0c04500560300014040c0d0168460f0340403600102c6814021521200f102d0001802160151650f600c80e040110010800c4070001c41c0c524080ca5029008044481c2820811400440c584210b00c200311116810780e000768070744c0d070300c1c280011500307c0001454450340c03010841121130681054001e04c00c40ca20402003400c0c8804000383c2a841c0c0c410904456661000158070bd21954100094450600d01c041d1040b4500202503c030007442001500c00d040f10121400440303181341c00d02c080020500c44010481d001c02c686c0042e40c41c50003407050381d203840d038890007003a0103060035405113030b22905055807141800320000b071581d00b00000711900d407468102200064520403402d242d035500b52507030500803050396649600c03060140768400072039900d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 119469460 1250 119468210 119468243
    0x6022101090b040e010c020c0d052b0809010c0503060607020406050a08030405040506042a0507052e151802040504051806090609120a050c010504151103011d040201020a 74
    0x20300a4074030301c103000c3c0382080146041e90300180a04100310300b5503801091110301800400c600120300386401c0e5030074020b5003011042420301d07045000e03030503c9041c03030701918040303c101c002c0c08000020306e1074031680d24007807103010300941c01011282c025000720707451916548140001401800c0c039921056000e03680c490f0020f074015021001d84215241260200700b565144805e220640340894154180401d2068140740004c100380c0203140240c0080c9011818400d440d035546140080d0690b400c042c4003514100d0340106510b01e02140e1200785019014000002c903e00d544120020340d00404091640c0245044074030004d40d0306540050078010014440d0742400e414491045604000c0109140640c0001840402001039103a000c2c0d500c900c01403d00d081030709040c0034550880380340302d401c011040250080a20b0b090103003502507802090030410050902c4001022607180300c21450107807900b031004028440342e005880322050b0a0700c20072112039490f840101d0412020b26401080081910074092 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 119470710 1250 119469460 119469479
    0x11010f0605130213060305040503070b04060506090a2a180e0601080f040308060603060a081f06090c050306100c050313090c090b1603020708072705010b0706022101 72
    0x102100c8040d40c02421112129a80b84140e228003113403020700107103041d01003043d035200760700240d40203019000b5a41054182c3c2e4583c4005c040944c2c040d6142d64a034003c0c0540c44c501210f17035a07040f1480c410104004c2d401c4600701d0401035000d480605590000482070746016000741c280d150360aa1401604844a84130a200350b251001035500c0c0c0e00052109000400500b107820340280140d415440d0700340b4540e10501000442d0b0300041209400288001001801000411468203080a0201c04e1415003044003200411a0750551020585900344200b103040240c2040842e50022004d98007500c080381c400350142c0b022400100010020b110001d03034226403031740b504040c4064400c003000901c400e10000c00201c90051081c00ba01c000582e04201c0d40341c0e88e010f17101d0303080c01c134503c01c1c0160385025503500000c0381048481d50100c9040031034404042c051111040203203404503104202003010b541400030008050142c0e00c801041039a0001c2d2400c08824109176560380c9401900c44c50f94190b03103541c070a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 119471960 1250 119470710 119470721
    0x40b1314031b010b060906040b07061d060601030b010201020a090e0c040f0f03030212030601050a0806030f070b0c070806090d200318041b0e0d0609050f0307020109120804031211010f 80
    0xc096511304903a5650a19002c0f048424500000301028102800d000b5003103009c4d440030f030b001c42d20f590fa00c043c61112441b00000c07002111891801805484c5081400502034550460f841411640704000c034040c06c64202c001c9009a40e40006000296a548514080f03e44105d82060598505840000424680c0c502c00305007620310960170b8501c51143d10341e0b9080315000503220349000c1042803040c00c04982c8038140b91540101c008048072030041000300d0043c1800c2803600006030b100030010740121524420400c201c01030840c80020081807500381c031480c2c0c803110740c82c0c884000c008803842c00d001c0c0c0505651015030500c4000b0203903aa00d2000e0721840c070990a00c00c160358003071401c1030b100f03017062480303107070544031070600c1d51035100a03510b0304010080c81910b0000304594003581c0d260700402140040001d036491644480c01107585000900014081c44c0c8190702c00207a014400c2d00d0038000071940003c0e03408036035003c0200711840c0da0b00700c4240d804011130840d03005150f00c2c060526100381e40a8124 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 119473210 1250 119471960 119472007
    0x2202061801140c0c1c060f0203061203090307090c090e010f03120806030a060b0102010f06260712060209040b030607090303090b0c0a0b04020411070605040203060f040b131403 77
    0x11040c28001c10501100d039030282481c084444e40040c1c00050050801c00c503c000c08560000303203001c2498a40c0d41d00c00440781b03e410003225065000c800c0082c18249121940d00400c00300e0011800c1c80c041000003503450b1001e02444101e80c2e02e5000c0b0108581c05941000064105070b84a03000543e10f070442040303100b1081c807041c0e03a040c44c1100c01600040c01805618002c4001030082c100480d001d4840354040c1103440c6090b81151740e110100c0701c603510280301e0030024101d41c12802141040700d0100307609844c4507005980007900000d00030421408564002000c4503442000580c441180303200080042540110894150060b4810040119072000880041c0d0b84291101c2070502d48480c40107c00f40a040410304a50340640030a101050860700c0e950392041c801000460070500b01180001c0a4110040844010f5107460601045180c24000c441c5c7c4548492500f426600d0181c580c03958564018019800c2100c254405c0390500000139103444040716a0001c030395940342516922014426034104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 119474460 1250 119473210 119473217
    0x303060102100515010c02030f010c020f0c010906020601030b0423030a020708010608031b0328080f06010c0f050c03031b07050a0b030c0f1c020405010215010b032202061801 76
    0x84262401110740f0034607010f50741c00c1c0f41007250314101d0b000540362a0303000501aa0315104841800600036024050b049100782d41d6805032400c0c0014020f550b14200300303103085905120801c3c4051003026400900c40c0d0450750001030f0311400d81c440341000c0e045c8120082910a1042924841003a4284000300400c04141640d0803505e03400d9485403e00d08880107401402c41c1c03904204143ca20030300171420b00c0040561003800390303071510fa00c5110409000c0040640c5203102500d0402c080c56164021100540c412400115005246800c10009001c8041ca001c001c00c0100007030b80b00400c0c010100003013288888040d04881d42d810040d014807100f0612040722101c03520880708049018100601c0803400c840c00d10f00c0721400c58031041110580385d004910b00f10154002230007c5250550003a20020280240c010010380d59414107000900b01811605152052880302004001d9281901c1c02c07280d200401c5443d4044140c68044c1c515217200f0303405c90203940300001042425540813032040100c41400240c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 119475710 1250 119474460 119474473
    0x30204090221130c1202010302090a1511030307091502031207030605030c03010b03060604022d030a0c020303060a050105090a1205010c031d06070311210106110a021e1c03020303060102 81
    0x4094081d00740d5860000300350110004d010000702892031903030344010b84141405400e01000c00e012400100e4aa44488a00c0254058601d54142c220f540560083c01c50406980f862800c140060721103e003d1069414001d0005010b443c6a8800d005403801029803140c4010f03503003004200280603190500a55110740180e00030b8000c0c07490140300d0440071801c040d01814442d500c80d070070840250403000c460044580596041090321701000300489241000081d26070703c80c00c10806040840e080c0700f007400290760040041c0005136031345040e0541110024601030782c3d15180513001c00e031489142d0b4442400d410000c1c400c0e2041110640100c0907405481d50100f1021403101e0401c05d100110090039692604030f80c4c0442c0c0f00c0c9220f41c00c106134807020707810f079140f400b0794200c0703d107a1128000078040e00040403035005103c0164015828223005204100130015400950001030740b82044040550110000e0541007401d615080246200c44100340480c05003002030b0f045c00781d00ca03881120304a00600904 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 119476960 1250 119475710 119475721
    0x2010516050918090106120f05060a0b0105190905060f0d0c020d1b0623041406010b1206030f0102120708070c080406050a0c060c17010807031a07030204090221 70
    0x224161202c0310030041c100c0010040781901a400c2d03110292070b050865490b01c00c0803482c0b401c2c41074542401d600c03c0c0820414401a400c0c01820800041c00ca4110141042e020b405541c0e03011040e80c10300116002030744036010300f105003030341c410f951907020301d03003207600403485000808526018000901030008244043c0221550481e02c0302c249480017008074144950200d5803c401d01051301d505441884000f07400701200100f070f1800c040784070841c03400840c59010401080700c5920103ea215038180020403455041c1118014940a51800c400340d2002d1a00003071415a004c101b602c0303800c507408000315680c485142a42d4090308040f551203010541c080c012641103072087c01c3d04060260070103286414981071000c211000c0c0e00120300c0c00c00f00111314603890b01103012072141c100c05814a85840c4610402060300c90300c1030f02c0591195000b504490410804244070070142094031680484c4154030360b4405078250000e000e190800150a03101040014182c1580f44103101c1e5122080260f00955960 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 119478210 1250 119476960 119476967
    0x20a0c0e0705030118090503070609061b020c0f01020a0c0803030f0c03070e0622080c0a12020f04180c15080105030a031d0103060513020306040513050a020112020c010c02010516 78
    0x151030724800142d040004105940312104c181c50f1104030003c012440d040907890b40e40c40e40d08103010960f1955a00c0022200704000d034031405550b80403100070450043d901d4003029407510841c41d605400380d5000e4500c84801d038800e0049240c05076001c100c070080c541e01c4032429503076500100c0300008034294050100b000400c00f60140e0b445210f040da91440d080310300005103c41604082c0303106600d20f45040d180100580c5107030125002c5c0c0482c200a00e0407803005010090301ea00a07034064003006448a0485000d40c58032150102e0164060300c0101d04c0c2d00f20148004101c0142d554060075134601c4070000720b80d2a50b824070300c1c2e04101240d900c000190341c840d0101529141c40c1000200841d00074216071996621040504400c440c050400250403640c1c1c802151032000f0516072500510380c0002000010f00d8180300d910380000094910034003244541c0e41c4c071540c544c001880607060003043c0140a20051041c4c040300c1e00440250006d102e4100504c5000c0c0c0a4802510010310000c28030640014141c031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 119479460 1250 119478210 119478239
    0x51003080703030903140304030c17040506030103060905190312060b090108070311040b161709031002180a0e1504110d110c0703050a0611031005060313060606020a0c 73
    0x40148105240605682c1e00b80c2c01414000002c80900c4403070b40c024441d510f8101c010b548214002d465940c01a200c1c0c0c54020425660b682c903d81c4d04030001c4c00207100780d449102c01d43e8152503205100064420050070a20b18107103551001c82a61007400310440d0805510402c100f00c410f07040031061000c507490b14040c8000d4040c04036402d000859003000505490701ca90080000c501b1144c220b00d15090704c0e0301d952001d03541300850100d040d041e141254410001003050440058849445550400104000098460720714004010040f60045028210810b01c55545d480c0c01c0c20052498210b0703a612211082500300480d00003c03100c00040c00f82c070032402c0900842c1040382090b1500b524003000c1d480c0400041142079003460031100f05100520249208022810240d40901e0062040c1816840d148050b0f900d204020200781400b8400c0c01101c0c0d203a0082c3d130065030b40c125050340e02c0340d40f0303242e00708005d10620034050503086c10181c0004085030003046848059000f82c41002150380c035000703034000140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 119480710 1250 119479460 119479463
    0xc0105090607030f0e132901021507031806051911030121021008161806050706090b0c09031501120f0f05030408030a03230a110409020f0706051003 65
    0x10886040004d10444840d089014030781005c416201c0701c00b010a50500c1403444081170a60f58030000d0090300a85442c2004e00c1e0140d1100280b0b5840c0a00000d490321040201c15615160500c0410718007800ba4020401004150448400100090500d00080c0005441c08456054811420700215915026162080c0960050545143d18045990134400c840208118822548542c4000180d41d00c4400c501c240c07a40b07650304400340c207081e403066071204000c950f01003e10001b12039001a80344c40c00c01d00011a0320504003107440e44c2c540d08140025100c4c441008003001090300420024402c1c1402038420214180d0485404881d034810074640b00790b003806088011180300004000044000c803510544910511303000b41c551202d542e6980c81c50f08160010340c11074101081e00500305506205102135940c1a038107500c00e01206032000e100400001d031909855a4480c540720445019807000c480042004040071565102000c00f000c0041e04100d1084510904001c0402ea03c10021038419056a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 119481960 1250 119480710 119480719
    0x3040507181a010c030801180f0f05040b0622050705070210030501090b041a090612071502160b0d32010e0c0a1d0d0605090c032e0b030309060403140c010509 69
    0x60342050401d9908c2c844920100c400f164071181c1460002d0442e0147c400c0b02091000003042c8c03402c1c6494810358020b030041445001c0d07d550054990f41099031014182c072041082c80004468071011401c60351441003c5000e900817140210070310385d0642c9a032045040f5410303950200060002d0314108000d8403d0106a0f110800c200c410081031450205e140e1900080020800705002254040482c180307807442e48031481e9810416880c5c01000c1c0c052000290f0a46a0007101e085141051030f008440d0003010846814542d03101000004107400103043d42261030070045990b204100003400441e140000d00030101c001c0c15000120b0543e10000045c0c613400c46082d1a0061041c0c00540b64080f07101c29001c0c0307103a0100326110803c02162052055030302500c04040640b22402134107060624240ca140c0c1c580c004080c0108041c2d82048000024041d04100c0350000b243c01d14241001920714069403200590040002900100304002c043c049510400303400155090302c0180703001503400f80503003410b00340c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 119483210 1250 119481960 119481977
    0x271a150618030127060b01030902060403060504030c080310230a03150f06090b041b0f2601090c0f14040b03090109050a0803060f0405060a0b03040507181a010c03 71
    0x6201d05000307480103099000d40000354281e1030002c10141c1d102405502c0040456070303ca00f405016190040221210b801c1c2400e0040b00c0059010807070901c51880054402540c0754045010548102088441c203904071940545a007011500319006001610401320030f1b902c40e00180044003c40b04010b211b00000822500744545151940307070b011142482074000c96075442c85003114a982134450140544030024002468405c1d0f0014001120314151910041c85a0040150001d42e4803030f00390403d0380c62915140a125141540c01340c0b544510407804100711200342c0c00416555010340c49500b840e902659540710707800c00030801340ca02071196119401c444208110900007004c12a00441c1c00c0002e03400009248900c0761125400e007000e003402100d81e03100000912500d442c040c10580b100b40400c580400c068100000000e03a50f0485200c1d4080500c000700000303090190030b00544000b0001c1c10414050000d5401203c4002c00d80b454101c8489040450400d029502c078a40d060255545925003182 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 119484460 1250 119483210 119483227
    0x2609070303080c0c030a030209040606081501030f090f0615060507030f05090a170606011d180402121b2121090409030801030506010602030304050d03271a1506 70
    0x155140c004003580380f10003082006400030041000184803810302560f0058444000c002080140c903443d5000908100e5808180b0440101801100808290034200000c1c004840d880c503c0241580c01e2000e804007d60030120418800c1c00e030001c20a40d03010401c2910f80685492050325036019004001e000640c02010b40c2080078051f100404d14200014064240c407950303400d041400c100e4105200000340c00c1481840041e50700301d01c2240102031103403000c2e1585000000401c00d8005c1071003035150082100c401117010340d2919007801d241000204140d4106d070050b10b92550840106c00c420314082c03182980303c11401c0c1aa1111240c0d10358000025001600318180001c0e807141e0a0343c4079800100e401c100200d45030b03680384251202e2500c2911141a9507143d401c141d0b040c60301c168000015134108004000002e400412400c03c420610f040c000b4035400c04006d42c4121807022400e0b2200306009954407402d216960941451030740019202c00515543d6124816042e08402030340c40d08100288100342 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 119485710 1250 119484460 119484467
    0x70e2815090326040b0d05060f1509060705030a050c0f01050402150a12150504061514071b090504021c08041a090405010f0e2206050703090f032609070303 68
    0x70031841c02d6400021102d03503955103030f031083d5000b0f5110040742c8900151b000c9240c405406065800b01e000c1301c2d40ea9000310070002080c0c00d000303a060f45d1036400000095000c815a40c45055880e05904902180d40711030030000d014003141c1c804611020f44c0d106001d440c1520000500130f0602c925405090110079051818850032280c101105030740911420300c2080380c18403c1e610a10400f6141040744800035494082440200d885036049840286085150820141d4010100314000c08501c5522a601c103800e003484980d02c0b8130b0558160491001100000c0c4111650700402d0185001301c42d10b60320744000c60518200c00c50f94940082c07011101348020802900c0c0c444120f80300b00a4010994640000c1100040c107c0b0400d80145650498003141400502e2804000c56803054022140040e5519501c0e10500d071304108100080400d40c50b0400a4411f42c4240c000340925640710184200100344c038a0080c1c08415400b4408103110141400c0c1000050031801303650040b001c00c1c1c040c01d00f40c3d0968400701c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 119486960 1250 119485710 119485733
    0x409060e01411c110109060804080901050c070801020316030b0409030e010f0306082b08011a0d02040b16140309150d0603020d060c0201050f07050909070e28150903 72
    0x2503119043d6102a8102d0720b05181202e4400c1c82903903c00030004100d800034080788038035006202004516010031000440e50000c0f03c07148039090800350788400d902e800a91a043d400d4114844550000c41840781c04030401fa094444a00c150700c0500c205400031062004a4045c1040a0005452040e20200c1540150804d6076040d4591401190290b155403407039240010000210030103a00640c07902405481440d401ea24810941c40c000d2070300e52401941e14049001100c41010020f000142500750304c1d003560403203009000c00c401c02512841200041d003525908040700b030b41c03400c210114138012000040200c41101030018203406183c5215419800b05802100c8038048580d590f060200241e60360b487e10598030740c85003d02161050072070000070b0035610003801400d40084004103000e42103400c0403c1d40c903951010340324810b1030703038410100711480d44d604014150059981038511a0300444007145001070b000c0b25564440327140d524a911311102018003050000206910014000200e00c500303030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 119488210 1250 119486960 119487089
    0x203070308060109120c0e070c0201080c09010507170711060f0d150308040b0a170708010501080a1b0302070605060303130b070807060c030c02190b010b0a050409060e01 74
    0x12a41c40d440305e0040706104140c4c1c0040e1000c1d00c1009040105810b848019a4000a03d02d001c14800006900180c01190042c1140704003003404074070b106069100c0c10a881d001c0e0381100700300c800d0100035032100380260700510b0140d4a1281e5441015a43d090500441e041305800c0001c032440c0c0041c402a040007440701104c2980c0090195000002003204c0710b02030b1019010000725941d4484403840040c00e24907210031400202d4a40508200350a5001060b241c111202800c2c02e07103a0f9640c0d001198014a415170380d42c030b40004004094610164541c0c003904806c3d110f840e007040a41c880d0000c143d9a03014426480c1070050311030344140312809412010301f10441c0b0403004541040d1042d601c8a007641c0001c440d04000035510b41c00e15192950402040705014000c070030300a603405040c1c07904440b1034014001d2281d05000002e56030585131082c5c085078003c1481840400521707444110002e01008288034a41c01103525000d000e519848008001c0d1049950311946010b001e4403107152032901441c40d42 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 119489460 1250 119488210 119488217
    0x402090a050a06030606081005011205040302031b0607030e0f19020d050a0b06090a020711010807091205010e0d0f090306090206091306090e0a02091317040303020105060a0b090102030703080601 85
    0x10000d102e40380d54000b440070f885640c8000c40e0175810011300400c45400140751a15522280d0002c0141e660868822454149030f0309000c52983c1d00c50500380d1a5101c0c8280300317026200d503c16200080704000c0b500d28003035199030743c00784114201000e069544a5051506c0d000d19082074900504919202c6048100144090f000208800d2f15484007403c0289010302612041d120204000680c40c00311140c9600501d005030460400c030340e41d245d90303004402e044403080c188074130000800c0c2a90300503680c00004214984e8401e00560040c54054040c00201c1c03100c0c031076803040c060007004950160010405526565440c040c0d22031464581001a180c602c2051b60000d1082200000513140c980b102c102c40d50021401054040c94041c40000701ca06881c0940c60756002550b44030016907510109640000300d42040c070b14145240e09050343e0003051610980100040040d00104140d019086248140340480b000902540d4440c0240801e202e14821680143c104020900c00a4000c01072941c00c910180f5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 119490710 1250 119489460 119489479
    0xa030f17130c0803030c03190c0206060d020f0307080307020f01080105060a120615110c0306060604180209030303070903030f0c020a23060f072603010e09030c0607081e090c040209 79
    0x3c42c00d80c190b034020b171070900711650000200070509003815a184500d0000d00010080188003040003034881c003010741414418468100d1742c4043d540c9103246040c0048006059880e801e50b01e0391044e5880d400510308034000c0b80381800c9440745600a2104031704a400140450303240801c6a28200c03100e5980d142034912441e5101e502154808070400200d6410302c003601c6103030800c080c043e891031a00c494030030200d119030302441c108186a22100203035400c88202d01c6003000304a11072a4014040e00802d82699050710010080108040c1d200e050071007124000d4440122200c10100100d5150310490340283d0840d9130800100402d41c07030128004807201c10311107002248448807001480e0390703000ea08420391203031000c01c000051010561030b080c4000e0b2003400c1c0640c00800030f1078001c6540014030920a2803440e03200092030040d001c0c0102e500000c0500181c40740c514040d41d001c3e189040a0740c080030316180000c0d0700b410084090340300f24024481c1e1001007a90907500340401019500030544240c20400e800c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 119491960 1250 119490710 119490719
    0x303050d0906050403050702031606091403073c03030c03110c031e10051b03060303040b030c0406090b12060f0a0503030d0b010206070f0c0b10050d050a030f17130c 72
    0x92080500517882940c0c0c25941781c20030300402d407810079a0320152a8010b42a00b0410240b42c10248038030440e020040303000c500d12000d100090034034038160702046003c01608000d46030262001a0041e00d813200480e46104181c00c050710b128075451078040100458100c03480540441d0044070110901800d034400c481403c0444c0c80402e0901407a0604004500d120316000c03030808009020740080f050020504010b14070b803c1001d4125203221940b0b1144030b00001011808a440c10b000b21400b0340022443c45070b4a0803c08003142c80e035071003403003500c00107410b420000c80c0b10a20342040714480c4803070815000c04d90b04c5110801880e410206040ea5000910950006071501c0900141140a040d050300044014441001a0900c14010080720801400e070b442800001d401c580c00c20320310f5410590181e816075440904180300a910b8004982c05030b0044218810010005001c0c1601480313582d4206960b8183d0307000343d68101c003042c211888091044001030504006030280b40c045402500c0101c440344d584c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 119493210 1250 119491960 119491973
    0x203041e050d02060105150f0a030204080d050408070f1212030e0f100b060c06041203020f120907051c03050c010f090c030c050108010e0105100c02031c080f040503040303050d09 78
    0x5121084940e60810642c0c8216240c05024640c01814252008102c045d101303510104075210b1160589107010f008030350310403140c0c4130394103403005007040004584000600c1c200c0a0078036001482a20024425414086840c500c503c04000c02c80328210990310303d5604569500c000d500b4829614420150303110b00319124480200314000a885c6608060076020044208120a49001c00419800742004011107211a0000100c00e6482031f001552034400c4d0034600021006840741904440c00a20003003410300300601030b806250b0142065504680e1070f181d40d5420322408054201e00841a10030741401c00c00801d006000400c041558480001810500303170ba400c1c1c08a50405c4000d031b42c0d44030407810510800c01d4101c600000b81c002401c103c919503140c0068007080a5050080d14011301c440340703ca0404078011007000c0c0901342c0c000e091700c00341c41c41402100444040c0c205000b00144c42c01010480051001d1000b90141d50404040c5103080c1c25501d080d105035100c031036000c001c50381d00e200c510085040b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 119494460 1250 119493210 119493263
    0xe0c0d0f0f0f15141e0604030803180d120216062c0a0519030e0405092508070603050c0c060903070614060904110d1506030203010c090e0406020304 65
    0x1403070000a440400b42529000f15030b854030410700740d07a140c00c074240903002c064101142810380440d0802c40301c9005d6120007500c842c003140b0302c603001080440e02001300401c003005103208030764001401081c0c001d411182d0b95901d981d014100c02140460f807601c4e0300f00e803250300104443c40740c090041044410740d5890fa4100c07460720030b034400600c02007030410f8034403009030800c0030180100c0700040c544140941c68054941602c80d400401c00c003107812404d001c00d4043c0390504200f00b002007003048240f4042204984561501e0901204100b03189462448480740081400a540d900300c02032442a083c018150000c0101a0031520000001d12845003c12010000c1920804a8102075901d4242a14281c000e40f840020091850b085c900d08008540e00c40a06403540150001041f02c0d810f840480440c510f6480102e02500707182018030680040c1c0001e4111000310317842580200203110440074100c0d02d40da982d000e001e17407060520000c02c0100f14950040d5030054045c1102109040b2030181074028450b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 119495710 1250 119494460 119494481
    0x2181203040611060f0606310915060203190903080c0c010818060604090314070506040b0a1b0302070303021201080c09180c1905041103040c0602070e0c0d0f 69
    0x140005820301110703038040305906014a404001304002d0070405028114401d0045c4480c0c015803020505090001800412a1910400c90010385d09030804195082c1050724502900c600303141000c045624400c291045041126500d5004d1800c120306201541d68400c1f54a04d803104000008030040045000d1800a04c600c0302408014403421898030005071102d1002882e02116031416804000034500c085030056200e50100c0e0000381003440c600d030580b8440790000194850400100d106020042c0004000d070040d40110b02281d91a0307a0485103506490b06980a03a0540d842c0d42c14100c007280c000e40260100ea4801d04000d400e0030a0aa8650450a400d90100d40c03580d01102c0400040d0420160241d040f150001c41148a0500088050350f51a180c00c2158000d0001c0810064a94041883d10002d1315009009000e07081506005030340703170f030029a400c0e201e2510031381001a0103400000c0d0842282c1058804060903034486840c07a80c16008001c114070800c0e29001a500041d61a204580410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 119496960 1250 119495710 119495713
    0x903012f030a140907030b010603150608090a0804090605090c031e1e040c2d050f0f06070c030201020d051624050f01090f05011a09030712030e18040b0a021812 70
    0x11752642c24156803050040e031003001818500380308002c2c80100c040d41c92003568000d050110468441d40c00191615603a81d0000e4803842c004200403805a5064010001306c903c1101e075502e16840384907505407184400e60b4554850408840c512840d00c4046000c00e40c4100001104050004001c20000d4801c4048408441000341d00388113001030841d0400051844401c5201c0b2115091000042602c1e807801d03003c2c1505c41d0b4500035401156a8941c02003881c1c100c0081e0100751507000c98986081d1042003804124058003880c40d003803003203d200382c0540700b400c40d616540c100303c1d0b0420384074010303403401a40301401051a08201000c408d001809940c0c083c1c02d40355182000b070361504e00c480044403407240400304460f04001c01004400340807082d014150302030880840d554000381d00020b103007008541c8000c03806005112258141600901c1c0d144c0c41c0c4109480009000119800041c401001100d00a003402a03d0300801c0c64080c40e130303025002032001c80d031000302c1300d000050000754020440c43c02000103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 119498210 1250 119496960 119496973
    0x90207050c0a0602161809020604080a0302010b010c11010807030e06040b010302010e04090302060610020a0506010f03030305060f1e210703140601230604031203020903012f030a1409 80
    0x100c1c1040660b410050000c3c0c409060030b00d0b06a4007490ba03003042031003682403005020411880401a0754890300075254002c0110355126968606140c462240100c00e82c0594038004c4200e01d40c0d4051010f81007841d0780002c610240c01c2034800150703035001000c0c09100030540c0d507021242e51a0010018140101d0040d000038841d50304d9031000400c004076402001d8000ca0905294600080d0009605074020b035084400b00c4c1c441d012807000302c0c81c140300710001510031311607030000280b801072800400c0140ca0013a60203006d02d0359210f06110100c1340343d07110160402d4400010241d0401030701c0c0c5524442100410200030300740305210200f07008044000c0750030943c0107403d0400411560800003841400f07040040c2480e0740c903040d0301c0001741121100c1c8480c5120000040c600681d58034003200c02560380035200c4411042d00c0a0005c00a4006c2d1080500039860100d0102d0850504d206805104149004c600000ca4603c3c3d00e84000740c2000e40704441044e107400441c60744180400c05940b181c072206005080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 119499460 1250 119498210 119498233
    0x1050d0b040305040f03110a090c02031602120a0309090f0b01050301090213050603070201020d051303020a080a050d05151e0f040e010e06040614071701060c08120a230618070909020705 81
    0x2103400301503110302780651a0103202c81c5040c2d0003000766481c2a001d00d1100e800070045002141502d824245118146e009000c0c40108141c2c21078030010070399603180b00030040d000107844981c0032980001c154902040c42403004210f4014290018070a25130204624102c60b40d8400124046400607506040941d4000c504410842101d12800e94020809001c00d00c80341c115031406919010103180c0940050400a440245c0c1d13802242150001400c49008002902d88041002070050f0300e0000140700b00c120000b802040c140d00d51a102910380700800007060100110b00300001440e005545150a540700e11903036001c0030f42400b40780e1150340a248045039442840542a030302791801415074050002044921101c1d8480345000b905651660800b40d58142c0642400187c034016400005485d0020307600300180e07902c0700d4002c000420509443e0f000000220940b90300010f50407a001c41e00b203040405040001e50081700c103180c1040081c245080c01e107494030900001ea0740500030603603030343d80802c24a42 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 119500710 1250 119499460 119499469
    0xe0c101d0603060603040f03022506140309071809020901080c01090506030705071101110105180d09121101170c070c05010f120b01020f070815060901050d0b040305040f0311 76
    0x6900002250014030310300c0d0040001310540005400a4021511120200c0801d8000c20084207030b01d26104045030701031105000c6400c01e8a8900941000503500382a40c1480c400b0181030b24010f91501d0050007030182044018000841d4603403103011705540714103880015882d40c07040c050203030800102501041040d08005030040c0b80b00c0c1e00c13060181c070381041001315031540300d01520039544e4000e070b5603a05000004012104100074000038001c0354603003010300519460810181c00d0704031004080d075030482a030780d405880010b100d1050503021040170a250700015110b0b00503036021241410042c098440c0b20700108510102280c020182c0b401c0002c645e0144442003d03071200074402480c0c0b410510b407400000401d900490031a601720552980d96403034540e070080c4001e441c14211803045600741a41c0310109030b9509007000211400d0f0210401052050610140090687c0d03409441d401050308155034603100c85000410580c10440c0c10310000c0741c04148209500f008500610001140304042c00400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 119501960 1250 119500710 119500757
    0xf0d060b090105120406090b010e04060507020705180a02040e0705030709080109020f01030515041107030908070501020c0d0302100515010f03090b06060702130509030705061003020604090e0c10 85
    0x2040031840600612840303030f90041c1228100c40850070b0345210354035076240c4000a003218140060600407802d001103400110000c901d071180b0300036442440203803a0070300107903240c61083c080c554003c5003c2013801c0800c44c0c401d4680b500310280000051900e9502c80c41e460120000b5141040081e000209120209030b000385080007801c3d5000081000f0005980025503c14a101e0b8071030515441e000000c41d422000240c04c0307054036020b001802904200924240507520811084010810b10b5102162071000000c052040d5070041e0001c1882d4040c030340c1002041d840d1240110308501c83e515a1502d12141c82c0034642c018a6050b441c4000301c9114400034001030911002034040502d007241d0301011865480c2d00582142090341c009544007414008203819070843e802002d60386040009201d080040000100000343c02035094a4940c0c980142c2c101f0340f02c00600c0085d44c01030f004d10041c020404583d004d080a10401c60445080104c1c80011032202841c002e1104041809200c1c403101070710000485 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 119503210 1250 119501960 119501969
    0x80301120b0c25061506080105040e010e03070201030b0d1407051002010203070903060b0411031e09150c09040615080702070501020a020d06020706060317030121020f090411060f0d06 80
    0x61a082c80b080003000c1c203101000c0110380515219420b8180c043c045180d00c94908602e40504200c6486c0d242c00000d070101c0c0f002e226450003285802d605d904000018407980c0c030049071400c05140f41252035001100984202c04503d81c0c80710503002c0c6240010091116606405c0118014285180c13030482008900621101f0301019a401041000308040e0b10050031419260b0207040003c2c8034207800041001441d246031203c810940c0002440140000100c036800d042e140104210007658400a40613124a100c81e582c281d4114124089080180b454014083c6424013500000b04981d992500d50068500444400003051060f82401940350341880604080c0501f07000030503d503000c55002c1100e80c5031039180980348036400304a80302003102c541c124000554200000c0580c12240e405042c2d0b20358020300c210b540011001e0004e682d01d140820542505030740042408214040d01070a006460340010000c07102662103220303a001658815011300840114141c0e085c0e21500541c19400455650307400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 119504460 1250 119503210 119503231
    0x150a0201050f0708060d02010f02071802041802090307060c020d0206030a09020306062202071a01170c030105041709010908030d020903010506030705311404020f220c0507080301120b 80
    0x10000f191b1240403005541c1642031900c04602000040c08a040c02c400340c100f103000c5040040c0032680024030390013a005407102140101440d05003804420100d00c034080843c0e0b099000a08100700e0750b40180040064103001809140c4040026800209194011034641140c01d586c0c0c890b800039400c042282c103a101900351a80801d0f504940405040304c5242881090f080b82c001400c1d80c03c1060400c001184405105100c140b19611550500f0b011030200d1000c250718412070800010f98501405151f000350b80005511144621a11000b80590301901c00541840743c0007800003002030040005040c000790b54100182c50707801d90010036003921400f03400940b00382e00514051000b40e40b1455039100d0070790707062103030502c01c42c5080c911ba4565248084640c1c10700d141811402040d0500c035080da11482c4200e5a2020400e1b021081011610280c0050f8800360f141d840132524a400a5002070b40f01c05207030404504000140d51040495030090700a43d0082089140b000200404541c50b103400c40d182c0034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 119505710 1250 119504460 119504477
    0x706150602030313080705060408030613020405060403020609010e10030e07080a02130b0d0b0103030807030f050403200a0b130606060203190f0e030a0c05120708030315150a0201050f07 81
    0xd8025034074080507003c180420b001c145100204095038085171202d90384102036818500e041d061401103074000322082401380b00507003003060641c90b0501c00ca03015207070018001d508050450702402203070382005011742c0c18001074140190301a6107a003901c209103581e6550100c4c01141000d405410280c02c5e603c072040715030210b02114010b0340c0300307404405101c1146100043e01401c0b00c00040d0250344c0c8070400303003840405100200a0503880b0000318466031035520144060031036800301c0421521708982c040c1c0002c0d083c1e05050702c00b440300e400c0102a0310b480011a0085034264445601c440400d031512200e50408901e200c04001941c05440300800050000d14204402d4003081280d60b50010b68580c03c00a0354003c4403000f5008414800e54200064110340d5640a41c0c90100d07603405081c001c1c0c40c410545111142188030340056440e09482c0030201850440d16006003000b1034140c0241c4460f40710400c08000e003076148001d400340c50b000c490703035002050300e0602018884c0060b0001d40300104022140c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 119506960 1250 119505710 119505719
    0x6080d020c06030a11161e1101030e01020903100b041107080301090b010903140a1a0c0d020c0a0204020c0304210c0501120e010e01060302010909051608041707030302070615 76
    0x100d0055615401a9402c41c1d0303951300e0b101444001e1282c800c03600500da6000c14a010b03980710340200a00c0b8507208540f80354010310007640314490f2821524000f00000a66070348603405510941001040d14001c50005d4203180100c000a400c054801180d840c40603030701d00f4034803880e151a008950402d00303d1442d00389002040e8071a045240700c140240520b05032143c00e40c10040c0d00c518040740045421002c02c060340110345020325200c0c01407940a8403903c0c103008410b03601c9035089800e14000e0811801c494503056104803280044c4d000700042d100c60303000e00f50003000036031650700050100d0030100001d142e60303504004224040044028004905030701a11040c0005800815a03500340c2c0d0007420300c040050b12038a04000034059860009540b5400d0056070000407a05400070400d60303201362a070003901d0782c44100ca0822030340211060340924220004104c08107000f4040e80c0c0d00035005118051401d0b01c0c2148a0005c0d500a0030100c0029500207012803e02600d44594a805030842d06552900d500c0c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 119508210 1250 119506960 119506963
    0x41209051e150301050d020d031106070809060709150c0302070806070f09121a0604021605030d0e0609060a0c0207030f0c18090203071a040905010b070311160b0901030608010509010603030306080d02 87
    0x2c642c1b000340248000105082031500030700480301c030981d20b103003291001d06d0100320050031448151003125851103118003141c211406428140c0036541c80c600d4241d0581c82c510811500404444015001d500070000c02107456101409094401c0085071100342429641070002450642103038400503103201c0d040d000c180015003c4c500408034024400b034450b21512000001802482061040030705140050128070400034080098003103583c031107004000d824158481641c448070b04803038500e0141c1160380090786407000c40d070112031242041c1c4116102c07180c4a50710000007840ea00760907640e003200c001c010003c04103460444013040c41507007024401d401c416030229613629002d0160000020200482104a0b42c0d0f10003654010b1900da801030019503507403c600c1100d40e06c080c00c2a40020344440009044002c0082d100c0d81a001103192183c8040c904044540ba54201c02c80260425895010015240d0400d02030315000348500b100014005241d45001b8040700c80e43c6c1c0c0b00c01001d400520004c02c04640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 119509460 1250 119508210 119508229
    0x90c131d0f16050d1103070c051c0c12020102070f050102090415150e010e06040306050f06010e0604180207020406090b120706020d05031e010b180d0209041209051e15030105 76
    0x55401d2244e02c6403c4501d11401900007401413034042034011040150f0320368820448031140b8050010b48404100e500000d010381800305010b00f022078080c0101340c000490000c201010300c0320510004bc20304600d0b59401c089006800b0b0107a07407603074000c03030b4015980c50140704004030500c0d1103405610013840c0c015500d44129812201e24240008080c0485403640a5107020404034001480c03250340d5a22850b000000300000c2d908a00c6c4140c1060004945501036a5005500d034001040b041c01c2034581109484c21a0ac0900c10680f43c0341c081c02103c1c01a110303801924040c01c101c030804524040b041040c0710b4100d485030055012a4803042d010080190040b030703a084000658901155295901c00110b4118072581c2c4101a050b12804000111030218601820070703d0040d03035040005092000402084812800d000ba50100100f0040b600080100e80400e1100c1c8190238288955642e410001b0703a50302011780d0707060030414480c03054404c2c8d02d0031224002007281220f0046046504140100e1150003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 119510710 1250 119509460 119509501
    0x2703030e0f0406050a0f0e010506180909240a0e010b010503070c050304030503040b12010915050402090d0c0305100b03010207050c012105070302040302010906030903020c090c131d0f 80
    0xc100703003a48046440c0d0380c008001500d001703440a43c02540d6511041e201e0001031140740301d0404101d002142d185424000c0750150080d541e0f010301c0c000b031041c0401c0081180038201400b0f500c00c603041189a0714103014001003140182c0c1000e07809250004452081d1514460384000c113901d13040b00c043c4560f03001800d8903000000740c5040b003400e0b03025240503440e42c400d5401c00b404d0380c0b0010030001074860610004180c4d84640d0074540d015a640e410086056440d40000c00c00001c100040620030703410140c0c0500700701d10740100039030007802c0c0c0c680b10522030030060307001625150404034006a90000a0084400300701c07055008500d003208d16208d094072400300200e42030401400c1c4c0c080045504021500003496075011500700000c3c104240050000d44c0144802c0340402d01d48400011a503000707106000e52540c0507000780600c0380010040210005009100007010304c2c080c40201c50526050b541c1102800444020101c1340e1540d2010028404004203548800d4003441d00300040c00084102510802d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 119511960 1250 119510710 119510719
    0xe07210c051c14012403020a0b04030302030403200424050a0e01090902010c02032505060f03070809030c0307060614030f0706121b0e0414060a0308070c0b0a2703030e 73
    0x110000440980035201071220981d01c0030702c0e40b04100046400c5040801102d208032303281d10503990388910105040c0a03601c40070700547c0051000b00b000c00c6024102000c42055800c243c900404810b00140440e540121341001c3e00880520b29010b00c2c040580c44009402c045075060700291038100020f080600501071444950748034001041164002c1030b003400c47c2c550050a4035000c0740b4020035a1440c12555100003a5402c103c4000520750419808942c00c80c0329400006140d40d880200c1a501d400d4060300003207081c40304112551040c1c90a2001d0500d80e0711070340c3c0100e142c80c50b0450f04410b41c403621111074403d030040140042d0445000462000f02c5000f418038843d01c0f0700100c1e0000c01040450b82070031901c08103110b002c24040c2e10240e00703030140508807800c20002850800342d11040034103d40d0780d074000d240362006201080c1444081c004c0d06105070285005a81c4130f031040c101d0354101c074080e0404648031144200819401000d101840400c04150031405490350318024240d0040200c0c240c003c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 119513210 1250 119511960 119511983
    0xf12080f0409050c070302060109140f1b0f0c061f030318050619021009030801140301110a0302031e0402011409060c060403110c01021501090e07210c051c 68
    0x840c0c80310252001800c40c0e00c0c00704514900440d0703401d216844514104d0040c0100400400c00e0a03083c807410040110558100344150340b0300002348441d09020308141102d501d032403c20000b0214200040200c1d0401c10001358a072405010308502d42000540b4040201c002e0303010403034080c1034034441e40c0100c0317401d0318101c1d400709407004900108085c5074002d9034100c01c0003d510010034025401140d084241c1e0741c02c175540700580740b04c0e50301251003882004000591302401046024038015130f079038142000500001741401060b4128500758400410701000c66004000c04c640c112000d0291203072411422600d615030b10b03040d80001c00c114100900c80f046540c0c00704810000f03071900c1d8283c40d48000c04108a8400d410182400341840742444d1740e00d20b19200314420111594404a591410b0000755200d941080e403d000d011005410406a000807a11401000064501d92104903440d00c064110341c02c80c407a040760505e00e01450070750b00301c6c9000701c5041e43e00e40d003001d101c0c00120705d0417504141030804 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 119514460 1250 119513210 119513227
    0x7030b060418090308060d020d03080901020f031501090b03090705090a020d0e160503071206050703021603080106140a050d270305030108060702072321060f010f1208 73
    0x201e00854110500c00c48040340300e2400400140e10121486000741c4600b400c075030b038200800ca600c0d0303060f220003500700b200166000002030080b80a141c01503075070f41c000350802101d0b195292881d04100d5600c114903004161031205960440c0401010f89128100c2e01d00e14500304000c640d480c4024400c8a0081c802400080d0b07040c5075a9056510700689800103125149a100e0f2655840b04540e0000180f2a1038044c001080c0c0b0f80090f041c0704486112029904440b0203403950001410000e00301e40602d6001c00c42c9400c0c0d100380c50541103041d8030030345418400d541031a00080400c6400d02c1601d00003075080161440710780d0054282c4805442400e030201e500c020380c3d0380c50030580803040508038440700c17031034404000c241d04000a507050b80c0201d021100300380d680318003c1340e40e03881030322410015040300d0300ca1030285c01248028507491034010305400d000e15a841a401d2040324100c0306504c0c590007820901009a84200b1403600404416500c3e0450905005400542140b07501004103031000000702c504 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 119515710 1250 119514460 119514469
    0x611030423070906060e01030e030406020a030c060b03011407080a0c1409010c0c1701150f03020111030408060c0306120c0f0607140118150c08270a060e070506090907030b 75
    0xc06800071003c2880740596480010305120410840365010a0501c214400b0322840081a20112a900e80c002c100c680042e0b03c0c00d5500c03000c0100182c4000d522030980800c5900e00b4000e070010a2015147c500c02c0749040c900003007240c01c0280c500c04682c0d0501c504c00507803691265170107882c03c0d2050307032407591658000010b85280407458402405078140c81c0c000142c1c940310306540c08040710204000e001100031018400840e050f9070140315410202c5040c02c0c00036510078820752041c0b00010701120b1a2039160340300186421002ca514094140c00001000712500b0300d0b101d00e21003009101c0080c4085062540001c2d80304c680320902901503036000c140101445072084002010420840007002030990035200180038082481040e181c20046a000154040d0030340305090305008540e40b010000d460f40701640f480c0440782302e21450813040c2d854940d55001d2060007101989403050320f0009041452880e59420403205501c03841c0705541c107101503409616403002444d0b0200c081c3c0340002e0034407280e10004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 119516960 1250 119515710 119515723
    0x90109020a090e12040803040608070504090609050411090f01090f021b030408060106050a02100c0e030303190c0e033a0201020a180b0909060127030611030423 70
    0x1950081c4a401d00103000401a0f01c04040e246412007960f1100444078180c0c140d034402e620442055038000c2104000c0b0b0341c0f048428079080412880c0551030705550b54202c000751540c4c7d4000840841d510028082040302c00d942103030304030720141e402030410311303040c1e4818850700414401d21942c81e0300d4080c0f0002624495048521554110344c41c81158051070320b60641e40d4001d40200c1e60725202c1d41c4000f19125028000380c40c405a101d900604000101a1244001c0c080c032020328402d00c941160000e846583c14805503110700d100140e00b50b40b001c0c40500348820707036103152003038030038400b0308040c3e42c100d0b49011400028102c0707511100b002d50200c440c0d468055054030380144004024500301c210340d070340c0d064004002140c0590b6580c140180b0815000d00254102c2c4a0803c000e101001082c0403400c1010f0741561100e41410030204001410014030f034525a6601c00200115541d80203004010f2980304124208048049050540c58503946825440442c0c1d00324100c02c00e40506004a1400d04000e035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 119518210 1250 119516960 119516963
    0x160c0510020604020306090309090c0d140c09010207140109331d01170403030911060d02070c0f030b19090206130602190b070e060910090501020d03050f040b090109 72
    0x800419803403048009440b40400c0d60124401c1c0601c101140303907002c00100340c442c21200200756400c152620890340020b41e0101108200c015140c644182ca104c03801e4011034810415042c4660b950300701c0c41d00080c02c05c400f03600182007150340f04d100c074100d50740e00250030016101c1d1300a17842400c1548082040041945140c01140445a0203103480d44962105940c81d1721101d040a003c1c4c0740d0800401911101c9980300d1000f20034005800250101e0f11a41010744402c0c0205448168080240c020079510390000c15400102a00042c0150030040201707040001441c5074503c01c00c915003940d4a079002030801502000c0d0041500d0300e241d07403528055000c40001c50f0f0080a29941304491242602c2d001118454800940165180401e50034511003048505540c0f246d40c060b041d503030340c8109640c01121540d0007034100806001c05c0101381c03a04400a0000509074441452152826000a19100d0f00c566030008060401c400c0c0b085410740e0f03450491708694400c1074900e00d40d40d014036180c01000c00550 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 119519460 1250 119518210 119518219
    0x9030509060d0617011112070c0209010b1c0e030304020123030103110f040203040203120a031518051f0504050714070b060103050105060705070e100f1706011a160c05 73
    0x51529282c03000d03602020480c0c101c0d0b507101c038449004811081c202c0707540c4100c4640c2003108100001030340c1d241c2c81400d9441042ca08018004080d00c0e004900c28500903008412860340000d01d07103242c440118225034039440039030402d0060b16140350f0710548900028000a05115420040141c0b4019148000000d540d25071462a00c0390380d40d040a003051000162104d00a186680c41e03448141014021039100303607000380003484848a5001090580c0e80f0070b10507502019076404102d2071104102c10708070000c14829940e905d02d4002d40800900710f070005083c00000c560103100041c004010b000b0181e01315901200d0000786540d61601c20754034414000001042c540303000903a07030200020b842009018150a030390030840742e038840061122620400d0809040c0360f00108040003009a00008981c0c40702d5800c04040c07926684a00c0b85100001a40205414514800b42c500c40f40d401000402c2c0100f42c080031046036a13041c2120160940302d00703441e8650110141209006001304210305000801d0007a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 119520710 1250 119519460 119519467
    0x506090a1502010501140904230102040b0a0206040506070903021809010f050103081815070b06030703142401030b07030507140a18120203121e04090507020d02010501180903050906 79
    0x10381c02802003109000e180c0c9540100c5010304080d040c030304100303840b40c0d50000c080c0100b100c1c591074049004d02000f0090b030140d902000042002e14210700a0481d0300306680061059003414074026051090082001080040919081015a80e00c0351444000303510703003440020302e44903c84118054104044c040c003c01e420540000100702c00d0b0320041c010140c0070b10f14020114560300403c0002e441c003071002c040070001848400d002c20030b1000c080c0e401800080072555150341d203503104540c1c0307070002c000080590810559079510507090707143c0305801e00c2c1640d90604e1541c150785d81d40304c0e070110184c0340134101035407a0001007516006031407284600f9411100943c50301c000d1031000300b5004c1907400c071031780c074140802001179603070f58500220358045ea00a018200c080000c2190004035002006004010a1211a00c2c0303000443c1a0041c40a010f416001080314500054068641307608101d13044116894080100008114550852610624810702103440c00b540d0a0442d068099190300551142c0e000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 119521960 1250 119520710 119520749
    0x405030607090504140f0a11070f031707020d020604030807021501091a010504030203030901032f040509010608040b060f03030f120f060604030c05130e0102070f02040510030c0506090a 81
    0x501150303004c4505100340703040310070103006051041d11890000c0103042c012902d00c500940000c100030f0405c503901030501075a501e48801c2c12044501c1903001c500e94240c41c042d00469200c20f01c1c2d222015000800c441c0c3c05003a0003e61711000100080d0821184101003a1043e200f400380352a00383c00b45884406558407641e4100c014544020120600e580d001090700d101d50080c1c060341c04482d0020040c0d8108480100150090f10711004542c02c5503007691644040904150380020569900c24480c640710703810f040920101c0c42060300700909101c0405e00b0807002451802d4480d510800685081140208841c082450b501802d6038036181c1c128085003070b4524030203e1844c240300c4c01c040307600012030391038020034454a40704502001d00340300345401d420700543c2003013442c49512202161000843c8811038885500f240c10040088402c1070140300d42000758030f428015075400042400e103d8854614640e11451454140d00c5000e01440010510ba03510b5620100003200806540078402d80c200e003174 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 119523210 1250 119521960 119521967
    0x290a0212090a080a151a0603130c05030a030207080114040809131d10050c092b02180604151811070204060e1f230d06020a0903020114030c0703140405030607 69
    0x2510a107070116441c2442e03a800c1e10168070f011080c406c030080c00141c95900d8450b02001040c4106c0c1c0b065402802040f00040c1e50f807803c00c00002c146002ea80500015820721000313038290384400e114010000041000e00012603002070495410040c100c5580070004201c0784007001420300031b11080060080a02001202c00c000300f0175007450351020201300401c0c0d0341c2a982000500408120a8000324444d2903406c0c0074148440385a40030040c102d540602c42c00c140d0000340386900b20701c541844200c003a01400290305141c00781c01c07520b0203d18064400d00b400c000a464602c4c1c070405000c404036840786501e1203403d90100485455940291040c80141d444e082e07007428034027098400e840c101081c412811145800900010103503a0b26000040f50488080c5488442c41310010142e030784090310407041c2000603000d10060003140c506803200311460b455030002601d6610340350a5280d070f5020810801010074500ca00315080e0550505028050780b40c07a41e4551410b00030f5070405030301846100300b84480a0b40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 119524460 1250 119523210 119523233
    0x20316030605060907050f1b070b0703110708030a120b0913020a0909080a20010504031809110409050c040b04140f060909071116290a0212090a080a 65
    0xe90024000c2c0d448034418800361090840701c260010300140403d46a01802c40020200d0510480d800c00020f00c8031007056082803004d500c0480d094100244540030540c0010310100c00f01c010b14041c00d907880c5010001600c1c0d110b045989010004040c00c05400e15481c0d5100200c0c2007400340488469143c148030800d260550320505911a01560307400284025441c06240c080c59030087c5154148410a00c05698580c1000001c4e02001c410740c0c089403c08000344212807080740207684d0309441d600b1034040e41016000035044403807a64200200c5101d18190701c011941180c5140c0c1d00054541e50303400304142ca80c02180c1003141c9401c4000380000e6800307000303104e100228030100c1d8070003030403a01d0b002003020318072410741e0040e0400546c40019a18601801608014cd100035055640500765040520b4450740c003a0400c17003480b982d100d1520800e0718511810307001d13020170550007460550405406941e465010395034101101c0001540c51264030b0300009100209020740445107158024940f940c00c400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 119525710 1250 119524460 119524463
    0xd050907051813060c03020f0309010c090f050915030705030708010b310c140d140901050405070e0c0405120618060105010f030b040b030604030906021209010801140d02031603 77
    0x10302e545201659142440c0d000345400303003c40b110140c0a0303503a90007a1090b902c0c22000d00d64284110a09801c044004500c03480b12800000b40f00e5411310005040b41c901c42e04001c42032241c501d03003480310391103a144692f0041c003114480b1121107180c0000900d440d100350081034150144840006000b00705400141042d001100c41c542d040c0024003a600304201400800102103205180c023108980c95580110a0740443e03141c0594150b808001e0340e0f0050b070000d411000310540d1026080c5040565052030b980041c85840240074034109a21200daa0b80414010b440c40c4a00e00d00115800103602c42c1110b0060001502d5005001401035220f91501d5048031000c0c0ca803008035003012501100811128140c620507181d03000888000c4000328000d00708640e03183e41242d6140e1a0382150381c1d0401c244c5124511a80d1124401402d024001341030603489251071602180920407120540c2c0c0214030b0f030781035811900c4011000d07032180b000244001c1071440c01a405015040e980c02980d07071140b0703041c3c00343ca = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 119526960 1250 119525710 119525719
    0x40e070206011e150903060221010e0601020736020306030d0207080601060c0c03140a032a020f01020a0b01080d1b020607031808030a02010c030f05070806010f050d05090705 76
    0x160380c0d41021000142c0d0010400400107044081804101392440b0301d2801d10296103802c0d80015120350300d000403a4003090520270002c5480c0003842c819280c0104141c050301240685142600304200081e540351024001d200800100c005074610304005000745c1070742e0303c0711003900c0c2404611007030700b0300001c5d44103a44041c042d01400d85812440703400001d802e0100c2d00c3c040c1c000c0a590b0700c0e090b4221645588104101c03003021100c1000004581c0501040c402d5808030710190100007100d2401038030b04108040400c41c05a5402c5003c03484c540c2c01d015200025070192820141141c4800040341440100e42c0014051418040041469000000c10300c90030109500c85902c80d43c001c2c118620b1818071180020b42c03010301003000100282c884c1040d030361504440c4590700801c90300d48840504641050b800800140c0d55036200a071043d5050103502500040c82c2c8080182d82440d483c0103045102c010076050600c5082d123915042e081c4614201c41540030402d10800c442c0c10480d5580e80c80b00d60500c00c2502c41c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 119528210 1250 119526960 119526973
    0xf1203020f0109150e0c0114030702101509060e0f040605270a05160803040b09030712030201050a05060f030c01032f07020306010602010c0503010603180f0317010e0106050906180303040e0702 84
    0x240580006d00c00d0030548161903400b0942101d08091045510060803582180500041c0d415600d01c94003402080050309004480d00b07a0a04804408031800e503030028480c3d040240c180702215132460b43c15034000e07410940209150b40da0040c1211505507596040e0b00381e02028440400002f00400e0f100ca0541c801c400344c0c2d003d0103404044805001c0c89000d0414035800c00c120030400c40b40480024500c0d80405003c0d41c1c86c00b0b0740c440b4036401d110032042069016035165010003003102098801c042d03008004440c8114522140760200c0da8a0215440752414541e0720100082c6001440c1a444c91014006101001032a00c8450040c4541c10141c4103c0c000d02c80e04001040e52030060003199010001030741c4943c01d41e80380030f0741180038000c070031200c8103c561010205004664006142d8104900945034000c4980d00c20718004880001688841c094000c2c081c011300c00075601c481151900c100440c0c599840720950118170000c0440140c0140d807600c000240044c0700ca0244011901c0785919070282c840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 119529460 1250 119528210 119528231
    0x70305090304090e0a060e03030106300207170a2006071e0c0b010909150e0309121005010909030f02120706020c010b0904140d090f1203020f010915 65
    0x56410544800e000c581060106000b401d00580c007440c40302e02c45400b142d168010300d454000441e808002400b6480e00000300522080340c0207450f00e007140d110f8184040351010b03410700140d482120b500401c1c20f1980c00054120078864084103e03000000340c04a604d5440742080e001a01103280c450303080c000d114405140d2445540c0c04038107030b40300d100d040c7c440710901d44180125014040301c803880360042c01060030500c00805c2c1203014042c00b9001c480f0000035140d400741003c1c154900c0444c07042c0c03a140d080c200001d50980010050300d016a100f51440b540c52140c180c906418008035202c031194040c60f00d0000a8a00c0c8240c00019010b4025141c0c0040380451400c126180d1300080c01e186c11380c810030002d500000c0ca0a0340207020714401700c000080ea1300c403180001004010b0035130741502c81681d40c840d1055040c2040c0288000f00031603040c591161480c01800740590103041c410044a40e802c1e040300c005150091140f00d1312400404000c0002c600185440c0805950822451100600d4922810f1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 119530710 1250 119529460 119529467
    0x1f051317060a0209060d0203010e0f0a020a021b130f0b01080105030601061706060928060e030c04090609050a300e040902041107060f0e010204030c06030c09030804080d0807 76
    0x22650000c540281c00c1a5030354200901c00382d4400c1490603000b08041141002d00d58403807001d5401390000d01c900d0f69140c00d00d03000c0c883c80751201500582450b8410003002c2d0f584c0d80c000980c21030814182c6185610004203400195050b001c07084410300990809003100c082103c140d22924444070243c03100d41850b62902c081c10307a564000d00441c4082046900c20b2b103940e03d01010710396449a802001c0c10310340703035607170020411014180400071080c240080c283d2041012a5000310003a1105150194200380e500001036960304070490003d002c1d030340d980e8000c07040c004e164100b03c2c500e40d0031a00729a04858a0b1401d0100d040032968190400c500340e00418000b507101f0441c170741c0b90075134590780e0502411782c15080000400c00e509080303a015a40d01030002100c03031120083c002150082100003004041980c0031801c2d2a1441110006030340304020506c0011030115080c4281c40c118500000c10803028242980c45520540020709840c10125000411890014503020002241c2d62080d030713030b43c54a40099 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 119531960 1250 119530710 119530739
    0xd15031a06060d0905030304110303030601091206020705010204060207060e04020711040e0723030f010501050d030c11040504140118020105030c1c0212070206090c0108010e061f0513 80
    0x900d880c0d14004165038400c0144042a0400c100508452a02c040c107401e0718101c60140d001151660000b20170002840f103200704489e01e20800b44c01451a40c940030000030a51101340c0203102e010a00a20076200f400030540c1912002a40f2400031540e840d244c0d04040d40d9110f440c440c0310001130b540919040142064025a0461680400b91082d44035400701000081d00c4000c09103441803103840c400080701d44002c40100341d0008422403050f9030315000c0c81454100207402c4044940d0368188001000103807a503100e004075858051900c603580b000075160807000550745464599100382808180018091a0307440341e003035114620000c100814904054403140441c40034040c0c042642400081e180441e004001c00140b52a09881c43c03c622401030380310120303003000081d01c5160072168208040e040d010000c840d04103003000010815030001c1c100080001c1c805016004c80f04c609940429940d48030400c4540050305030107070110701c010000e080106150040c81004131560b03400309001642d881c500f40311 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 119533210 1250 119531960 119531963
    0x510060c030f110307060f0c11030310140607050a080904050702010513120302070204021c05060108090a061805030307111c0c0204090203030f030f010f060e3d02030d1503 75
    0x20034070702c60460036040d034024881c0c020b0142180001c01c603a00005d44c10784030700358500740340c5070300001e01e1070501d00f005050754074a4080300c220b90300800a01401c202040c01c410122114190018007948007107000c9040340c010a40010258446c0c2c503800c20400082a01410503070f031080d02d00704481d0303a400600700e0980b90309485c1494100361400b00c4034041188071060300c4d614180c50a0142c980030442d0b0101c1c00320f0b0b1002200c852000341e00034101d407079542c1c51b00417150441c00920b0440e0f00e40c28078090f100d0f101e100303041c8010078551b5507401c954010300e002d03040041e404e90482c00342c0740ca0b03185c11040507080c00006600503d542c0140e190321408691038614100c00207089030f859a505d400c45500f0305c4003d00e69400b0503603051001f40000c0c0b40700403550006502c21952840c41ba04035501d002712000095a01d80c00840038050201c02c403511603143c003104003000114903d848040001c002c5e1102e039403800c241540710407150085016002868001004050107102c0c040100855030071805080740d2904c45000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 119534460 1250 119533210 119533217
    0xd050702060a0b1008040c0f080a120903031403150a03081b0f07120c0b041502070b0901120b041b0c030e060c070605030a0216030f0210110a05070311100510060c03 72
    0x1300411144612080c550161294402251454542032410004079003079001180030351151a442c4100104d4040140b03400080e4105041424110350b0b015101c1401c4800d421110303180030000400d2900d01d01b540130072022015016403080e58690401c5000d6500c06080c00494030005070301ca054030400041c0c00c1c010091014058034048d4105203081e102d0546001050741c2c4041c0c03000000ca22400101d0044c001001d4125242c01c4081e103d120190414400380c0c000d6003880024491010a0390f0000c0341c4540541d0748010000f40301e10303080c00280007410040c031040410907074524075440c000d400c0070131040307000d01070b48440e440002c0741410059140300e103401425039a08242c0e81000202d01036006150014100c01015080a503112102d9403415006c8200742c00080c1c45003d0050590380501ca2003000417500ca5042c08070610841d0400d100344580040079040100000b00d02082c0b41c850649030080307000541c01d0701c140010a0603d5000707070a085d118498004195100042d805000d00d5101b00b0455143c0c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 119535710 1250 119534460 119534479
    0xb0906090318030f1209010f0f0e04111c050603120403200127060801050607030c02010f090509010e0405061806040b0415090b160f080604020a050403080d050702060a0b 74
    0x4120494038207455001d80604c41c8041e440d424180900c1100c0d10003001144107511021500001008140319114590510002c00d507408101c1e50b10990360f902465040e2000b1690080301c07020341200d07104d030840600341b084066504c80c1e004020b54011074000c00e002c030112071100ca00190724100ca4070451000610306580002d615503c161520054074454030141488a1881828042445004515031606560ba441103505100c20340c1c02542c0d0602401082e43d000c2e042031025940034000300200c1c80040d0501c00300b654240c14103440307149120003610000e40b5604455075580c2d1135140e88036040e9012151802100e00141045000c82c000e621a0b4041000074400307500c0c0c41d00d0f0802c3c04100a0016620101ea10080c0101032101c0d02070807501e6403003210400002d01d092240718085842c00c02e03c1d50704004810b001c4084880e400003203039420440841d00169100d028002c141c60502c2103920040040d54040b03921000c03516a0350095101d400360342c0a032603650b95919071005c204d542d844012a80081182e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 119536960 1250 119535710 119535727
    0x10305011b05120411030f01150e0402010f1d060a02010e060604021c0506040207020603090307030206061909021b1204090c09150503040f050616021005091906020f0f070b09060903 79
    0x80d55025006070145d9000454040100080380c248035031080c82100350b0b91100c41202d00c2c60000c42d1980c0081c500b012440c02c06040c140d0008040f0383e10f070070512041100000b814045a441a0071303040040d080240f00320b650345406000640a40040340303092606005180c00148103003440d000310b9000c401e1079080f41d148100700310b140d2002410003401c40c80d0410341c01e214400050311031100550190901000440d2640030520b0000c0c82c24000410031405072808403482d0070801103074020701003920340180000d80c81d026556244105100303081c0200784c551081c2c4034000c01e4180090018802c0d204184c1d0305101100c1030500541e0071200a1040406070081c800301d903000e0300d10850145030864071800003080303140f14544420303280c42c034180ca10b111010303481c001c40788816404100e084560080076000f03008501e414120240c80e14136060841c0400150502e0040401c20240d04a440440d04c0001c1c1319222a0b8822410005801c0898111100700510b0042441400e000408621821201c0000d52800001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 119538210 1250 119536960 119536987
    0x907050a180204030c0b0301030b060a050603061c02100504030b070806030703120e0d060506120a02060403121709010b040609092406080105090a1a1608040c1d010305011b05 76
    0x44403580c440725509010110000e007003400b01000801e0760002e810386030b50560410f040c048001822086c4194100042040340da00c590381135990180080b50401481d89041a041c41d47e1a00300d40001e41c03100c440f14440c112a6001030140c81600d024480380110340d600c020081e98241401c1d100164503901001081000070141900315a94900300d180400030000030501091405030120411038a00d5120303400c011540c1018845d0403188141c0c080180321000240d00814014451400042c102c84c0c0c85950003404140650001c0f00070b00d40d5032a40c90043d1800ba0744089c02401103000705480b079400c2000003e400d1a4a018848099400c00d00c42e51040080c2c01c2008013050900c8180740d901341e01c0740c07000582660280306603442400d0500252501013114135000c0381c03a0303014000000c03400c0c0400341400300501303001e0898002c4c001942410082515181400204440903a00a01d1141541445006186020b2503400d04a0f0b228034000d10400c008580c5408a060941c0f019600190b028880700d80301c07420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 119539460 1250 119538210 119538239
    0x30c0609110907120c02010b0a091a060307080901050606070203060a1d0307030c0b0609040b0106030b010507060e0d020610080d08060d05060408030118020702092e060f03050907050a 80
    0x204906641201c0380c040040754050408039510320100c0c1c1207803000c1c1c610004901401031110701c0c910080014900610000c0c40c4d15a460107082c0200d6030b100c1c0000340e003c0403428206202c0c08000c0c10710b80c0b01c1c94407200007060903004030f603010741650a18020986904100b03040d20b0f41c1d59401405040281d0313071554690001c18080c02482c07804004206440820b02c0140002c2080b5400380c0c4e40d544c940c1425050800c490703031014203230a000d540d203e0108004600f914503401c1c191815490046100b24881c0c5c0100c44030701030441d0141c416481c000c400b0444040004540e031006886800359060fa50700da0034410140e0000d4031980042c3c2d00440c3c1200c1c502d40c450311100754003020080010f0981d0302d140e2140c524049040710100c0d04001c0000051041c02104a40020074a14003002035140003281d0740890800d9002505418801c0080d1503030030421f038040d078000159a19030000c1c80091a40e00c2d24001c0c09221843c1c010008203180c0400306071902030205020003a202d000d044009064602250080300c600c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 119540710 1250 119539460 119539463
    0x201110910090f0602100e2410030615140d11040b060c030406030e07080f0c0409031704030207090f06050a0e132f06031003060e0f0724020a030c0609 66
    0x542d0a0040380c1c03000f01070f0154000d809a540100a82d02021ba0035070304070341a20b11943c45a90041d00f05a149500c1c0d000007502c200380d01003003044c10740c030b90a1440d107241e4503a400040031a800c05d802d108129086450b8582140d46419440c40006841420b1096650310b640000e010008029010092400d06412622504601419440c5081c62300300040b400e6402075003011000903121510500c000030100100c00240048901034100390205078402ca90301d80951540a009588803101e13101450f010390080901e1149240400c1c40528147c40c00039195069405000081803030249a00030104c1d07180301350400da81014000780072045c18542c043d208604010803580c4801e240d080c900c030004030b0700300b54004009510034a0420880d02c074203002414060781c0c101c0d140103d0080c410089480e26130603486003100e4005100041450903e01c00b10304003106402981103a1145650004003142d051420091800400700c41c0d03038852030341120480e00c41040110281c002010725000d00d0128003164001075a05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 119541960 1250 119540710 119540717
    0x5070215030c04350d080411060d09060618060503070306050a02071a0402030d050309030a1d060c0622050a12021603050d030509031e0d0f02040e01030c060201110910 73
    0x42d64504440d9142804c0c200a0104040106402d400d05065400324a00000d0760f44054a40030140190040c260f190042c0054511004620a03d200c0d48408044a80745500e0030014021079070a401c2000140c0401c0c4940203101c0e0490003070900d2100c0910a007425140e0007805000710510b59222400505005000b8a800039420091080050b00350b413103404d1100820260440030b071605004160828003060f40e06801c2c03040800800c01541d5000c01215100750541c1041c11900000d0403185600342607105103550045400a041c90f0740c031070700188817841041c14030145c82402d0300e00e183c082c800100000005201d917001042c00c00c00980103185010800010384102c0e04008401108024484541d44c03040d240c0740c02c000110322803a41e140c01401d9000f0305001c001e5141020078034801000c11440c10301c41d05403901c0442c1c4a0140c17000c0ea08080c0c1c11941081082d034640f43c43d043c0410b0710071020b1008541c440d102650000d115070040c080c0d0b01610f400c141c0310174107042a031b009000203102ca1020038002c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 119543210 1250 119541960 119541967
    0x6010516060b1c0c030605010509060603070c05120d1d0a03020a0803070311070b061002060108070b0a0c0602040e1008120406030b0303090a3c03030f12060803180105070215030c 78
    0x14500c41c64003103115a0081d01d0813220780740346080590480b08181c00c1140540030102c04c01c4507503110f00045075007202180c42d11213201041418241d04100e103c40030f9007101c1c80005064580c4401079007110000c10b0390741181911411082203419584e0100910080250704400d40d0a030201e40c851001e0343d801005814041100800c010100c44c483d445010201c441c101c00743c0c14070000d800e10240301518075003140000c110950602011a94a144a00c1900e80e1144d0010358507074070510442c03a6900302a0302802c259152912140071901a0000310340e501c0503460801400103065900103000b106090032180800d28081c00c010040707008c1c040c6940306940501c02003048a203144c468611040041107103140429500005002141c0c00701841e60b821071480c42ca012a14480401d44090901200c0d030500304154080d20f80c4400341ca080215420b40b10626181c40000160700d18003100901c1147d03000001842f19001810054440c0d001d00c504c0030f034103c030b1000e0480b01741d48114802103400800d4080716504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 119544460 1250 119543210 119543239
    0x40c0b0913020d02070c05090609240603010f05010f0504150c0f0f0b1005060a020606040f061a0705060f01120204151208040807090506150a1403041a06010516060b 72
    0x41c0d0303114840c041c8426500051000c01d00c10780e80c3e0f86d00040c5c00110f82d001024200000018580f80c40500707100c072500c00c4c92410b80c141c1c0750462144081840c0180503652250b03543c20324962010101d01c18a40851407480e003007101d035803180f0200e405903410080780460214074403404841032042e0f03c0084445001804000c0e02184a01c102420420b01c1000960942d150440604005101d40d42c000d03130142d403013030010f22074036500840c43c15880304c01074400045481c07054080c18068151903000034981c10000741d4290150390303910000c0502a01410403100c0c4d41d00d880301061840d400c244181c0c0700f1001d0766082d41c401464036030011120301405444000365141c603000040001e04440074201c2c2e0041002404001e0824180400700c005c0c40c18070406c000d103140003800301d510034858504801c0da07004005100b00c4068003811221164001c004070b015141c0ca0135240031040015504580c0899418141c0080c0c01d640c070031300456071013600c5903040203c000e00546d5030350003406004255681c400314070340d84401c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 119545710 1250 119544460 119544499
    0x140102131505091206060f0a0605040303050304060908040b12070c0c030305090a0801020307200c03150405070308030a1a091501050d0608010509011e05070e09060102100c0e0f09040c0b09 82
    0x2080600011302905441c1401c108110024070341080041c0940041c00c4101301c01074003c02510100c13034050410b6980ca503180d10f4600020150000c00804980e008030b0041006009e020107814400345090005500b500c2c1c2c0700042d14403076940600107107500c00c48002800041d03c03450240035028030150103031505a48030304409003a40c20880351500061200c1804001820b4000101203584400300081c104004510b00801c2d2a040441e011040151031040810208441080301074021500841900e40320305001020001a0000011700c401c4000003402030002032070000f0f201c5015401c0d0a05400000c17040c0030055415030400700c40044015039810000940060a0017880d10035440b01000142249030703503040c00201c0c0400845280000d180a040002d242d41040220f0b04020301182d0218041d0303070303500040345810302c0c070218011071909080c00c6d4200340350440307100c00141504890000154040c0c906100b54a501110080e001030382c0c903507040102c00c00301c5001740100c2c0d00c0a0f000c2018140c0d600003c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 119546960 1250 119545710 119545729
    0x9050f0d020c15130909080c03040810050901020a020709110c0109080c070b0414011d031e0c01020328110703030c0c0b0a051803010b04060305010914010213150509 72
    0x90380115100180b2441c108002c0b14410262000280c00d2440000940510050a009a0325030565a4070070fa82400161000d45007001030f00c0c0200c959a545a81d406034403140382919650151b41440045104c2000600030741d040014070764024103100b450075440b1000f9000310710010354065401c000160201c8020b02a0000e140e0003074a207243c0e03820000c50540c0c60080c41d0340c05902a90030074002408480c028940d04200c4900900c1c04540d980c00070038031900c3d12a1400c3c402640f511078803100c2041d20000c400c0c00d41240e0b85902c280c82240303030b5403c01a80c603032185d0344085148400511158040ca01d07031281300c5160440910384411a2241d80344420b10300070303240c1c00c240e010820a00c1c2000402011051950140c01101c100500b41034ac007030b00143c141d0284500e01400404180f50f0700c110380c0c80950088540103001041841007e03a40d05101c1d008000456090710f8035a030031800c54000f98014000c4440d422130000440c2091072034090305c02303003101007015118100710040040c00c40130750310300303000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 119548210 1250 119546960 119546983
    0xc280f02010e102c03071e09021801091a0a03050921030a050a0902090612010e031c0b03010603020a12240507030e060f0106141c060302010206240409050f 68
    0x4041e1013000000c0700c14410102400d007070a10500001e403400403a200070035104100c40040100c0c1168584a0394450800d9500790000c0404070f20108107201c1200d5403041c184a610420780700c80d8405070b00c40e0340c9014110a004022824a00200308208100740f0071350015500c00061020794a03014501605060680d00071545000c5001002c0144000f0030550311815030440d071030150400010803c6e41c003240c5c0c43c83c00201901d22800d01e40c1c2000c400303988290000400251030b42d0550382c0e50103000c1c01da0380302d41c2d22000250341d0051828004443c1801d0504c15841030b07039001171604c2ea01c0703441c1c00344050240804200850341945001081c2112100300b045890202685c00000320341c900d0511703001000c40324030401d04500e952040c4107101d0b80100484407103041d515076140140071203840f00c1c00d11810b44110005040200c06041e0080306c404410790088083d07034800d034261110340d103c00b4022506922000419000d25403401c054400c5450180d0049110a203d9400c0c1c84200c90050340c52420030190020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 119549460 1250 119548210 119548217
    0x409060e010b16111207081f05010803160f0c0b0405040506010215040227090105041109090d0f0c14010504050d030c0203120c090603010603020c280f02010e10 70
    0x906010039000054040c0c0035111858009007408004000c40c40042e142080150808040b8070401c1025103894180903241030050040302c44031a5030b00300c0d050751401101d00101140d00480d6440302148141d0040c68101c50a81c4011420040041c50010011a245100b10f420501051030707100002c00c0f42a5580040582129058450703191000b80700c15154010a254115008441801600042000c1e015082601900d180ea40d4010480bd007007400340c403441c100c1c8001c41540042006451054011911961007503c0100302c070340b902c0c0e05005c0b07621000d659103841c40e0448000c00c030f9840c4c42000d040107107100a1810141c0d062284e21004041324043c20461040c2e51140e0400c0144441003044021020f21450100400b24519038025142d01900784c464200d41c14240c00b0540d511156404c0c0c0d41d1041000781465565607482c03c2c041c000354131030128668107005400500421030b6103c502c040c0d448500c2d10906401098079070f2080b04000f032200089050060b040001110350700c810707005000e6281c4c60748 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 119550710 1250 119549460 119549471
    0x10f021b0d141c0305040803180c03010f09050706140d020c160303020c030c092701060801140103050c010903030c0308060a1a04080606310b060d0603021f080c0a0201020f0409 77
    0x154050540c40030103d409090508141c107201c002440081202d6111680300310345440010107840140c2440c102c40e510652540c282003052070b0401e80741d840701103001d101c0c07011101c4455403100160341d440c800b03a100d0300c0c100105102130301080d0355507001031540419250594403041d8500d856809150030903081a801607002035114000750601b0098051488400c036074028540c5402d844040e228030320241c1e605540800e40c20b10300c50300078094000e00007070300d21003000348040b040e10310b11026569024071090b601c6200d510b29001072035000364400000c3e80c2d0940d585010b2044140c600b0f459550005e00f40c141c000460b10000600c0c1002103043c0711080ca04048020b64403450801e909e490b2010103020f040c40307100d4841c4030760b4190711300941a007498800b00d048640e001c80c0c01c4001380020103015000640220000500e10700c40d1748164405001e80348221920301c11288900c40e00140003c20000c0000810258404500050740c10405009114203d20005d858100002e603001045e80044d480000f800d070f100c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 119551960 1250 119550710 119550733
    0xd0603020d0b01090c03200c0f0102030711060a090305030a1a030a0b01060e0303030105130e030d090f0201080106020c03100b032103060f10020d030b0a170f0606010f021b0d14 77
    0x10301030750210845034541404a00c014051305541020000303000f021a0100040072342c0c014200b44000001500742400840d220b28190300094403c030b00480701d1704041d0054a0000e24100610301c00ca20b00c0c9038150350743d9030640d40d40d00314031002084010740140c16120b042c5041c08490b5000c0241c001d01611468807088603526014010b4a0000d290408034442d030002e01c0144859110596200c0340d03020040c601207040554004082d0440c414980c0681c00036003860400d4050000046074919424400c2c0d807215000ea82e507007002c0740c89189010302c0c5541074200c11441c405185260700043e214000044c29500c3ca14001d6810320001e42c60680a601042d0300030003048601d01c0c00700817a11001400781c640c8480120921402074440385400801c406040d0344550303184050b1503008104010703110044400d038142d2403140d0070580e04c1c40c0f104a0310001c3c0c03181034001211035110b00c19002d6040c5454004015013094192503040f100d441ca00c5007500010012215400304044011509180601001602003078100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 119553210 1250 119551960 119551979
    0xc02010f0902060306060304081e0712080408030612030405100c060e070501050a12020702040e010f0c0504050609010e031c0822030801050d03030e030301140a050414010b0d0603020d0b01 82
    0x40502000200345040404405625150211303644810125540d80d526900c1d481d064915006034018445002c019840340b00407400c02c0b00060050900480859100036184042281c09110480d0010412070301800414468100f2000c10540c01c12031909990526480300d02060b42000018585d81c00074140300402e009100c464424801c02008100240c907180f82080000f800360701c100710b50401000030170350305204180c6040e41079810103070340240140701107240001200c0c06804040c0030340300890301e000c118154041c001c400701c904564020f400769042c591190010742c2c240035490001030f010b00444030800a840c80c180200c030204801a181c2d4003080c2804094107612610342d801441070303d401c0342e1140d8040b0b500447c01604407001160b1000000301945000c4014019900040506210200001ca000300c00345c03008540b503401c1900d140081980d220200000d607424589040e4124050000500480c1c003904001d1809034101030020541580e607134082090144030400585840358040d00600c180080e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 119554460 1250 119553210 119553221
    0xf051f0b0303040e13031e080f07020109020f040c0309020d0c0e010803030705070633140f061905070f06020403020f01052a010e1c0f180b030a0f020a030c0201 70
    0x401c0d0010b605041c188020881c1c003501c0078040c08511a010340918080600c102038880f00d91680d0390084c1c035207290320140906641000e9421a01480304a00040e154610500c01c1103201d0342c00a03c1d40207448814410300000300310508540d400c00d52650915805a101d081034044a1442000e40c05001d070715110b01344a2200c0c06030820f440b40c0d00100b080c011001e5114095400440c0c0200c0c001035040340f04130320243c00d032118081c0500000000c07c40304101540c140001000c440302110700790040100e541c1040310700c0380c0e4880035540c82001842440f0300322521002c81f5568070064280103140503c1d941f03442d401024604011500160006001c3c01141840f076402801c052080c00c0603428484e03101d0380135210f000c0c0701c44420b600e50f0012600c060000c509401450901903544255402104544045024141807298070000b040102c49107070305c100d220f0304c0c12000e0070100b00d00100c0e046082400d030282c01c2c0d0000d0480e07117402c2e444800c0d14103800390520080c89000b6042d2070000d101c0c001e1a00280c207544 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 119555710 1250 119554460 119554481
    0xb0403120914060f0c010e1e03040e04140109020a030b0a060b281b03020106031703010e070f02070506040803070605010e07020c0f130e060a15050a0b070f051f 70
    0x103005504028080020406081ea42d40848095032102c032120180012070140d04400121036090041941e6141008074151141c801c00501c0c0882d140603520209a40c0d105500c074019400c4403032400140881c1002108294800100d07001003000400e1790002940e0041c2600b0032b84071210168140703c800c0070240b1503072000741500301240d030510342d80340c2c030f4203001c02c4001c072050316180098076202e11054806ea000c0318203140700145400b40313030046082c028001c2c051030000301d91380326a00c4c41c00c031000e013403030000d43e03040380d0710081610043d503240e403011246800c0003005803096104041c1c01007226034030fa0000d480580440001141c9610950030034506644060744840b03102e280010500c06110341c086201d42d10400c00313980101d41e090a0a01044407450562401c00000380782110200c00108049112405020000400d0090400c4401b40c941c0da1020b5200d00d95105000d00d0f01005906088000380c014503004610000460003180c40d51400c0640c40150f04050412a104d141d007940401e1007692001c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 119556960 1250 119555710 119555717
    0x8090708060115080405100e0f25210213051f060f14070507030c060f050306030606220606020715050f0904050603071701090308130b040803070201060f0b040312 71
    0x6500d0b007005003440c45000343c100d1081001200000301070000c01c1181c61141001010304001c20008030044903240c80c0c0c40d00d00c8890900501c85143c1030138103196000c03655000c0c000785181c2c4492601521020417500903440c2030600324619170781c0340580d54078000340d1008201c80c5804515880d100c8010395180c868841c800048682d0846c05006c020b51003202180020041d0500043c2011307140051034250003481c1c001002445196404800c000c01460200215481c6445100d2520641c0c00203490304d000881d841c64050b400320300018032510780052041e20707128500046070283d40c81d0b0400322013a5140d6400000160384500020003501e00801c4180450b1141450514100b1000100c0b0307029610549011134800c68484002c1501694244a40c100030000030442c03a0081240c03048560180000c600c055010441d032400084060070a800d0303090107180d100300740b400c0301c0c0e940340c2e45d020703080e04050045000c540d80c2c0d45002c22517a450300e82e00d0010300b02101a59880c0c40c076500d003500611507110090b4040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 119558210 1250 119556960 119556973
    0x32206020307030e190809010201090c0f060237021503090114010501090f090c1404060309110604060c140c0a0e01180209100e010314150909011a120111070308090708 73
    0xc1042d2000006803042e03006e00c0960b0344000003c0101d02510003400040e00b421600c100c0000e0310407207819840d00310340042e020b0314031000c0041c5c0c1540040f8204120903040b214541004500c40c12801082109188018034015078400410346103042034008641d440040d030742d80c09042c8a02082500e0031801000240391031940a824060a00c0d00c9403070600c146030005846690184a0f1800340c15541d81d140308146200783c030b4940d034100c01005040031800580e8004101c00341c091450400004482c1582c925440341c402c03201043e55007441103081480108140c0c01502503680344e9642da440da0744010a11407100007001d504003c0c0001740916410341512600b0301c100182d072103a440b60305403000c580c00103050501c21200d001f4016030140c010010700390301104681d8200092000001e041c805080c509450300207640c0d650503809422112240b581001500d0306000d80079107481c02c920713940080c03103050300003080c0315050751005079041d0480320f021001308107034108100340050100310305401004008001e112 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 119559460 1250 119558210 119558233
    0x20f1215040e151003082101060c17070c08100606080a020a08010512010e030f1801020109050601120c05090a0507020f072405130b04061202120c032206020307030e 72
    0x366141242c039481203c0000900180080445011043c01181c20450341681e0300c40340801940d4826a610f114402c0582d11000420303d580324810800d50300d580f007441240300703101e0040020000d8000c0c070740c12030f0203007030310900441c8202e01031109016507200414041520350920b140540034000040c0182e40c0700d481170100c00f0585a0260f40f003070440714152020000000c2d4244420701401c42d205071030015120000d400400c10070000010140700008801901000d021607004900742c8071015400b8200d5402880188101000c0c1c42e0040300907885044000d13031842c0d55801003420000d00b21030620b2026a10410080b185030140801c07404844808050851581005901d01c0321907004c04864003050044c1c070441310198000c41c01c0700c184440918005094950b00e0b0070300040d59100d805050700041140a818103008118005c0e00c040805d200b81101103642c9000c10f041280c0c000070820407000741c170124000c0345540740d003820059203400b80e2005a03981c40c10540140681d101000000caa95010148800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 119560710 1250 119559460 119559463
    0x30d081501032403050d110d0206010501080a0b03060406140c03010605030705030604180b091204120f02032118010903030f030b15120411010201060602030f030901020f1215040e 78
    0x103160109080c0001d1140080ca810038040c8100800c1c010041c2603c3c00101c10b0000004e1201700c214504d42d12200040704600074661207842c02c407280d002680c0103034010b2116600074000d003a8007000f401400203040b000781c0300081c80c2c410113840c01c0d07541a5030b8480240c02c070b2541c004000c0e44070010154061231545010001401072100600301700030000040701180315513869400281c0c3e07036541f502002d0880c180509203c2c40d51201941e880703141d80301d88106101d00c580d005065408446412052a464100d56140e141c803146001808036814092000c00451501d002842440319880c541900c1c0d80350382100d810800c0410b4810b0441d41804880c40c010400282d00c440141e4140500745804144a0004804030f003505a59002051307503600041100c00d419620b0764440d40c81103000705100005440c00c1d02c01a4201c0f00e00c2e00881e4010303001000800012004600115007040900000503e0021003546100709500034590307240503000003d06004552180e45c0b0410314401d403ca40800640b061004160b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 119561960 1250 119560710 119560741
    0x5040608040f02062b05090c011b140708070f0f030b01061206150509090a06030b010509090f0102130e090c090a0908040509040606030507060f4a030d08 67
    0x80410800705082c030119100c035020b840360702c80340b400200e650750180844612180c0b21038000c82c0065280900280b0140c10001d46248011010385030801c05040c440300422002c50419419610140d41a50b8a09001c0080029100070285040500195820981400c5094086034044d01c5100d802d0901800030661404000741122903d0402500700c10050009001400581d1701003018038003241c1815040c96003040041c0008017085545a0300c07940c40c4406001140c44500014004441510052005050452106030404050000c176060503891640443c207a030301000120700c0f07000d05804100008215a800690413001c810080e0451004002c04141a00c10040140400d0358480d04204140030b401c0080714060000940f85000c0c91419003818006070a091004035454420014006015441a18218007410a0380d03a0094003400c04511041131004030300000ca1142c466001500750305c00280102c2e003a220804005a1486103400304040c1040100740b100d074203200589080160b06814811003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 119563210 1250 119561960 119561963
    0xb01060f0f030b0d0605010b04050a0504060f050d05070e0702070302040614030d0f090509010b1e0a0e0906120f0a03020106080111160305070c0b130b0f0306090c0f0a0509030705010504060804 84
    0x380c030f040c0300000200c034002041c0d030260116190100228400c90403200a00640301c00350750216840d95524103020840f860792054201107442500d05200929240c3c400d220524080c00c11508029199034507101ca0120a54407000903078084141001103050034003c0c0001050390398841c3c1c40140c0030001007600c440320701160388204140021540309581c050010b9401802026001d081a5a100c480d511101e60181031641071070341444000e00700081c0b0300000c07500081507541c1c401d05148042e5050111245000d000c065002e00190903002e042d54042100a4038076009400821a1103903a040c040c4c212107880d00481c2560b4100b0b1840f526800310740003180c04060981484619044490404840d60700404500030010740c4105e4001038941440710140011034100d9110002080d9252140c040300e11800c540009214000d0002501034075014005640c081c4814114610380001e20580b8200b540c40102d200c008510041800e9000c1e040400c02c2d240501000c2c02c15900c0c0c6410014041e110300f100400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 119564460 1250 119563210 119563217
    0x914040b060907090b220b030105010c0f080d0507020604110f030703020d060f050403020a031701030209010b07020d1425030803041e050d050301050405070305010312050f090607060501030b01060f0f 87
    0x105444902c0313400444010720b60510895100c008103049002c3c100031030203500074040b58903500410303641850411607049410507141c0300300291003992412181e06040c1d8090350702030b17420b11411030030040c41e020b0f00348129040c0d400303001c0130320b01881d084540c922410001070140180180081da291000036070201545d40403100100244101d103402c00c017402c00c4010111541b0700740003d0100b015000542445a02e10a407110762a0b00340115281c1c2505109100103540a0600001000032031483c0000b03015107030000e0142803284e80c05803a0304100c414aa00d024a0a904c40a628130082000600c0f004001304c10413403048440b4510780f21407449000180000d0a82c15040040c0c1c1624084852030b013221542c408145d03045080300e400e014016400c00d1240030b0003103082c0300004458070710a00c50141640c0e0301c1000e0144020f80241d0445064202407041d20030a2020001507010fa0742c0e22018005441c400d00000c41e040d8114501038496140c103911020034044008104101300b50070100b10440c0003418603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 119565710 1250 119564460 119564479
    0x209190f06030f0b0a030c0501170f040f050c09011412060405100c0207080f030a110c010f081306110304020103182114031005030d0e01020709051302090708010914040b06 75
    0x681400090131071007a06039000e82e5001000041104181e0310030100c0e0030989a040c0d149842c0c2c02d040d00f1a09088491190107001e0000103000100a03400842c1e1146c05082114840303071908000c0744690000f03801c590381c0c20004103808000c624120240c000a240910040d180700c0c01c141c1d40756a603400e1901c40020310300d502d803001d07000c07950702c00c02400d0001c01ca4002119005c105500f0003a84a030310850a07140051404810200034141c0003400d541c0c10b49060b5510f94051900c00f40403124003101a100c2070400a42c00641404034215020b00041e260440d04044d50b00e09040c8005402c0301c2c1402d0460340052500985d540103c2c8400e850b040201e21001103107595008281c03812603565444c4401e0b40341481d0007105000b2100d120f0000d0005582e015021508107a107861810b6401a0381c1442103401607110b00020f0150051a400c41034005810b1030001447c0c81c0b40c0c0d400940e40f54400c03a40c940014101074010003654203180035045a01140041c560103a003441c0d1219211a60300401042c018190503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 119566960 1250 119565710 119565731
    0x60905040908120c030405060105040b031c110304080309120114040807030e0405150306011703041e09060b0d060b04030c0608130206030106020f060901050c030609180607030209190f0603 82
    0x3034080f036802d99001c503401c145601c0c040c41402c016410030356055505106450003c14141450710903405550070003801052100000310040564120707911041003000507081605007514403c00c050b01c0540f80c280c0c091900c8140b0001800940e00240c2142640c9a04004c0c6804241007102d4100c0d030026004071800f40c1d21002800c058036032001c2e5482e0990070514200401000381d86c489001d1000e600201c0940340346036030300d000ca00240100400050000c2c0c0080004005c00400c2d210722080c094400e00b841c000440c1c0d201005000c83c0c000344e0040605079000904c5117806032052080710094802070855500301401e5490b02000310030b0314061041401050804034204048501102c013240d540107007965600d607150400291207103140c08801c15144074030b0020902548043c01090310542d0250300c618299030b200020003900c50005800c490380f4400c0c0e000341d64448002401498856009038034003507541c40c400002d120a801200c6508074401e4040b4800f44080b5120f06e1000046524038900031802c000340303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 119568210 1250 119566960 119566973
    0x705160f03120e030a0b0115020607080a0f18060c18030302030f0903011d1006060512040b06060d020c010606111506091902042d03050d1b05010c1d0a0609050409 71
    0x1c1e1000f00350702d0300c04e50800ca0100061000e034541030f215800d0318041560356001040e41e962006031940400720380920009045241141c1c40b00b0840c0042c0003000c1000e150900d003080301c0040600003994011f0f05d5444051030107800c4180f4040011142c064603408030b2461300d0007900d9014966240c404403200041c8142c25a4094004024480c0d0780070aa500d907850004900b81d03a00c50030440e000c1c00a0030a040001d4180c0030b0415036000700d51145109000395a03541d1942c1e1007510090030580d01031014040300e61081014030103041299a481d000140e10342c00e10314003406441d0241400d0039039034030080040f50f80700000740034240c2060041d6041d6500d44c0782c1d2003d003400044607a100380720180c400309000500c000000111880080e85a0405071005520501480c0019440c000134107544e100d0081007511510442ca40c03104083c3c03040a450703411055503503c5003550701116128000a082c103452810300e091801d061007196400703d03565203800c1d00e844000b80c403150807445950301c00c940d21120201800700 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 119569460 1250 119568210 119568227
    0xb010e040c15210b03070603090803010b0c010204150e01090e061e010201020906070b0406060e1b07061b110d02010e0d080604091b06030e01090b0a0e0c030f030705160f0312 76
    0x70483d14084a2542c0f20401c0007000d60100407842842804000a00b0a0081c42400c142642200c141444c582c00c00d00307142c0c2d0b6580310080c3c0410a40d82000009100e00d41554030303030000c0d2241da0300d0f04403103012500010301c0c0d401180c0107084001c4486081c4005a5902c1c0d44e0380743c811008500c0907841000d40c4005034028040c0c10304054003c00001403d004012161880f584180d101d03000410039151104804100240c003141c40c407a1800c40c40350416404140341d00a44102031043c0b00110304c0c0d580b000701c8200161030640002006c100740c84485440c822040c41250440c1c50580300801c584406019a15994507280b0492000e01681c000400c1898445401c1070011507003103040c140b00407000c01e03d00ca0f034081c154401d000c0000d02c2c0000e00400a4030601540072607035040b20742481aa00c0f0301407024010035600580300410b11601c441e03041241c5080c000c406051103c1006103495680d20700b05141407036101c401d4201c001e00e44180034007003284864101c0003079a0300b00d2208081c208201000351012107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 119570710 1250 119569460 119569487
    0x70e150f180c04060210020906040e0c0403060603060603140d020714120d020309010206090a020d080d02070204140603191e0c0e0c09040e0105130b1f120b010e040c15 73
    0x8070401006000c661500040c402c69007030b5821103a140100c00c0c0c02c1000c134094240040c0d4006401c1004000c10421010180c0d0801803072410940351039a2955080c1c101c41660f031040390450740300c94080040c8030b50712503800c80c2c098000d0068207860203040c20003521503190703009078001c0413110801c04083d601c41080c0100503410f10745c1141c1c8004065800690349810143c02c142c010300c43e010001c2d403d0360010808601056000d4510030503400c0c660f40b0b401d40c50b0004c0f4001c070022a801d0040ca005030740e9900031580c8140c50850100030f0b0b410010181400d1002550344044017403c10320f407120006248800d68500854294489900482140f600c010458441c0c4c0c0715401c2121000d013805009240c28004082410046408000102c401c2c0042421380d10110703851401a40c00700903000c0450040d212480e40304000300900d01c0d060b00c0c0c040007521032000c035401c11130707403000300c0700c2c1c40d80c00c1002d280d000b1805015400d0182036036160941e5000200d50460107603044610750104503015185c040c00442a256 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 119571960 1250 119570710 119570749
    0x30702010e0f0a0203010c170c0a0522062a0807030311071b051e2101060905100509090a030302160b01030803040201020106150e0607021c0f05070e150f 67
    0x51102d24a855440005450691095180000707400b51280500f000c09944c12030a02014242e98a031100360445404c00c509590034400100030030802102100144408030062404002c10301e404c18000400d001c4070b00b0445040411442e1205403903808000005030300c1a0b004061940d00c0c03000345001c40151840d02105001290042001c2003040400c0d5501079592001401c0301812503590700803ca21200c408100200881030307094007030380c3c40c02c08640c0c250b2412402c990180c0e090346003401d0182103440e0b9910036038480b6986d00501c4480d008030400c400042100b101d4100c0f190910f482519114143e82c1782c01410b0503070000d040c2d223410a80078440210340303420007000452036a4909101c2040d40c000c032000ca0040d4a04540411000b0503050105040c01440d80d6070410548280140111170780014802e0341d0020201001008180c1c1c2e01000c2407000c2e1184214246400552409929200854002c0d2089104170700400002c8004080412030f01c1030200c40101800413030002081034241ea550156902 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 119573210 1250 119571960 119571973
    0x12040f081b0c03060f04020415031218051504230306010303050d0b010309030f2001061511030c06040305070f170a0207050d02030706030e070e04030e100e090c030702010e 75
    0x400d4040318070748161503211041d03400d4044100c0801d610703808122820810fa00301390000c07402500f000d0b4051110000b44190000c00c581d01d035110391404446400f41c00c0006900a01003030056604801010010f06040c1c42e045194400449107101600841c001c02c402c441426610003540e1b0807c100010908401406641455841c0e00300248164030521005040c541022040e00d1154480c1c441c2c04000c5030107603182030051a01400445d11541ea5000f83c0000b565000d02c00400b410080c840e140040c00303030007840216005131060281020045803800203480e081440031207085440800c1e00e661003075041c9085ca1342e865441c90034903604071110901508080c80c072a9050300310070b070303c400405040d80710342c0855842c1940e400c02c11518111950000750140c0001c0ca01308081c0340030f03801c8000c880a610b000d0b646042d4a5101125070f0410860b401d800051160381e4141c90350800c2e01006100c42490f01d0038041c045103c2e400300740b082c8400b03402d450741101d0000000722818402c0d4404d40c03012640000783c444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 119574460 1250 119573210 119573227
    0x6070b0709171507050705100515030118021807080112060f020c010902011407020105041e210318060c0f1509080909010501030b09040609030c08030103050303072312040f08 76
    0x29103200030451482c80f07280200108003200d00641c242d662003135010b401070900b006a400c0b41c1010302806028000b8541c811111078a49640078000c1c130400c030010000b0b0500c000741d176004020f1101d04241c00c94040400100c14400740550060391507055130b5185c82040801450703441d101c40241038070752004107610320105240d5201201034200c40d20184c000d1361a800c007050829240341140c456030800a01042e41040204000320a196001038080c90704407103524101e030340e60381400c6803407ca071420041301d10a4081e41810150031100191401d4102010503446908000c406030030b9002c10328002c0d11641e4601741560801c450140001900c49000c071051003a40100e140200399504100c5006224072410b200100d55540300b40300f1903140d068010800b491a1319961580d00090450326020340402411410700000f28604400a5000310f210340000c55907890498001002c05c610341c44581c00808044010900361001041581c042c41d0580c515210261101d1801418424071040c00070003050380403804c1c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 119575710 1250 119574460 119574463
    0x510020a0e0405071103041806030203030403032102030f0711070312030b040e0a021810050402040b03090c09010b1c0b03010603060c08070e01120b06090d050303061801030206070b070917 82
    0x5501d49041e5401c1c480e81c1c0300d0303140540300402043c1e803100f900d90007172104010808464904c04103906a8510001e281c9480b07030082030541e40305030003d401048c0c001d241e4210030300d400104019000b054040443c21030910490200100101070440710070000310101d040340340c0b501403222400440e0311034850415a81042c0c0003401420f035002180d40b05525204560743c0c0744c0c102041c081701d0305900800c19003c1a0a10b24508104000a8410f0f01511290074000c02c964445200070400b030182d50203d25142e280c21034003141307044c1c0c42a501d2400799030050300403c410501101550f2020041d00b20383c19015000c424a40000c1c04a160650340c10b6091a40c0001400803e5212042d0031a16940b02e00c00c82d13a400c5810f441621911000c2c9000070f0701ea800c02003910003a0f40c4400c4084100408140c50414a90300044118503a40d40940742c0c0d0704008280850b42c80c10020050b034150270501c2c064020340c91600019168054188043e01d140c0d450307000291103074802d4401c800074010701c400c400c6011101c0580307507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 119576960 1250 119575710 119575727
    0x203120106110d0302131e0e0a05041e110f1314010314060f130c120c080d140d051506070c090b0103061203180b0c0109150c050d090510020a 62
    0x20b07035980228400109194440d0084580c040a1407104200842c9043c141c1569038100060843d003401c403405010450035500000c00c1e0060752200c401080d40e0a0a0600f03500310014603645084140c04842d05400060504c440c3c00c0d200348080320002c2001040c0008206000c80030364980c0e103594a01f0b00540f42000340303e80340720306907405040603419110400c080b850b99080b05031030802070b00f420039001442d135264001e003000c16203115816510800b65501c00f1100102d503540b03000c9841440d44942406054030030080c0004003403542c0b805c2c8004550269483e00c441c880c02103940307171a944410001c1c44001d170010304651180030180003e641ca50440c203003101004041e0040c841c515091166900ea86e6200380103001c16076407100b9468040500366501a1100180c50281000c90030440100140d42c2103010042c0c10100010301c0045460309040c906841d650444084400d00d1900c0d00c0d130700008440c0c0c010240e80005140c20400682800c0c2401d00c103180c5041c1c0310800c039501e070001801c10902035000703218 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 119578210 1250 119576960 119576987
    0x80d2a084206040f0e0a020d0c03020c0d090f0e0c070209070c050c01090b1c2a090801090807021302160f1103060f1f09060e040507091808030402010203120106 70
    0x81d0400d005040e8208881c1d031207144901900406590340501c0300034090b0040c0b9403c081c610800501e024100c00344001580d10401424000c00d5001c81c1086140342e0078010b00c41c0c0d0034280d142c440c40301810190703010030303112150140600c804500c0c0d00007041c40c00280c0c200e4032115002066800c0754a80380000800c6504460b40440b901d014800c9080440c3d40180414001d40c0e004104a90600041c005401c41041d507460306000d0719a200c44110160001406040384001c88141d42e001c16143c035a8000b50107070009034002e42c0160f00d42400240801c544909490702a0360448091004001c0c22540901034001c8000d6803506200c0d42006008200001300e000245510a60796443c1c002030b540b040585404080b2401888a903080001400301c91a40c4440c002c4000b034a03940004154030341804c842140c400d6008141c3c0e840301a0b00740428040304201c05001888241d10501400070710000340c01c2d40440c0003d0003080401d011003c00d08582c024002e440d00710f074585d02e42d0112580e642e400100811340d23500e507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 119579460 1250 119578210 119578321
    0x7030b13261b03040501020607030b0103020d0507080a0c110d0e010203040e0a060e090f0d0e01021906060e06060304120e0d02040f090210050a021c0e090103080d2a08 73
    0x40000c4a20b00c0401a18115001600a05100d6582e00400e401a1000440441c10150f08101c8480707441c803280300d01800380c2e41540c0c0f281c4661a2048042e0200e400550710344042c400000c6085402c001c0c00a07500302c20310010310700b130302c840480c80d00140e1942c02035802020741c3c980300380e04101c1141d1196003e1070446182036060310031501c408807080d40300c140c0014403500a421045007000d00303c0c002c1c190311014400620480300480d4500c04c459032803d452150850308140c880d50200020b24880d00017507040341084684c90700d1800c0c142d032034190701c1451421040502c0b412121042c41c40e95400110307a03907140c029105000001706296804018002080128401c68030400030b040002d1140040c1e800b00c4140d0b8000b001c0c3c8410b0390f440c0b0b404403524030202004004004032001010384410320750070b00031840303071240c0380d11606080c1044040c0d80c0c60400b0356080c2d048604818600d00b8142240f00100e604908101007151250340009410f00c0150003580c2492500700c040d00c1201100341d4803081c03000704501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 119580710 1250 119579460 119579497
    0x30a0b0603040f1103030903010603050c0306160503070f090f0303020d0f02060c04030609020f040212070f020c0105040b030702010e0f0304232b05070e150307030b1326 74
    0xa0030400140800c1d00c01401402091501c00001401c0d084c0c0d03211403c40081c1100d00f820841000a401e59010f034100b1070b10b5400c4002c82d039120341020080c0c0c2d9000041d40c4100071600c00e5042e0000c00e280402007a6a007041303040c02511040900440251014050f040259801a034503070030042c0d644c3e21451840b070300152030540030441080c130202c0c581e80034603079a0f03055501d454515142c40d03001c0d0004a40680e800703800741c07820000d2940e03584002c10400c021204804910b00d068030b0040c1514010f00743e0702055403ca02d00c100740341e0b80c0c80400ca0741980d001d5083c0540383d031101c6804900400341011484801c1c070824003810746425000020308101c5070035400c005600e99500d400c03a0000604807484607040210885481e1107580c01441444a600c0c0e501c2250400f2900c50b15110703c0d2046681c084106d0041d003400303005000e4265078100c13841c11010750050181c40e1840e500c00c0e28000c0000d00903035002c0d0710b920b0f00c54200018001c944000c104601d80c04001c214802600402945c0078440003884503a815 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 119581960 1250 119580710 119580731
    0x60a0e1905090f010608010603020c100213080709050408160f02030f03130909050a0f050a240e030304121d120c010f09060e040b040207060905010c0f03060e150604081002030a 77
    0x18443c4505036611551640c0712a440d002064001c1c1d040030800071068054490891544407103403000d0402548240700c0c01c0c1c1060300c3d00c9601d50410100da00702d44002d81c1080100400b00b507141c401c42c2c0450300b801900e01c040b5107240c1450440b0071041d10009605000c2c07004083d1001e14000058070528085000c40c4031003035a58032a402c02c8907150754004007160013401d101004101d4401c4425a0325014000343c03000100c155603400805a003140240c0110100041d9039014420b4030300c00c2c0601f250341c588c000c1d0302d1070901d51640c5084031695a103404c20414850750f0180940358508081d01c9120005e041c40542a590750802c9885080a500300c2c1e00041414050441d00303840750230004100e41e980d40350b62203101a113105000144c448540f00a40040e002c00414001840c54810a8861405040002081400c9a80c01005e8007070484e4140101414030800703101440c6800c40075508250300030120038210721544003041c0c243c001e039440402940078850080c0c0c83c0c8112a0002c1d4860400080704201d2141403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 119583210 1250 119581960 119581981
    0x1b010f09061a01022a1003020a081501080615190503010e0615040b0313120201020a021002040521010b06030f0f0c1e07060e190201080f040f02060a0e190509 69
    0x14656043e005a2102e410b9000742500c002c4820300d1403036031000c0089a80c1c582400300f442e01c900c1d82c1c0c00c003000981c001242c1000540c84072500c0c0d00400c5c80c07110407184d0b00e04074000030100300340031b80700074401c0d42e01407188202e51804000f103515980d5054003140c1344100320384010303001e5003091055850f140504400200e040c07a04984001c6a4072500c4039440c107150408581480d80d03007005011310450270a4400010101d0310036484400301c00324031350025070b54500c0c0a0000341800010050340d0050350041c882480fa6581d001480080b00360080e0544040a0042070a9400b500e43c201c28650410030000a000030040310041141c0324007500106d2a11075201d03044003403802c2c82000c0006040d0902c40c01f80c41d15062441d002802018020035012810002d4600e0550401038072030810010642600d42c03032401c550f000300034994403008811610031245000d4a85042030350050300000e1049400040c16400e0728020024026450300280c0220244410f00380a1580840240241e6119880620001e60310750003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 119584460 1250 119583210 119583251
    0xe1501051503090703081215090907090207020102030417070501140313030e130e0105070207051e0904030912050703060b040e0c060c03041e05010906080702060c1b010f0906 76
    0x8001d052071540120001440c0036942028040710120301440034004081903448002d0140c618100911071b4850074082d00e601299201812002d026040030300821a88000101c0c0c0c0c40110b07200244c016949500b20f2004078103500c41c03034000a800401c1e481154015840c00101001691030a0f01c0e40038049001c00c40c0302c141400101e401100100940d45801c000901ca10001182d07030002801c01a4011070001551085c1c0d0198208018142e40d514104141150704106040003043c09071607281600d49084007014555082c0500c2c90301903181c0b607012508040c8a4006480104210360007204407a9603858240c2d102c503010700c02500d5983c00c0010210141c64107119254250031210000c064522070308050110320b4004c2120281c160009100014031001310001c0e4000f0003003147c922020207403c110000d001c5038220303004401088030440c1023040701e503000a13065402030000e01f0440c6d02c0d503003012900c004060942040c9078a43d4240641e4445589076500001c464910031513050201e01c00c0c070900c4019222 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 119585710 1250 119584460 119584469
    0x30705010914240304030206070801140d1e08040308070501061a0703030507030e010f050603060117030a03051306061503141308030a020d0608030c01050a06050a030303021b010606030e1501 83
    0x12441800c1d001403030040800c80550309250201c1c20f0210702c41e070042440703420844064001d0303009501044100b6038402c3c0c0da24094000d0391a8030380f411816001042c11107a55081c01040c2007042598201c403480c120690ba582950722450180d9100d03101d250010594000c0e08040320698245200030590020001e010402c0341c41c5040f0b00303030134104c0366141180904405042807040c5030f9200740c500d00358070003030080e00a000c541c0039001c2483d0509100780752070100141d0210b60b42c1003d22131000c101030700100482d0181011442d000c02c035034a0368011880107818072040200708074034008000171021005007204464a003242c604104011024019801c2401d0450310012010131402d0341700c00080b5504059600085010303801400d20342d0038403554044804580141443d68004210620503001c00d008090303020034080c074207100c140d161201003000c01f8110b00008091540100d8050b44000c180540b1030070348a00c01c3e0003030101d40d80c1d44001070000c0c000000c50240500540729600c0fa1030007901d82160413035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 119586960 1250 119585710 119585729
    0x30105010b0901050a0311131403030a020d140d0f0c02010c0309020109120f080705070503161d0c0c060a0b012a030c021504030615080c0102060414030f13050307050109 74
    0x50b0700d40300440b500e900480c580024541e40c1c0d443e513444c07944590050034180c034422152283d580c5c14214003045481d19000c400380b003513104000510046902182c0248544083c4c20080c582d4884016000d1103405440c4c0f262002a20b000121440c001f4990004510100070307400801226107004011030540390764410107030204444000801102e1052086420418025070b046c0c800c20107140d8400c0750341d520001003560719078080700f018003085c60184424540715500050040700740c0d00e0898404400042540110800c1c0318250020f140c0c0320000d0100c17100401f80704180c90951902102941c02092582505400500c0720403004100020200345403906a1400c108103640480075036040701c00000c02c1d1012a0000b000812048000c000c502c0a0706c040c520800c0b011072460014031052040c88040c3c0d00c4448298080300c042d00741c69070049900c541054000b032a140300800741c4840680345100303455481e401b003040041d143c001d0840701c0c5103180913240c0803001d070342140d56142e0044a4242440c0907035030700e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 119588210 1250 119586960 119586967
    0xa0605030d09031101180305060412090f120222050103050c0a030302070506030403020a0503070c051c0308180c0a0303050c070605040e01090f0b040218040f02040815090c0303030103050f060105030105010b 90
    0x4070b0040c134405030001e001454240311030014549201d40301c20781584105c1d00c41c3e1000050104014519441e550390450a18211240f107240406d504c0b8900301034031440320000c0d000d041040075520360386040b5030480300c00d4481701031410725520498000c1c1001d1209135894080c84148403014507001942a084942550081c41c81c2c41c00c103820005950710107003048081d0720400d520040001d5080c400381903041d02824800304001c0c500001d010504010041c40205040318070900000aa0807201c01508918250655203100022100d400e10341b0304808501944000802c0b4000205a807050042540001c14829610540e59441f0151040e0061703019020201d99071310300501c0040f410342d120440c5402d02d0301c1c01083c0d0800c1c1c04003003800c9030700c0710000520001005840d02c0c1c95090500401600e10400700046240a141010075030302e0710762109180402801c1040071494203042040604085403005003525a00c0d69a40340903541d0700d103007202c0480320b80540000000e10b480c043c481d95040b00e9100c01d07071914 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 119589460 1250 119588210 119588213
    0x7020105130209100e04081306020a082205060d0c0e0901031a0705190504060e0d2301020d020c0f0607081005040e16060e031b0d0204090206120702060a0605030d0903 73
    0x405020040641d00b0048580e60009138a2614100ca280518061400d8548d16103001d040005000c4080d04554259401782c00306400046107001298486000001c40f0442411400c084018060b5560f21080d4840c0d804540020108a547c1c41b1131101d40c26600c0b22032091084c1001d0011081c42440040c005400240d04034011400b00f204013a4000800d25140341f6228041d0003500390940d600b503600c0000740003c1024441d07a60019101c4100480c2151a4440c1da0066990a800081d015141060000101c3c003030721040305094054614071004004295140c0e040d2001459480003400703074403081c5200c0e00c0041010365001d0003646000303149920000b02110304140031b000141c010310b003529100d4451420a1046118a08542c401919056603220b07155690307241018a00f814211030940b111035501c0c42121b45544080424440c80d5064802141b8203031540001850f038025980c9002542c0c1c170305801c200c14198045481c074032410754a001003107502c0c0c440c0c2c141a0b540d10401d032190041550070f0424030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 119590710 1250 119589460 119589469
    0x6030109110f031302120a0b070509120a06020d060b0c060106051305040e160911030a0b04060b07030e03061005030a030804020a150203041401031509091106070f020405070201051302 80
    0x148041144145a1802e4141c40d0b10b4442984102c4100581c0300105201301c00714640b03001d00e516813078441001840d04d40c0d05507c51076446c1c003010340365100340040062190700300c0e00c6240441e81d038408807134150340b00141d860070312802035400107007400c0d8458070f03102c0041521115030081c4c6105c4d00301540100903d80c01c1c05020b850b1540801215000728081c8500010540c2e100e0048580701065203029010340702e040100380715407541c15006201c0e000e0034074210301400203e06040d6030380940300e4a4007040c00406000402c00404198125000c0c60000180307090030305400c0003404496804c203804695003079484c48511845000503004496040d000910008042842040745580040c00200180000c0d41d4640000c265203c031416610302607007010070704004468848503003500840c000e08040c000019540d07030008090b1058040e4001440d914001d00e02400030400380e10120301e501411031a0780300c0007030030030404010040108038840c07401d100001c0e856600c18000c950182c8034502550480d60903642c00c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 119591960 1250 119590710 119590721
    0x21903110d051306020f0c010b0a050d110d0507080715080709030605090c03070810050112030801170102040b030a02040905070e0618030a1e02010216060527030d08060f010c0206030109 81
    0x10440d003d95299400031400030300c01800c44894181c400c603a68000007803254251640c1da01010301c038a690207010000b588030502c00c4021543d00141010f03902c440c3c1c80c001844600c0c0201c0250030340c03090300c50101d1404800078041081d01c6440408050000802d002110000c0049900c0d80024069100400018520b17801281d004440300045c4c8a082c444000801e14000945d406090700e03902500b080d807508403d41c400d01d800b415890303200342c00500c1700d510b015101c180188201c44580701c00f000e40081b1250294144e50280c0090303000240c0d20300309407541c10083d400c24000c0c400c0142c07500b00401e802074020106400c2c03d0101604450801501c16500500031201c508941d415001b22001c08001403458030320f07902240d407014403641c800b40c00380c0002480c2c815180c4014482140b8100203005681e08207049d14904140800b040f04400c402c00204144403a05042d0542c1612440c01d10b1382c0d8064108107880d01c1400141c1d002036800701180c00459103c00340b20b8000e50000d50810051115840a4000703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 119593210 1250 119591960 119591971
    0x3220e0f0907091107050d021e010e15130f0c090c020f0c060a090f030b0a0b10171302121509010207020607080a0e1827060a0b030c1003021903110d05 66
    0x45040c0001c5841d5075080101d40141f036030040c0c10104c54181d8801c1d1344030044241c941100020807000260b404020b984420802201c1905804c2e280000d5501d82e241e5089100c8690011400c0d501841914200f8020341070741c01140ba05030f0400a49196451002802084400190000b02180e180d030b14184907071544640c0c1c0100801c1100400450029903c010b100021032142c0385113a514580200f0303581c00c032401d009859210700d2032101406403540c0d0040c514800c1d4540f800002d02d840d00c0300c0d46d61400c44526000001d4108682003007801c01840b02080500c10b0441d0a14580c0300d56072101625400c0384140440294041e80901800c4040380d02000035011206140c14825038603d81080054600d040c000c0140c000e0340c0e80001003051401c0725601e01c2c0c00c0c2d110b0b403000740c0d039009000346117460f1a000c00400e5405419940c00340004660b034200b104002e1441c014148010128101e10b0040c0a940010490301004400401202c0749600c60711a844d90000c0c8101d50034180400b8407114030103040050b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 119594460 1250 119593210 119593241
    0xc0907050f0408070302030705030109031211070c06020607080106031b1103040f080703030906020105071407020d1502040303030b03030304050a031209051005010315151703220e0f090709 82
    0x74648080319010003030000d40001401400c00303618520400d4a01940c03034001a001e0390528544900098100703441c00b640821802020401c40407920190b1701c0c82c0250100501207900c1420000f035419004103c00d0f000340c1c881d545858a50b130f00c5400035030903207a8500300d44201d050801c24050305544200c030340c600d20045040945e458541c0d509241c00c04518941c018003d2500503880c01c204040c2c03c00320440060140e40024091842c061078003500c030601e00c4002c1c005404000403440110f681c0c0414510320140e0041c1801a0f2407102520b4038001c1d0001e00045012a04e0114084090302c3d0010680380700c2e0b0390000050100848580c4d0883d810300900f912505525207031074461000680c1030000c5c5400301d40c0c3d06000282907156003040300f1001010880d201602d440c000f03001e8654500c1303007503010a5070280008001c2c4d900202d50440c5c42c43c8a000790810f214094150110070310a0b403440600112030424500114540350560f511500d42000e4070381c0551680003210410a09415800220002d0000413 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 119595710 1250 119594460 119594467
    0xc060f1109010507050a060e0303092a1309060c05030610050c0a080a091802070c0e07020a060515040504060504052e0902060f03040c050301050702010b060306240705060601140c0c090705 82
    0x9950000f0745d82300d40540c0c0825080032080000e1102e00704031400602074099086488850b4002034125a9801441c50300c0c0078140480400311080310a400200105030300071020401c4483d0020010641d80058500511408803107201c5c8400520075801d6900c03409039400688200503840d40c8002c0b566000040401c03d012141400042c0840c03c84c8000e02d070681e910f40e0141c3c3d51402442e022600c4ac00c260080a11100d583c3c05011b00d80342d00182c50403840307502000c00500e41e20f4003c2d40c02c412021800b1200e50080c100310411081150780e400442c003c0344200300301c80500307058001c03086000d022440400000075800143c1003c108458104041180c005805030b4038145c1a006040c0c0c265104071b03815503499030940313400c01850809109240d8407840500c02002094502c00c00142c00b84405042d161013082142c649500300807808010621841c4500b50301503642900346402d644424040710181e01007082000e451003150702217022269081c4042e009400301c0040101007000c02034019100384100481803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 119596960 1250 119595710 119595713
    0xc151a0907030e0606100503040f08090a03050f07080606010c0803070915110f1606030515180109060b0315060a0309060c020c0a08010c08010e04060b04020a0c060f1109010507050a 79
    0x45046000300507075a00441d9110344207060525001020304000d004000041c1c0303e0074003550183c01c1e83d07003007a40702c2c00c41030035080b890801550714051010583ea114945210000c01c2000c0007601c0380c428103400d800c1e02c10181c0e98094003500da460072102c090104040141180008140300d000f1980402e00d420131041980e1240d40b80030380364203a11406404210744815500c4246401c102d0303501d60031007140013081d100070148500041c0007094829002459203690118080600c0c0a08115649002401002c40c0e164074604841612030f003032060803c0546400b0700810b84201c1c150440b07114003011500030211001136000e2041e15403195011408041c2c0c0c070890500001d0f01401800880b080c01d074028540c0d9000c0d2401c001188019a11640b0143e04d05094480483d8000c51907078116000d1000e14040c0d13947d01e05007840501180076092b07610510000d040c20750540c016103c8081e4034050b1200f081500b40410032030b0221805000c400004800900c441070082d8854030081c1012071042c0f09445204105 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 119598210 1250 119596960 119596969
    0x80d081815010e04150501140f120d0201021e0408070506030405010b090108031803060f0a0e030d050a020d060602030703082a030a0903020f16060c03031d0c010f0c151a 74
    0x83c1c1052002814003424002401440c004505c0c0c0301c0105c800402495140100180414100441c038178010300102880f101c8507615031901d2040d843c011015540c00850452000b4001e60100308036014020417035260394015442601a0780950f9620001824010300b803070f042007516000180308491a640b100124030043d00c17030500e01402821500300458a40301d08086900c0c180302181480d50003584038508000310f100912204079080700e01d4190000e84070345015545411480742e1a4640400c5090000780000c00c0603a9008100f503002e111010450b054a5200490302d0784a60303500980000c90117004202440031184c02605603d481b0000ac00c0c0b1050010075030701081d081161400f00741c2c0d503981d400d0f10906406000d0b211410300d000340503150200380c0307840505a8a006002c1c1c2010400d0014803681014069800301e80784001d8580909190004090384130ba5600e811345280d400a4181c0001883c0d00380603064100a4a501800c003405204420405130010450b00f5211280d100c0f42c003104030318a0b242c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 119599460 1250 119598210 119598253
    0x30f060204091b020d03090f080901090509070908120705061f05190e0c1603050c16141807020309041a0603040f0b010b040e01050d020307091505030106080d0818 71
    0x200007008036110360082d20045c0c28000600884014581440d0350900003490502030b06982e03541c004041600d134550301d40125085000c603001070341c000e942c0000f130081141d0062542400c0f03882c407004a0740700c8007101d81e01c03400303170b000e2031301c00030400da101f03602103422114520341c0e0702c0150305036032441c4c5440350799540061646000c1d40c02e40e1a0902d4400e00520a00003071010081c8c0c0000107000d4a4a401c20080d407038400f0469050024040000120f4100081e00c41400080341c203100343c458198a464465a940118041c29100c0b80d104080c0911900c81130148501034900c5440e03550051810a049a424070000e070002010f840f103502c1141d007640700203641e00406140030f0390181f00300c2d0880220516060140c550180c00282c44510140710400c0f00c5e03040c4011240c196501607e0040701900c49102207868849240c00c00010349062a03846000d0340c401d10085402c80e44202e000703000781a5249a016101e000042c40100001d60200000e0300407907541105080c050941030440b4181c0165242c20b625031034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 119600710 1250 119599460 119599481
    0x1b1602150a0903060510052b08040311040c080702060a0c0903050601030c2310050708070501091202010c09140603040201120c050405180708180f01061409011d01030f06020409 77
    0x1080da01040c030502c01c51780310b050b41c0410001c052003078a50510001031261181c48000c2180140329500240030b0085864104070011750110340706403101d441e03203407100140410784002030065181200303030300402d8890072095000d28915008bc111640729208001d0280281054a800348500510b0000006008006c214001c1d80991035100724036040c4181410f1095403820320101d47c0d00c0c80340301200035580d01030080040d040c10342011982c0f00030390310b80b01c0310f14045c04e0790280c030301d520b40755596090061001d08003106991940c02041490608441901c5060460103909200c100154035010b441c00c00c040115040380c014106144413a81c540d89200a030340201004100156010078108400d04005040151880c407140050516242c07802008000160082514a070950320004446801d481070010000c3d01d4000c4000b40069611022200142100c0c01c010318045d04e115000040c400c001502c0c0100c9204d81842c044403aa481d40c3c45101c0220301400d01074079000d070b0800000442044511801c6101d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 119601960 1250 119600710 119600717
    0xf06010c0b041101110708151b190905010c0f060f090f030e01140f0306040c03020408070f1406040e04060c090504061202040c03050c0d090c0e010b0309061b1602150a 73
    0x79012200042130004101060700c05c1c0d5006400500c081035011400a008003400c4040a0841c3d44040380c00c0c0c040b80d0308200c0c03a135480100242c0c061a005811100c01d031194070f6034071005000d036654801114802d88605010b00303040800f00c0400e00045894204c010900406074000c03414402544030300907405018901280803450340142d017041560440d021091000c1d50b0f140780b5062100d2038145c1061803000901c030510850350740f008105030b1402a416100902800d10480754400d13156244281c206685005524000c0942e810040c0c0c07900c0e082c012034066601e41d0f010050b0640f604d0781d030301c0040c1c100b12100742e00b80000186c0200b41e035125803040b40001c10580c40c845180d010386006000454061081a0b0105030401d820810741e4446d610032210900d40003040042c4400080c00d00b10410800340d0010403142c5845400003581250450203140115545400e42d600c0b902c03500f2110075280c2c040648803003d1542482096004030000020b01d11050000d050045003041e020000e22031680001e1020010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 119603210 1250 119601960 119601983
    0x2060904110403060608060c12040c0315020a020c040204080a081305090a05060108090d080106052b06050102100603051519110a020f0106031104110d050901090213050f0f06010c0b04 80
    0x744100f5015940040c40006e015244030708007140b41d542c0c944221004281c0884174180800d0801c801843c0040007583c03c00d216014032010328600d031000e540854100001845040c01c2e03500d0920341442100c00320748115005000006040d95058441d4111000400088202c1000051242c58417805030340b1030564094002490310f8660009400320341e019100030215440806031003481e6403c481c907581910742c50308200303444009800282ca5056003d180e0140903140b0404640d06859031900301400703459090f02a01d000504440100302103441c2c42c80080e105034454109400f014155002c45034000d540c40b88691048120f134106075043e0b0b40c05e600710100d40f800000c0e1a084080d41408025003600c8807400a2044030300d1341e169407842c03240702c1103020320855840070500000c80c4a142100c03002c5045550174000c070300e0503844080c001d102c02241a80142002050f0520840c05c6105040c07041d08448810141519001c400fa1140c480080c641818440610403040118849501c0c880c40369100300c0ca100350 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 119604316 1106 119603210 119603213
    0x80c180108060f130504050c01050309030a0e0109051002160f050607080a0c052401140904110102030d02070c090608010c050d02030403031104150807020c010210020702060904110403 80
    0x14060b1104c21a88113110440e000503208600440587d00c01d1881c2c5001507030288000c50b14034600350020018442d8450040500c100111810315001201e55164400b090090340c94452510140e804542d841c1c14528061fa085009080340c41c030312160041c90200891080c0c0144039000b001540040b07940ba94681c40385d80e0f00f43c1c040740c01104482080e00128011250407031055807800c4003141c0c81c1d0010031001003911188098060207030501d580390b500c940300c81120710440d0300164114003081100da03e20003142c2c0003a181d030500980c01c0100d01442e2030384a004035141507201c3c501c0c0d41d0405644841c65034100007910586820313403001603134aa036186011802170a140c550420001c0d0081008150760000d400d101c0300303400240d1106103154a64400980e039807040e8a2500740140c0c03207480b50340c0c20181c668014104a500c06084141040c6e503010006051312a042d003007600d01c000c045010030 = true := by decide +kernel

theorem cover : BRFrame.Cov 119424460 119604316 := by
  have h0 := BRFrame.cov_init 119424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 119424460 ≤ n) (h2 : n < 119604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
