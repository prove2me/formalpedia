-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0825
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:00:58.838738+00:00
-- url     : https://prove2.me/submissions/1dc37a14-33d3-4ed2-bd8f-b0a9f037f58f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 148201438 ≤ n < 148381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 148202688 1250 148201438 148201457
    0xc01032c0a02010801121a0402011806050c01150f14010c060903030203040b06040c02210c010e0c1503090a06090602070803130209071103042c010605130905060d260a 73
    0x15a040704d042801458a2840e9400700030b0300e50748000302080c3c0040c1c588148054100440c0035a445600d50101b1414007004003c03e054a40c44050b01ca9000404440c0240d03007442c1c0c2802411201510780c00032148503101000c04241040150440c903640003000904200c03c0c44014400700d0b0b501d0043c0140c082c080c2d00d0050f030b24109400c0002220100034a1a40100d09245507901d003a507000030005040d8003201d0840e0716445d44003107440150312680c04804101d609049a00c01302c0c0c41d000c00d4004564800310b032400c030a01e80507510141140811103800441e03410549642c1c002c503c168112442d0140f01d600011f152170b1007a41c8000440d0030559480702c1242081c000c140450030569806a001000d44c180141411107030b4041d16a0381c411070040150360990800e05200e4001220340e0304003e44484a0803038015a16048010b1090300301c04e2100d11010000303e40020154400d2040c4d80c001c403005002c0500c80c0e00030b03446000d41d28510f490700c51105a48406424688a4400d01500e0003207601e80d0f030b0706500b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 148203938 1250 148202688 148202693
    0x1401240603150b0304020f0103020d02130f090c0f030902010207030b04080d06080118060b030a02330406050a1125030c080d020312150a0e1e0402030c01032c0a 70
    0x100c40711510302d1140e07400b64a1080c0401103240382604e52160781140c139906175140800048019001c0c2c0c0c50b00400c114000310740440c0300c80d162001c8400743c82042052001d25559180443e09413a4100c01c07450100b1554045080e142e8883c0c0c01018900e401801100c3c18541d4a83d00d00340ea150080310107403040d030b00100d203a10741c1000c0f0340241002000031000a200c25480c000320240c0041c2d0b001701c001c00c00c9654040040042d00c1c203000700d090142d00180b00d200c412292a461149041700c0b014a12142c501014040452500810685003136900d25a980d5041c880c140700181c41001e03070741c03003142842d104141d0790303000003c8584506002c09003809114910b003031540c41c0441840200743c100b040c15421901c20392900340c1d4000151100703410780030303400041c9440300e40c0d01d8a558843e4040d0640c0020076040c0228030880b40e400305902030303c0c60803031f00200c6e15a41c02100220003419a0001e40c903410000841009600ca40c00c2514403403400d4180d1450080d1201c1d150b500302c0100d0915031510303085280007009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 148205188 1250 148203938 148203941
    0x2503050f07110304060f0905120a02090c0a02210c0f07080d020307020f0603180604030503070905100c060f0f050103050d0f020d090506030a0603140609010c090e041401240603 77
    0x82007941410400300a215115040d920303402503020703440401c5410415900054410000807004000c0a04040031021000c0001038484090b00001e90080c29988003099041d51080111041c00f42280d011b0032400c1503501502940142107241d56202c4001880a200240018400f040d65008620014400d1516004003181841c8a010065055410a0240c0c0c405a10b40402c40c440c040c2040301c1003a56650b81c616442800e13540480450700c503100b15001c100416411500441c0500841d071102c219456607007040103008440340f0320b408002036214140300c000803040d4005444a2552140100302100030410301d02c22914240e0054881d9030001103158440c540291072074003550398910180c6020301000078081c0c00c03443c1d14424140540700020000b00c06010961000015592207000d042284808580c05541c40809880f10200e41d481d000442a1140c06a42d00d0b40c102d50205520f4440303a0360382c0d1501c03030b650290001c040d1420f5484000160184003694032111410b80c408500ba2007032820000010b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 148206438 1250 148205188 148205191
    0x70b0f0414031809090f030301030f110a050d0b04260915031311060d02070b06130501140427080a0e01030b150c0a1509020913020105070b2503050f 65
    0x1a0640040100c04030481e0290310407290b034003080e904e03ca016110036080c146800040e20300c0c801d060002000100c1000000445030713102d18002c04000346404070b20801c000c454800d42c803840354012802c0041c60300140c0000038159101e80582500c106130104900c00054291484c002007107503e200248071090340c0341941c00a401450460384e4141103140810b4001480f4405c9200940300540c1d15119001c00d0391030204480c440d060074403065403100c0307140c600071a440c00195022441032206910b00004603806114860488000e000c0c2c444000d943c2c5001d020050081020010085000450a08040c0324030014030740c1107449050000d43d40d04145800401500d81d4003965030415061209644c00b03556150244000c0c03841485046a0790400c0715000391800f200c010004140741c81d140501c0030840465803208000ca802644c014140d540c4030000340f1034183c4140c01c020b002c91018000000030466210301c4a603c440c1040c05511040d24100402e84c040c50105411030000781c0721400c11088400c4060b1a6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 148207688 1250 148206438 148206473
    0x20105090705010e0120120d0b030109030f18080d080907080106030b0a11090405070e030d0c0209010e0c040e150109060f080c03060607080c0f06011211060708070b0f04 74
    0x1d116860410000800c81140c481d0320320304002c001c01d8004400e604039004400c800c100c88003100c9060301c1c10032504440d604980315086605103880d103504118201802801c4a5a50607640c024808455185c29510440c0a20321581c80e0310404030040750740c1030b08005000400407540c89203a040c1c40c05100c3d80d803814686030010003182e410440e04200151046028a07005070101502181e190044405030009001e032100081c1d04c103040070240b05a494001248180c1840160103a6030340c00414841501d01c4189520025000015840104074011440c1d64494018480054403032a250740c5010b254120301040e140c4c5940101000c5108899613008034583c0b0091880d42400814001001009040e1031401003228950500010000d605942d0300c1d01120340b20390307001304070b1512004000219540c0b6000c40c040d83c1003904c9048004203008000c9510908165405001e0282d95081c00c402c0c0110742d0488a41250a642c00744002d000042d04661191b1190343c1c1070682c82000d1425040110340e007901038094 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 148208938 1250 148207688 148207693
    0x6060509010b1602060f07120e10020106320a03030504150c080909060307120803090106090e030a050703020a0206030a020901030501050f032116080a0905040b0603060913060c050a02010509 83
    0x40103600f611844088070030f80440e4660380b11800c00240400500c20014001c20304409803864000e40c41d00700700c118104140c141c444440c0c40120a00c140e01300c8120303003c0c03400ca049c01400d036003418500d00800c41f54507141c0721200e0396103180d41402040074035881d50811000700d1404101401403a401b09818240004946007081e4185226200e40541e48510304032980200010700006980380c90400015005007040c41807000b1186c40341c24a10181e8105032010f0215508210300001c946c41e0078010480481c0401c4013461030f101d150031061743d190303200a80842c25400740615040150b980c0c48d000d10310440003040701603641c3c11070900040480700140c001c107120340342e00000985030342c80014410610000010702d1000008041081b54818000d1603401d14500003a1a40e0381300304005040540f060001d95140c030040e25441d6400c0009490410008a0700300c2003e00c00598030b032a06a10013500590040c5043c00e09140c03039100c0d0010341d280b07c4801c1c000710f45d001441e51141c40d070900c185503000316140003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 148210188 1250 148208938 148208947
    0x140103110405060310080d030212010806010302062b02030a090605060d1e0501091509031103070f030e130c030506010e090408192105010e2505030a0b060706060509010b 74
    0x4015400740654024a0f000d48000710019580c02d080c820381001030b0201304210785e48000c98090040181d4441c0c2c03150f142035046800001205d42e00000c4060584c1d5000380601e04200d50441800c0188503250034045d031108001e40172034018101440110f00400c3d2150020a50341c1c034a0402000707441d000f904203805580222207900110b144090401010203040c00c0007114a050307401d02c81d016140e4030501070b1117402c4100c1180a183c09685c407110f4542d10030340390600c014149400e07098a80c040c0742c5001c0c00541c014101540020301c10410001c0307201005010b12a111381d2600c4620480783c640b0317800000709640c0c005001d41580c03c2100385211b014215010340803450b00d039030780395401d003d0001880b088a02d081c80603500729028140442c1d03144d028803464840a074100c0ca548024101c02e00c2095100207518000c0b84079106041054030a0a40782034200301c00d00c01c036400440350342c1c1c0020000810b4607038415864119a071144014540d5074021203010451078100003c01c51702140603444200c48590070070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 148211438 1250 148210188 148210211
    0x11502030306030706050c03041a12090d0e01030209121005010e060607030e041a061615020705060f04051f05150f0a0909030905090703020703030c020316080903010e0601080601140103 81
    0x9040030581d5160b00d821a00c4a81c03d1f81850300d180116000500706404d50488c1c01600c2d0100c5000d0062070541c1c502c055130607184c1241e02c0791121080c0003841d00141d02404100c02550080c1c005240c0c003030029101e080f0304000034800c5800d254841d042c41844617280c2c0b004100031409074800b5034001d0400c44d00c961405074207541c058282d00c40c900c48180142d841c0c0180b4481134440c000612011500a40f215598510741c4801c454114403c82048441c400300d8510180a1181031098540d5658004018162901d52600145e41044002c0c411100c0c2c1c451200b100d280f80425091000034a282074002142e40d007041d02c01c2d0054403032402d01150040509001e0401c5030b540d807c0f800310442d1601000014100807600f422141c5582c0c5401c915003120f0300a051040d41a8160300034180c282c007941d02000000c90341c0e142282c40340324042041032600140080d072008100385000038109541c1c000d000240f1182002946801d0003c264840701c00c0740c014a00402c11b107803c941310030311005000d180400c14044ca54 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 148212688 1250 148211438 148211443
    0xd05090a20100c081201060504030b07020d0c11120f0d09080c03030f16020d03090503010f0506060405060901110105010e06150301030506130501090606181d0c0415120b01150203030603 81
    0x800c0d60100044006418140130600c01180c0c007200d8030710490f81980d81c450304094201d501606c0219040c001c0a070008260038404501131141489550740c6203005d50141c0c0340d039040b104080790440c5d442489400307c001d0405040180284110700200a0b104d8600c3c003280140001ea450350154400360002e020744601c940c0c01104070b03a161809400350f16121010b0b104800c1c034404951100940040544850f00203054000c00e0280c00c44904038001c0c814100d441998034140d9a0aa805503001001440f09108524004020300210314040c98070b8001c00d440154040d09461003a403190f1441e20741e0005000d01800e2141e0300ca856902c40c072000e2480e41d4550f554450381c03140014880380346924048030002c200002900810102d0760000018481e4503107400001075440300d1a443c031841249013005610380700c0342580d01c1c107400f250a9806040d4480c48039050001400502507440045811130300c003c20500d180da50510070030b40c019801030f038141d81021b030840d040442000700c400555205004004882d90300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 148213938 1250 148212688 148212709
    0xd141005040b01081905180703052d0709110708030c0408120c1b0f1305090d0c02090f0705090d0804032906130f33030302030406140d05090a20 63
    0x145c0e0000a4a56100c040c0c00c00b200324901c03244100b50041c1400002070202c0010700219201036044402409051402568942c4650350450400c5402800d001c0005402c2a03216070710603580004c1d0f007403500300b20f503451482c1580120307600c2100140118060124420801501c0030071007801c01000d20300400383ca0318030b5a60b810892031200032600561100c00c580c4503034a40e05240310001d44110400c1030845600400b4200445081d2543e2145084044921348034000101020b50050440c005513110309245035001319000b800c0a0a11000700b045000645680307d0b0410b007103001e0029103440382e0841c0342c618104070301c05880d00841c8291061a0a403410000b1303545030800e1088407441080300380a16000040e00000400c04000c900d841c404042e60420700c20f200801140c24030648080c0059001d112046844600000d0b0040e0b1080c001803103800e01810ba811a804084481300703041240184008054030304c2191010040e4000c85a00c008010642900050054444000007180f05e40c5030046404980c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 148215188 1250 148213938 148213981
    0x90106030309090213090f050702010c0e10081b04060503040323030a020c160f0609080706050f0d0902042909010b0313060f0e0a0314040f05060d141005040b0108 71
    0xe00003891171403168041100c80050401c2841880341d0014101c1da9002400120f840101650030109110b070014410001d002a42800901c031469030651403c1c00c480000000308122070301d440c40300b40c1b01c0401c0c2045014000034200d907903505a5031b240602e4000c0101300d81150030036100030708035560b82800c1344101c152035100300410001602c1c1d9280d14070040c644019403111940c42085907001040342c203036040c40c990964141c2d803036580ca4140d554103072540c2c610b0244030b1000042c0c410301c0000c80d8000c0b180001e0003036110000c0f010404c01d0503500002c1c22034181101300070503d011043c0d01071050751680010b41c024030040f9990321203503150046400062100528034414003003ca0904000c00025030301984148090740d038100480c0218041c183d03520340318010f0660100341c0e00503107401e80c170070441d0803201070340e406100700841030f45490148030641d004051940c0b01c151320361085522030700440401a209034003030344d000c1c900e6034900070502085514400d4090704000300b80082004143d50589200300084 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 148216438 1250 148215188 148215191
    0xa03030209032e110c07090509100c09180c0905061303060204030807020315090a0803060d0629010f090e04020d02060d0c0909091e05070f0801090b09010603030909 72
    0x82150010303080c01d0301000c0c0c031014402c06088001e42501c03035040700e0205a54229041044d482c2a841c130400302c0c042c45580741556070010b24248141d0001e9000580c02c103000c401199403203c0e0480900c0140e0b41440400300000f12513820401ca5081c114202006145139480700308146103410500411041440c01424003407000055051407a0f40000f02040044d50805000c5455a84900c3d000f0455070000304203074401c0c4514542c981c160f8100381d01040c041c04500d401464034090650f1010001d81004107010f07401000d2020050115000380501e0101805541d49491078000301010050906407032030b0020f040101c50100f1201d000d4011042109544c102043d550703039543e42e4800502c0034055603c4c025008000466500a09140f58010494071055501c90580b13850b02c03104000c04841180700054a481c044540710074489454101d1504c0c00c03070240080d65150303500c3d00d00d040400c0d4101d500001441c0c0d516004c4074280003020b107000760403600c104000e1104503e9030301c0050402c00c1c54090403e800e07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 148217688 1250 148216438 148216447
    0x10e0612100506040305010614010302090604030b07020a0c0801050f01060809030d051312090303120203040f02060702030106050316081e0705060a0c0204050109050105030c092203090803040f1d090a030302 90
    0x210001d010400c01003100504199503151249130181c080c20040c8104008180d051040b11142e6000c1e00a440d07e01d00c01820540c1024615124021941c601a00c524158041c00070f0000100d0031044500024094020011034541014108402841016401038040080303d10601842c0301012080314002002c1203c080307456103610007280028000c0000040180e03244000403200c4981184000b41264041c0d1180c80108440d20100c1040e803000700da00401e440c1310711806d1401031800c0720180000c2ca001800000b0030302d80b210082450b000c04110b0350414800088820004248100070341c840040b40d04041ea0131400325031418558500450141d284101030114240103000d01c90b080700440d00b038004109100302d5075a00c40d20030040000b0f008942c042d01980b500440756051111130705005240c00e40507617804804443c03291080d402038100031000c1021601c00010242800c0014001601c54280e440820500e00b82500d549410346a10002812580d1000c1040046010a10320501601401c1c090b030748 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 148218938 1250 148217688 148217701
    0x130e150913030e040203181b060d0915050c0408010e03040f0e180105161b02090f092a090f01030308040204090809060a0c11010302040e0402040c111203070e010e0612 73
    0x30f01d440107015402900c00720411440203901c280745003000140805552400300680880c1203c00c001e0b414541e049502000782d51801c80da40d500c000308003800740700905150340505092209841c029943c9040c0c8510128051181850030f1041549800c07112005502e0645801c491850040c10780c416684140c00c07180004224100d165070710450036950b840200031034913042803114480b6504507005000110300701003a0b00300181c18003038407124035001044a0803513622110fa1511030700000740001c0c014024269051000e0444801c41c0c1c8180640c03140150805070402e0901080201c000c1600850071030100040010030341100909411580550f8040b45c0e42070503040000c103130b1040055040d00240300150500c007035a4021900c11030301d4410510400000c8001004505900030360142c00c03207002c07070240071500514241e800f8107600641c504000e4090fa244505150810b007500e80240240360000040240b02e40d4000d1804420440074200390a00074038210100f02c05010b02c00801c0040041d41010906 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 148220188 1250 148218938 148218947
    0x50a0f0e0103061d0a050d09060503040803061912050c040f0c09140d02121e010b0a09020c01060803072009010303050d0e0708030d02070c0504050108030703050a0e06130e15091303 79
    0x3070075181101205c650a0452500b240c1d91074400700044009550300c080424002c2c07044c002c4a004a41064401d415a20344030104400c24450200c00740c01007168280014030b4103070030705004e544540950013070095943c0e800107110903503612040d1084040c3c0b5025041c0700094010000e1403c3c1c424141c581c0305188d04030008521403244408000e03512a502c07a40c000e01c80c0750000380711901d0400e01742030300c0b24401c070144c1c440c2c2c2615041a9100d0740b150414605120300245540544980c020501c000310701240d0710100c0c64111307888071406544890600704102c03012603003c1070b0321816580a598000c2c2e2503145440c002d0107401020004a0025141c0c030710303071003003007802c122203c090301085080e80c1d41c034055200400000d600a0004903081a1740b01d400194500e003910905048400400c0694034042803a58203c4183e03000c5980d80c0240400c40302c3c0d85c600384c0c80e402c0140c1501045a0300d1000d0207070030842c0b490304101005102c0300b2502c4c007000d005600d585854403c00c3e041011008009000b41d600e00e810385 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 148221438 1250 148220188 148220231
    0xb210a0e010213050102100614011101020f0301080a020111070b0a05030a0912031d0a020d0b1b03151f0e040b040605041e0b03030a021c0509061201050a0f0e010306 72
    0x55800880c110b1501c03c40c0310350700b4040711000d03001c480564046ca80760400355001441a110104071030100a43e055014200c019007801c0300100052510061540d80407a1307420a0304101c2d40d03a0700048030b80045581140164405555a200400381c00d442c0c503c0f07079901d503c1100480010800007001003400c00c0b2054010382c2406a0040310110140d0410034000c008001d104440074407016a405003c5864030041120000645c010f070035828403080760f03101c035004840090b001e62840204c1c1c0b190150345100300c0d40554010b02c113510203551301030940c90800a000c032100f031140c3c5a40124049000010340c000c076464010200503613022801c180c02600103001407045038061034000d810b02210f021042c11b11034004884a5202c42e04121841c121018150f50707010701849070015078040d20044030701aa030640010340080403031805a00e01a600d00204d00c440d0400440822250308010040c0990b1428414005c06003091300000c05986107008410041540e041c40090100c40e0b54058400b1101c52040061 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 148222688 1250 148221438 148221461
    0xe100605030f06062a150c2503020a050a05030306090c040b0304060f020c01020d02070c08060402030607031a060403050307030201050c0901200a0c0305060a0e0c010503010303032c010e070b210a 85
    0x7241100e4100010340301d080f426130034175020050310006000c044046003034600801d450810401600c001020b01230020007142c100350306600c500d40600300003c908109201340c0c6ca00ca003000e5604ca08003081800708108002d000030811150a000038000c6c2e4031240d00b9244d0050300500c01054020100350944002c0c030070060700100a50000811032290200b640007401e43c540b03d200708814003981d5041d0301c2e8540006850095058108402044d14540703e0380142c0c00b80e03040c0c0b2101c1008004800c000075150303403003980111119000480c000c800e054081c4a42d41d880107640720702c14540180302c80001c0925401d0040309030f00c51740030a90042c0c4034600b0049044140d51100342c82c10040d4490408503a28030b412600d40d0417a03424407002402078200401d000c0f0030000182c5605003964210759056000e040d40614895044110512101d880d08248000915001c8001e00000b00b020b40e040003641400d030a90090300581c1c0c000c22a980c01202c0081402041c0c11910505140c161920000c04024007408480d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 148223938 1250 148222688 148222747
    0x10f0e2205090a0c0504060f050909010e07030b070216060905060a050418091b0506030c03090312040303020a09050a03020306010b0f04090c02060f0f1501120f02040e100605030f0606 80
    0x1003284242000401001090003a0a504d102c190b42d0720820084d60361a01408101d03d184e403004010900b071003c040764110f00350b00000714170a01645982da1074106298410369040745800103100302180c05000000102d02d001c00c10703c81542c100700c4040d080181e60b1242900885000620000030f1f48504150350160407c4440000e4400768124100050100c0c0381040e0b80c00c08000b0901e102010500603940c04071000a440142190303607000715010b90f604010140c03040780c0020815200401d1030030080c82c0c45141701c2e44005032200500700740208041160f40001c0d02400c1000824000760f680040c4c500d0440d540702c0982a6181e503052201a120301403039122b00981c90503d80d19005854001c603445201d0800c10448848969030b4580105000000342d550041100441001c0c0c8140c1d413042d910610201c0170603002080000070715410004a0f80b240d80315411a881c58010f004004000c0e0010381c0c0140301da40381403411804e02d103581d00e04130400580000d2140f100010001c0305640c580e01408107080380c413440b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 148225188 1250 148223938 148223941
    0x10e060a120e0a1b230402040e28020403080706020c071203020a06050709060507120201060b07060905071517090c0d060b100207080a060207320c010f0e2205 69
    0x81c080d0765481c04050459169941d00900c01444e050082c101c011100000008440204070105d01e1120180c0a8800e41c1c100d6000c01000c01c800b1340380960680540462107085030b00c500c200c5e409801c10009a02403030144e80c0100700800c0400c2004094076034154100100503583c0348846402850191603503c50350ba0203510f031128000b80341e004034040046500035241030180760307101c0c0030459500415000f11804540b00b03000f84400306036243d0b4a956000711500000803255102c0c3d800c0d40d015007140c00204c401507140c1250100300207007800301d030004280e184c50101d01051640e03005050044200d00305070552603902c6c0010700714074040000420b0004050140f054060303160a24070701601640c03030010700a4a40f0010002824400103c0f0003c45885c08042e240c1c1d0600d55842e18042e501800e425a1404018040d41040e156492090301c41c0400010032030548118000859040c030352007059607414001c02940c03d070f0040d9040b50520f114202c0444155662205142000302c107a030701d03415281c007403510307240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 148226438 1250 148225188 148225211
    0x20a0602030705010b09130609150203011e080a0320010609110a020606030d02031c020d020a020303040c09060e1902210603100501210201021227040902010e060a12 72
    0x20080002c00d0103400244006100d00d0705210064200b035480c0f8040043c220340070404100b0550003000080d1041140001c070744002d07044981641c00031307008107007031080441219114284000d4003500921459010b04440d505030f44000d0318125601907810146809910403169840c400e5029070046e21401c1001c1240c820b03c6010030b02540c211a001c8009841078202007003542c60005001003041d811075004502c5d01151030401101140700c0071a80d502c00ba0244012210541c250024000e01c101540c01035443e440c05080003400e4010f00d5200b848500e160440c140141a05083e105a00c4030340300e52905141c41c0302c401028000e1148680c1481c14545c0b80c0d0710700c20b01c081c0c500303030031405400300300d00301c54815594070220400c90700e080c0b00d030480c603c5134441075480300c02080d14404589801401070700c601c0d051151b0b1005a0b81d11034000d014066001c40080c1100090f5040c15540f005410348040000b8149540007074000320211001d98860000072420f64942407150f540840b01c0b4035407038002c0c840d801142 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 148227688 1250 148226438 148226443
    0x9090c0f050f0904060b041806020a180b12040c0b120907080115140f030d03020408060c190e0a171c0c030c03050d020708041e0501030c051c0207020a0602 68
    0x40c00362a6404031008400580c928040c40c4049440c900242030110a84a07590307a5801001c140400913002501c9014504800c80d0f41e5030310b20f50081c083c810142c6e42d04942440100350943c5038000d24440110300341d043c8880350540054550807010762800901300d03100e0782031240d0140d680c1c4d80400071801c00020b0981c1703e0040e20a03680e001d00204022201030303603140d41c465400d070340ba00b10080d04176403031400b030070010000300c4052902c19031710140452003450f80388004682061603041d4060003107038000400b0402440208a543d42c051452411181491104016050308840400600c0100090351104906a0782c5110f5040f00502e1312404640c8580d041441c4151140601c2d10300600c40c0c15003034044810640581c14046406605540311224010190b40c02e940030740000c1c40e50310300f0390341c2403000c0d0300000c6c2e281000b440a0500c000300109150b01d03401e90742c160004c070340d008941014101100c41e211241c128095030001105100d84601190865001c500240100503029500128451000406070f401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 148228938 1250 148227688 148227713
    0x40f0306090b1506070213020d0e07031703010510030c020c100c06060f030b07050a050d02030a1a03160605090d050d0806011b080a0804020409050d1e030506031e070909 74
    0x10360340b1840142d9841103001c4070548003508580c0c000c4801c211a20041c0380461911b80c424000500050901807580300500c12104001d60049141d400000306005005072040380759084800d4044451a560500000c9000440e661214000740740e00c0f0449201c00d28020302007400038100150440e100c5003d4180000c4c002c44414005880d402e10740700011840c410f002e041c0d04180d07600095103280a40703070300d081200c403503004039011410030209001c01142d40070503000860060100c448081001030000c140442e179038041250f0503100c0d500c81c84c9052282d0050003c01000c550003428120b8941e14a0400702d4800802600010300a000d414200c840c40e6412080c000d0160000780e9400f0f1818814200783c044c180183d141c007515450040c004161070314841c1000c02c2d4054400380011507c2c03c469501c0c4d501d06424400d611000c1070710074204d44003d0040303213020081e107041494180801d0401401203505c80e01801642101c2020070440040ca04408001c1d850003071824410030072582605007040101480d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 148230188 1250 148228938 148228943
    0x30e0d0510021801030b0a0302090c040e09010603061b09090c050d0e06010e07050c07150e031e0c010216140d12050406030615020c012d21050108030f0a05040f030609 73
    0x5000c1c910f0120ba51091040c41c03207514003d850280902e0854081100017003004000c0392148000f000017060b00c0400040c41c0380620001c0303002007012400c514000050342c220032903082280316000000c0c4d40d41644454403804680900d00006500b00310a00115401c0c415000203500060800500a1484400042050480c1d9001da01022140c980b1101100d0520848480b0840b50380109070600c201d55100418171020000c1e802c0500e162450310000c241801000c1e001210311b665010008103007000c090000c084040000d101620004038108032240000c003a40c01081c4800a1418402400e521026055482250002d00702203000504810003051075105004100c00241046800615800a050484880512500034081c0b030703085000115100c0c03203221180310b0200d0008801c5000f803990012507100b1003550350380784c000780070a40007050301d4a00762110709010903180c20300400003014040103840c50b030074400c0000c0e5680d075503104040311030780120380080c081d40f00a0b0b940003040107582c0d0710610f112403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 148231438 1250 148230188 148230217
    0x150a0506072a0b04170313032009090d14120906090c15030a0504060f06060e01140c07030206130305070b0910170a0f15031407080304030f030e0d051002 67
    0x3107818158150384107041c401c1100c4414240010b00184d428241100184407045c400c030b909040e50f02c0850480c00aa60740141c511220707211a19a02c41401144040e4086080d0760301c048600344001699034981e402681401003014040043c87c0c00c0280c51308590144807a00021140c0341007145080d030f10303403605841910707403441413003900240342c00d100303003940c9125504402882c2980e441c040032502030071004000b204e110303641710059540b2074264841d280244c0b00703581d285500c0000040000d028101d15140d215000c80b024030801012400004503041500e6040c2c407031545903a007105001c84030101d203030402001c5008403580070503108502c4c80a410140720441c2c0c0010b110780380ea030050303c1e900d00c4600d032040c04646060025500c520513401406e00080c0c0030200045083c090340b0004441c00294004407030201c42401d07030600900003006102c1c058400d50020354905444c5554140074030202c04402010b0001c0e260003060156281c0c891620043c0e0824156003110030300d02e81410095100c15070703101140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 148232688 1250 148231438 148231493
    0x1050630180609010908030406050601170901051006021603022206061d090f04021903051603020102070605030903090904020406260618071701021605010608010501090212150a050607 80
    0x1050081845c00c98101003040c0c41e58a81da00c0d11805018001d0013a13041c083c40a0f00701d0450328084100a210340783d80030001a850510700b20841c501c82c200e43c07000e01154400a0f0039214824003404a40440368102e6250821070f100c1001224040200301c4a24200c0345000000a103482d08402c0141481a0700b900707112840d45100b04014001000b903802810348141200090010300f40b084100c880c42c02005010b140451340c84cde80d4245480f14401d40c0350748550900e1010001c55804101c01c40181800341800d0381189400d070322060350790181e160124408c2035840045810b41d1143c5d884500a040e100020f11031418404440701d2905901001e0001ca520620001400f003d0603418001d603500070078800303420218980460450300200040000d203507558200440c1103900d5400704680405031246001203103451403c0582c40c21500141d00c141c184034010004907044106820902e40e2002e1800c0c00d1181000a0001080642e40c4603007015410040025000c01030224200b5aa200309501d84074400d002c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 148233938 1250 148232688 148232701
    0x1502030901020d09030807060b0415060306030c080a12030c051608031b0412150e2407091a0c010906230604060819260408010b010206010506301806 65
    0x80344c40b00d10000d00444402c0c00004000f81c026000b40d000104000d00115003622015075447da00f004641c818008203079201001c1081100c011081c00042120f08050007107042162540c032000c01031078940c0c00405907140f000340d901c40e0245068440302005c0c40d0f01802c2210851038404e241d540f0940f1111441d10701c602d10b450035000100c048509a0b0403403c1404c0503a003180e55580304040c42c000011107a80d031034403060340e00c00c1d030300304000e1641d00700076450034610054030650700c0740c800c2e4044c040307900b040040074050265080c01601035942d0f40341e800c40c4584c0c0780082c41c40980142000c141c01041c0f50300b80143c4100040020301c11940701544114014010380780c0130200006c4960034441d011054120800020034148040305582c1568020014051a880c0041c1105080f0f0008241c00043d0500440c2c1445409000d02c25241890400e0005206a5040030009400c81c010121110b4460121404501e2407035803200c1d002403411003a01d90f03400d03907041c0108000304440070001ca01c0141c1c410400010702 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 148235188 1250 148233938 148233947
    0x10e01060809010c02030d0b0406050306070309030f020105060d080f0c06090106090c0215130213020f030a0b1012020a050d0f09060b0604140915030f0c0906030c010203031503071502030901020d 85
    0x40340444d42c2c000350301e418000004a0003404e019420300c4e900c207580d4480080d85403002d00441c1c2c4103040b03d03540010a024203140103003a030902100c429046a2602c0208102134548802070056590800d4405441d0009101000c07198801c0740303d900c4040c022101408002e07003054202c1016035854140034480100c582004903515550300094148000c444e00216414018052444103102e00203400003280d8017a01d0030709000e82c0d22040803c07030385240010070420850785510a1401c440390844014081034030700c4000418207190344191800c01d541c00560070700c081340180106d410301d212403a4140110081e192030180288024082034400a05041000226161207012907080c0c0ba040f04603121202072290902c840b00c04018070444078002202804901c81c0e070100207140341a441c2c1c0e8000c001c0703404100144648000f014103c94003035804a40101007a03030300231095951119202c81035010071411000000e207020311035400388041c410300205030180c02d41d010004105096084c2c013107a15080007000200ca = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 148236438 1250 148235188 148235201
    0x5031218160b03090304080a0308010303030b090105030c040b03101503150513030c1a0c03090c030606031f090f08181f0f02070f0b0711090603071e0806010e0106080901 74
    0x1090345070703400414010206468051900321440c0f1040342e09083d16003e075185401d11640c02640411f000a00400c20140d0600940413100000d40300318441c1d514001c00700380c0d10201d140205102c3c4c4c0e2940002c0d1320b15102045881c242c00041c0c4420b000c2404031a4a000c00700c00d05010903204107603490030600f0044094002d187c01601d194000944000311910221140c0000c0301c4102e520520b6003c03192100f20180001a000340300c100e00c0240d032810709858a17403400d000051024007076048a0b0401c029940d0104101541d06400e0044641da200c1c0e00012000800c0d8501004001c0b951140b0400240a20500031b011800380008446141d884000c04118003012031060450201582e41c00c481512445003110311801080342c0116003201e600c40d80d12004110742600315059070f640100e00300c0c0601c0940b09008041080039282a030560602c003000c00c4d1161302c1805407440d900c0340240300498004207402914000d1940307006441c50b650b1940300701030101c0d03000c3c031601380051b44007408151a9503040c81240b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 148237688 1250 148236438 148236463
    0xf0429040c090b0c0703240b01020c06030c0c0a050f01051602010908090d050c09010b1908012402030403051204240c1b050d0b0a15030b190905031218 66
    0x1c2c4060f072500701c008403141d022010400303240c040c000300040021880c114000d0206680d00400d003c00100d50050000c0b030b05041c031800d0440d071015043c0381013929051304980c0c01042c81e080007a6901e505000582c5020703e100d400524034130400911403504032040d4801405085450a00400071909040c101d007070f21061303000a07284210030010303000c5c223243c42d1003030200c0c1d544a1400d030391005500f8400520310f070038240d02030f044c00e10700003c0070582a15000c0d8003008280b200d00704800d2550411545026058080035840e100b842c000c0d0440045c2402081520019a404401c03200b16031900302c4030750b01e581c100d407040702c100000600c2852026803481100030490f8946549440b1255201e8541946402501c200009030490360f49001c2010b40324059102455801100003650600b84a48210211031140482d0490030400a00600c00614134000964006559616200c40d07405210080f90080ca132031200244144000a900d040070b4021440092003020300d00d001c1c440c0c1c08040600c19444803c09401da = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 148238938 1250 148237688 148237697
    0x118060e070f05090406081b090a020c03180a08030f07050712030f120e0f1b0307120602030606090901090c110c10031d03040611070b1c09020f0429040c 67
    0x8032402d80740715001500390910001c02c04156070340d0750180c160070026200000c00c03112202200141a07420f00e120120341102032a41c0c214500401100318640f01c2c0100b4006030741003000c9403018400ba640e0000307508050180c80055940da0900030040c4503080c0d1000c64219032500440b03400083e0300c0881d61540c88a0390b003607200c03c0c0b07000021030b008640703002801061003200384e911819921100f008104d010401648040201050b40c600030324110001c010810051181c1e0203044141704228208250f4490240c2c000c20268803600c1c0d11300000c10901a040ad8039412400c03000002170321154070340005180791201e45411084598610000303172140655034032140c028001d0b66200c1c001600c00e41c0700807010300920605410311844400440d00b1988194090300c00a01d600c122842004414840d01c0c00510060201c1c40c5400d0015075905410030304500024000341c3d4132100c48055403a45000301ca900300d8020000c12407a00c0348600071060300c4c5203603006c40c5018074906403518507090500c2440351030040d9488 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 148240188 1250 148238938 148238957
    0x6010e0409020a080102030c09040b04090201020316150203040c060f08011a0f09040f0c081303140903010b040606030507030f090503041514070c05010e0321090103140118060e07 78
    0x28800a01107980c022038015200384000528a2001e00c080e602824000c8030301d0b5a144101e000b04400e41c1c51751005240700b1850090781000603038000045801e0303146c515410741280c183c07504050960503066002c07504401d0000080104101071000d00f0822384110ba100c1d01e0701c42c04c2c6400e0490313590750240100c105002c81c09102e5050305201c0d00c0600748032044041b141d480c0868000c0428107850115040320b0209884410310b9160710f420880382c5a01800742015500c03101c000da2070080c844004a49480c10a902c0054040c0d20740d102074202c0031049101500c103202c4280d480f68024002c0504030380c038000080ca0142402e81170780c4a0302031110010381080c0158241810600c0401e10240841710081c00e00031508a090040c0b004600a4010507001300d44080e91103280c00005805034000c210303168401d400501e40b14000c00c0c4400c1c1000841810341c1c030000d460707001080041c1d00401004080c4508011300b20000289083d0704850b905100401580178000155620400e01d0741030400d0380c141000c602400f1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 148241438 1250 148240188 148240217
    0x3030501060302270f0a0b030a05090d08060402070c05220e030f09100903151a100f23070b01080c0402070308010306020702060405090a02030f07020c030705060c010f240b030601 78
    0x40240004a0080410303002e05100c00000d24030000e47d40c01a4074001021042003002c40817807141d40d03801045500501180005541c0090441030300a002512a0303a001c10f0080038414002c00400180801500c001c00c0c0c40c10560400d080f400c44807800c1402a1f08001d52030020071f030040259910080305030b45060400c1440801c0046005103c545d4804000e1240e1000012a5440c17440c0059684001320000c0c07071140c09042001c12285c40c10b1a107000e0756182d5076903440d15a001031050840c0415107008032011200110b00180001c10300c0b06800ba201e00403036034005020042601d14100c603800001c407140c0c0743d0213506110030303070040b0704014000c10304150040003c035040740c00a01000384003c06c124a016101e10015000200a60700309840c0c583c0401007281100d90b44c07880350b0700508180000d100303410a0708000f82da280001c0c0103e034050140840d01424101f030035000354034110380003042402001c44038114910040d00407e107500ba040b810b1140000d2514016048a00940040e074814250b8070780344 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 148242688 1250 148241438 148241497
    0x30706140d020f0a080109020405060d0c0c120f020601080a08031b0d0609050105090a0605030c131803030e0d0503070f080711010f0209010e0405010e04140a051203010303030501060302 81
    0x240c0000e41820204540350070080c09100525080d032071005290380396001034a00034a0b040050b003102c600d042c41080144282d5a40006407561504c0141021840d01c403402c1040700c038404001802444e5281d071400e8050443e07005450132240410540c2100c180ea030303071100f1080c1d9843e54400042c0105c00100b01081c90380311114624013005c1c503424070303491400d2400d2004d00100c8450f9841800d80d503607200014449443c0c40c0c8802500040401020b018035806c0100003034546c07115800f620311030540f048845080c0815a00304081c004c9040e0211b14401019050244c0900384071545000180500c0c903500403501d0148003540c1c001c440680d1106901082e6020503560400042c10b02c00c103200c80e0b00c0300f4100d024802d0007039044078102e5410144c0c9400740d440c0094400a00e40491034803403420000144044d504000c00e89e0f6206400c081a40000011015014141200500060170724040c0b070700210a070b0300349900114105c03403180c0d804210a82e40c0795021800c07401a00520310200c400b00924040482d4603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 148243938 1250 148242688 148242707
    0x1401031e030c0c1d06010e2812050d0207051207060804080c16060f020102160816150b150405030a021203130608010906120206160f1505040210020c030706 68
    0x2400c04869034400b64503140386000c180d501807901c00d0581000b0318000749440c44016000345003804c20110b610f510000060b480002c1003c2c00012014000380c110396020500f4002c0011320020103181d002109604180303071620b908569a80251181c801e001032a8103000086401070785400d40503040d81424460200c13003c5030040c00607640310707900344103030308211205200d004d06003800c1c10b010414a502e46000507085104901c10702c010b5900c1031001c0d0301d0101c40e58050610203540702c40a00d40d2000c102000000d00300f0140700c05042d100d020b19191194030311952115010142c100c402145100c4000402140c0f48590b01416030980c0003140c007000141807100115100b4030141081c0c81c10015100c290030000c40d12580302100080800004102481c401d1141d5400b500c200b5104e681e0b441140d80100d00b26200743c0b0040908480c003440039805005943c40d25211a5610003190500307002682800800b80c4000d40c0c090740309100c150400c4005c607000198207009844042d000e001050f107000c10954000c043e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 148245188 1250 148243938 148243943
    0x509042a08072102092206110306010818280c0314010f2c010b040213050906030a050d0f0c0c030309030b0f010302030c060901020109020301060e240109090b01031b03050a1401031e 79
    0x850303011000006c00c0307070003071238014088021003988030b240c444001490550060700c01030811008030010250303042c0200e40402070303c4400303a6004440c1c0302e042192510034032800c006880201c1902000c020041000b66001600c001e0100074440018100684803c58105040c112000380780101c0220341540c4620800c031048010400010301031411b10007140c1039a1001c0b03041140003042c40c00c24066403402007145604400190000c000c0400e0729690f0325680c541180300310043c0700203440441c0b0814032500291801c0c0c4d6000005402c601c1d41e81c0307005000b26502c3c2c007080714201c90130000140002003d090260407030350010001c1a1015800c024400d040e84143c1180c0d046549859410b00517071000d000d440c000306029007042c0300c1d6207012626600c2c45180c403001101c07108040b0304008806d80e03002407500c1c140c0e0803035400000c4407045c1e20010390040c20200080d61030461610402850b0540503400030788140d1002c14207000743c2540f040c19121501007400000e201030b18880405d4000d0903440c907041c2c111171 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 148246438 1250 148245188 148245241
    0x10f090b030c04050a1d0319020a1a0c1306030b0a0504020a020718022817040c14060c061005101107121a0408070204060509010509042a0807210209 65
    0x211712002c070000d499082c800c440b02548000b139170600c00c00900008c0d442008061000c0c0230410305035030395a0148402d40e5400c00c81300231301001099480605d081142d05901d81c101c81c620000b070341c0304030180c00391195821140c880c0c0c420320f40c00111810180200c4403444590740c05412800d080c80862402da00110032000c4a56600f4403130b6014100a41000c2c9503500d5518003058420542048010701d000c079003c5003c8692542202440006600600200c080d111a95000f105d04d03203c100125030341c2d00642c0c1080e032151003040b00380a0035001d050101010340710140c41146c024030729044103940c800003034072207000e655000d90b408224081c40c425004603024400d01c50f070030b03100f030004102c04402001998203403120743c030000b40f51085140510030800180f43c01d41e561021585807000052070110014405403640100700d01c400c200f803a807510151941c080c141e6040403403948522185a8071000340c001c510098170a075902d0f480219100d032441600390740c01000061540d071064480d82c0088036080c00c00f040c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 148247688 1250 148246438 148246451
    0x60a0c0216060201061a1629010306090311070f09021309020301030302280b0a020a020c0909070806090105090a02010f0306030c0b0d1a01081302010e030312010f090b030c04050a 78
    0x2440211070000040007158000300d42142041c4400070034541b070700900c0b00761840801146200c6403075088050407081d0003600e4240e00d581e1182c1600709840743c1551400121211600100400c941680000d4000d0b0080d59601d0703203c46590001541c03007806000c0e44d83d405483d46410001c1412a0700100100786d1508504410199640c011030140d070002e804c00c0b00540c100345401c0c00382c4034a0f5410221550a035110104a401c41303600e50601840010300b19101e12600024000045802000303c0c418803140544042d0151629090240d2502114000c0d40c806000780000300c0c18944c0140101070107060608050112902164010340b455440010034106042d01d03000c002000c60490240b4034010204503022039038440004617a0b0044440404e515002c2d0001c0c18102c00d582d9a022003e0369000101b0300c07810301022424001078604220001c0307040c1d8140b100103525040c9000c4501c03200d040358140c2454415040d111040c0707006603160824030f182c1540c00380109921034600354200ca500080c41120000340f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 148248938 1250 148247688 148247713
    0x18060f0d0203032113080403080a03020c070311100302070507060503060307180c0e060a020a150603060e0102280c0312060b0a02070e10060909090309080313030b18060a0c02 76
    0x10350700800c40f41310314011000074240e841101400b4450307001810100810312801141d030344c80030710b009500001e4003e68001c42c040c5117850007581155a1842000100c03a081a5030b8a0100381c2600f0800c4c0c0d26004072410080d082a480c000e000303984400d41e014028050b05030a0840031192600010006036151040348000600400780001c200201900280040b034064904070b405454100c01e081c801d80610420058a41a5540820305500e2154015140786d0031b0030300180c0080c050101a0000341078549004070300500c5100c150300070912403810a07003a41c1d030280c1c44a80c16046182c001c031100c01140b04003030b40ba00003a200d80f6841c00c031401d15150009004d81c598540c140c0503000001c040d00564010007003408001c10011402d503201c5150070700440c40c1828548018003001c5203200781c12646d030301c90203103030100360083c80701002170f0031100200c0e070b03c50082440b10311080130701e44010740b000c03004100482c82141c0a68203100800e00072100800543d00e4820400b001440e0044a09045014042e0856013 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 148250188 1250 148248938 148248943
    0x904080708071b060801120b180c040e011a0301060302030d120912020307020406090c0f030908160f0b01051503041e02130603050723090a020904050408030f0618060f0d0203 76
    0x34880b00346503d51150358141040a030150b8410380105810b80b02001481002a12140175158002405001418960780600c9070728601181c11440c99801810202c80d106010310545c4182c0007000d00ca84428440802e0b402807608075100d034000650940c101a02e0000b0340740c0602c51444068042d500c00140c41b01c180c1c1c6400d64200044448400140c0000820500754502801f610002d0104401c08100705080800050000201218060300b8151500740420500020b00c0550b400a040d00e44c2450000035289489114140c4004007180c02c0c80c0710000120f2a8181321103601310010758603401e03d145840301d8840e4454140d071061044054441d503c1c4c40740040e12051b011020051104501207260f40c11454400c2c105a61070b0494080040310000e0184034000300010b10112010030707580c81c102c42d2a00c0340b840000c0e1042c9201c1d1504103003844107001c10800c040c8011440303040540e0000c500c980f2100200005c020040d84a1200c002111010681c50702d0901d141c5c146002008004460301c003c994003290 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 148251438 1250 148250188 148250213
    0x30a03050301050f0f100c050a061104050a0b03070e06180406030506060a0e0c120c13080705130b01080f0903070b040c05100c03020d0302180301290103020405090408070807 76
    0x10001100440100500e0a00c4420708450300380c105c80c0350a0207001800481c400c460f02048803400c1000d5025034006102c42480301c1031445030407040a2000300010030b188605984a841100c1c0035040341e00c0300150b510402410f032801105559629000c680da000e042101c660030004c0c80c0710540700d4451183c81582c0d2603104180c000c6100d03001400d52071034250208055000345a0080a40701c1ca690104006525824100d84e00035000050079071098880c420220540c0c040d86d428600411f40300c01d40410046400120b001c21100c00b01c508820b0040f0885594064404086502d80070401110214207881c81043c0c810360701003018401c503401c1c05940e0716800d201c01010348040c1c601c803d00301014401c0b4140050010320b42800c50825481208a0369002552503404410420406a000c9820030380d0081021046500c0200107009000080e4203a03118501d00b401c1501d0100e00c0e0381c10844241e00307940280281d40c2141c0c0020300c17413016641d554407601542d03070000ca81203e003001d003081000000f4074a201c820 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 148252688 1250 148251438 148251443
    0x60806130c0807030b0a030c05060f0c0703050303091b100f02030d0c050c0d0813060b0a170f1005010b090f0303070804030b04050105010b1201031b0b180f04060806160e030a 76
    0x14a43d051100300501280c000f60b4545015800d5440184041980b641c2103008030390040d1000c0356124a580c41a507464011101510103500404000004ec41400030265001e98010020744195464100403990700c08000c5203070381d400075065050201e201c0d000300601200b180082c010b0b40c2c41d101d038800340c400480c0c04407545900864030208075180c144404100d03410440813203007000102410080801d00703580040801c01052640c840d03110f20155203074100b0001c01451200c00e0090480c403224861a2548444510b40005200d54103404c01d2041d014090306040300e011301c135203074604214901441110303020b800d201501488104003010014001e1390003000150f00800141307120313080c0703807402c039094034410f900c4050100d00502444601e103031000d103110304581d0f000c207110440d928660358011072644c01d80d10002c0b06090114551406014200c0249000c0c01c044401400ca4140d91042000300e880502a040d01c580c0842c00060303560208481a000003151420402c040c060210f00103482c024040f5400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 148253938 1250 148252688 148252697
    0x308130507081f0e191115031503010606080105040905031603050a02060a060e0a090302010f05071805180a0209010516051c05070b0c03150603040b040209010501090b04060806130c 79
    0x54021844480702051250030008600740001081c4407111607503246401824000311181700c44910030801c00700c4a4110181014100c90740c0200040389009081d04100c6116900142142c0481c00030700d41031248405541c02511380f40e15990a103014040181b007403a00442e0f003440100030007002401c3c6c4c201a25803252003569545e07030700c0102c50002800c12001070070000216007030881c1072200210070a245a4000700280d03001540360090f0508a0141a445550030340c924039101c140615103a205480d0521100d40700c0d804035450359110240150001410090071001001c02e021880d13003061074005002102c1d0515205060481c030318003052200301100d400711943e0b48003a0066541240500801c00d900c03204e81021814402d03582c43d034108205c401008502d00520000014030010f284100c034001217070001d4135058aa00c0c01d03140c40100840e081d20103030710a0094071b000190035071140c60f101e010390f031064801034185842c0040950b98107034060400c50344031031051fa109401180c1c86c4520b0f01d0100e0956603 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 148255188 1250 148253938 148253953
    0x7050a0c05120a200307030e180f0907060f0e0d1b08010c02010c030504080a080603120f070209060409080430030e01030f0b0f01180803030c040303020c010201020a0c030813050708 79
    0x1c1c1c4401000c400c040c98214110310300c800c20304404010b607406e25405003803034002c45400b90005404900c4c00004080c0c64022981400b08554655010078072400880088803c0b0302d0b111442a01c40c0c940c007483c143c1c00900c175400011031600b0a50342d41c100c218030a15001c1560b4041c45c0c404e1440094582112105a5442e490f030041680c0c2402081c1c1c42c84003030f040c10000350400342c50743c6805120b6504110b00340084100411500c0d203080051111a84001200944554981400708501c1d03024160a9209280d8840462880d10f414820515000ea10501d40c13131805103040c1008e8142200713121381d0802584e0004503502c03540e103401e80030409148240c1d9840c4940b40003000240844140d01e907201c11a030b2034444c4200300c40e2541c031044817010000b403c000700940d07880b500e03010820345d06410604043c04040280416040c561000c0d00a03284203400382c0d4500051800124201d0184c0300342d44001580460001020a015012494100c41c180800c40c100303421a80b10140340050359404440c060b4440b0a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 148256438 1250 148255188 148255207
    0x150501120605060a1419080f030903151023190504150506030a0b06220501090b030c030a05040302160e0106020c031c0e03150103060213140907050a0c0512 68
    0x810342e544410704980d5100704030b0400c51003d03100e079680d580d142d024900b640c050740b83c45900148400000d1400302e088401c600098107400f900d84d0444101c56000f0b10401c03000c40b4415414440c0381d4801d0105040c500c0c0c0f000e10f4040459a0345611844200c1403400200324a02161103039604514920b1000b421014598540030a01040b60044140b1004181e820202409980c0e9000c04594100341900b40c0405c844501800041701c030b12070402d02200009030500003400c0d0345050300340b50003242c1090301c48010341d541d1420001c4140c40b08403129842028108005020000700e6489940c119000e841120341100c82a000d840416845811070b0780c00c4d5042e4030042103440c2d8100440825207a0950107407240c00c503c10401c3c0d16042c0141c66001c18404e000e42c907143d5607142000401c0e01101918280105075a403418184000d41c03241100c1c1c1c5502011003070204014001c040c9628403c0c101801c403511503944c02d40c2c11241500012444000c200904417401d0210b1410064100c0d90070b6001d01c103a507a00c0c01d41 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 148257688 1250 148256438 148256441
    0x10e010e0f04020d030302030a061701060303110304181a04150f080d08040b060621090606040219080703020d0204140f03010e0d0e0607080301090e0c0108060a05010c1505011206 78
    0x30454180406030908202c0181c44180c41c185650b981414050b8594a5502083c8098103141c0c2045171900c0c0d1107403071a05000c1d015004a42241e019803144010000d41302c08094507403241f80110801d801c00424100a044c0381c0e9442a4009010900c00d0280462900001400c2e030310100c030034209400c844041844032121280e000c0b4010040c0c0070051068a0305032901421482c80200301030f01e01000c010000d90940c072803400b250303441400b04441803c1c841d1422082003541d04180c41c041c4051241100003400384c00c05100322041c611100c10b9a0750058901c08080382c071104010440410035401b07200c1040e0409840c0041c1000e03000d0071140740c9410901e041032010021013916103a101e60305004510b5111903011901900910451800781005007165001c2a0140304401380140550000000090412450340c003050003180039000b0f6403007034408407004455091043c3c440591216540b48100080d43c020403400500d503201d1150514001501000f54013102d500341c0c00612012194844002001440d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 148258938 1250 148257688 148257691
    0x10614090d21050901140d020d020a0c03020f0a03050403060c12020f0702090a020f0f2214090709030804140109030203060f0f0907030308040204050c0d0504120906020c13091505010e010e 82
    0x2e518185007090742070f00008041c030160592280039400b0029042040c030303401c1e404943d050074003c1c00c15980c0c0c041513040200705041c440d00990043c02400d0100080b100007082d44960b294041e5030305818207046403503800003016051603031024000d414401d801114814005090380c8604200d0881d04e40c0f00134018811b289100805212246104010030480c03103245d0404d03511800a019a900d440b4106148814021005030301e590041540406001590080c2450159100f40041d9030300101038503111401d41e0050140c2c040109001c0302400140703c1d9944d074400c0325105a00525005401c1c0d9582d402103810503105544a00d45c6400440c00c010160700182d0f40a80c02a00e04070040100a2440e10000c1959001900c0288500c0d1504081243d1449076000d40da052403030301000300b0542c1040d10780100203240c034520000105035143c1f000a242400441c2c402c0340007030050500d0b50341320140d40e00307003006017400c840441c3d0000303215903990040500b520425002e07080360703001040d065051158003100b8050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 148260188 1250 148258938 148259003
    0x10b0d03020d1101021c02070201020a0b0c040302100305040507033e0103050603071202041a040c030b01020105101415040f09050405070b0c0a030c02061c14130b010614090d 76
    0x100185042c006c840e8082c0412448030443c0140c0307c0d10300d0300c0101c0c101840c5e07030b0300613007480c90701c105221380c5c0581d0100400440e031088074200d0345071081403020360039038034101c9015005030032407035042006c5404648a00190422116003210a11480e5501d008441c01c41901c04c4c0c4401c2c034040c0031419940c05204064122804030001c110007460045900d28603518040c000b401076888900e60288048000601c0846e184001d00c14004880074440050041828000c1c80d8019802e01d80450001010280203205035040c1d2000c10420341b0110701800f89540303c65120000c904810040041d81c500d410f9941000792010080110b40c6081c2070401ca413500300c190b00002c001c0d1004014100c580000010180c41003035141c201b283c44070340300d400041d00300c1c05141d520750840b08d031400d0b101d24452003503400130001007512551105180c554440350a10340141c03d00052180140c000140250343c01800581c101246e070540d884e01d01b000c61000300710039080760751040360031100c4001d07410710107090008e025281c0301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 148261438 1250 148260188 148260191
    0x30f0801333606170c0c01060f06020309090709081002180409050604210e0f1203041e0f03080403031b05150a0c0201140c0715060617100506030a0e010b0d03020d1101 73
    0x1300e4400c6250201e01018204018800c0c0c00101d10b50401000e41180000f440140e126100c401c0ea1120b0103900c1c0e6108603c464850315603400050a003500844020040e2200e1100074182120301d403094800942c000d041d03801c800440020003640c5941e9078000e00c149107100e4405404c190901d460502d2031450ba4510722072105d002848000403840e407203910091b04101c2141c00705c0c0100c1c2040040350341c2d42451a9a200710f03001c00100441c240c41014250001004100703445e90101c0d580342125450868a0700000b000704008220800103c5c6c03117880f45011a00c18200480304480b0150b07111483d2191120550008480c1d060400a1404c264428074901c12170070f000a1002039a90310080c1c45808005045030040c40b00454403105004013100c075482c0d501590602081080d44504c805004480c1510700c3c0c01407815400c00160703242c921041480e00f103840c083c213440d04544803c150540584142c54080303011750742c1c40924000329a5146802001035009402410210800050080c103030014a690010030303a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 148262688 1250 148261438 148261457
    0x509120f0f0606180c070c09051501020a1110090807090b1807080c130e0a020c0d050c0307110d0501020a1206080703050312090f0604030f0801333606 66
    0x15110014420624280180c4d40203841d600d00e064403105024040c00641a003422480c00b00741c80d1103e9210a00900c0c10380e070924501e0502c4801241d654140141c020900000a10151001e01b000304c480c80c12710400d800d00ca504680c5450700d55142245660084409a4030317144c0000300d9042080740d4072350460019041921a1500590103000d207171001d0041d10180200207071811001e550044010090700c401201307020300b42021240400a074200201c002024040c510194508a00800072a400c01602a0203582806941d4645008200b0544c2440c1e0b00a0584116040002c8080c4010110307a16282c070f600e00120140d040c6078080b694190010719040d88403010a0000c03900001c1940d610005501d0b0000c1c0719aa82030b07001341081103070b42121741c042c451352050104040d0843c40c1310540d1852a030325511160703694810b086105645a81c04110382060303100e030b0020000d413842c400c80c10b05031504151502d004c0c2d404d1440c0342441c10401846440b814001100602c1c44000c12602c0203000500e00074902 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 148263938 1250 148262688 148262701
    0x30f02040b1204031806080105090c03040b15040f2c030309100e0c0d1a09031201031e0b0106030b09090105040b07181a030103060f0516030207030509120f0f06 70
    0x107500c6034516404140051000007003c1501c11140a20380c0220301d5401e6080b80d03558800600039081c20b003c0c0e031b03101c1c001050000700003c2c0d481c070581e446607030800c200032215268204086c00000b00035800c15007054036440041c0100303540303000f21002071420380701c1400f1094040c0b000c400c5503814503400c0300c023a40080003485918880010040300c000c510010002d0303500c4046100c0d61911610640403500300c05542c45c0350341405400c1c0e8444e4140c004c0c11600c821075603200302c403a944900c191031100c0200ca504000610224442c2801d1241007084101c10143c10f91540c0c07100050503909034040c500003a113a803141c2d0b00c98180004070b581c01c07400e001d009000c2d40c01d0503071318151500c3c3c000b408071040010704029800c018040b142d008005180d516031540e0303814048040c000580d030090005941ca00d00700042d00c22001c040b44200761060100241b442041c0c2000d050840181d030141030700340d007001000d0145c1045540c881d0903e24510003200700500030400030010321801c0007a1119000305941100c81048007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 148265188 1250 148263938 148263959
    0x15080702010e060c0f041e0302270f0405150f01090b0306010510080c070803090c10020a050d030c120608010905060601020718111603020a0507081617010603080c03040303030f0204 79
    0x1080300e01c1030341e015151003002024440301e00541d07014101c0b40c07c032001100000010340307210710182c0b802540e100030580101d43c2a2217514040001c04055500700a00040d0809240c041681d0454461010b4901c24000f04144101c0003c082c0c903488100310030040100180490382c400d00c1c410b03940a80240c4000e61603d00084c03450090f0b0b400c2c070800c5c041404001003400d501001203480c455484450942c907400c1620a496a40d024608140e026041c802a0f8000c52400042d0306041035610200803c8688070f08901100a07000c00880202032105040011420b10395502801e030280100704000200b451b02802c02d0740ca000405040581550091881400300c1040b031001d00c040d404038000042a031807142c040d09a15841520703140c00841000445080825070b020944185507402401140c404903152a8081d8507040a917440c0119462095010014401c05044d0208510b05c14000080d50319035a0f00c403443c880c0e1003158160420f40000505108041e003504c20668548400300c002c60074142403854224 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 148266438 1250 148265188 148265191
    0x606090509090c0904030e04141513061d0f0106030b0102120c2109100311160f020604121a060105090105030a0915020901090816150e060415080702010e06 68
    0xd001c0d52102000035942c00c020003c1c0040d40c540984070009a19143c00d00408428030103051610690519858154195038454094000c0c911014480c4030001464108110f0151007c0b240c03048507111000041c0143c42030800315a041194000c10b00a441d2420038034266190580189084c5480c2843c0704e1126640060450781c01c0038030743e01403960b54480d8290315180c12101040c43c6c1041041409584a03007441c540900726041096407101c1e900034a40405405032062103011041d808424400c0070324510b0808010001580a002070305051703400c54000c6103140d402500321501d1101028401e20410015041c1c0d220708010701441c4030110306048000034054801c00d1036a504201001c004200040240c0d40402e4140e07500462010490807020400c00203500007a8109012441e890800501401e001c0b07201c80568805117a55107943d41402042c24049690702200820000b0805243c0110b45644000b880601b08088203c001c08500c03034401466240c00400310740031a41003004101c081c080008055 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 148267688 1250 148266438 148266449
    0x501180b041416090b12070e0703091406040609021002010506030706050a02030d1b020f120f070507080d03060509010b0a1202090607020d0605060a0b07080906030c0d090506090c04060609 82
    0x8080208440b03101601c0c11606404920400340380a07000190034075030f5480424106820389001d8094468420440d448209a1140c0d2625960281c00506028826803003072003450301c1000c61000f100d0306e103001c2c10302d05001140e01300e914503900d10100042d481d0645401c40002000d20003403100c0c0ca44034001c0b030746400440c401d01003401400328100801e50300034411703210f5251107604100088448040c204919109000544001d4020000007901401020400074403d070003481106142405003240925168403d10068031903005401c4041751940d0240808039108030242c1e00424500c1c00c010401c40c0280381a0b11040c64182c040241500e12500415050766110a5140040c0c1314212900851000d1013001402948a00100380301406c1000591015000301400e072555a00b0545a02100646124401024020b424140120500c1d450110700455000350610501da08150080c0d581d44140c40e100c850498a90b0080c10410408080c04c000700803a810b811603050200903c0d00e54041c2c1940c041c0e0244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 148268938 1250 148267688 148267703
    0x140111030a17040f050604030c170a140a09050310051e011401180807060810050d020303220302120c1503161b02030303090607020706030603030503060103090f060e0a0501180b04 78
    0xf403d0143c1541184032894001040d503002c3d00e070628004004690000c800c84100b23924180c0703440f00030205411740d07000c6203107922003881072502034100040a4100c0240e035010440300d40c1021a6a4909120308444044501400324040c1494042805c0801d180c134a0110550f656100400c5411081c80e0000ba1170402820706ca03901c62404011107125101c1a0040c00843c461600c001a2844d40300d0806441081c600500c132660689580c10001c400a1440700a5895841440080c00d5110105220420503101c0030b0341d9041c0795504c0e404601c080b54401500782d00c54000d203400459500b405010b4241200311860100c0c6107181c095514040c05000101080c104184170518400340301051510407159a0024102c03030701c0c0d15100068a940b008111071306030060189032030000b07500c0c2c001e00600060b40d90503107510742580d4542c00110000d0901ca031090303c1001c9501400300102c3c5c0c040c4180c3c6917000380f0314042c040c0c0001d03500b00942517642249100007003070600110368004c1100010f06907080b0b80c1c000503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 148270188 1250 148268938 148268941
    0xb092805390613051309021e0a0e040803010b18040603080702010e040b090117010b12030a090611030a050a03180803010f06080906010302090405120d0501030b011502121e0301140111030a17 83
    0x40401082c413000029040390000c00f41e842810640642181d848c1c804940300a02e16485a1042c00043d00070380b030051244500f840144400d44254010b8810307280440c04d000e0400348081300080590f98554419202e800c00002c4003070543d40e109818004080007070b20280010116540841e5100c0c070144103d807606d07540a05c0000e078100c020341000306e008400815407005070024540d0039881f13903c210b501c8000304030900760016256004c0c00e02480d408034800041c40c2020030111040e070b220b03405138a5600070107030354a0814002000401c42030900a0055066589a604194206400c841550070000c01e2184030410400744032400214603054a0b4140c420450b1900c546c80c00b1440d0200c1440c01c90041040454602c5066842c1d601c414100c0380540381d1030103583d0740c0e411504183d4502445400060304120f401a2094076860000e080502c091140710502c0e41c4100c81406590b002a00b00c0784980d044640260301c1984c1c040c829484040929000e1440e040c1d10b0640904142e0786148040340f8000c0110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 148271438 1250 148270188 148270219
    0x2010609020706020d060e011a03060a03020d1202011d1917030405010c1d03032d040e010807060906120b011403040503070b09280539061305 62
    0x1005000104004503066446100c0c910700300000e5042070707000611507460444006110700200800038101d60f03501c540c11070b00310b0402c51546800c2c2e0000f48a581c100035402e81c00401a1100325440b140701e805054103614485003030b2002820748815040040e103140404202c0d42002c02e002c104950011240c01c4c0400420b4514907061088031225181c900c03041c1c40210030041440810b40105000f0306256891891800000d800c9070f40401d2824a02034050744180b21019085640c03d1519048150904280f000b1b0440185600361550054118003580d0710210300400c6201c90410021f40039114a040c080f20041c02d0000041015080d0900980c1c02a154040450664000c00103440d50300200380440e079880c07800f4144155a54010f280450b0344440b402e000405c80300010a4bc04558444104070503112890800e00d140f40120120064450717004200781e42050300d2208070140904986110342c0011615942400c030007902c0112390890060408120f014004a07000b004007060390000c40380e0006080728107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 148272688 1250 148271438 148271441
    0x30c09171507110d0201020f0403020906040b03030a1101050c0a140d060807060c0201020d090e1305010e0a030905092d04051005010f180905060c0c160f0e0c0306010e010f0201 77
    0x404006403041d007100c00380301c0125400500c600c280d11401d0111981051014012400c0f072084a211581c0c1c01418441880107141080c02c1d2900031100500c0420003580f414006800d540c010200e107004101040c0342c04001280c28000d190b03008000562490a010300d4010141c00050712900d00c0034071040009440343d880c813030782d400b160280441204590100351149000b8089156111080e4098420f00d451200311910822551003038940000c101d00264840d40d41040b011302245000300d034595200d41c412400642c0c1009444005406942c0c3ea5400c03030320b86801d0003c415000361108140070702c13031492414507048104d244010215820407800443d651403c005082011940d501d00c0791901300400065015071454800f010303100788004820415245140710300450b20901801021a0000c0380083e90502c5503201811141a001054407100008000380322040800303a00f200020f60f1020105010b00912500507660100d05d0703030406403840c18400c0c00038010307015031400715040004484140c900e0610030f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 148273938 1250 148272688 148272703
    0x2208070f030b0a0902190f0311031c0806040b0607050304170303090d08130209070e0102010e070e010902091809010f0b10021506150f04080c010c03080711150106110c01030c0917 78
    0x40340d100601b465140c0e44003202019451009031455292203000414500e0089403505038030075250072a00c1144408481660700d9080241050f80c4141d039008691081d4540c00300920445100308003450382c560809200d900c0304846450100c44540c010310810070017140c00149030094207030f641010402c9580d0b03040c203c9034400c00814000c2d00070a4a5090000f07140c2c02c402098400d2001760000d2003a462200900c0d81d0710040c501c200014a003004004001d980c509600501c6074010140c100003071090004005514010b083e02e82c001160354910340c154001c6d49510070309810f0401201c0c814443c4500300b1000396200c4101c0c1c5551100300d0340c04040389607581c40304000e0420f241c0c441304003030f100ea04072000714a180d0400c0c440c22140d40034007442c6220940c4900c80c94030602e80d140d120940c194071b400d00216402c800ba070508091900c20116003140070318488440600801944d0382d48903003854490341141c1401021554039041c10305007124640c1c1503402c001114181c4070b06c4580b4004034a02101d0151803e000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 148275188 1250 148273938 148273969
    0x902130513140603120418020f13030506070503060603010902030601111b0a0e0925050315070e0d170703020102041a0c0f060c07060e032208070f030b0a0902 69
    0x100078008007110102504440d408061070b844a280543c1c0d510103058032100c2d00c81456038003440802081c0401881a450a20884105100103007090505001004981c0c00304025001d118005030003041000070802c9040d9118405140007030440c00c100d8082002400103004d9400c0d03c07034003c800902ca03a481800c03c1d00e61111103504951140101d184a81c01d0391155102041c020026600042241500c50000c44e000315041c600602c2c0142048200050150032b9080002481e488036400041c0c5035030070401e090040040e5103035107000d4204040080c00c14000841464080c0b00f1303d01c00070010501d24a4000011a1000340f281d554000304e1804a0091040782c2001161400c3c0d103050f000003a612801900380b0040803000c0310038105502d05815038849003221030301100407081000b1000a65260806012844168112411700d504504a140d1038501c180c0e4819000075054410040b0460800c0760500a00000c0c0308171450b60b003940c440e15042d070707001400f078280b43d038448400c2c2c021034a60070030b480343d040c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 148276438 1250 148275188 148275199
    0x30c060f020109061118010c0206040e0705040806101502010b030a150b0405041203050c07050c060a03020705030a0f020d0507110922030e0910080a021504050a03060209041107080409021305 83
    0x18003000c2c0109540c2c020500c0705000712500790150041f9409130b238002a007160010300507030410345072030101c11680d84014004410071800380000102c1e00401c10941d8040c625041c01540e940e4203203404c7c0811018160452403c580c1402e020920645011a1190215800150071003c400c0000c1d04080504803c00340d042d0840c0ca04000c00040c417258404220200345141c0c0d0500207915001c0d418411801000c030094002c0c4c120ba9414030992030003400500020b200d9060160a11071161207142c01d54025500d140c021038080208d85030200d5041c0452080008541042c03420010b154545920041011102d07501900202c1c000c642e00d201c0503044615059074426250740720440754913005001c621800b80c56406812a000824583c400c1c540d03114056404017402003210002c640c081001c02181e6002070340b02d0010401001c12983c4540d0740190241d07008440159544000d034007403000311801200003143c4a081405107000182c083d9086408803442c0726005610b800e0a844000201401c5600465226 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 148277688 1250 148276438 148276451
    0x9030712060b010507020a1206090c03030e0111031e03060d1403040e010f0e060103150e16020f01050c0913060e0106030f050901090302120a140705011b020106030c060f02010906 78
    0x1444a030a40032514807403201407010a001c0c100640b45800b90000007076211a0b200e105000d450040f20124004600808002c50440c00030b40725000418681e800a90003e0007010304d4620b0707540c12620304281c200300c00000b14500b80074103034280034001203032a4016104034000085615555882811f00440d504940c1124101c2c917440d4000740c0d41d0303102d0b12414219010410000550700047d090010484401c1c5400090320740d11040114001c0003815000c100b00500481e0104007901d006190a100b021580821a00090720714000303440d0600d0191480103580c1442e0400156500103070599940350400c0e03580d10a10070281107407034050017080c0c0101e8004c040d410000038900781d040d000490111403045040059031220b980550a86000c0d08002d00964018000032041048020050810329101e00c0c100c1460140c60340756400f00e5000040036540d0b6911a00300440681c40c0d506119603203031140c0000c100c2c0a2840e5280c4880f00c4107485100144000b44d40c016601031700030b40003001000e90180040040c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 148278938 1250 148277688 148277699
    0x60f01080601261f080a03140d020c0f01020408010f06050a12020a0803030906190b030d0503060604080105040f02120d0f1214070201450206040b0a0509030c0d030f080a02090307 78
    0x200c189036041d095401ea44c000000170013181c045030302001c607601036440075464000e04503408807580c009040180401d82c01c0200c00b4103000188052884140c0200001d40d40342c0c42c0c003c06600b9901510001202145020010041e907a2200042d400700d86440d044491882c40074000240400719a034801c07c50b50100004128494601090192144012410000320401740c400c1d240b00700d078605030072241c0541c000024a04d900c1d0045004d10343c40304e0002c100501d03181e101c0c8095401e4480540e022648503c55540640031403400b441040a003414800082085005c4103000920041003003416509107c110b0b0381074021800aa00013540010907084842494241140001c2c02401841a01600c003803441b00f50705200c010704d0310440da10707580d00c12088014003c000002c2002e045032000c120782c000c0d41040b000440e030141c1800360150919907142d89445050860605042c1031400903141d11070789120a51030002500002c88840f18806403928241d941d42c0c2c2113140c0003d200d4641c8140c0c2c10300c10080002030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 148280188 1250 148278938 148278961
    0x20c031204051e1f0e030d0504060506040209091612060e060301050906010506071b090c110705060405011403070309020306010b07031803031e0e04020310060206060f0108060126 78
    0x1480c03082007101d2400003c81c03d80e00c1505058518240e8540000500e105010001c007a0744c40964541c8100058000c502c02000f89554883c1e514601d916456508000600c410380c07081c0c56002400750b0703082d4a01102e84000403400385004000100c4000421070800841d4401c091f03542c5c03840c03030110301008450340f5100812000c0004450341ea100f03609100000f000050042002c90495034040d1042e42031001580e507010b80e1000c1c000e22035601a5102e10002206040c074021144c2843d9540c983c402900702980840341007920a8001c0c5006100804c01003000da6407100113a150000c02ca415952261205d180440103000d030180080d40c18403482d0004285030521100601c405442511181c2c40d400301641090401d000902c00900450040e540884841458080c81d44d40d081281c40c1529036a50340c1c400007400c980058444c0c0300c011034040c805005c603a40400c540d0741c20400486207242c222822a000a00c03c0c1ca00818140c1084545940c0281d01c3d1551f810403000d00e1480103800409142c120b01155 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 148281438 1250 148280188 148280191
    0x80301030b070c0c0611160605040302030d1b110f12030a020c090c040620010c17010509040c14010903150c1b03170c041d0109050105120307060b0301020c0312 70
    0x1c40e4025a0800324418500480611070b002e44c0c0a0814500b052a01400740c40b01c0040601d044600e0150008100a00243c50802005800c080c5c581c80c0c1c44a0540c01814540368080d520300f014001417840f1781d0003003407a24501d2082998001c03011000c0c0040d00002c02c4e40030141c1440b8a800c01c5401840340290540800503103d000455030860f10003140050400c600d40c44182c40c22a4950350400080c40880e01c1100e0201c850400c0070340120314160300300c521600712071b03107920a40001803e2803803105000e483c0b44000b500600d1b08560444050038261110540c51038a4407840c2c069084c0da03a110003050b4003c807800c000550f005480703030f0f00f9415000250006044d007507040300c0001e107042c4139a850340031100b180c3d0f10b54150540d89050b0940c6d0356036115007030000c0141c03420b9444602484001a200b2000a208080082c5ca00001040b5490042504191041a0425442070300c244024a002c60400420754480e241c00c0007000c41c000c5002c2c00407900900c1113111081c01400001420b04101103500c00d8107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 148282688 1250 148281438 148281443
    0x15040207030225210f02030a0503030609101503151a03180303040f030806220c02070b040b070204050606040302121507030203060a1401140415030605030a080a080a0e03030408030103 80
    0x200d81d2415442c002c014205101d0103500c075620450701200710b210819480d00c0540500c1140710104c00c805c10b4000901e015085030003150b0552001040014a00340341103010703004103041c1d04054802d4107001403200702e2260404400201a52a03035010b212141c00c00b4504014802040740c02d5800d40300c00d01201d100c1d441222140e800f10941034108003804d40000490b0300c5980c201c0001001c400403030744c044030040c1e00036000c5139205601030780c42ea100ba0028000c00ca004e0b220307907000141c12148900081e08107a5103512004494005200810007880341200b1a0001581114001500d42d940b0300080c505020319000a50080c5410320920341c0035000041c15840c10075641440c49065803044030883c140c0c13004544d0290840d0000f0401c0203001a40002010542d00c141000030080c26100c140f4207903500b05500c12048003103652141c0e004541c1610458020300360507806805104560340303031000548102c0e1400340070011800005a18181564001c001401d82102900d0783c80c2418240300f01d481e00b0a0005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 148283938 1250 148282688 148282723
    0xe040212070b0f183015070e030c0d02060427020c030c100903120c02010f1a041d03071101090807080a0303060b0c100209010311040f03030e27150402070302 69
    0x11130f04c89180c0060280040e0700c20a030755000103101082e40501c0e0f040589603600d01403080d58841188081043c403800c5c41003030141e80314507060325800b00b003610703020003003c0349401080d2080340700025881d410115002d403018400d2041c100b042000314800c8104009041141d214030100d02c2d120604000700080800c0c1d5890000c5820f06d107490000d6404442003600b006010416046039260096804c2d0007410304012640000600c02103019a600260303003170612958070b600c240040010710341c9418402c2072441822074605142c01c4104c90481c0e5507900c69045c2c0904029010030140107140e04c80d100342c001074034219080d105603c2e964411156191110401100441c0c1404004542443c14009407003400c00300d01d006200702d428650f5110020350196506604040d11071002d89031188115006200404080048941c040d185081c001c041c03000b055071040c422880308840800c880d8040c44092607004900702c04002d951036187c0c1e101c014403030500b50030b500700c0d00118080703040c55004201840c140701c2c40d554 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 148285188 1250 148283938 148283977
    0x1806090c030d0f020309191509050a060306080c0607020301110706060f0605030601021507021e0a051506010c030e06042c1006050f070f0b01030f1b0e040212070b0f 72
    0xd05583c0c1807443e101039401640244401d545a10341281c040901600e2070004014454442d824000c480e075903038000782c001c101d61190401c041d082110350040107250b185403c2040a00b404091500c1c0d071700c10a00e0511580c80441c0440075517a0070360241500089100e00f041d42c1da481d07803a0080140c036140c803461000701c005500025180b4090f200700c83c4249070503400750800b0018095540c08042d000303080c0c0b804501c22459030903400c00386e1070060460340a44100070a50050680b034511b261500609001a507a2410020b0004598104010b110300f80c3e07140c240345102c0f5401401054280c0150307405024100c0299000010a54240d541c00041c9807440d808644541e840708400514034090b4411280014401c0040c0c146121503800640300c024411804a40d900a1984a401009100b81c1064495100150f280d40230085a05120800821000040380c0702910b010702401c150b00d001030000e4050b50719929541400c00c000c0c0010405040720718081c2e91a204020754850543d0024100c0c0703a4810041074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 148286438 1250 148285188 148285213
    0x1309050f0c0102011416020c030613050f030a0c081804140f09060103050d110109080c011e09021011100e06060a050402041503020c030c190606090212040b1806090c03 73
    0x1528240f410b500403601702c152696900b41d10001e180202c0101180200b00c0c500d9102d503418850680035941c00140400310a803141011824480b81c001c0710151680100034205041e5080162203a903a80c02050700f07503e81d101d20000d411075424450300305071b01c01c0c60190b101000ea01400740243c080e01080e10240c036180d603110030780c5503030703030002e01019216071f00c002e40013407620380b1514082e041d10009900204540f48582d407414265000300e007410300c1e142d4450002d8011080b0007161041d101c0264101031000c04010303000b0a110f940c41005500c10400c106107164048101000f80340310500c0f00341c40401c0700c840c954248549610094901901c00c6422841c0080c051800340240e030180c80c25480d00502c0c4221940c0160000d50100303070301c20b65034001401080714980082c44214081080544103494940581c074090040302c9040d005080c10502c1030010030310011246120b02e030b2095000200604941700d480070407080f01380008c044c000d01d100301000c0000c120008600501c031100254111200f514054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 148287688 1250 148286438 148286441
    0x7020303090a021e060423100c08090a0e1003050c010f05042102090723161b080708011b020c090705090a091107052e0504021309050f0c010201 63
    0x341c42042403684948400c10151901403604290003629110700280324070690003150040d0029071009211840c0c00e20015668940002c410303080d0003049441e003100b034118590281000072544405041c440000c611010140c0b80c0c090404040c100c2e02c40c40029038604120300040082c4280170885182c064810600c0080d405444020055000e60f211517041500388992011200c580d4203450100e400e00e0401040940c56040c003075030140c015551001c010000007550000d03504c1740b410244041200400c100417401c41c44010040f8255808502110510441101c10380c2e0081c06401001980c003903c1000180400c0562202800c0f50761941c0081d203a400091040e40c0f1000c82c0d440c0942c000c0545800510982d00c240014041c4040051100c4c0d035181d15402a50101e84800c200d04428010024600c1c05112040004a109210300300314000307030380c0b4444a1021082c03c1380e40344d0a001e82d11103001c50115641e01007601b8500303800c03000401c40190326080942d540e41c80c1400044017400b40c0d410118455106 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 148288938 1250 148287688 148287691
    0x7020f060412150209090702070312050702010c0605060103060305100b03061005180702032505160303020d03090204020c0d08010303090e22050c030115090c08010f140a0305010513060507020303 85
    0x3800703407210900d282511883c0030b03454244440303400c1613400c2001420070381c0c41c21040d6000c1c3c0300d00d034002c00c010b034194030344800020555100034060040178402100140e07171098414500a5014030045110b840b406d0058010308265003008225000c2e084008a15241641c08404204800c404542880c0c0b203900800201e22602d024940d0040810302d8009040105606016006045072048074030b00f0b00303100c0005801800020410b0f0384c0304040c0d042e600034000100480e1030011240540030000c1d500d10340d0003a5949030700000c000b0505480b03260103000e40d9210303410340c6c0c6603407921020303901d260300003050041c40320b0405d000840100c1e0b000d07107000c98000c00f00c0311098400c00481c5c0c01c81c074461034071a503a143c1032031a800b821a1b0601c200c0101c0e010544080c060f02c1244000001075020300382c1840b50ba1020754198003014010814a00d00400803520b06290140440e100d00ca00007110020700d0010401821003034002030074035804c00d4180240121310810285005020311020003560b1182e0354101c3e101d200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 148290188 1250 148288938 148288949
    0x5040f06050c0f0c03030402100f0206180f0601080304051f0e130e010f05010302090903070b0105060d060f0602030d0f0603020609040e0304051002030d05090f100515060d0207020f0604 81
    0x4480451000403036a52240303821048440b8000e08204640c405250a80e1005803008100d80005c130912045003032840048000000604204410303000d2454025035906008098401442003170f8400f04260390700780600d403001603001094890540c0c44100c15a544d620034407800340201e4420f189038014480281283c1a103003940e07a42c00d015110718a0801500ea0901c00101800c2c81e0380d90021140c3c464244948c986801002901140640c51401000f000070001007542c225500308110031000114078001503810340d60112001903c1d50101c6890030000e05498000d10913103a02d4010110b8a00c3d0000b0141028005410b400c1c131446081c3c3d003a83c01551900d1200039005801481140d50503d015086000b4018000084900b055a00c00c00220662640402080035820000342c0e0300d8034402d180a000d9102c420b1400504085401d018216502c51082c15120611a942d0001c030391140c012010303400102d0300060196485a482a030b0503c025408408224840c6070418240d145600f421030a4a08592 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 148291438 1250 148290188 148290203
    0x1060c03080a05060a0f03140607050309151e0f040b061806060a110102160c140108040f06150b04230a06261015030b030d0e0f1302030a0f0504 63
    0xb281c140da4100070f80307000341c01c0341d40c0400c000001141d99004a46071500460060842007030044c40080744a0810f00c025040c00d04001c0d040040001e40c02000804010340102480e45142e1603482e00080ca40c0310401c0c2a40712001c05840050100c00d2041c007103214007680c004c03885100030340c1300d40c0204071601c24080d402034098264040081d08a150103009450800c1c106d082840d201e007040d00c506c9003241e01400080349030124150084040c894000a644040c089002140110340382d03540010307105d00760041c001459010482c08010401055400000820140201981c4180c1c0c603039603c42e2940c0c03c1030080e0707802c0204244911060b0030401e5002c402103c0060089015241007801c110b40c018901803154101c1141c03840e00d5038a4800c0110389600c60b900b141c080a80083c100062050a910a41c0c03140e0209418035540800035600031400741e1034882903040002ea140c0303182010543c201810301c2c4036a84244030b291074024610294000314801e0700040703010082c404030072514008460702500d000d072855 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 148292688 1250 148291438 148291441
    0x902030d08071803051c09080a06052701091103030901090501050a03060b0d0b0102010b03030f04050f0a17010b0a17060a0e010e0a2004020a0503190605060f03060901060c0308 77
    0x280e014400d07864100c19280b900c8550074210102003050344810390300407105580541c11342101000303116140294044103140201449251107061030340c3d18111a405020181e5031004a08504214400c04410a43c00a49146282401c2c0c110764020050103109442a80022441c0c0046140200485100307103c140c543d0910306007014011101034021b106550180355035108049595840803001d094212200c9001007421244207000a0942d041006118002c0d802407219001207820103050314141c80c0c0c00c3d6840001e19001d07000041c4400314951081da400258040c103c000f030031041d00050016402030b0b60814201d41e4601c00a01d01e000d48450f024402d80042010507242c046c039800c42b05110100c0340002c68030880c001445d90801d9803050f403c46a298880c030400c140c400c501e120f188c45c2e105082790114101302954802910740c1c0b00080020706c1d00c03501450b440400e006240d22036400303004003078552234440d0309419070541154410340d201e52241c0444c00000031700521896114800e07503815510280315 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 148293938 1250 148292688 148292713
    0x19170a020c0a0b09010f0e160e04050303010e070309080a031508071a0c030705060f010f091407200709020414030c030a0201110109021003020315030d020d0c02040b04051e010801090203 81
    0x56a0103014070302d0b103540b661040250560640207185100d8003200281400303003d09240d188c2c1400702a80300660142d01d080030440861408815203044034841804c000351036458040440c010441e014000f84211400b0890100265041e80712a9403610030b54140c0c00c8a64a0b1550207a4820052043c940b2884800d4100c48000140030013410403c03020030100d90400c4120fa44c1c1070300f45441100d6441caa202020010461000440c4168004019024041040c80f910b08281010407800400358824440700309080350115441a5540c0c5550b080502a240e0040d103d5181c000a5070003881002c165117038152000069180100b60050705000040092400400d0381e4011344200e10b003c0764000c0b00d95620307200031016840e40c881440001c012940c0c010380c0c901d084004000c84039403003c050790280e0321401c0348502c000e400080c9108c0b540203e00300100304482c203100040141c112003820715081030511041c014035440381207000440250351440c481d0381d0382e02c0f034640d9822190022030184d451390128070780814 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 148295188 1250 148293938 148293953
    0xd111503150d12030b06071203020c060a0c0219141203010503010b01050c03030a11040e040305031023150412120207061805090402060904050414120f0415020319170a020c0a 76
    0x22012009442c0f079080441c0b0f510340542100004440c800270036000107268580f004103010741d03a48803081d404204541c00c00048000c1d9500c08080c00580343e104280d00030700c14004006070b21241035030342e10106c40399280c0d014103041c0150000c0c4500d5021b5802e00d0180380300d07036024106030b9030051a00c00c0194255030f40c04107480b020b0b084140320000103450030000412942c0b01c1c032080503c101d000e40c03a4180d4900301114050303642c01c459444401a136030f203805e484107210b0042c0041016042d04640c1d00701c0008522540071407911a50788184d0354242151b150004001c845400010000f880c7d8083d0341960b940d43e00c080e15a0303c040c5102900d8000c0301c0006100a00d041d04000d504180041d02c0c807400c0c40300d82d00c041412104c2c1910301b5107074035404501e801c0d81000e080000d41807180030820200e06252035200c114005000354012803014074450356059503914404c200740c82d0700d40800700721042401c40c50b21019005602d500260114207909100040b0200064000ca401c0e0540a0006000e642e4444c0c840c9007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 148296438 1250 148295188 148295201
    0x90201050408030c01021206090603031215120a05010c030509070603090c03200922030c0203160b030703050603061306020a140408030901020114070c020d111503150d1203 75
    0x906104091101050980c801c00c0608a69121200016911b21160602e0f440052006040070701c2050b0710820090640c9001c002d4800c001180540903060340ca46d40d01c07000000042a8140d0f0b040710000c07a008001d42d4001985130405409100200507602c80c3c3d4808605440d02191701c0c04090303005110800c6240d119501021100d0301685004208546a0380c0d610070021010205038034018075188101c826107002440e03e50011190003070120b10740c0707080742c0888244039080c40c060144a41c4152202c15510140528161000500d40c80303510365455003d502001d40040c4c41150009207402c000604d1070a000951501136a00c7c0c15405045021959803940694889405481046651075100e50282c5051020340007030320160001d561542d602c60002401c48100ca25011340c80c00e50304003440002600b281044201580558501120362041d080c00076840c511410340c250404203080c1030f03800103090000594090130f018110455800460070800c001c41d454501c014101460040450b04924000c2d44582d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 148297688 1250 148296438 148296443
    0x90405011407030f1508061305160603020c07060c0b010302041a0405180c0a03080306191703030f092a030f01020706060302090c040b040306230a060303080a1a0409 72
    0x454981501501c000c901d90040c0e4100000c0b03a1030b800701c41d000c01340314041c42551000c04140983c095180034a4185e4800d0050200b20243c071403c03400304240242800707510a04200400d11101c40303560303658020000d50100c500311050b4000c1e2100451640d1042d03100f5031880ba009130b1010740c0b5900f0750f000c00000f41000c5280c2400141c4502c8801484c3c0c886004051003000301d01c440e10030f958034040712a800c0443d90840140710b488a91004c0c03000554440540342c1009080d10311301c01e62564804a4108803245800246448103d01544590400004010761141c1ea20078011800c0b91204030700c6070784c1c1c3c03801d0443d41440788880444480b0360b0070503405d00840c15403000341110162410740c00081d007282c2c0011800d40e01d4035140c42d03062041d400c02d4442942c000c01c40c090300d1880c1030314110b0410a107000d107001c010a000d48038032002c02203d201480c4c148400c10390141040507800c04d072442c8402042e40c1d1202300c02040c107400010303185c02440d00c18103100000344038041d4140c14203682080300a003c011402c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 148298938 1250 148297688 148297691
    0xc120f09070b1c1e0509300906070c0f0902160303090c120609060e0a0302070b07080d18060f0c050a230304030504080613020a260d090302040f020901020c09040501 72
    0x14180f040114000c0700c0f100d504442c480e40304501010309041c01ea030781c014100e80b100d03070045503070021303484081b01d180c070512002d843e41100044440d201e8520520603039070403035031011000c03840d8001c1c807030311700317086000c5070f0900c001d00c11750641da41c5201080e4091080011400f5240c0c03038185d00440d0003034021040f0903105181141c40d540d112512000e80e00044002501d0b050f070b0398040c107820010030344604803a03c2010130007840702e100030b507900a5481c2c00134051500460320115081c0104840700054410080030711b0028080801545140c2c5407200034007005454013400c101144001104600ca0389090380442d42c0c466291041010307095030451032302425200b645008000c455070f0000400d0145008034400c0e41d410340da82e03251064441c503140c03000d004101c04030ac601d0801c50060782c0d00441101151a0b1a40a00521004900380c49103420480c04105443c05407454401144e0341c080341100540e0b10843c3c0c10400034030300ba100c41d8102d00072071554a0250f440f5a00e900303000d00e880500103600a104000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 148300188 1250 148298938 148298977
    0x803040906050d1509230d02100501050604060f0e03100207050d080c041401050c1e0d020609061b0702030d030b030111090904030509031606090f05120d0e060405090c120f09070b 78
    0x860400307164400c00c1b0008580115810104107a418080811020a62034040c403844d410580043c099100f1445801d05000c03280403803154650003aa507894040200a080d9a50301e44001c142d04c0195005d208200c543e4000c0c2c9849001560080c11501d000e40d0159010a0409041c0a103848003040500b0255042c01024055513003118020807448210002c600e41121210003a140700901d0040b0520800095401c00c1080240900000950310f40c421100761201a02150b4a08034990340d10030360310069050302508904640d40c0c0d403d0307000b0340c440e50300950003004000c0702000300d514940550340c0c0096100310780c440800c000c00d22420150101950007010b84a10410501d8800c0c1401200c2d0b101902150103440c0420040ba010200da00050205540032603105001a01042d1110b02c40001042440b001403068012a2140c8040d100a858003601c3c0d00c04a00b800701040002d41c04c181c046440618000000405191610140c43d0049401200902415040003050b4403944c04c1b1f0100840d03041c03010312 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 148301438 1250 148300188 148300223
    0x7090312110c0123070c0801050c0304080f090d050609060129070206070501140406090b0606070503090d110a0e0115021c051c0203130209070806100e0315010803040906050d1509 78
    0x400605070f07648100c1d807012120b447e00b800d09013075910090844180b91424002c100203e61100101c40c6030210b0b0a22465403800c00c5800250341001166000d0410b1080303000301315200400281d4941a0b58180e040c503501c1d03030008001c06420207040d248000b8007600900c1000c0040c20f00b2005000024030a00010a6002d00e40e010600500360496007554034580762070a004c10f200d02c070304000d504000d0039034001c2e141504549805a4a100302c0b0354207806074181d10050014444001252003001ea4014452907416648002c10100c5610070b0181c0c585180400e070785407140c80c0c000200c1c0b1a0004488044038506686048140c41c00e800c85000423084031308005010000411520040d80300f01081034070305940e100e00c1d0050201d00d0800415034804d00040c1d0341884076590300d010f1514140025440c006001c00703507500110b41040c82c1404c40304000000c0d0000840c400c3c1c0040054070076603840303010401c2203d9803501000103e03203222034013600704014507104018014094100480d414013820405130442c0c00d14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 148302688 1250 148301438 148301507
    0x16120e030a0302030c0912150123060d09080c0c04180201170c040305070902032a0301050d080d1b1202070803010501050706140a15090209030d080601020f0607090312110c01 76
    0x4810f045d0540c000514805802001c0903a23507014014400311110050121046043c0e15184001e110344104404660740c2400c602c1c41e0040904650710103c043c3e05c4641c0c0324441c90f80ca000ba046454412230914101c050360b1181c5002400c013154059590058420300c12800d00070403074010304002080340e0108000b0000c100108540b4005280c2c280c030050b41e91401c0329821190300d8550754454030041d12403001d040c1384c0c402101a02d0640d001100c040080d05d00614204600780301d40c1d9940424a4100710610002c1000c1098000c20980503440c2c02d43c26090405000e02240b00d44203004004c5076092005000725407040000c3d0100c18440d00000500000c40741c00700c840c941c81100c0e40002c040e1501e6000e0855403142030341c0801461042000c0d42070088c0300c80040d49513284040c0030350801043c1400601d550780300304113642c3c0612854080c2c1d2241d00301010010940d4000b400140c030400742d07550858002c9440780304040c9601c041c00c2c02a0502c102941d0045074000c0c940401014007891030314010440d01300c007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 148303938 1250 148302688 148302709
    0x9031603170907090501050d050a1209090518010c020a051903050d09050c041d1c0c0206040b0901031103010602060411060f0d0506130c05070809041416120e030a0302030c09 76
    0x50030010080300e46080c2201091705c00c1600803e00445d80814800c000500014048200d90b91100b10410021910002205c0d9074070940c2c4000705d500e0a201c01d0141600c040d010580e15404c815000f4808040c001ca02665a041c00d20001030441e48680d2410030820000402c0c5d000a178131a00e001c5140600f807620742c00079500502000d440c2500103251294803480d1a210b0815141103007080a0b160f2070b404130149880e10034440f81c3c42660181e070320039040d44611031400070000d151b000701841e480310340310000e0161a801006003140420f1070007540602011003d03060b03e048031040e030700810032641d50303584040b446c1800000d4a900418140310011007810400003400c40c0c0050301d48005000e01d00a801c00201d00040401c245401e481c0500240c015940131040761046c41e0402e4803d90380f140e81d44081401000a44000401217007520140446c2000c8020052561800b0b81c2e80d335030280e00405403050480c1c0030000e5841e840e170300130000c1e609071234040c0d00031b10360141408090724104060b00e00451040e402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 148305188 1250 148303938 148303951
    0x70605090303064213030302030c100603080f09030a0506071106100609061808060411040f060b042303010501030311070b0c1e0c0a060503090c090903160317 69
    0x804410411541850b200b940b112011380c071415134040001014210340d0059120611050000e03403100b855044031313610202c0d0700c00d56480c01d410b403d1690320305000f03440c2d0304840d10f69001401019400d001109542c0116015a500052820318041341040460103e52010b805203807d070042c5070b60840071400c280100c40c0b0500341a00c07200e5a040099542c2414910003c0111a6051004001b445081c5e40038682209450301c504182e120b81c1440e0203d04030310703805607100075114400c4004020030444020040e0b108004241c406101c00038201c45030f51700340e9945000d2403101c4207042c8002c0080352072f003040178100220346c4070b6029501c40703140700403900b960b0b403d0700180c1c0400c12000d05c04003405010032950000b0862034a8032800c0040c540f940039298840c005242c003d050288500c1140d9402c107010440714024000c04c1c05030043d90b141c801502c00c1c1c008449138140c41c0039140b00d018090511030312280c40b0341d2100000c0d61401000c13001c482840000890150700300a82140407a1005c507202949a00810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 148306438 1250 148305188 148305193
    0x703210209010e03011b0804050f0109080a14090d031b020303030103050708120a0903030c08042601060902040e01210209010905040210031107020d210306030203100b060403060f0207060509 83
    0x10607140015208021001c0140e02030307850528004045040d0040803d04086185003076806a2034505150f8074040c14003200c14055441c0420320003c02280c500189202102a00c502000c00ba0401c1d8200d51400b07446203058000700318015010000740304644945c5200000100302c4c0c0018080e80200c0d02c2e58000740c00841e55940504410b22810034100301520f030203282a10038a180404950f0020001c0c0458403004088c44064141041007220080599000d004540b00140380c0b0807102002040c46810a000d41c42d0f554a8804041029010b50007290151081c40d4102c0c802a460104102c0d4019403070841e41d90b554010b1406240180c0d250b4034998003d0000c03620201da6402c150040100608450340030724145031504400d0300d0b011041c101a2a01160100c83c400d80004940c01c0c03088808803100840502800d002c030400c00380c1501944440b041d64004e070200e542d0313010854a80402c40d801c4402481d03000400380410000186a03410421403181030080141c10004c85503540d50941d20306882081c0c458 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 148307688 1250 148306438 148306447
    0xa020708010b06040515070602091f0801050108100512030705071806050303030103030f1b0204050c0c011d06062101020a0c05060a0c122003040b01080d0e0a05010507032102 76
    0x30301090248540d0700c00e048440c02d103802c1c030b4a000101407101c1c0ca6003070000404003050b50700c2402090350583e14261b00c007804418126141c1061030a001280180715000f107119540081850f5119008883c03050307050001258803141410208900c02d0005084040148030030000035001a1003848500d0050001d074000c19082c5032140c005030140c034410780046009a0052004102080e48010380603100040ba042c0b0780d0f2003840503000e0311518411000042d40050034441801f0781d074940100141055403c400c02040102c00c8611024460b81403112188040c0d4403030008030301680751107a0191264440c0001c0900c3c40c440118038242aa0800d411240100384420901814400c05101c002d921025940c4104110075102c0000f80082101d8685040050381d1401000c612003220b000c2038200d00c059021468072464180f42210328040c09001d40079190240c0d2204d00c8589019500ca416030410007805510040d0400c001114035812040b810703003c11030b000300344140b401032400050400303076a511030240c2d48 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 148308938 1250 148307688 148307699
    0x61606020309100c050717070501051513090f0b09160e0103020f0111060109020c07030206070b0a0c08160804032c0f0f0105030a0c030b10030e0c220c0201020409020a0207 75
    0x100031010840c001c079103003014400c94507941d000c021202e0781ca610003100d100811f0604c80c03090403400303105001880c940ca4801031180302c03403480aa810500604480f40e2030680d100080078000d03125110030081034200e251848000207246184c80582c0030085204039420410406c80202e01c8031087d0713000001d80000c500041c41941004c0d81e869290900a0070422111840460041d60f521014415a11307180d03070100b90705140501c00d100c040c00650b0010611911400319080c645810704041c0d070015840c2d8902000c0c041003500813801c55211380b1751010780410420041d203044d114010001c00031000c10008000450301015041c9200e880042ca241d00600059000c40600007a115079403612442a054121000c450340e901408030380e80540d942d1004101598440002d41c041c00c0d02102095014a992030740c4171300140c1c1a8020402005084122220031112106000780c50540518200d561003c144d923030103182c40d950704030480c1e001c8a031000510706680c0301a01d20898002c00b5a000040e001444100207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 148310188 1250 148308938 148308943
    0xc0e0405070b0f090909030f040308090a05030a05150915041202120c0a03030f0906020301060804060615050702040e0c10050a0806091e04240b0306070e010206060f061606020309 78
    0x14155902000d443c1a00c1c15440c0c0c0c0c1540a001961807262003950002940030300c0500c142c0d20740340b030000c100c0b5480316103071318142c0016080441d20350702447c2c0c0c160000441b458001064484682c10401500d250641818a41c0c13550a00801c0c41c48144204002440403a008400c0703613200f02d0044854824010804a00900300702c5070242c43d2409040900406807142c1000c070f00b285280d13901d4240041d0300103c4d50940d001170b110000c005070403103202100010b01340e40c110880c82e1140c0d210318800c020ba140c032b6040e10b1920b068800360300703400100c0070f002050042c285940480c40085200044078001c8014400140003000102d184000060001c1150300426820502c001e8101500721403d00303180c030b8400e40385001c203080001c0c600741c1da0903240040707400c4c825070806140540f01c40100f05506408404030b020040d15492861900038464a000200c43c98030501402c4882d82c016406004544c545a040028030349071010f040742e106104001540d0100c810006201d103140c4203020150300d91500729441030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 148311438 1250 148310188 148310203
    0x21803060103030f211104051302040e070818010f0b040b040504020913080d060603060f0b070309030210050409150906270f24140a0e0114010c0c0e0405 67
    0x900a03808800107000180c0c101c0300100003070380185440052140c5055444105160511284810f00c3c0380001c0d551000c1d2401d0014403c2d6101078071108211803000c0380040491040340715200d0408585d5000c40e82040c030440a503500a420302c4d08100b44e00540a80580c00c451600b000e40740282c0e51450b0044190800380610510420308403003c02442c60550045180b50704d0050402101101d080c0300b0700704000310502a03c1c80f440b40c00c0000c0081c10b0301ca0340080e004000d24003403896510200c0c040080d03c070b5281c0c8101c0d40c0da540c0c960780b181c002d00d02d1542800701107400007040c1b4051000511020416851030300c00e03012441d8020b0710f1210454542034a400032640c40350090751401e651820440c02c00c08001e01c5141c022020b50750001516141080c00c00c00911828050100f55125000840c08070281407094400f5162440c0c400515480d00d042000f0280c4000d1049141e040c0c1d548004000b60030b82035407080100e60041c104205420141d903034108050200c0e4204440c103900c031000303201c240b100c200403c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 148312688 1250 148311438 148311487
    0xe040509010b040e07050f040f140405070303140c0307030e13020a0306031109010605030403050705150a2a090302040b030705121006090212011502100c050d0509072909060a0302 78
    0x4007041824a8085003902c40c60034191401192204082700b00d1100c1640545a0a00817800744e00c1c150600e80761081e200c0c00d861000b03400107409a0107204c3c9036440502240c07031546818008516050302607800b0740d040313402e80c03800d590b01c511481c0384131050010703074001030442040340e5500181c079038150b280080171070340c0741d90f640d84c0100030380401407003a20303040f20489401513051f05003d0f0702e40c1c2043c034000e450170501d50401c80c0d040c42c0074414416110038580191186008c0b020301e1503a2140c9103e04d0802041c080390071040024100c1c0810005410103170701450000b2409401c0d1100302d0303100c03c0032406030545200383c454141d11402c3c1154030040d40d840384901030b160144040d403912034000d000348000d0b08107010710030a5174110300c0c980b0300581c000c001018034424400824040c80e4154400034100b030f048440c82c000700038149000244070090200d020b8050f165846204244940e64140200e00011112900b20880a041207240c013165203020142c48100c13410754001d032b0b6407801a05400710140041d041c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 148313938 1250 148312688 148312693
    0xe061302011e0f1413061706040b03060604110d0501150915090504112101140604120b07050705070801021822110d0204120309060903030e010e010e040509010b040e 72
    0x4160b03050340d00c400c2680754002c451400f0451142c801d18200e205110754a102448601140d000140454004550064444240c80020240d907181800d03c8140d445c46104968503410000008620340340c5540706401c2d50224268040c06c0c10300a085a50403240c0a80085000c0000314101c0c601203680a400c1d000034103c0303400d440d1000c110071540904290224090144501c2c0c9916240400c00076100a4030708545055510244840ca09440511108030a01481c5c0000c148011046200c0c148a021a000c4411032220100c80c0401916110b043c075102901001c20040204450f41c0410010410100a030800c200016545c58076090026400303031036903c40500545419502c1000032885000815880062020101d440442ca00300f00c07055204102200c040188040b40104088180c82010b103545440303602d807500d640c0d0315444261400341d01840020002040983c4e031400350f5220769038020701042c0604109616030200b138001420380300304a90f24420b80e9540c40b151006840c00703010310344c2c29902c450301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 148315188 1250 148313938 148313987
    0x30717030301120f06090b041b05010e0618060703021c08040f0209040201031104090603021002010209030304140307091d060c0a1205040f121d041802010c05010e06130201 75
    0x402a80324001481000e25001200010905110400c104044142d50000080040f40524505120030482c20b480c00d86a104088100e1a1041114091201620416140c142c1c0d540c04840c1007145c2d541c0a9004500000400c0745094951345136480a400b20b180300760007801c410708810710030007a415200b044079805c0107812030500c004581380d030700d2000c101901a503074040155036a00040c2c000d4000d49645000d91b5100040005188200c0d9101c88240c0c2c1c4200c80c8080700c14502c45049090b40600007240d589604100802c1044440c0601c032855400009020364007140d0366071100300c044414000c01001344500c0700300303400c3c01e120040c41030b05d901c50031480340c5504000205e400144500d2401c118204583e41e91408181030200e410440f1142c0707a030100b900741c0034000d040d40042409130038070b00341056182c804064001e039140034051200300f070809000301e0100703254940046443c480c3e049000c1d2229542c40810503402e10040c058980b0076503400a0329050f9000038800103002000c4820301e0001000241c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 148316438 1250 148315188 148315229
    0x30e010216030803250201020703080906010e06130b060d0c031b1d01110316030f090e070c020111070303080105100c05061602120d1d030703020a080c0a0512090307 72
    0x41c48401e036604036801d99200d5540003c000e1035014881560904400a041c040903034581c150005d20425100303542c3e09089407503c0f800300c0c0d6078000a000d00035034a0180e0b00081c0560800601c83d030036a8200380c0f00441e070002c0e4800801c010b90700860320303411520340300d115164801d40c243c05040885142c1480444031031302807078001098910800c00c0d0780100c070248090955a41e104000c8220400c15000c180c903512003190710f482c0c80c0c03203000340d4040300440c1d4807611000d44980190660811140403041080007956081d004444900046208a042c02003002d40c0001c0311004101074405548241c80303100555042c41c080000c40100d64480008001014070500002000468001c0d040b01c0094180310a00c40c0c00352081e810000c10326062003000c200860502030454440d0020005100d0040303291904031144c400351a203a1154080207030140c3c0c442110013002412180040141c0d082000c00e0b22320b0b208140c0e580c541424042c003101c03e0040000b01c3e2290b038901d42441060001c1901c68001c2e04000d0007035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 148317688 1250 148316438 148316473
    0x507050a0b0601110708030d0b09190c05120a09060605030313050f01050702031507090f210312150503010b060c061321020f0705090112020f040905070e04030e0102 72
    0x800340180301080e480042200c5034000e1074400e01840f0300320141d9611a0700c494005030307203400103942d408807141080d0350320400f828844170080c00f40844c0c40e0501e880305800ca03070344009041000300510070840d00300440c480ca4501100403038010041c500003c10482c8403070a1071000c1c1d840b6500694800e400410a000710017011000d031104454081d110f800321900588016251405160406501402109100300c800440d81942d00e02c42e0861741c4481c41402d44520074038480e80560b000e01c2c135852603680001c170007060390120303a45001ea100b45000014441c0c0d41c40b00c401500d00c5513021600d0f24030800c209004624081c003070751820b188d050380c6d920b04044003038007041d50b6000041c00c0205251a512903103c248002d0030081c42415592908524a00d030b19020300a40c0c60b481e0181c1024180500c5c5e8000c84c0f41d1500001c000e040f13540720301c0e607015220300301d80820140380c130004081030b400b981c0c7ea0007080010f002406440001c00062800441c0d030316080c00e010303015000600301d0a0464002621040140421 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 148318938 1250 148317688 148317703
    0x90109150507151d0607140a050f030a0b060f0c15060306060907020a050304260708060703020c0f0f0303060a150801030f0302100e0f2803140f160b0601050705 70
    0x480040c0b080ba1007800c0d43d0b0402003c800401d800c0d84d040501c1c10b00200e94000482c1030140d6000d0f035503038045100601007001507004100d8402d000402c00c003c02000303c0c0b40362002c2c54000d10740f0040050a207042800140c043d500904200b0010305000c201078a15a90134051040c1b036216412005155103081c100090b228500203100a1048642a0128000c13520030041da1040300e6004003101c0d621511401145134141c1920000c0628030f400c0100e000350b120000c9025400c403085480200041e40b80c1c8203041e40030790800b4a048041d44034161040d40114410007018000c03d0200010399070705e05050003809001d444980010f084401c141485100240e407003050541100d400034080c0b2a03143c1145000c070f060480c0442081d9070301d410006400e4802001182452016550f84111009000086070480c03d4400b01c60030103110041078400040400c1c010302c43d05200000c1c800c41c0c0c92506400c4549038100c1c1c5c00c00d6914002523070008095900300210900419000002420150b0928155a80b401e603505075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 148320188 1250 148318938 148318943
    0x10501090b0906240403060212060a05031c03050601020c091905100b04060806060d050f0108010e0a0f080306010915020309031005010509060f03030d021c1515032a0203090109150507 80
    0x44c0d400c0142101d42018041c1d80180d680500150f58450510b45042e042c0102a1282803149c1c0e0a40390001c0d15241c0012a007112071042404140640669403050b001000c00514407815406201004c42e05a550346400754070030780d124030030300710f41c00704000d03111007254402022040d22500c4000c2c18012030517410240c80450b0325619209101d603848802048440c011701e400d180100c1d05010a01610000c213809280c1641c2c0c02000130405035020362280f50759401c103800040c103030000d00030001c1c2c040344900000316403080c410704210304500d0762070441c0c0000264030f045400050300003060b90b1816140900626568030003080341400a0750400000403c1680068880c80c4101203004480c90651014000d5603804402080c00710340707412008010b05480d4080e401401c402c2440c1c1039884003949100d00790b0b81d00750f50070000001400b580c2c3c500158001e0100341c80408205034090707004400f481c0144140c003030495107a0301664889903c2e10015050090540001d56503d030402000e0003150346c40700a8034103258 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 148321438 1250 148320188 148320229
    0x2060417040308070b150a120f020411040f151e050310030b0106030f06090e030f03070c120504090f0b060928060306030210090302010f050a110f010501090b0906 71
    0x14540400c800c598455680000d1031904040f44210900c020350105ca8419900b03050544400e00050040000e041c20a002e84190306080d040400d020640505038004075a2000d0000075421501604400140d005a40031f001300ca07603141c10030302c0010101c108601912001e801c101a10403044c00701a40e80e841040f0085c01040300200010b0406560110800f00442c1c10030415511540c65070710003009800401c1112424a04007107000130030002a206546144170403401450404003c60b60581007a4000f0344054100a444020b05c00420041c601941003d04070303031102980d940c40c00c0c00d4802035035008118156402e2a14000038815190b5008a0b80040012078aa543c58111222002d030500701d0b14080240c18040300c0d00c04250b0f13603059071049080c0da0003195156071030305000800722100009030100a00081c040001e8540c814055409840b8801d2a81004903001040c00340c001d01e000c01000440c060340e0746900c0100710035040d41c820040408020746203041185000d801080031038041032040d102d01d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 148322688 1250 148321438 148321463
    0xe0a03030806010c1a06120c03030909073c02150c0a0c1a09120301030804060810030807051b0a0501051209030405060c0114010f030b06040911130f06060807020604 72
    0x20b038469182d403030b1025401920300d560440014800d070740440046070620b01568807d8440408950001980b60300044020002e40c501603202040c05003027031018000b8814003004485660000080c1a40ea81c000844806009a400b0700070b00d0514050380d220540405540003a242d02000c07040483d625a0301090322903103107950310b000803401c4401c602c00800240c11480010800880c0d00c96420015004a01060071240301d54540540300300603100c00c1c80b0007801c4141c00c0004210341d502030000f0780c0e40251015000d0088944c2c030b807100c400c10780c080e510846440d003000100e0307198180b580706100548041614000842801c00002a060740b241301801c0e00301c00c0c40300001900002042080350003411000c0c000e252591112400e483c0604411807010800c442407400114140210305d072036030300700d9400c9020911140c60384000e003c010400014152012001c43d6030301030981d02c07444000d40d4149000c42000076421162040302003110707000e42014042069030300600480c16800503515410076040454042d09 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 148323938 1250 148322688 148322701
    0x40c110d030b030c040237091203030f020a0e0109090204080304030602031f0b0309060a020a080403050d060e1018110a260c0309060603010902010f0f021e01020304120e0a030308 78
    0x200701820070025845400040d0255035900d00f02ca0700c008a0b80347c030500040070585800c580f000030340360400c5580060040c5004110300c1d120b54008288644c040e0a0028140800c40000016a405030400c030307010440940d40800c19517841008140103001682c0214189030400030156144d02c03c42c40058920307a0080080b41003002c0d114401049000382c600094020f81e910f00201c1e00035003080721009503034042c4c0700014251800900840f6030610040d6201c00050703446070f400b41d5850f000804110115517075818041805040c10b03a0241c01444038100c072117089e0f8500301048100c1b040040480b007055041203052000302c2c2c1e0901c140e82050507942000000d010300d040074540c2400b940c212003401b07000480c00340100c140a01005500490042d020303a076040d40d0b900c041c1401e880502320000e000860806001045910070449240e41a9840c0705542071145001a48804035101141d60009030354004240720412559415500b50013a4a05002c0312503c020703000192010000e01c000f805112259002448 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 148325188 1250 148323938 148323943
    0x9040c17010608070809010902010c02120109060e250305070b0c1c120b030c01140d020405190801050714040902031305010507030f05060a05060433020a02040c110d030b03 75
    0x312a91118410041e40e50392a00502102094480c0d001061848003c038510510600481641c6901a120101410000d60a02c04000c0d5a04a005415541c43c0e24010010ba01c40c042c0011090840b030040c041c2c0300a0f44072543c3e2804114a160952405c410f2040000a078041400411501e0020b507440d1a803002c8450b0303c1c14140d03041d50822007611000c040d40080340e0840040035004000010400005030365206141c0e4072408484000d000c40c80b003100001c0c045510000514404041c040b001d8106640c0d400801c015640000820400202400f410311030004248241544183c0c1071900714000b076046541c60003507206c3c9000e1450265000000648c501c4642c3c50341d45031465002001304024507107080020000c1107020403c8103414200b070042045890028416000d981000303002c0381c64240307032860401c2407141c2101008140c03240d9040301c408043c90190200058009600905903000040c4104421a25103450b00820b01c410f0020002000c640015401520380c0f06040010740c90500d83d0004e0b1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 148326438 1250 148325188 148325207
    0x4020604080f01060f050402120a090201091208031605030f040f1e081c0b0f09060d0804060203070c050108070f030c02010f060b04030201080109050618070507020303070c14030f0309040c 82
    0x80003840b8004064030745040541c4460222807071100428510350720b84041006030300c00ca40d04480e130f00003100085802140940c2c00450114814107001442641d520900c6943d0720b0240d005035507052001c02000b0000c04e154400c03e1000d0b11603e00103245191501c4070041080f000b902c083e11943c079180340706081260007020611184c0c0c074401c00201d04540c80c60f00c103085501c1403000f0381041c0b0700908c00a001c0b20b00d50140401c000c0005005500d45c100315800d012200c0c030300400b46a4000d80e606100d0b0041403880d401040544044e81c0a540d03110700d20304003076050750f0103a03202e00d040092035030410607441d40c02844000300c0c988615002c5440d0310b958204070f01410524400040c0070b89800c200160010140700103000f01d80c400e8849046c16aa52004442228011103203140c000f05046101c80b01e40d14611003940d030218460401d9414691a500860b18542100c903049038402540704041c0081c005241c500d00141c3c1c4118000c1c6410f80211803440d4a0740142606907015030307180c0001301c0900f0702078039200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 148327688 1250 148326438 148326449
    0x3150b1818070b070203010e0a2316060f08090c01080a020d0e0d1d09011d060d052a030606010c03031a0d080706110c06010605090402070f050114010602010606090e04020604 76
    0x4540c455150f003e280407035485004100e20030b61a24150200c11a40807486813101604201040b8808a086001c8468242e840c94004001d001d400f9200303808000d60b1845802400740c654428110610300b48000e0422900904500c0c1a54403010381e50006a900c415826440a155400943c4a01100c1c0e040c0d0003030219151140300d40d000d000b000100141c1d0100ca4400b0100114100c1c40205030400e0600100f00302c2802110b8031014410088400170501c2c100044e040a00a8100c0100d00f40a445607070403c01c1d41c0189200001101e84420045003c2c00142c0d0b50f484412001380106040c16400078013054507512004090644458603880320041c2001d03004004080602280c441039a0f078504107105910404040710054174090002803031900320310940302501103400040c0360741d90906c001500c070ba8000ca80762a0784203408214140005040030810702240b0311900001c01e10940145400f10080303816044803045a150220030040d96900c4a03040c82100c91142030481c44d62110300102d1058803a40d0002c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 148328938 1250 148327688 148327693
    0x40305060f0a1d06061009090e1c090812070305070203030301060306150503011412011806050901050a020f0f07050106030206040314011a03300c0610090c090504021303020306070903150b1818 84
    0x100b909240002c12304286241700080700c0038803415080cac8240d803031401c035004d070710320551000d44403031840010b202c01000c0c2103029007007960030104a540028590f0b482600420002502c0c2c02c402c00040355410348500c3c0c10349a0b41801401c40d0704140074100c601c1c6522100c00d2185120080401d0383c44400c0d400f41c1e0300101050442810300340e641c24200080c200a41d02588290b1070540011302400c0c6a20036100940f00022030980780c401c0001124510b60482031064406550354040080180e403240000d1004501c01c000c0c41c5d82c02c0082e41e0700035084542620205190500050021165941c0420f10846081c2844190024490181c00c0c4058154201e210310080d44000211429100f400180d150700c40e400d000742c071407201c031744840781001500c00e9039003070001080120300144200c0c9000d80282c2045280c109950345c1c1c01e607a07030b00042c4c030b403a4060311810042201080140305001103254010759810740181cbc1407140c02800c4020079540c01c0e100c03c003000c01c140e040000c149012503001c00102582c12a008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 148330188 1250 148328938 148328951
    0x901050913050a0e150114010819020d06150e010819020c0307030e0307080a0c03031d03010609020a1407020312030714040303090f080f1c05040305060f0a1d0606100909 74
    0x1c62800901d15280400c15510502c2a0f101c85d8850662070f0505032806a6020107400040200540c0c200704040c110340d901c0d21440c1000d0150842900c06421001082500032804501d0200700c20100d203404c1030a40700700802d44264406503604040c0c1680c1200a0b41c04400c8401690385100c0001c0c01640d01188150000284420516034010041c500d0040f08405a40310180d9640e0f82300e03581c085801cad00610108504a04002085c041d014a505114031001c800641482500000382143d800d03401c560031840d800b1030004410703035100f694403804030680441c003413901c159a00003a541d41009002071200c0340300000010701552040a10b210901c3c107a0302b845840340d40b01c0c83c0290443c0c03c4c5000d044011088200c0000d04400000742850061003184007500c807041000c8055401146010045000d0000400c40080018020840e06203d4061445203c20600303152159006030345d030040807a40c11b00c07400c0c2058006030002103800d94003c2802c540f011070130f140c9200183c0d03100c000c43d0f0124007601c1c60300c1c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 148331438 1250 148330188 148330201
    0xf150a080a060b030d0c050c10030618050403021204061b030e0d05060405060a0903051602060903030706020414060a0516030905040e06040303050a05010f0b070609141b060906090105091305 83
    0x100510003030f200480607504002c07181038045401c40d43d00d03400681203600ca138942035890700340f03c03c980f5440001450301103841c071385500c25154485980c01e140700c1e42a039194108401e060341031150f06818550b40d00c1aa16051814070000d0021b0008041c1d27500d04a003141c800b00415020b07a400300217038800070b0010000302e02e00b410300030345504007200c06441134007070b20340051885a10b030302c16801340700e034151200d5041500c818003002401c030b03100c1001c81c0c10035000c20003050103503001c00141840e43d01c140300150b0b807541440380603005d041c40ca009250103590280143d40b2059000419224503101d041c0b901d01818856080c02ca03802d440560100c1c1d041031038405589080240800d5091259000b51801d100d29114040c0c102d0840d0024401c90340d0a52107100e050000383d1201c001090050300070b80c0f002c2240d0f80d4948030307440003007101004070348160300c1100c05a1400003805040b200c2e0010466050382802e002e0004030740144540d039599810000c0c000340703044480d6034290f1014001c14680008120a15020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 148332688 1250 148331438 148331441
    0x907080703140c010806060d0b120619140903030117010f020406121404020f0f0612091f020f03010b0306030f0f010f060905240a1203020a03090b030f150a080a06 71
    0xb168107401601820032106a03550040790341c140a80c0002e407440e0f107800c00d5200050005c2c034002c0b178040c3d80000e1a14140d410141c041001c42d020314001c2e12080180d4510700e54a5017150030225101c50309441a8040120240c00403003501e044034221aa1074034035030041311aa50060441e09120f20000340b01140116aa81e400201c49804c601c0e040420840030b56806046400e601d800c4a0095104400003901c5010381451000c0c07c2c04104054107842c03e1001c0c5090540e00780c90300311864022603001a0645e0700450421042c2900e14406900443c640386030f028134076501d480140607030664500004040345950b1801c00030208a807550f40152050086220116402390480304c1d0740900c51750034504007040c24009442200c2c014811120400078407107100c60002c80d0034072103804076a8001d0380118002268503a2070b00f005c4009120780d0107006680c15601c1d000d44105075a0300100078401003402042020ba020f400d807230350000c0c41c02e00948440ca00100000784400c485810104460180c4d0107d201000013a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 148333938 1250 148332688 148332713
    0xf010c17040303020d080702010b150f0d05130302070e0408040e0601050c010203040c05150405030601151803030503011d040210123801260a1d060a0c021c080907080703 74
    0x3943c41c2941d0341c46100d0105d092b00c122281503684004945007184c0e842d40408024281080080c0d203481c1428214009030040381c5080b5007508000107524409003c255040c0b01d1107014250704031b541703002403c09449600304c500136170180c0ca096a016001144903a03003d242500c1c4c2040a5500070740d0389141516112943c55407a114590060f81c2043d442184101510244c07003d9400c00b03401800241c1c40c0412521354140c01c03146aa041c8034103103a50381a4044102400805940a034451940c0c0e541340484042a1010b2503441503000700740c8505120041e9503032812a49110b00034603213080302c0ca8265011200609000140741e0a40020500c41455006100d051815224510003046100c800c54401580c40c09400464a00052381c0001107103032423840c6c06c02c1c0940107096840005003100512942010121040542480b036030322000420044002c1c074062041c15640d80c0c03014060305582164220b29445002150800344182100010b4640d08200700c040c000f01081c4d0100d0310700660741c0c10a074648040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 148335188 1250 148333938 148333963
    0x1503080310180b040b0f010f0518061b0c06071e02190609051215070c1712010302120a02061603030b151306021f0b03150103060522020f010c1704030302 67
    0x342220b8920910b01903286c0b080b0f458041e184c5c045440c0c81c40d941182d20349e0022141401d02d40a039203084040d5100e0a01506144202d851039504440355580c0f2249404403034030b119031040f0001c00c41075000031180501c51964540d4840003003610311b440d100041108802402000c0c00b808402d0700060b58540c44140310b811a0707815603841c003551444400c07503520784121840f00303c203030304011010500040c803404d00b601d0b01c0e6005519425030040c491a624400b584411380103564026198010b0096240c1402d07101c44091301000140a4948540c0c0412007a01a1034000c0181714003101c113150030303d0f0207604046500000106004c1500c1c010f03015000c6c80c0e8000300b05c071000350301c40c840f0b000c14002d000169200c2c000000132251000e100d00501c81e403024064500c2195014050b81544090816441000d14041e612403134003c03403c0d150182d815a188031614141d0046c9000e041c6869000d070b240c5070718180c8007000030b183c40044001c060074205002c40300c5580071000352200040c00401d0590100d4240310488 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 148336438 1250 148335188 148335191
    0xc09050105012a0f150e0c06040e070507050609030310120f020405060a180507111605060a03090501021303050c010c0b06090603191401140c03060d03110109050313091503080310180b04 81
    0x346e5900e20990303a0003d0310070b1140c01c410104814026225000c080c20b40c0010285081498964255541806c20301c040d2240d440e994030200c20300c05542003c00381c0030040d2a211001d0030f00341031140c41d60800a003081a000c0d0140b566500400e04079116051600302400c41d08201451805c9100c0381940248400c07036681000412804c004115070101050201c252080001d480076030038200410040194405c88000c030906948d0f600380000280300b80041c0c03140b4100400c4080c1c40603d942490fa08001c1204c0c01d06041010203042e8100003140318410de03802c4402686c001c020355403240d0219140040001d85011181070352030310751041040c01c81035500c066021000a00c014240c640d29608012002d075054604c01d07100380002041030400f0072041d100c01d4004d18050b8000e1105080181c215a50303508182c403030303400005824008140c0c0d10242d5008004180701080300c29400c003800c035082000f50100034146080000404e100304d19564200020300604116408030f1032900101d84010300c0001c4c911790299 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 148337688 1250 148336438 148336451
    0x3041103100e07090f090b0f0c09040c0e01080a0c021e01021303081c0b0f010507020a0e090a0605100608040f0303110a0e1014180307080a0605040c09050105012a0f15 73
    0x1100e80e4062900303500e03840b00d05001c942d00e03034404400c248800100340403440041032001005030342cbc450040030740d000c110361642100c00290b800010f00c1d0480050000d02c03003d04100b1000f50069000072251b00400600e417060360084126805140603214030120140c03c00e9204030b0210900007280300410131031000440c00300f4001e844241800603140c4001760380e6407100c14407540204a502410090034258802025a1352460300d504550103610004e4407114031aa200320480b208000c00752180c5a000580450312440c0c481ca00407006004030b00040000b401c000d000740d000307030806001342c0014410a181a039020b4540f000c20600400e0310710411031032fa204091248149a00380e024044042080b84917444107845c18900ca03c8941143e080c0c406e00c56014892424005841d900c2800fa10f01014410365010800c0d0415040c22009000c541d00580003c62500c001001305a0700102011079100d60740c0e800b09035000d2030108a1345030502d407002c0600804440c540e80c404200c501103c1c0402450010301c1008003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 148338938 1250 148337688 148337711
    0x108011505030c0d1b02010f11092b05030f0306100302090109031b090501080307020a05120c0d1104091101080109140c0706061706090616020303041103100e0709 71
    0x41039000200c03030100d107040011540c440359580c001c221409000d02c022075001d03507031090072161a0303140c0c4c814001070755500b0751522a45c100d40030b422629020b10ba50320382044501d1000a918401c002c03000c2d2004080310f14a18040348400300b496a105410109507510340103203030130002d11a8000c0b20301500c503c41064102000c18002c0c0f003a03c4041c6810b030748071580a405c544d145c400003210403041c94424000e80e440000ca0041c01e0050501900605000d152590380610600c400381445400c8103120310b19090803450014400140b1703d01c1540c04842d1503022280b2420024500d495556500e500142400e070500140b0903a400c400705003544c281e81e82d44840c5c1e0784d2200c10301100c1601cdc05205101d44000d003c9401000e0110240031400c2c000d1a0002d4407a5071044440e1302c412000402d08400c0d04800c00b04040b80c002808816800901c00d409441c40504805009440b4400200300174003600c0c00410f180101c4d2401c0021070b00d607407071004080101c00c0ca1101d43c26610007003445400e4080d414003e00340d60f03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 148340188 1250 148338938 148338959
    0x60a03140106020d140421060b0415090b060405061909030f08090307060918090501060803160b010905220c05030706170901020405010c030c0317040b0915040803011203110615010801 80
    0x211070a0071f0032900505040c2040c40140020300c90244c4140ba15a0304c41d8009558038403901400344031890780080070b546040c0c60f0500703452104000900ca5101800108540d460301000c0b220000400b903a403801192401d04203403042c00ba01c7d00080c0c030010040d018641005040c034014003d06204a04035140740740e83c0c41e0125240744090142c00c54110405151001c100c10300d0300401c604034400c0740040780c01501e40b0700c11803444e0045180c411400c10800303101d01c01d00403030f004028090072508105200e1458034429141c0b86804c01429080300010f40d8001c081880341c3c3c200748074003602004080e2041d440c0d45200080102c050500300c480503400c210045081000144203c904a402c10303100e1030303400c41064906a030388441000043e41440422150320030451055040584994030546144115040900040740381244400303240341221400e4041c003000c80c10f41020f8a04540c031012030145000f440d441c0469140001c030100c2041407281c8002c2c00925282c0c00030581000200fa42e55865507a0b0f1642c2e10341c0e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 148341438 1250 148340188 148340197
    0x160501030509070f0b070c0e07050405011106041a132001260f07050f160c080a0b0c030a0b04110706110415050307030b03150106020129060a03140106020d14 69
    0xc900f08540e510070403245c0040e1000e130079814010105180714035a15100d000100804070361400000740005024840b44da04045900c020800303010040030180b03072030758800d059100c00820180b100a0341c40005040110f0080902c005654084681c81c52a201040744521081241b40040e0204006203c9400c142445444011500d01090810680c80d11035a0200e81c00c0075000c0c150001f00070040110340c144d864114020039280c0540590058108081d060000314041907422a0720b40e90000a80d420104e0260260240c00c0740210f07220300c0e42c03911440142e8006084001c1c20759001030800c81c41884140e0f10201401020b40106014002560142584440c038403a0340983e9039040f883c03030b90300c4034040c0c4201c000c0c640c802c9090400180074122000084e2900402403900c008141100c00140f00d66070b828044c001181c814010581c1903a107101001409141600020b41c1c042c400100d0342c0c0080c10f120342c1000040d080c10f0b80300c034040795840e940021b4840101d02c100700c021454810610040b002481c0455 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 148342688 1250 148341438 148341449
    0x9272006070506040b070309020901060504060f05360d32060703050a0b21011a01090b030606120c040e07020a0308010608090f0106150207120b040201080c070516050103050907 77
    0x1400f941d913907640c51070502c10028000004142d902c899010042c2c5400917018068166510f90a84803407038050001d09034240d45242204101c814058810450f0781c1c12150442186020a0001c0740081c06068100e110041000e942c4e00c4400980c1050074000c004003141d24550032a402d05010082d0345c000c80303050200101104040d6404440040c03401ca101c0d42c0100d4100c81090400309282d400d0308001074901342216040101100e8810554a650b80300740305054101070340700c0d10811004000c10019081080301e1142440c621000400900c0968450040712030b44200801340c080d003420210341c030078803940050286011911380000454005030000507090710b420b6055440c11008e80c2402e80488032404081d10390400e80c440e582e14202401c0d803e0007200003801c84d502821040300280d100013440d06407294000f40b0416028916040407803500080c887d4010340a01304040c0c0f6850b4103549210700c3c800c03071101400038081c0c00000c615220700440c210b01291400d9800384015280c22060b84e03181d4006103c2c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 148343938 1250 148342688 148342693
    0x1e02210c03040308280509100905060c0f0408010207030e010f050301051f20030a0207050916030b0105071a0a2403030f110f24040507092720060705 65
    0x5800a485031300700c140c0c40003504244400341d142c28154044003140d00c0b201201800d4a4404020740326008000d0118000c194020610188003107445a81c0c036a0000b17000703d0044500010f865a1703940300802154001c084410085513161006e0500410801401907024001940303001e000045e40c0c460010b8034181c540c014400481880040500b2084141c202408000e020f8441205240c0482c0c8003202c00e20026000061903032980c01050003810440513411081c460b503520340038065030509411070442020740c1424005901c402400041c3d40e0b84c050164020668030484c01c64903202d071060764820b0300600010005000d82d00c40a04031042c0303050414078003502ca64423540200042407084113040307030a02150401c210940c003440d1505040554210900c00300d680080e480303020348400c5603109492401701c1070408840d41071941e030789a141c0c1d94500c1400c400075141c0c094440100e07450820303841200c58044540000304118501a8100c20f810010205005050541810a401e00c01d040b150805c1d4850b02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 148345188 1250 148343938 148343941
    0x140c130e010905120a321303080a030501050a08010c080406050402032508060609241504080307020a08010912030b0112090605060f0109270902060f0304050c010905090103151e02210c03 81
    0x510314064000c6003222541c07c0c0305d000e002000c01c8400f0000d00c0b4040b020381d0040b83d698101414400d030301c0e4855201d91280e81c50103004500c1c40340c0c0721000c0c6400941c0140b0120f0703680c039580000384c985031654148525140802d0b00e4003000802499184040b034940c0c0302503c4040da1b40c0020811004004c072915a1040c03c0c00300f040e2150741d02c84000d24003130200140140d002c0d500c4043d1141040d0007076080300d02c85038400a4901e055141006035000244480b50082c00104119966034210f030b51048100001e140d142c040039591a03010700b484115441d0300c0e0f1000c004454541c2481c6c00500702c1030350501d014500e0030070040d0342944203550020956480d04100d42e1907031a07480340d060400500315442e01c0c000c2d507545824001a070f614002403ca600345800d00036142e04240c1807d90030554000111410700411450420007070300c400c501c440c1100d8104c4004150360300c040741c810380030345070301120144055042d10b00310f01e1540241d03018000042c4080e43e0007040301201c4210286040b401d403440301405400f0b10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 148346438 1250 148345188 148345277
    0x3020901060c05010e0f011a040908040b1303150c03150e0705091504090e06010605030631092a0f090c02030d1404140c130e010905120a 60
    0x102c0c4091280300da8000110b034a0102012030402d010314283d0b86241e5190341845111000c0c03044911000c840072101000440ca45030340b104014401e5116510306000c010940c403002e640e090289100854006484809110360300c4041d01c0100320343c900c0c0001113854020040c3c0703c01400d407042c0b815190340081c42e0300b0684410b0310070303140c507001540400d41c0003440a0a103c3c449020001500c0206540c42c0d0208500e0201c0e0900360804c04140c0081041202c1401080f0301a560100c410076451180c4401480e03415400303404a561114455102c3c41490610041c14104451002205010b48400d440a0000c4c8a0314501100ea00c400d803042c1d001c0301c0c00441c2c1c14890554a41d01c04550042c0c0c038012030b40340c28001020310094941500b5045810b820400410040c81a00301b4001018080780001d0f00c3c000b1340940014051200140c40c0c4050710741e4590702404200d9095204440064019089800701440305443d01c6141e400700000400195040e20325122318803c0c0e80e03140d003100314030351000001c0d14001e6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 148347688 1250 148346438 148346447
    0x20312030a060b070b0708130302283002010207030804060c090302100f091202090714040807081e21070c0b030a020a030c05131e0510050a080f010302090106 69
    0x1801d00008959500780000d1500f03e142d0041a5192090100c9841840c01042c0036002410050440c1d1030380100041c6030700000d9011810030307600c080b000703a10a181640412503001c9404d411400810790044070402c4000592089076500d0031400c00c80303401054100c1182c00320300741d0189003001408203207582d01080c005a4280c115100c0301d41c076464220500d070703034079000910050784420044000c1144580c1d482d00240d4498440c03400340909000b5081080d0380340c2e01042a5881c001c26050400000d402030740000c3ca0044100c40040800c00c0480d180c0c103890348100390f00d07480403030b0444c0b041e12140040c91420a202296910120240c00389034100c2d520a01e00c0007181d40d00980c03048501151804000ca49502d405020b1801120840310060321041101c6c030140071912244030020a0000502200039030220404503042690031409003001c0c1d4100c08290181002e45c0c58100e80c0d804041240c094000550000181200004135a02c0010039220f12002c0060000f00b80800f0750004086001800103d015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 148348938 1250 148347688 148347691
    0x6080714060c0a0813090b1801030b070c05010e010e1603080910020c040903031b0201060e010b070615090504031404030503091c050d020f100509060103032604061509020702031203 79
    0x441c042e83c1e0080100e076920000c0e03034419480f510340300200d52000c0c00419203521030441d180c00d05a4050080360b0031881542a4103805110040079000701000040c0420b11542c20792050a901c00028882c004955a0f071501170400c680000349070740704c0c8141681c0039150004214081765003060303170b4614001c000c5092140e00c0040001070400d40c4508004503226882305d00c80c0072a810f0003a40c0020301003a03402c0c01c41c14458164209035085a05006042c0322041010140d02e044400100364103070741d4002d5150900141060307481d149800a0340000c00518036003a070304503d128900c40c0d039a5402e02880410441442e0150340000f81c4150f00c144070954160074001a10304980ca8444803141d02c0d00000d69a2604d007030308010300301c030058114a0035083e051b401009800b0742c0c140401c200f1300051401c0340780680e4400c01440003604002140347c80301d0808296924290100d000d0440d107165515050514001030410104524032424000c100000d8200d41d41c400d5908442e402005000b600e8510031550505410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 148350188 1250 148348938 148348957
    0x1e0403081608070c150e01051206010e0d02040f0b030607050c0d08040f0b09010902030111041d1810090210080601050706050a020921010f0501050310090c05090106020a02040608071406 81
    0x30040540403504d60301e07240d0b0041c00d01e034150155011010030000c110100340e801c0b49040c000c05008803491a800320740341d0b0754071800a182080c910480900024007090344204065089880d001903018021180e03005851500c0095007200c2c25130300d0b205800c42d4580b040142030302203034000f9512483c43c030788201d201d541c0090043e080d07268030895035101c80c44a0042628000348580d55245080c003141400e00500d105030b00c4507144c444c2050314000070300c24090348424420603c1c103c0f0b40d001030f407050344400d910f44c0da10800008407080c0307240341c4051500070045180240e20880800214a0856124000b035a201d098180e40d482d06041c032641c4c41d00050800582032070707282034091040c0c40c215182c02c0401c001085280c03c002e1501c0782c1c0e0401c0030b400c54020305803c6039260304110061050362400501d0358080b0b03030a20000144480c09007001e0f074075040c44d908005e03405405100005550ba9000981c0c81c6064000c41d400c2151642c0c1d200000c1ea144407034800c80c6000d803180c100c03140141c908400503200802 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 148351438 1250 148350188 148350203
    0x60108070b030603120c0105060901050901120204020306271f06050a0516120302070c05090601270503010c05300c0a05040e010b0c0d030204080a060b120708031e04030816 75
    0x107220302010605e54000084c001c0300c9a64910420600c0d14168000310b004090a9031340408650414120310905045600080c2c01113800001080e1103071140e00400401f02c51030542000c400b00d6540c1e65031301d451000d07188442c260900b001046010001c3e0028a02150302d82c2e00c40c07602c0c14050b56001d40b4550010800c5180308281d40a4807004603070300c0c2407005100682c03075500584d0f41000307107070020043c9220342083c0c0c050b40c110410881180d811040e0b040d480384130030384002c5001e50150650302c115083c60f0006601542000c118412884d04074024013034160741110480380910360207130b2940e00c9188080300741041544090108040d00c0c000f00050101c52040c3c5440b0749820b48a0348003280c01d802c06c1c0d10003494910700003440100c0d40300c140038521030000c042c0307030035890a8507101c1e52a5951120b03036001341030b440d503443e401c0300943d9500c140084015501403d0f03c040d03039554444140c0b00d810584003074011140000042e503404022800303d50907668010851800d10071010760b07581c0d080d4a9190300301c8515 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 148352688 1250 148351438 148351453
    0xd05030d06030b061e0d0b0606071a0402041a09012d080714010504060c03081e0708071101060b0435011b0306061e030204090c050912060108070b030603 67
    0x601003401007201440c0168240c480c0c0341841d905202c0c00318405a01d5900792240c00240701c9855540e0a07651400d42c3e00300b0245900364881200183da03d224902c03000704003100911048070704640c0e000e0050311641c02150f040041c10450361a00d4200907002c004590300004031001404a0104c100c04088502a20003c5000c15501c10342214501d0300c80e03400c203010550006504120f617208004081318518820301e03041e0b080520780040604207404900008043c090354000207001c1c583e0004100115910a1000480606064502400d03102d800e030b9418000170054510941024014001c180031122042902e900c0c29151450840c2940400d80b00304200f8843c1c1c24142d5055840b20305a01c04400447e0000243d43c910f8610016030320403e9030342c50051504141d02048490341158404280255130000b4035001072070300108170b00a02c519040000c5040c81c18582d1104507a0250191242d8001619410000c04001d25015540c807001d12454481d0340c000441486099643d4000e550484406001c44000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 148353938 1250 148352688 148352707
    0x5060f010305091f090b06040204080709181712010b040b04090504060905010c0512090c0906040f09170711040e1e01060510170609070e010c02010c0c090504050f0f0304050d0503 78
    0x3ca080902c00d8955071105c1243c82441081106180c01070007c03101103140c5440c00e00001e407200c0081c86804d0b409a0f03184110121a5201102c80c1c10300c035400050201c071089140088070b4284c0044600841c0317040e4810000c00c00042e00011142030326045806241803038540900c202c09090001c2044032100c0e22440080c3c006003090084241c40115911025180c00c104220403003411001013034071310b1030350001c0203001e0746032280c858454209030b080d640480e890440c0792030007001c2c0c802078400800c00c900c00554841c00403800740140c40d034184525900b040e825440b030104800c1d2812182d403000103401c030032a40c060000e02082c080d042c80461500201c0c20307a58450028640035100d80724000482c201004074241e141c0560742007076010104440b006402e06041e6401032104080080d141c2c103014121400c00156030080c0d400d0015182d200034003c060f41e13140d10346407014040130b40c3c04903142d1092005100300f1010204043d505600070200071424540391100f0001850180320050380d03140000c01100d9107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 148355188 1250 148353938 148353973
    0x31f020f040b090316030b011401020f0d090f05090906060402070507080607020c01030e150f4506070c1104020906030906060a0b070213020c010b0a03111305060f01030509 75
    0x1d20541001c0c0783c603180b01c00b09050402c0180c04c107449004050020900000c0c0e0007111b1181504c452074030301d060000307003c0b005030300d00f130180d6800c084544100c8090408042c4c3c0641c51030140d500362540c04e809543e443c1e00340000800b083d01d00002603002100000d01074100350380a820300d00d009900b1920303119a1802c182d418210107856510040e048158451000d503054000c204030161864020200040d45040b01900014054241007a1200400205501d0400054050350006c8140c004800b00c641c00300f840e65240300c070301000d002c810a020164001c0d40c0c0d0301007078240c81010a9102c0580700c2c0517690340c50803504c02c001e281130b60080d070070710110344643c880e0000745100c2d007a590b0081150f814010204030800900798040c140300c81c010414400161641204000b03000709400c005620380da40d444503603001d0700c0446510b035000a0701e880c0020500c11200121030321024113440c82c03803a4a103400040c40654104440b0103801c0108201c0000345544681c0c003441e031224040054a0303884005019502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 148356438 1250 148355188 148355197
    0x905102703110d05031206030c030d02060a06060810090b040f1406030c1e0603061c03120c0801060f0f2304030b06040b0a271401091802031f020f 64
    0x242000d0002005004200d40d140e80d581045808554031844050203540b4142d42e4499002140c1c0049a488081005a00c003000440c11403007008055544615008400039514201118101480d5003484030020304a4003900c1214000c2c200c03107045c0d14001c2d0400140d500a031000800d41c1e070300301c0c0e5560500055600148507007442c0c101c84114140503810088105032801044242c1c10b4410040e40210400c0c99100541440050005449454480c0d44040000380c00c1005580c01e1008850351300039050401d580200410f080d802c18810800621403030a00494840000f405680f02107a840500104801d001d945000d5081c0703050f02c0e0030b445024419020960b140341990400f40c561030080b80034410040d1100c10035034044c6059808029143c20f0b071000032001c0c1c2e4a4441c0101d640e400300b0320080100002a24a0302010110303c0c10b01082407928080c81d0151801d114251105241080004500450803006811075400030000c10200d2044514480214891001003459543c20801c103070748000000d004c0c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 148357688 1250 148356438 148356497
    0x506091b09100b070c03211d010509120c03060405010b120703030503070c141606030b0303030609060904020612101706090d050f0706060801060306110309030403230312090715090510 80
    0x42ea61f400701380b00281180f40e101c01e8000061a014100c6070050340e08c4003d6546c03e00c000c43d0b214428088062b41c0505042e82156055098010003013004288001500500404002078468001583e031025250781c54400034000100014410000700325107501c01c1001d65405405005100808414650780520748400215882d1902c1c0c1c0500c0104002505441146481d000c254041c501d5440c04d44000740b00b280d4010000c41c400c5008401007001e5441d1603042d5584110501040130541c10304030b6016031590500d100e40101c60300c0100c034117901403102141c4240540400310040c50b099002400c01e45040c0c00294403d96041c0f030900c42100810020f000d40401031030081d00004500c0d0550900760140d8501d140c00c015101000c10a01140c0d440000840303007200e0f0000c03506540118404227041d107115440280390018400441c40022034116918018040c00c1103104840c1c19035500d240d040c01992005580c200854802c060030080381c141020031002060484c6450040f410680b901070341e401300900e510 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 148358938 1250 148357688 148357733
    0xc020a05100e090a111b030f07060b1318022803031e0e030a1203090204060306020307120c020c0111070510110606041503110a030506091b09100b070c03 67
    0x20a8840e04080c90701940024100009100005c0c0220715054a403040800881c400108101060031440c010320640e415829000c040954500203030030600c0c040d11403c440c2c0303032013280310b526030003d03815862003a8100210781144456070600d10b9000c00c0342101800b2007a45418189452050b4000b00c142404d102452103a00c0c0c4903502e240c11a4003006a1030003844910510001500281c1186d60000d4407440e607a030300140d0310420704102c4d0f8080f03019040d1308900030f400600702080481008501e07000303144981c403e50783d500c10183c0d024410b6025a0310413410780000d40c202680300240b9500c1512400303000442101215001b640c0c6a000c10360081042010034005007240b50680c409100a0000a810a40c21502804520200c400d480c00c0840c8610000304161120406441c841d02c070039012000940d0007805031500380c5403044181352511102c6941c8a4048011500e00714a498005d03a00ca0040300070540040006003010005945680041c8003074807001c4950300000f00142042080c03030384105440d00c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 148360188 1250 148358938 148358957
    0x30414030301060c2102060408030c040504050403030207110102010b010509040903140708040618030b150d0c0605090117100302090c07052a0321090f0915121207030c020a0510 77
    0x8000e01c3c0e131806100217011114a1052400d6282c1d400070304c203508260000101656500c1e00e4913110014480d40d444507403c036013404200014075030142d02604001d40101c90403501034261000484c01c84040d00040c1e404590b052180c3e00301410194402e80c1c68900c2070410340d81e2041c01c50680d0802d0b410455003194404d10006080c081a035111422842c07000c0d40300c085d6141c0d1411680d880302100f00c0100b24034901c0c43c10708590800e03030b511154800032483d0464540c80c200d0391100d030020400d0384081145400b050106039460708584500b403116104110380001440c0d618116030800c1614070000d840000b03100e0043c40b110740030400521170404112a00398240e5030702c00224a01c2042da0b0300200d0603d109422610032024108504850004a008102401540c030300183e400584003d417062002c0b60008102c5e810845088845107508007146d00c11a0704c600f800704005c0c052a650b41010301c0c1303d05601d209001000010340a4a80d5280700c44c030041c003c003185030b26000880c2e5014903000000700007844450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 148361438 1250 148360188 148360193
    0x30809040e03070b0c0a031d0604120905031e011d0303040201080703140406150902043c15090e040609021201050112020108090304030b01081c08070c08030414030301060c 75
    0x2103030485805166026604000c8591544d4036030b1500204500940103000441d03131134081c42a404240200f0000b00b0707003000c2c800711400d5542e981004031130445800311481d808070401d07030203504ea000c01c452000b0000e0040601400c4202144041c0300041d0740309649500b6449400340c40c1c10b60341411411448011340d01c038501030000404920340540340405151402c500d504a203484020215801604000049482c80c1c1c09100e420301c5c02025401641164400729010070308041128820300546900c4c4010030f500c5c0915a08511264800340d601c0351b0480c5140001c000b200380104541d100c81520781041e1040e0340d500d05040c400c400342140d00b11b0f00789940708120800c614003030b0f240b5026141e0000c0200525814044171244000c10100e003e81071000501c00141700203810030803540034651144400c0c0e90b9580d12890707541d0343d2110414030324060f45c41055240310706104038084ca2041c40c0656403400f000401d9110048154070203031054441c0700034040032560024040008500a00c003540e03810107060f6250 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 148362688 1250 148361438 148361441
    0xf02010b010507020a0b071703071112040e01030b0a020f0f0703021e0706030e0a020d0506090706031109060c01020702280902090f091008010e0c09010905280e010603080904 76
    0x400c84203050140c00c0c0094405030300c035641e5440646a030a640c1594580c1c3c01d007807140760655454480360622100000304041c0c550b1002c61258600c0d902e0f403c81c0c141c071000145880082c040c034020304241070403c41c01000445c011b0100960041040c001c0107191001c46940030b0308583c4640c600c3c4100000c00510f4408255040040101e42880c0c220321845002c1480409a15001c030751080b4020552135584400a1141c14031200c031030726900411484503824a8900b068a40070221160ba105004003080028954024001e81c011604181d18142c0b42505203010811a5080322031406c4096500740821401038440114181c00c4082209450200c40030300c01c003503001d44035941c00948905006200380035a54503824040c119800d805c881c590a5039071042500c10034032030b41c0d9008003d2503007004199020300001040800340a06c0a480d00d04c056130729900d1140503180c003a91400071500b0b900c2d500c0109010180c1e020303000815040d030081005084a0300042c01e4a42070b4005581d0b88000080c96000c40c41c1c02d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 148363938 1250 148362688 148362701
    0x2040b0a0e04121416080c240a180819050c0303072001060605040b030a1112070f0c110906040f020f03100f0f0603050402030c040f1a041a04020705030405100f0201 72
    0x401303050781c41d0208011410000591201e0001d200305004600354042ca2800e2200e40c0e9100d0541c0c40d103400800c100d8070b00074000c28042c0d810440312443e100e203480d220300d0440071184000d41c1142e4a6840c0130381e1a140e403d24000c1486081c41000700c10301081184010a000860084080707a80742000c440e14410b4100081420f00d80071036560785022400c0007100e4005041d503044400d158405074a998400f440b110141006c074189000e51a4005080403a1444104400d40140100e42d41c100b0280600d1509440407041648050510b03403d46815952038600815080d40c0810040d02c04264140401100c200740d070007070201c1120402c8084100301e000c00078440c200d801040c0003007407680003610300069002007941c3c03401110304040c8c86600003030942d02c00300541c070140c0c0d0002e0301c100b217001c0c44030003e40c0050030034180f030403500103c83c0c4d607280c058a000d024014803501409000509103281d1810003000758801c0754101d40034003044c07000042540c0c41c1000401e20b107582e40c035900c0203840c00d00802800c6412 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 148365188 1250 148363938 148363967
    0xf0a0b10020f060708060a0e1915150905090f040501090b090d020c0607080a0c05010204050a030609060e0d0207090b0301060905010e01260c010c05030904050a150503030304050a02040b0a0e0412 85
    0x3070a204100082d0388880410b001c2314240000c1b1641c907200c008014510000034403140d03a0040c04c004500c50f412849804100458040317004080500c0101e80007240d60781083e00c10b103907011544501180d51100b00064803504107104200001e000201556015580002165810306d180c00c85048000c4154040c050b40794041011142207245c000c0c05d5403618034a00400d0540c03400c02c240300c072945007006000d5044801514000308502901c1c0ea492610401070006240300315031960824202030f03074054001446415603801c0c0c1e0003800c1d00340d0910b082c54001380104982c80303a241d903c40400207144000c91040d503001c0d11140c50b011030158102164a49911200c0702455407600e00c3c4070340340600392004540ca1940756000d10382404842141d04000346140158142c00b50300a1a01c402d104401605a00c4001609500d6a00c0c0d40307060b6868003010f0b283d010465003e0711580040d0300040051910303522107030241c8001007c3c1030907140c03103582140400c401210202c400c2c100e4032244401068010210022040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 148366438 1250 148365188 148365197
    0x14030a1e0b0103200a110f060a06210215180d080a0206130b0402100306030b15030f01060308070b0603010204170f01050609070507020409060e1209040c09050105030f0a0b10020f0607 80
    0x5050503420325031841881c08030700c200030303180f00084a801b006001031917103c01722804a64040c10a510044024200343c800c5c480307100f11528207c11041c001c00e40301032080c0e030010b100110014090040205607444031030050b000c00d8500c44200c00301d81d00c0d040d082d0174150240c1852610348170707454000307442e002e406000000c6101c0c0080740c0000040f602d080450f403166040c0c0d2488010104203900b5005005a604000d03d03001044040210b20720002c50341118404084084503040132084003a42d088890340e00000e01692020440c0320049080c3d00340310f64100318041d00051400b590381c5500b1003240001c3c1402d000380d4124112010410000740146c2c1d4014000302d65000d22400c01010140140c07090440c0240640c1e110112241441402d40c03250705a0103048054981c44041a5804000b5034050000c851140b49044000d14880b80704207045000c1d01c0c0103854046c9192101030704c0e8229070300010200c030325082d10f54040e4015500c0ba08040c0d07000e0a81a001882e5441c207200e60241000b000070031600811 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 148367688 1250 148366438 148366481
    0x210c03010e0a02091c121808070e041430030609060904030e030714010206090c030a14120d0e0105090c0108071d06040f0f0b0a14030a1e0b0103 63
    0x14009112a142c02000e900001030f0344403114000f2408070600c00c250500c500d094554200d05110f4216194445d007035280d03981d10b0740501490f1911418240c24041c00359181d10044040c400c21103d0001250045c1c0140b10342d42c2c40316645a045844d24840300402501c0065442d1a00b600c0200050340c1c2c80789034650707041a4118900440858442030004120a2065540b07401040134140100c22001e0908006020794058a817aa1201c0340000303514480f0b03d00501c00c0400140507924041400d81c080d41c3d00074054a2070b0802034403080100c1590a440a50a009a140c0c05032114500700042000003185030380400c03048141080d490071120b0080503801c04d40c0100c40c00c1c0303a10342e078010b503210380c8010310b410200c18407400b91580111594040c5001600010000340c08251000410501000c40307030a0844102c00315100e2081d40c1e41130051481290210341c00001010210410b40c0c0590390240ca6201c00141e91040308010140081c40c40801d580030301e55414401a41c0e507071601418200c54400030254501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 148368938 1250 148367688 148367699
    0x206030712090605090606030d0206040f0b0c0c010212040c0e06010f030513020a24020d020c060f0c061006090602071815080d030f0b09070c0b100506210c0301 70
    0x2440010680000c00030382030000c071454450382c2d00226041c0d07004603080000d4039201034000e603204001c3d03070010b1080c40f91708841c0b02c280d440000d4041c0f0a543c030406110f0410313115030b1a0b0a038600094001d13002c0d200300703001d045c00c000000d2024008403c8a40150041c0303050074140840380c0100c3d5000340c05040948400c100f010390f0404070480b03101c15130340b41c00076840ea1001040c030411450700c84000d6100300030079800a0591880a501000d0712902c02e081c0482000c05a000d80e51000308102c1040581c01110070580d41d0319111004d030501e000100411031809591640d640c0c24213000700c0c2e2a01030240300e08400c0c045251300c488108040c110b01e000802d259400c0041da900001160400e04030310549031400c24031449500141d8100600c01581110001c05044a001c0c0c0607007a101000e517129803402c50882c825240c003500540c022020358031641c6549255443d02c90794500d00074031060504101120000b82c41d16100300a02d4980c001c100d4088400310320001582541ca80605032101d4084e05000600c00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 148370188 1250 148368938 148368949
    0x30c090908180301150e0a06050a06120203091903210203060d020d0c0b0301030c0e090a0201080f1b04080106030c0509100b0d0b090f0115031e0b01050c0105090c030f010902 76
    0x1400e030700c002d1040d40212910002070701500d02441d0f0042c80400c0d0b800001042018401e80500800752005e040c001e01d0303118010703c05406020701c03a002c00510f502011081400300da03030040d0b030819441c1d402ea40d403045030794480512000203a617044001522000d44098800c0313080c80204180e0506120552660030204002000309a0aa201a1084540c07000c0f51f810040704144480007403109080440c2c881d80d490812020100c0c4a1082c0580e112031000015040d100200743c50141c0c1d40e058403160002e48440c40355821303100c2c0c000d14100541030803140f40310700d40106030050001800305000105495003540303840300070b2034107030382c06140990301d4182404003003009502c1a606640c40340d8511511101ca4210440250044000e40c5400c02042000e10100d15284440d00d81a00c900c0c3e80c9000490000c16021011107039031b29004044040c0c1407041c84840e03243d940049900302c20515159060036205081c01d821a0b4068070584004e80c00f4800030b210a040501172800c022003910000c01c03070b08000307402007034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 148371438 1250 148370188 148370197
    0xf0a0e06040506160207260d08011203110a0f12090509100b0a0504121511070201090315021c0504110105070c0e06040e01020a0305070305010b0418090212060a06030c090908 76
    0x940c4040000841450720b44200b00706c00007040c216480721180c5c45100300d040d201c2241c060140000d80107146030400c101d8040d00002e4100d40f0b176120094169032258600700c03038000d803490103813240c9c0c0600000c0d240030030310040203490750500450064002c101c1d4204080c142c6070340d582c8031318095240001003201c440100d011500481b00c03040d0510760b968130231075800c840700d109a030016441101c80300c00100601400070350030013800582c0e134010055129002d1541e00301d8003c011000b070001d07040303590a00c00201e18100704901d80d0442800903087c94900d41c0101034807600c07107103071401040e511350805c014002c241c0000768180c0b00a0078014138018080d240e5840b48203542c02484c042080070008505e00303868943c098100114000002c54445803081d40080c00b0309000d581c0700001908100012803031030388181c200c0b030441e000d005c2480100070a50b0004000741040000036617200100140141e030719801405103034031410756030100280030381c2140781a0803203503a0364020740040c0d4642010400000c08910858 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 148372688 1250 148371438 148371451
    0x101e08060f0903070b010b03060a061e110115090f0c0e010c0b04020d020a1203030b0303030702031e04051c20061602030a020301020d0213050d0c050105160b0f0a0e06040506 76
    0x181e540c1d010441c3e285101c1c0210050488000c0000016264070810141d400b130703582142e80002003503650034221400d40c4084032460b51090070400c8605d8041c09403100034101100794001154620041041030411001c035480710306216200d14000c002c9400340c0c0303e6000708180a08240301c0c08007410000a00c83c10100600078030700030341072021505650756101e04000e4203a00414042090343c803001c040c03c40403510801240800c2c10034480003e02c0c98080b007581e205c0d101c0e5a0065091460450011194080140b52076810080802c00812191180080b10b90380128072140b03818484854030340300c0d841022401a003d5030b00b05600381550389075120401c13550950001450842e1030106400040d0802c140348000030342c15031000070004540402500a4464007100300304000c0e49540d2141400f2621100c1d40005160707250014003070206601803c068414004c007580070b0340011420380d403803000711b550a841401c2d42107200d01c04c00000d40154014150501040000303088142003d41c0c2c0d050786d854014208 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 148373938 1250 148372688 148372711
    0xc0316120b0901021903020a02060f0c03062808010204060f050a0801030f0201050c0610060f0804020d080f0f0c010207020418050a030f020a1509020a05010206010305031e07060203101e0806 83
    0x1180401c1c03800d405039502d41c00c000d0035505d4548402c2c00b000d0000e60101c12102c0240c0204030004170840e150540040c030524070084131601e036645260401400000411548100c0301850500c5400c00c940041480050010003000607034450130002c0281995080b1401103007042420440202083d84c890314107411254082e07139000340c82401e440141c900c2c0c00384443c05030b00d5100740001c010550700c14107205000c1720b110b5118a4442d41c07101c0004c5500e080c0440b4041d41010b2524903100025070190014029050441c00d80c500780000c05014110310380c88007101409030380d008292001545003a00c80c2584200d002c0d5160310760984595901902c40e0007100c070281c21b021a200c50645854000d100b010000c80d030142d041c09984c0c1080803101c0042c550103070103038041c040e6120003140550000550354140ca400c20011400d110408052501c282d5285610181a19062041800085641c006540035050303007488200b03103070b003001c1c8000704501110030919010b000c0d54070b0400042d503010507950b80000c0d04211 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 148375188 1250 148373938 148373941
    0x301140f040902030d09090606020a20010c02060c06041b080a060b04060504090c0801110906030f060a0b0a0201200a0905150c160603050a0b1e03010e07080c0316120b 73
    0x1c0c004002242c0080e40500403e2503510b26264818105010344d00710f514100700032034503104100e9490007501d6004101c007807044185004012442112103698030149885048910a580800c80c141c1017561900e00a612080500003041020074582c0a17403001020100b50f040d1805c42c0060b500c42820101914182d1b030ba01006071350380c0303a81d0012005001c000d081408613840740e24045600910601c500324142d4a8610034500091000b0304940b240d54000340b403d421a21b40c00802444804050480c80d8040c4581d07400050718020b9401500001a60750000503501080e02e00072050400e0711310207001c03862000c200100e141f5070051a840b050303130800d50302d00c0443c40c2c4a92006195200300030001982c1e02c12480308032600c06417003e17040c1c1900e800d558180718940300c00c074600d01070713402044146a000203540c9200090343d0207100280340b1488002c002164021210b600542000700d0381d0001d09194001c90494400c5050401c0481200001c2d41452210300b45442101c4030700014090004007101c024a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 148376438 1250 148375188 148375219
    0x21603060e070503010204060c050c060f040509250503160f0807050a0903020a080a0510020c070504020901030b120729030c031008070b0403111014090a17060615030114 74
    0x1080001400f800b60003190303180c1c2c1362140506402c10040c01200c1520801d000740800f0705124081c4e564104215032503a00f013a051104010390000000c00201020403e031500340c6240701104006600d404a584419030743e81003900e200001e44e20304800b403600b800030501042880c03c0e40911610343c03115507403615070340360b4114000859119007103501c0079600a804420200b4030280100381c40440602c0b8408403100c4800604c1d00f0026030054100d611000c1e08511010400760810790010840360005150003da0700b00142c00040000000f046054015400302005109880c140000b03164049066910b04409200c200b11000c01d500c40140803104070740c408404506881c681c41c441c0400b0342440400d4510182d01c41061200c10b80142c03000f035a00c608091901e0030b00b4200102084902070555680560740380444411350410741c01400f10036080021410001101010081010060396442c3c01424a9042c414204400c00c108000c0810090700200b00410190320240b0601d44c5c0c2c00c13026144100b1b03030309018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 148377688 1250 148376438 148376443
    0x516030903021b030c030f01060603060e0106020a0f08070209040c14060909130503190206101208030402040c090807091b03050f070c0204060e090a020a06020f0309011202040f06020a0b0601021603060e 88
    0x100425011f1207107062a943e006810340061043c2c5003107507030401040303642d0314141300520020701c03600c000f582003550020007042464200030290b6006040c02894480c070f5a0110319403200c00c0780e06a926242011051100824044054590800c211892410400010009620b030709010b000321402d120324135081c10802c9014015a41101c5141507285a40440c40d1400794803004200c0d03204041f41d08004002c11280e509541c100c00c41c603040055a403c5594550a00006204206003102070041d1107100003881e00d0100482005008804404105c0740340c0c8041088001020b403035404123040c145000c100c43c00180c100a5071384120a443d12a8a2060345e0012500804580e00100b800210780420009084000295103c041d4420f80d1100f00d4038ae80c07040201e0300c810700400d003a1015007040020f12420340c40707403242104c1e201944400505c2c1950f0ba12030000040410351040c0096007100c4c1103034042c0b11492902a03070250082c006021004010480f2025654443c0130050045548a8107507440b40c404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 148378938 1250 148377688 148377703
    0x2706030703170706050c04030f060b040e030a0f03180807170c06070f0219080f071b0306060302090108070e0c030c0903430303030c11030d0516030903021b03 69
    0x3040c010181c00190002e0b41601c1c0d80103a40588010f41020007051194510350101c408403600003400b5100c01c00d0a658000292414003400f50b030191b1506c24010400ca001e00080810300440e071200344508070780900103410748800a140007403a0807500c4101e400700f41040203c0303031141e03400030b800740800e041d60010981c54001c9654000f500d2007000100000300342c0100034a5581d100b1a021110f46044804c0314000c45085c0d01c0d00100135503401d21060402c218404090000d9910a102c119294800c500c40f040040e0081d42c8203440260315400100709601304190301a024210020250102c50708061001440490280020202c03240c00400106880081015205100d00040654080441000c0e000c040404e04d448640392880042c02408203590030b00018201000403502e04502003071075903c065000b0400f80380c012003403160850469405a000344002c01c0d04034449440010103080500d401640000c66001c21428140f801d034212003c69000038011890031030136608810421102e20219050288 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 148380188 1250 148378938 148378943
    0x41802030723130510020d08070c051b0f0105130b0706090b040507060311070b16230a020c09060f0d11060a120b0406030b0117392706030703 62
    0x50402c10354420304411000f4044502c0c0c4125840500d6103500401030103040c1045908050380c0701059131007481d0300800c0210740c083d0007410302c8a9000310070b8540300c1c188030004038114401c0078101c104c04d50600d8030103140204d2610a181440c10f00c4c505441d0f0b80d000d62020700515102c9240420400101308007604032204203684654413550505003441d020b0340d034010324094580800e0400105010308103121043d184e406801407000c100c1a1107002030040700d03009100d84001040283c804010006810340101c0304901e42c403000e03055540791090130003070030701300c2c0868030605c10290720052024503911520481f03084403040311009201d0900e0319100301d6a8811141c03864021030080350f8070210b513810030445030034001d280314184848440c0350100011160035000080c48088242c0050100c1841381c008103070f8102400b000c44441003461440c14000c00f164580392503c000c142e1780c0c0030b1148102000300b00c01c01402a42c0c0c0b48005100343ca400c0840c10804407403075a01e8448a40003460a41d2700700100c000854 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 148381294 1106 148380188 148380227
    0x60501050315060d1506020f070e1b09040e010c0e01090e1b03040804331103041406071a090d0e01020c122b030b01050418020307 57
    0x3c00150112000e117544954030321650f45c5078800e0b038001d450507400406202091440052a05100c0c2e040307100d480441605201000015988405020a202c1c8400740c590250300c0201d40244079078003030102c8560a02e0811402181c0114007070040b0b04003030f030f41c0c1942d0075122100c04446030380940700801d03083e003500c240d030315110a24005181c000340700b000c0503407034280c0d106112855200800c0110600603039103941421210090341d4181c10865050600ba550760f101c421100b62640680c0c821802100640d00e1841d2aa0b0344240485c0ca542c9c1d4000300c032044101030f000c0e40b5000c1b407c00f201e5450a600c90081144003090054140c8548845c0581c0140342c00c4881c1c1c000d00003140b40b2007100e020380e8803d2620030740c00790714007150107d2660090388a00044165042d0000c5c1599000213131035051007000c00c020f10044100d49030701c100c0d21110074030140c0d40e07840c0d50404454500b09002e103043e494 = true := by decide +kernel

theorem cover : BRFrame.Cov 148201438 148381294 := by
  have h0 := BRFrame.cov_init 148201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 148201438 ≤ n) (h2 : n < 148381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
