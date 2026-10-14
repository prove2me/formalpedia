-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0426
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:45:16.465391+00:00
-- url     : https://prove2.me/submissions/8b1acd11-a36b-4501-8476-c08132c67270

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 76438850 ≤ n < 76618706 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 76440100 1250 76438850 76438877
    0x605010908010501260a051b0f0d02060703050901050705070e010906150c060e030c03041701060e010312030c03091b080c03030c03180607080301080c03011d060411030f030a03060e06040b060a 84
    0x308820344400916034050764401d020323510700c2681010300445084882d85100346020080162584003104003d42214061240308003082c016005010b0350f41e018141645880001c0d0340342c030700300100c5400c120514983d80c8014442908c90f8440e00c00501200c12541c0c01c011301a110190040d40c9010006020715101c456907444d075001030098414075074500085903150380e22925030024010219014000561034a00c00141c510340c540303440c034101c0ba0481e0716210691000c00c4120050b180015005003072646800130800000c07840d400c240310704002c0030200c142180c149001503050111885c01144240e105110200d1219008022207955548041c041013118642d0008078007240203028000c0c2c2000c0b408800040c4942d0045980b80003814100c0c000c0050b10360440c64a851f120504242c40000d80c440800500060404515018000303001000c4400d00000540b5031451584008002d40002c0e49a110170001880803103215038210000319018409003c00c98080b90207400f620700d80e40200a5444821607 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 76441350 1250 76440100 76440103
    0x604030c060b09060f240a030902041a01080406020d060b0c0303040b06030105092e0608150601030203040314030702010e01051501170f1f12030302120f0f060d06021606060501090801050126 83
    0x6181658906c2642d00c46d43c1007540580100039201081c2d0086080c84110810010401c0c15444142d10503125038001740c856444003c0203400c803140e0200282d46d1000003190103040036016151104d103220080d0b40d280343c649024040302c040500501d000361b040605002244a0210702c0e0f6038501101c00d00d0002010380c10410a01030188905080481132a22001203004140424600304d0400b140b8075228542e111800110100c1c40100c41c0900021140d6030001c0155086030000d41d00311a071440045603110301c14102500710382c000e40701b44105402c003a101d440956040340403c1c00380c130001c02c80502d040c6400051070071100c000a08034507001340790b202c8281e841c0101d40362201c05030208034a0410040000e1501400941c03149000c54400d070558800100d40284030340701030b0710407410241e40030301d152111814810800954001100d20a400344241aa941050000081d580303000781c101281241c80c00d40054034925640d00700702e1460f414040103000d078845880d03200703000ca4141e800001a02c035a40e100c0c103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 76442600 1250 76441350 76441399
    0x6030e07030b090a12210c030b0a060806040c0201020301050f010f17010602010c090806090705150702060d020703110a080a0c080f07060518010905120703110604030c060b09060f 78
    0x101016100400d0101c42e00d000600110485d1162068180122141c9410f8910344d00c2c030184e80410302e502d200708808030b13991504220003c20840c10302041f0f0b806488001031201401d9009140000c040d00c0400c000d61626008600440015000840c03543d410322010908500751100b24506105840c40480e107554829410504140446521040c055848850084c040c00c00140040006070010001203852180807079461b004806100c002c0040b50714220901070109a20708010540c60014400480961202401031005000841005070307a9001031502812002c00c503407040c0c0095104044500c0080c1100088401e4030b203440c10000d0007590103103032107280c51041c1c03401a050500e0100c0d01c2010050140c2090340100c121140110b4041908403006080b51070700c0303002810603441496800b0240502c10000d010060280c90402e1030b10000413512841c2c40000d64044001942c0280450203005461180c4420007004039800402070400d48000381c5040c10f2030350341510420101030446021074491480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 76443850 1250 76442600 76442603
    0x302060c0714250e0c12090f1b0a0b07020d060e2b300b030703140d090b070b0123040c09171501150c0f060f0f0c05030106030e0703 58
    0x300e0343c1e21000807581401ca214122800f224a02c1800d50200300703050b07003c0300c1a100303203100000903082c2003000e010610140005440140c686c0200303403005c1510300e8140084038825111500c40700d50070880d2420b00290b00d00603031114040040501c110001a686c124103401c1441d001b0b600030036940d480c4030840d8100400120300c1580700c0030441d00140c071149805a05208070328580c07160458202d103004200c003402020900640d007107885d125450790600d5607a001c02c00e10070014045400e080d03203030307a41c0808000c0401c0400010340d108840c01c420003948100417402a049603100d441c00c02ca2030f607907452210241806a40550314846e03810202805c121b00070744200c0200204103200e00c1800d244007402c102428001c0c0d0301d815a80c10b1081c10700707410014244823512810401c0c0c00680e0310341a40080c605851b414000c04003c449c85a00021a00d4050789007034440c01005c0002d10008200c0c641710484050a035440c130b2860505404518994100c82900d04680040c100414a0852000a182460400c2c2c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 76445100 1250 76443850 76443853
    0x9040903030902181501110118060e0706020a0c060f050d09061e05090303010509060109080709151203090302010f0e030709020a030c090e16031b02010902040b010c0302060c0714 78
    0x2600a05a00d038004041e9180261a0740001309a003101445241204070380c10000080d40d640d8144195118605040c85030303107440300024044485c5082e105c09071304010019500070b030311050219000b6205010b810010b01e91800100b214101030ba96448003880544240001d1003080e10002c09074074000d800300c8a40e064519020030248500b40b034068018910742e41e480c00048580c0c812803061180390721605024460312001942141c1c0792208010760504000c01c00c1d4100407804c100084d0340c11003040742402600783c0b1b9802192840603002240900100365004901403900c0d10359a0700400d8000d405002900d0302031803c8540366505440690f5008110440f007074162240e03600c0040c955042d41e02504241d080c96400b4490382c18a01c1040741d1440e047d0090b0034445120101140f08a24034002000e0500168140444c0740115000300301c144d140000b00c1c0d000541d46078110700c401c520313092248041e0483c2c24240300c0c261403907030f80b0029a108170050103681c1613400041d210742807180c6003040319541c0c4103110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 76446350 1250 76445100 76445111
    0xe010c020f010b06040513090f0b090a120c080d0b030f10020711010c0210030b01120501150f0504080705040f090212030409050f01031101081005030118020a08210a050904 75
    0x260096468040266000d125483c19049500364a03003402102c0841d0401030000f2003003440c01041000800c084013040b600410700a43da240080e60031510980304110f04000740c54002d24a09080c0c0179086e046407180c1c200701c0c000303841c03200042881003540c801d00c9030315800291070790056010a00c1d00c030640b404149039204407408001c00c25515001425400e204181c4c1c120f20407104070041d02c001d003000d04000c0d40401c111141c01e0001d44603070703c02003100383c051410810b110000d0308032004899007a04101c02c00006409881c0c0e841c0d821106000c07081c0c1e09403500c3d07440c10b450181d56940768070003400b50070b100307540780c2443e1000000c9680101c11007076001001e80c40c41c1824049040c2d0f80340d215104030115103003042d001035001016a10703894126500702d1000c41d000d00d00100111f480b80700040c4581540c403410b43d00801c09071000d1180c0603014a82e55018459605607004010305a03085521600941d4041405c01c5c1d03411801b202810030300b28281c04243c3d01c46400c00015541e50040c50281074009207081c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 76447600 1250 76446350 76446371
    0x304020102120d0e1203221b09020a030b010c0206041a0d020a08100801020c100207020103020c120a1d0307050d03090e0c270109030b090102071e060e07080c01120e01 73
    0x1e81c04000e140c0c60060803101c00c0800f00d0030484407070000300d590440c203142ca5583c410788103d8400780354580f036125451000000307502c1d00380702318034088942101021540c0414401511505885140621402400d1a50403510039a00044084c8030718040c6204503400494518551029082030310801240d4036070075901c990440c00010003000c0c0480d600e80845c0030501c00000c0c480418800c65010300c2c2c2108c050034004c007400518001a600c03201d01281015403c00035942482003e000c5000b540050612503030303032203401090041418180e40003e18550010b41441e0285513030026601e0b08407903082c0c4040b000c402450409030740b482d545070b001c840031040460401074854001801010040b0b2602200401a52011450554100c45045003400310f0415034060020400c001841d561145031500003501d810714543d900b082d85d01460322200c4003205030318648401c00140d0300400919644280080104a00d0194995552400340c402d6906015610311210190483e80d0001c01c0c94105210080c400030408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 76448850 1250 76447600 76447627
    0xf150609120105061804080a030c091203020c01031d060f06030313080106081608031b01060b04270e030703030905070e071107060305150111100c1808010b15030402010212 75
    0x13100c0345880760500c00055003107040815245402660402000f90038a0704040d13007600100108280c140c240083c0100c0000c080480d4044140010f00c00d5010b000e00401241c00501595039005440d440240b01d0600c0110503c400502158030286844d002441c070384400000c02c2c00c500c00c0080c0e01c00c07900c800039804109201d054019500b02d951341c400700c0e08410381c40c5401044041d1140101e0840b41c00820007a1402200c001c811899145038800019a20765103908281c1c140d4403d40c00b0701040428403941c1000310301030345081191444402414012214900e80e815140c0c89a503071300074249a513078040e890a000701001380c03001400c06082810040d081c55407018040f00c501c2102c90010748519480442c032540f003030040d2406160500300210500c8101d00041d43c0c0d0100900e1401054440d40d0621a4004047e010b1030740080358035199881c02001c4910540c0804449800904c901d070305207040c5101030b85480c590403040010b517040454581e240da00c0100d041200b5031b5035050104102042c15452602c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 76450100 1250 76448850 76448861
    0x4020a0306140f010b0702100804020f030d1d10020307120e09190b040b0108010b1b030409090c080105040c030308040221010b0a0f030f030507080d02030114180f1506091201 76
    0xf9425459032050780ea602a404040c070403500000e400c00b580b00400315046000d041c6482d0458030081840c000d00c20a1000300e40392148012505001075110000360031202c00d819442c6800300b00c281c50314025181d0707014000c3d50302d2148180007051038003e01e8280d46084d00c1200c5c0c181c1c41c0400144500e2540c10118600d4034590001c03d80341150701c1c50000d012501c1d18040c42440d9103610185c4401c44541e01c0c06035070003019000440d0300f1440541038203045c92031640900090000c0c0940e50320000b40c18a0300e0810000c00c480c41c0c0c01c244c00c168589018003001c00c42c410003510840f685858006d009640c0c3c0c0c8045002d040c0081c201080740350342041541c1c941007040d040030028080583d20184001da4074404441c40240324440544804a184011800700384a18028505140a9003c503454914070101c0c14040f40e1090b4000d8100e06c11401c0c955034146021000c0e07c0c803950400860410034200f13811682c0940801801a82d800c2d0500032810b42d180e29000296488500000d00c213034a500c1207404010701030007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 76451350 1250 76450100 76450111
    0x10501030c0302070203120a11060901050702070b04080c15040b030f0414010218060f09120c0108070f05031f0b0d05040605070201020f03130302070302100f02010506011b060504020a030614 83
    0x207041044688803240309200395034409400800600902c0404580701900d44c2c8200004810002078101c0c82e004d1001c1040402c0c000d0221f10000200c81c0703800d42000b0709120070383d048030004040800040000f0711000821700c0700e148089550021613405407820b1081c2c0d110f50341c0a13019041c004000c0003195a101071040380f04074043ca074070703100328480500c1242c00c0384514a42c407860740914400016050034118080c1c0302d20883c0c901c44c10720741585100010f580e60300e00c55031020300394410504800c2559000203c01d030060050b00f46810ba030350f82d455002e4101e0100801441050300c810912280700303502ca030358010082940d0f01d0340c43c1e81e44640f01c0560b40601802c9405031002410300c1c0105010510500c01c41c0d4041f407040402601f1610348100c407181102000d60180c04501c18007030003001583e215125210f5012080e16212055084a000a401d40300003e140c5030510034a012000c0c8001035000c480c0460581c4200b000030907a03110b10008038041c401d034001038400341c607001d500c9188032201c81400b030040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 76452600 1250 76451350 76451357
    0x40302100506030705010f031a0402040e010914160f120c020307060e0c03060105220c05030a0b0d0201090501050a0201020c0a0507081b0109030206030a090210081609081b01020f070e010501 83
    0x958405043c50b980b10140c0c40b984e030002e003443c2800c40c5135520075030003107850118003003d6103200348101c40050260b0300150065507021501d18010441c3d10454441c9459403040d01d8824001c6161804000b60b40d500103540002c14865007000b419112703413190020800450008004100107216044001d50703a801c200d0003299420b00d442c0c076080b0b01d210000340c010350b88032008008100e036070700b0041071001340800610514800540d40314a14199245405140d80d0100c580d40c50a45a1603c100e110007600d11740503042c2e015072050054640981d0340141c25a094072020308000340d035001840e0003240244100041d00d40c540c0600210340040100c007080050485a034070080350300d94101048007510526a24000c0b6000c142c11200420060820b47d01039580108211000a001012070b00401ca000108401d80d03000035400d00c0420010200c0030607125803007082454030201160810450036030f18246c0c0c2e90481040b102145020742c190b8400c02000d810981000300303592300d003566010391185841080c026103020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 76453850 1250 76452600 76452611
    0x403030e0f0706210603050d0f0c060c03020d0501050f03101802030a0807020301110c07090b01031e06050a060f081503160b03010e06010305040f0f03091205030706060501020a1a130b04030210 84
    0x40880600170001500e4000010f4400d0118400702940d002061403400418400c9454054012825611480241d80d8107a20003603a0b400454a00000310b55050308458444c084100c8d03824076035207000440590040d43d02c580002c108118000950107001c07a008001e42c581302c0d14039200c2c00c104145020300380c141d209070002d0240005400004986010b50300643e0055070050b541080340310516003085020803010305002924903c1e044a2140007a0348080008003551031b008204201c0c240002118018a614a800740e001d0b00c030b1680003002c000c0050704c001c9188120034072061160750148155503003901100c00b480e9600c1da03504000842c03078100344213041100010783c000071102d50082c0075003032045a00510140d040651030b030300c10040e640c1141d000d07008c020070f20310041990142d8107049002c2d54062002161101c1140ca004015034126400850440d0071200a20740014040c5100c2c0207070b091201c401e510280c1d030b6401103040a04070f1580241a00102c2c60905c014160042407400c0c1031052030703c0a000c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 76455100 1250 76453850 76453907
    0x70303091401110d0516021902060d0501090c12020a1706040612031e0201060308040306050a0b0a140a050613050d21050a110a02090703021e0705011509050f0403030e0f0706 76
    0x106c0c88010307042c42c0c016800440c40041528001c20121400502c02408a810140005e448808550b0244c10042d25666904085000d1a4200040f40c50340341c80f4013010351401013490001071030564180000d9050070041004a11140d480740c00010181c440710300c504094400c1d5050081800b0300f100c03040072007144c105074000700700d41c810302950007600e8100c0307490bc0c41e1903e5030360345000414004102d01e2640760f42d2151004640d84807480c0c0001880840002a48010400700700f120f00403542e84460301c104800c05c20303064800d4801e1041021690100c4001c402010030b03040c4204042201140105403e00b160301c1009030542110245c11020b0f4a03a450a018240509407141d960a1801d00654010307000d10003d4180340c40380d0001e110895030128488071000600340395522507089007004039904d9454401c242200c291480201000f031800d42011f02031420014a002c1d0710110280c030190801d4acaa406109810300c040086425092003131044034070090341d03100b0061551400030011092026840900c40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 76456350 1250 76455100 76455121
    0x40c0e090c01050a0c0f0302241b1b030a0909060605120a0b190e0f060108010609090b0d0206071101110f0601051002150a1a1005070303091401110d05 66
    0xd106010000c02010400d0300c07600107503000e4100340b035140c0412216400140001e1032900510f029640b00f0380080c50121604a04070b4032821207000550441a21320307040114519550a01865960918071080e507245000f20000340000e6110011014a02c030001d000d0035481e5000400303000f203590060003040803c4c4c071100115414494050a40ca02514440c0494404441d55001e100603d00c024003100c00c8125101c8201c020800a501c868000041c1c0400c0140f81068030182560059003440d1400760b540c10040c2c042c1180a06d0b01465000340da071203007810b890b91983d400c051080fa030010046911000301c3c2c030300800080341008440c0d0025520f070701e076038a02e0741c80022082203072000d1101620260303003403509101c042c180f038402400440c86032500005064501c035000b1801a46c000d180030521098020824115140700344045004001c101c481c02c003060341c4501a02d01c00c0c2d60600e00855190600c0c00d00703400281028035921469481c14420a040440c040000d00d28020a58001e1001340e94460558 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 76457600 1250 76456350 76456379
    0x10312050a02061927060b09090a0318050411090109140d020f060706051e07082707030516081002031b030a0e0a060603140a12030b040e0d0206040c 65
    0x14405070780700794013050079070000641c50440c2280407070380081c00c0e68102000308881529121002200d0214000010500c911401501c50082043c2c48503c0542403119149030764940d60407010b020403542c488060042001308502c00001c050040013840202180081c00025034410b8001c54046200c5c00340000c2e546680a4460b541e0f008020712805184425800f030000300c004100120341d02c07030801c00005002500c0c2d40302d564001d891882949a101050b40403002d1825000340140062223140d10401c850704102100d05514038a444850301151180208140c4c540b0380c590704001d01d503015032221100c903040c1d001c0c0020101e131805002c9400000c000b04a4004074403058407014103400036004480000c0f4903500042d6080991090005040c10320541c025043c05001c0404881c4291502d60070400d00100752218440000f61030080c090481d850f54034203442c8041041180706041d211403401c0584d40d9a98000030741e040d10507090700d51050f1241d500a45401c0100c81c200c1c0c100301d503924049450303040c8030440d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 76458850 1250 76457600 76457617
    0x12071e080f0601050a03022101050901090915020903010e0609031c0e1b0307030c090b010e033d02040b030105030d11060703050406090f0309180c0c0209181501031205 73
    0x1500c0880c2c4511004550540c0b01c40303051003d164003000640600e4046109101c2d106410030300004041d4101010401001010307809465030908002540c0b000c0782281481d40c060940540005a070342c102100400e0141c200e1410500303060017020108240044c0101c020300001034101000c0d01694000b2044008039060f003a40a011684800322400700c0880705809a01803510040c00c0b5002d0941c0c990340d40d440284180c2040e00c145450300e0010708503582204074038200c4030048000e002480b41c18003105600c0584030703400e01c00e00f00d01005040e4000017941030268604214107000e558a80d00c445122905038400c0c441d0600030710403c84440103040c07040151804e8025600d001d800b154a980c0303412005440c015200307a0358265282d0b0b001c80022088005810014807030b403240c1c2429481e0110400c1c14010091741000098100407112001c1070780400d0b2010980d038100c2d8900d005803980200d010029103020300349489845032400d140041022841c2c0d4a04072442500e80d884114240c000450361800303001c0f00d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 76460100 1250 76458850 76458871
    0x1206030b0a0c03060f0b09040c03110a120501050105090d0b2d061905010c0b061306031a06040e070306051801050106090305060601051903091104050a0207020909010204150f020312071e08 82
    0x5981249230030381041d81d0400062030701264898002c556100c45500c028010300110340d1041040b4441d80c000e0103024010036090130150b0500c01e4007804242121180980204000f614000003142841409072030072105290805404802049a1040c501d188040c0c07400c900c20b4031000014011610341000b038409172038041e515068800d603540e40c0c800300c50740050403290f0b2240034580c803090000140d03c5544011070082d1900c0c00d84140c4010f600500820150886016504000c0a8100254002402011a503000c000064580d4400e0044428030140c80e11107001c650a007000010f071998000c1e0f030300041d2030040c0103690b41a110b40e40191b81c2d501c21032129140c904141e4002d0b5100c3c50082d44014410f87c004d1800e0780710036000a00290441e0000c03a42c69001c240e02085040c20f500700070300c086500502d464002c52a01d030600b094180c01e040c074080300c4404c006c03452250407880d61080c4165031303050b04603030700d042c80d2420b011501404405050308a801071450518039006010304c40c10280380120380099 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 76461350 1250 76460100 76460107
    0x90307050c19031502030411030705280302060c030408060c0a02190203030c060a0608070503030c0a080f0c0d02010902040b240c12030124140301061206030b0a0c03060f0b 75
    0x90902c2556188012012150005004004081016190684054804000300582e40d1502e4941001e804946141c40c50103903010702c1043c001d6403102e0104005c000012490460901403402018024007500e810007508180007140e0b1069000300000030b0000c1d038003910180c0d905a55038001c128101d00070000341c500180d001f0341d0302091820f050200404501e00250035a840c3c00b5075034200902e018010346085d808195207200c10481520701b840b200303001c0c00c400c801440c544800c441500d44e5804071038501400320080055801d0344200e9000c11101041142d6060f2001d04400707a001a000b841010070903406541402c10300402490000c0020900ca81d4014803242040a4000b9030b24450304007420b58200b5102e452403989030110904095402840031600300030410044060600c0c0a2170454040010712000052144003c0b4a001c103a0381560000e10b880100310465900c031801600b038507440601200d1510041c4803100782143c0084507000034940301400a15a2110703640d10a812134403c4c18503498092 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 76462600 1250 76461350 76461373
    0x5030a050604020c01140702070510021f1517060106050f0a0c11040614030d1106010608040c09020a050702040608060c070f020d020901060504031403030c0d0e011b090e09030705 78
    0x3544050342100303001d032006044c007180c90b40c0503085501c2e000401001e03e6419040200e440d50412040000c1c15082da00c07480c000000c903c000e952501522800400b0019000035a03880340855401120000c0501c4420304406950740280000c45280d607008214a010700400032810f2406001118501801415041e00e0074607181c00c21240c040950a0440e02e501c0030361089072165940d03004010107400020742500350f00c0071610400d403a0034580705084040c84460b20035941801c0340401d815046800d20b0524110070342e038618103e19003400c0c54004100d4544041244010707031394000081c00000d0710a0fa8200a030036198001240d4a020441d0260100c03041040300c9000101c0d91100401d141c4c0c07018042d0410025103900140300391509030009000030301c1c04a402c00600030a810620711b0345850350301842c074600f0214602030b03441c814001710300c1245490300c1074411200c400f503114181c00100c02d070300399240f04204400200803020f81d1145440018a08000c2024007501004031081079501070010a10320302d28 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 76463850 1250 76462600 76462621
    0x5250522020a14031603051b040e0705130303080601021b030c040b1306120510090f170d0f0b0102070509010e04061e09061b08130206030a060b0c010b04110a0503 71
    0x25091540030071400f00304940070742c0440000b6500803d030151050180030070810004080350b10083c0500d0740080354010f24021f2088800c1190203403195420f49c20b4460395100c105072113030320821b0248010101274601c0007090541c4031030b43c203004135002d03800e840054000c4031101d0340595042006a9254112080340b0009140c40c0d80010901040036050b055200c000c10083d200b00c6225502501c0817001c0c0e0011801040341c2880700840c00d080f100e104006c071600940b2040054058050000c00c558075504002100d092010140d804090002e0001d000c030000d01045003003c0d240344040d4902502c20104041114a40b84c0381e032a060352008148c0c41d41c25602c90712401c014001ca0f1403522500b41122480c9602c414a40c05540e50890103540040380c440802a00b980b41d125505880008001c0040c040c8020040c45d200b03e0701c03119804480d003c0d100d841c1c40c1c81141c02861180d0000c0c1c01c100c40004c8822030444190440480d000045508100310350200e80300890600c80d0100e0040050820000035180030302 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 76465100 1250 76463850 76463857
    0x2411060421200c0405011a090607030e0909011d010c020c040b060c1501030308060f01080a0b03010e010c120e150a0c0e09040807060c0509030d08090a0525052202 71
    0x10714000c1e1158100b990003801c0d210040380300c0c40194111905603e210f061a010b540e0060290342105031409681144000c82c50080c1440396102c1d000c0003d540090500c554661310042c60b0043c24070000742000c40b0641d009100d5000000d83c0c500c40c05030070034015081845100c43d0f481d03480d0080c110140c030090030040207002c10881030741e2014092103010700004080101058280074800042c200e54150709000d450580c0c0142610300c5820224112030403031340c0c4001ca0b2900b0000410f00400e00c0d01c24040081e0140c120f2400090b0340358079003070500380c2913548103511000381010a802007100381e0411460980300c00781340c003121010a800c6c2d0041122600b055011a0500c01e44d442c03c02c400c124000001009050f05590030f481c0f062002c241c0e40103100c6644520064036425051181c03a086246c004280c641d0900b01c501e00500c00e2403070005264100601519214540c00310a80385000036000310110310124140440315031003d841d0012445040002100c900c02041100300e015905071311055502035030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 76466350 1250 76465100 76465163
    0x29040510150203030708061e040b01090e0a09020f0307030c05090c040306020301060504090b191202030a02060301030305220614071b03030203190512010e070924110604 74
    0x30444540003501e0200c032554040d0800040c1d000d103550b0300b03060314003d00b1518043e041c24444d641034164156400c0c1d0400c0850582c920984000c2200c1002c2d00041c1c4841810303a0020050001500c1003040c0c980769680184002842240e2400c50b803006407083c0356071b5000a00004041d00d100b12400e115078a02080035a81c4903411010941c0780c2078680d5102d00598100381d0202e40070400101c0d003800419454043c0c0800c800c000e0b100410081c446003451240c0b406103104140124807100e20003015510180405017004e60041c20180d07595a491900800c00c0d404001c0f034030b8182030700a00c8103004008505410080320026904d03a0340c200c2507051401110b900c1100115551241e1950300b45014455080c000c0c0118002c0c0c024648944c5090b44000390840202407840410030100400001400c402004905659005100004c1b55a5689050314900e07525009a8010700315004040ca107060f85040b01d018500c45540d460100d8021007030f0f01699844281c50041c55920711020050304003410035510b50264 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 76467600 1250 76466350 76466371
    0x30313020d150b090c0712030c09051906031104030c0b09060903011b03110408100e0c090f041109070f0c03090b0a02010501080706020307050304060e061219290405 72
    0x100ca240d942d55400704800440d829510b85541c01d800d2203151a480d225485000f400c0a149005d81d40d550700800300d9900000d43c0249a910350a41c00058420350301303c2c028000c05030040061168034840c0d0855111349220300c0001906040c41c1c41161240102600c0403070f580711103c1101d842c02c1401c24030070351704034042c9240c004c00c09010b180701596090045400801c1112180f0ba181c0381d661074010146c2d01c41a45900d5043c1080004110440c00012001d642984800300010481c0241044c02c0c01c08914070101a4081c5101041c0410444802070203030146104042d620442c8107904d041c465031590441300354020955001c45c44280d40d00480580070120300c05d02e4035103401c6849006100c4e040d04a403280701c0050f90b503500107204002040007040003038001c030700003541000619070741d16640b88140c1c0a000c0811a845041140d40d45032001555a200002949c41c409440c0850401c00010003201d04240340f41e040c19543c2c0b05101960320001c880c048a5000341c1d10740908613081c400a41000f40150a08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 76468850 1250 76467600 76467619
    0x609010207030c170f040311120304050a0605030c0f040609090c030b09040803060d05010203010b2502060307050a0207050307090915060e0621010c020303010614040f06031e0905030901020d05090303031302 90
    0x2014595000300b0246102301030407840142844288080c01803200c91031078565008004c00d105039a5000250310496255142c004c4c0c0d25a03811082d04c105d070203118005000e40d180030802040d415081580a01540c03d580e604004114215000f00c0c141d03016030003090307003108588006c01c010505250040d030380040003401c43e0f8a56002546d589089a0090340490105100464410600034440c0c01e54503182e041507032030b004102c0c844d03000110203100280002d42803142c0020302c440810700901036000144402015260220340d203c0c42c0c20082e2080300c0003120152151503207110865003510070b140036940700d075014454980e9100d09000740702c08140e08154424007501d004810701c0c1402d004194220074640d01840d1a5458204003a25080030b140071055154030622062182c444011325400495880d8038000c40c851041e1920a03a5254102000611980c142884181800000402803a15850a9080380e80e848031040701102c0301d0040c07145075507141e0020004640c00010341d400341008d041c001010741c1d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 76470100 1250 76468850 76468867
    0x30b030c090108071a04030206030a0207050a140307121d010e040e030301090209100c0503121005090907080c0f06041404062303100b060304030807091a0306030609010207030c17 78
    0x1200009a00c052101d83c40f01600b17110075200400030101800040c42940d00b040d04640c00a00c06000003069555259030220750042481410400040002e030058006010142c000c80c80315243d41c41228140c9800c511076008030000d602c0759040b807210140d00450754018410100c011281c081c41080001c1d8800d443c1c464218201d80107000450003001c424600580d00c1c9625000d1100d86202d20034500244049110b01d4004981d000c000c44035010740c40e24520402d9504d1034650110710080d60170075a00a40140104006001c000442c00c00b0f485c0101c0c1101c040401140410005291552100750451000d0100704a21075118180c0340e03502c40300400c040303406038544904e00b0b00401244001464000d1203100d0350410700301400000b151007030300030080c42510951004160a172102400080410918400003815544510300820242ca00500c01500e00004500000d4042e0020355070503200780509000725075445c00500c03c9945280e4140c4071280e02e8030075526109003480c860380f0501800d07081001620b6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 76471350 1250 76470100 76470109
    0x11010204090606090302040b01090506040b0c03070f0b0601020c030f0c0103090c12030f0e030105070905130e060901020a1706240702150309240112020f10020109140109030e01030b030c 81
    0x400f9102c01d640d0038158619500400041d070b001c4241c170fa030510001e00707018012901d81030b003200c3c04d541c4629802c40d0f4404c00488881d10f503220b80c1c01c02071300a0130050611b2080110040e5081d0040ca026400c6030f2000d403220741010b44480c91000811603590240080f000594042e401042c078141c0600d950074103003540d8890030041c0f540a56002c500080c05c002c068002e882e00806034039060315055008002034609079601504801a5001e494410700f400c4150401c5080c99410444400c2c4092081d01d1003810503040d65070207034010486070000326072000311441e40180141e08281c132481c0b006100d4160b1000c8400c0e03d50f60310030798034901c00441004118000260315018400007030100c0ca6107207030b9a28540218524203012448c204e01c442d01980008a160700715542007c14151131030b209032084140e1584c0300080244955088551b04240d003045440e1407250194401d540c4039008003800001d400f0040141400c03520900c1000b0040741002002e80c2265129900400350210003404444808101c680050f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 76472600 1250 76471350 76471361
    0xa17070909050a0b0f060f1c1b08010c020609060718030506090a030e0f0f0609040b330703020615010909141816090b011b0302060106030c050903060402011101020409 73
    0x2030b919079003c603d54a080000c0c400354158842c105441c1c014017418144002000b6000e1303404801e110382000c8030101102c0302a074100800c0030354454642c1d0581c04401d40300a940c4180ca114001855107440e040c2140c450001c10203921400440015081e203030f81d00c0b40705403102e004c0e04d0802030860a41d11008000030b00e04002d040d00800480004042802c03072850000e01c01200c564165001e1103a01385064056103c000302c0c560402400c40e1004d8413038055102140003002d15220103507204003c1d8600c40740c00312360708140b8050601040c0314901c2800c044040c9914500c5004802401a4482000160a0340010f406d61444841c149004074150f55108000401da0b80c551134120514120141444200001c0f80314282084010501500c001511040340d4130001c3c0ca02c0c4103043d40691610090f005507031080c5154a810000380d50012034a0700d16080082d03445009008900101c0d10380018481042d00920a45803002402030003400380c1d55507035004550240111061110f41d640034000400e01d039180b030164 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 76473850 1250 76472600 76472603
    0x7060c021c021507152307020f100b040c0804030c06090f02060a050909010f0b0a0e0a080111030f060d02060a0c15020a020a11040903080c03040c0b0403061d0601050a17070909 77
    0x19261a12540e080541c04581905c90302880340b03141000a00118115010b2116100c49a0300980800d03031f502c442c10380c1420503a2a2100c154003900460803170b2000705e640072640701d0380d0030b440030080000f08183c15589503c06441c05070200d0340282150001a480390480e015180c4198041c1e0700075801980401c0c400c0d005000101c000c03803404a000500d07410030343c020a006050328120f030058503160011000c6107216012180c0100b01842003031007030540301d04503808001c1049030001c000344c000485004c0e08503002030f43d051030a41c0c44c16020943c80c0c600003510310002ea40082c8042d113002d118038020340f044100407504689100e144580415408140e00c054404004990054010007d0501e80b410600c0341c80c450a922452030030007000c01003503201c10242ea00c0801c7c0c0002a50300c3e111800e0400455030540e1000501d4000000c0100c20440b03e9000000c400c240380c60283e038114002000540c07070300024002c0302c5d04040070341010043da00c450010501c203141c0e0f40c425640f140d511079840d08140e94107101d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 76475100 1250 76473850 76473889
    0x80702031506030f120f130b0304050106030c06081e0a090212010c09060302120601180e04060605090108030c0c010f030221090f06011505031801020c07030203070807060c021c02 78
    0x801c100e504090001038400c8002002809800e005c481d03003001140201e0800021504004c10303601104000010036001410310f095075191246441d25203540a0040c42c00200c3d4809901000010351a00031b000c032501951409514260000c0e1000c1074407410b5100070f00b912030041d00c40d8402c030056180d004405003502680400410b018440180161114556034091010540b0400469101846001806410610900c1d280d25040400f05e64800d100c9803580095109044890074041081110340c4410120345041d2201c1109a07a510802501c1c0e000e42030f9400079682181c00c1d51105507201701c0080e101035000c0c0c1001802c0c0001d22440b02c0644030f556a000d07443d00c0d100814405e120303900300000e45083e021380300144119070400d0450031004041c0600e100510602102084c816121000c00100c400f1034840210348031480018001d031b61340c1061200340e0090161500100d03038020302150420070388205480342c0841801507400c0c401d0303003d0700f046013071429030a11103c000140c0e1006200480010001c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 76476350 1250 76475100 76475143
    0x207030f020111130510030b09070c0302070614070b060a08010c020f0114010510080c0d090b160201060605270301060b120109021201060c020a0302100c1511070f08070203 75
    0x10000e030860700d03003143c8141c1c6041c050164440f603a4842d0340d010181c4509450481c4413440342c3c1011b0b00602021981c05034865940001c00c007810b0f03441699180707814081c3d804c907800a5500c0c8000d5030501b0000781c4058a000c01086200003151086803066005000a8070103460540c0d110b801d036084403036207100d0200581203800303180e82481c424000d4010440c0a40651001545008001440d10b00800095810b0101c0c2c80700203003801d1507003815120450001c803002d1000e10310501d0801100082124001d8410700070b0031214034a03134414030845040d134903d40c50700c0345400c0d0040126003459004c511086881004428085199102070040200412030300400c103071107400502c507028506034141c0008259034030500000c45054884580300e030458009003001f840000c56800481d0b00f039540c0360406900900072510601240e0740c0941c0c51682640140d1000701c4130301c01401c008054030008000c82d410700c80305001c0300b40401c1845103100c10f858460842585012404c0d404241000d003520030711401c1203082c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 76477600 1250 76476350 76476377
    0x18060c031e1404081e0d0504150e06180909011b0c14070f05031009050619091208011a0c0607050309100c020c1f0f03110903030301030605062d01051c020703 69
    0x622240e00c174425904003510702c0c184041001003450185101c2c060766100071a17084500580a100d1020792544041c0004d50380c0c41115069444034a003101c0c1050042c1c08a1002a01810040c070840142105c1100204104a03082e00200c406011151050b02c1c6520b80c2903c00d001d402040280c1e134010f003070301e00e40c0c4d0000750b18140c2054107210b07200e20f41031501414251680b00199000c2405d035401800c0180c60f0041885024002c002060710f81e1004103000b001810184400740c0001c1c20302d0407915002c151681c58201c0b0400842d06000d000b00d8850207611210204403880c0c094400355512864450488a184450a4800c4161142d0040040158100b00e03031b85842c1d400d06a0710304800c546003924811107010640802001c0c44500c1111408055446441c25001c0c0b00340350440d20070782d200a04982e12540c580c24190020402039408a20910284240d0b80b508015203d20490b41041903003420b400c0c46101c001550584c0c403800b41d10183c4d0aa102d0881c04072009403024000460080da900c1c40c10a10030b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 76478850 1250 76477600 76477633
    0x6090607030e060708160c020d030201050f0a0603020a0504050703020c030315130c171015082202060720040903170a06050a12021302030718060c031e140408 69
    0x4498030b52006400880801241c9600600c006400c5401c44011401c1c81c141c03860304541c00480401e00951207602c20040f030f01495815000a4041c03e17140c400815207480d03540f111001c9400c2ca10001350003103060341c0108241d150903070285a001e1031908001d0b00d064080c110050641d0300444413403281c8103c6645a6806041c4210140f120708a0b640082140c0c8440000250400741704140c245000d03121080040c0884103025021002080b681c003002426071490301024000d040d044441602d8228414464041a105809041090358010f44090700d480032548580d076108001140b29604035220340780007106626075114095840e402550ba030310410740305030901c4110f040040d05154080e410079005101559a40a2a4088600c5403841c0241041c11707102141241501c41e0f00840003910100800a5254011003001d402ca4400031541c4980c58039000243d40400c3e070b0004c040d00180c0000841961199030000d2140f0159560400070058090300b6410400381d4843d07000300ca04c0b41c00c45001c00c80c0c111362 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 76480100 1250 76478850 76478861
    0x5011e09020f04050f030f010518121602090709030c1211010c240f0f0e0f0105091009050a02030d0f09060c0203030f13120606050a0503011802060a030b030609060703 73
    0x3480c4425403030165500038030500c03070040740122441100c0301481207140350f404010040c0e40f0100c00b0700074401464a008401406200c2e102050040d020b100208603a0414140407203224400381c1913030910a18040c2c0038446004001008003003808034034040800840d030300154a900410ba0030401000c002000c0c40c0c803504141c895911035040c0045000403600241002000d8550082ea1901700c50345140c00c0e0000d00d0103840c83c1c9400400003850a10b5075801c544950704200074900b00d41080300c0e100a012414503080303038021115800a9000b04408203880e8800d13810140071140542c04407400c0300c140c0e0f00000c0c240501c042c003160100380d940303040340c20403500a0180001045503044c040c0b6286056000302e9240e01c20001d0010044100058110100850780c1e40000500a44100f0020441047c0b4180c0b000700501d004062268030a95400511841d05004881c0100e518890f180c0c0d031034441e60700744030041d0031051008043c903132a9170285a09803000c01c107c521415000700141000d05060101408441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 76481350 1250 76480100 76480109
    0xb07080405012a06051506030a0b010908120a0302090f0414010303080612030403020d0302030415050c21071103010f090309090e070803030c09010224090c0118030201030905030d05011e 81
    0x20310850241c803242010b04a00900590401d0780171030b00d030b0384000070602102d500b289079540c095408010b2103120f40d442e41c4641601e030000c1e04c0f41168681c944902564a0b000c5515401000d01d080101000ca10b11a402604080101820341c002d0740c03c4101c0050262851040e5941000d400d103001082410350080d04160440c0081d03036011410b6024008940e03c03403003603020103402101d1104185080502c01c00442e002400186160131b43c8100c544002007082c3d00402e101c0100740308540c16842e984594000d8026544003603034903e0710300f1800c5d586201050144500c92981951ba640554550044500035144140c5c4250b80384c1c1001c0c0d042446840171194411042e1010750301c488828481c0300c0d400400c0f00c0d000114001c44035101c0c42c654004031324255042c0503031020a0940702c1c11000490910b107030ba500500c000b10030307a041c1c0c0b00007100450b2031010b00c203803841142500342400c10265019500c00c582c0640194152403501e4a049813020550700203030300084001c03003405030492420300300c04981000381 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 76482600 1250 76481350 76481387
    0x15030a05160903020f0d0209010f1703040509010608040302011407110114060607030809011b110d1718070b0a02070e010603090201200c0d060515190314070b0708040501 74
    0x10000044014403040c00c1e800700900074050380c9a80c110039071b10040f030201400d03401000e020a56031503886482010b5040d10900c2242e604038841c490341c0c08400301c19202620000f8081d03068903880d01800700d540700ca000e00140c0655588404844500d40b00307070411841054240c491307407a14810240b100d0b084a8000a100341c20301211414002c0a0752068120b40700300b40c15103070044d52915100c06680c010b012280707110342c001500c01924004141c0000015103401c103048142e640d150a035403410b848800c036a00b010b00c116441c180c005009281d400c04503540c2d802040c2c040341c00c2c0700d84400c0c0703040e010b5016001c500c01691003000e04011f102858542c4501501c0d030341c6024444034089030300203440301d81010450303603e40801c048510b5030800c04005d200c0c540440100003804400709814101c00800003a07544903002c80e041e1140712118105210124980700b142e403040c0341e2041c42d46d00c07254001d100c2d0f05407010050040b50310001c0d6100325840640017290085010681c1c0701e10300f50024213203842c05c00b0700c10f01c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 76483850 1250 76482600 76482631
    0x110a05011115040c090905070e010e1005040f0204170c0306100614070f0501090b0a0b030a02030303160c1202100f09031b0c09140f0112080d110915030a05 68
    0x4107200401e501075061000141c00606440318030700307102d40c6400b6070843c10031589001d0302070b02030050001d042c00859a908000f601344e66210004070005217822184041d0602803142d04209a003080e50107203803031524059006003055220500454031055202501215500c082c90440d400c1c0f0303052000c10740004070710710540c1d902c6207420fa01505c02d2006140d156988040071880c80144800d01f10f02000c01641b0500800c0801254a400007905100b0b50b101c680700d51600c5910391050030700003600414190010300950071650303100000d00c5880052012281040f88201c0800300051506508401d060050b4014001c1c190014011100b140c5607000b1440005042000d03881c0400c1e0000c40c01070916259149410302d500d07150521002001099000d02401490a0712a29011008041c05800350310800500101039989080035001c8039076a500c00b800b0040100700d000d203000213503401041c1c0b80c0700d4400380b281484032260015184441c1d0f00e10400400d480041000b064201507c5525800041d5681541c2c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 76485100 1250 76483850 76483877
    0x11030a030f1101020d02030702010f06061b02090919080714060402060403080d0e240f070806120708010f0f0c0906021e0106030c0f03150e060402010305060d0f110a0501 74
    0x690048031124200703000d018401580380b07100030740464545503a001800d41d501d041000c0028000c0c2420b50001814070700d801c00110b0f0207840b41c0c207807000ba02091206014501c1d125000c100c11038038003408d140301a2054a9104846514180412155600a00e1050344541a42c14103600042803240c1240c5990450380400006a0f105400e0701c050380c2d000001039071200036000002005010800000c0001d00c107000b1840c000080e0045817030365801d601c07501c80e00b5a841d1f50030800300b10101928001d001c58041f00c000b580d0381c180500361810400c2c0c218110ba240f540d54520307040c2103894801c2c1c088081e070f44402500404850754090f000c0090010702d041c1541902c0e08100030744441400740349840092803a03892048a613802d4210360003468100686424143c0c5e81e400b4940d90b52903500c421540b0b0b40500e101030003041c0305482558900150b0b40050a4199170341e0380110001c040049c50158016000007803840412007268041014a205155225261a04000700400c1e00710550115040000c2c5054808 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 76486350 1250 76485100 76485107
    0x103170f0f03060102030c01060b03100803090a150c080a09030c08060403080f090c0310020406080601020601030c05040b131e0506060a020a0b0c042304060506120f0604110f0711030a03 81
    0x1000685201c007a592252240310040b8258400d281d1000c540d582094004504020f240004502078018040700c040302a41d80d100240d01da0241001055000070030000030440d0031510700c0c49800e4646946080703005455203990300d030100c0e00b10700a00d0300060702d402028420481a403106c3c0c006041e0301d800401480c5055036004001c80d80081200038a1114000800c8100e50200101c0b16200340080c20303034484500e6030322100300a400034440e160000380d81c0380c04142e81d54008a1540d040e070f42c01190712440c440c18070003440b001d0140c10340d800b508603248081f50124644244901170b1009000d541c1ca555a089030b40d403040a40e00061716040c800e2800308000c0c50031b42c1d000118034041b15800701e20680c0c00d0b599848103082e00e025580c08030000c60301080800c846207142c001800c80105046404102d41a220001c1c001c160051201a0351405460000704101306522100035501083c020008036480814070400e00c2240c106120200262502241040c00c11000c2c40c4443d503442029401001d40c5095501c004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 76487600 1250 76486350 76486357
    0x61703040801110f1c0609091a060f0d17090a12021509010507062c060702070e010b0a051b1e060f04080f0a0315030b04140601080304051210050f0103170f 68
    0x5c0c0340c40599002e2104003034004600404000408005d60b0040d404c0030030040c02c11000c00480d290900001880c280740000d40f030000a0400381c100580c0c5840c42e5950071042040e40c210004e48101405400d1240e600c02c139600c00505182841441700411a00c14415041110242c1c45403072002882822000d9078080141c0f818140c0045002c66001ea006036540102c0745070072105001400c440e8410225000002681b5020720456401c0740e039540d65031110004040420b0003100d81d82c0c401081400e43c0c1520580107406212884072081031440d081104d0ba514000c44801e0081403529401400341d60610b0601103245d04ca03030200070300c00462600da41d400086104d246500e01184001003241d42d2030074407030340c0100c0030511105020100035441c0d0078460950802102c04850b40d02c1c84015180c02e424001c143c650484801c04001c44c1060308020820003c4040c42210a003940b00b010448602c0417a1802100d002d9080f100001c0565415030808100600302a081c0115800c1e00300b210a40381c0700c0c3c03103045 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 76488850 1250 76487600 76487617
    0x21e030a05070206070501060603051b0f0d02090f0a06090618080d0302070f1403070c050f0108040605070203070611030108010c020f0706030b0d02040e01050601020c120a0b0406061703040801110f 86
    0x142c0d910742901c0003c0c080d015100c03000d4419868124003040c96a01648140c1c002c1c40d1a1000348a820010b140003102d510955140050103101403180e0310700c003102d0b41c0107400303d0800103202e00005d40020000c0341107848647d10600004100401c03c0003002d070448801c600d0941d2400c1081d60550030204a280e4501302c503481c0c4400c0550004c3c4640a10020400d4100f115611a0384c0b00140148010b6040d500d400c00c000c181d0f1454180c00000981d80391003090541d40d0601a103500b40340d641d030741d2128002000e00500040548c00f00308682800220f0702c0c40b8850540c81807003250f907104e5040001c51070031a40101c03e440150b5100f103a50b180a91070000d0700d90210b6801f0328020500201e0340011802141149078000e400604082c9517802200040d00000c0c031400080c3e08490280f14180304002e80006514940c0c42070381c021803080703c040b0b004243d40c103500c240181c10100c1c1e40343e82d5054028a004421000103107681000c00d0920072003100b0f001d80c14410040e0010542803159540d40010184100440e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 76490100 1250 76488850 76488857
    0x30606020c1c030905030604080702030706050304031d03070b0708121b030a0e030912010504030e0a050a06030f0e03070506010303180b12091606090501030b0a060c0b0a090f1101021e030a 82
    0x10a0b041510501200024080203400d841040c10f1525101c122a005150700324824041e510b404507240c3c1c450800d803840340b5059520061811550060700b4007040b00920000c0d05070003003260100306150200c0c01441083c0c400c0c5269a501c1080d400c1159000d807001c2d05c50003c00e840790303002e0151107000c4425030342c026104510002c1c0e449600c03901d05d481c44c810070100b00c3d088244101d284d120701d241076100350f2003a400798440d58140d000160802015080d640105580704070090014001a8825807013000b81d920b09c0c1c9000200d10340b89103411032450f009507004695030781c0038400600030983d008220081d83d40f01c4944410701a401e1030508200d074045c00051034812132071040021174450003013001d5480780788401c80b46a076480d00c03000c006000308000e00500340400e060814030200d90030228103600482d4400e980c1d12071808610380d1100d01c2c2400243c02c0f40340320780e2100900300c08034440e40e840c00c040503ca00181005000080c001a00300644181c03d2402010110f4500d00e4045001c0300710f0f20341203281e20303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 76491350 1250 76490100 76490149
    0x615030606120a0219090c090f0b1303080403060501061d0108060f031f06080d051306030510091e0c0518061b030d020c0106050604060210050411040e010507030606020c 74
    0xa61a034030f0008010741c0a503000c030305145502403034001d0031111002d940581380d0500c51501e44000650b4103040314401e04204070703030280d001c0198580340400f40c140c4003030003c159600507580c1e403121840c90b085500705071100b80d5104010081c45803c5925055030070a144c10741e000119480d4000703004071100403c00e5000361843c0309a001c56603010301c0114008441e401412001c1c91010443c240100420300035845c403807044c00744a60781c6500903801e545c0100002c4040c0510141400812405002c0240c2280ca03e0961140040740d901c1c0b00380901244103110109080e070043c8150000801d6852030a2840103012003040010848111140411000fa0050302c0079035450f00c001c80c101075a14802035540c1110300003c2180240c80c040b0307030000d00da0418604024000aa00d881c108001c610a40c4078040150703000344804003510150f03420146e0b02c94012070070015400c00040104003601c00c60741d170200c150395441e02041509900740c440d0001520f8648028110108a880801c0119a45585c4030385501d9403003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 76492600 1250 76491350 76491379
    0x50708010f140d050609010605100c081c02130902030703060609080a0b04080c03040306091101080106080a050a0f140406060e07120b060c0d05130e100b07030e0316080615030606 78
    0x4410411354028100c0b0400c0c605820494000d01450040c01c2c4074440c50740000320058480d140700d03101640c20044031890500c3c07003c40031101d21250200c40506603028081c052201c2c20f284610380040c0f2040c5c0000d40c0c0d82c600000d00074100e0b84960442014060042400d010f01d050009050410795030000b0071900030f88a07801c0c000b015004a6451810611001502000b08210380c2c1001a803030344201084107003170f1080030040d04d00210901030340001071100b00000f5003030030b25038010039000104c000b00001c3c603401201081d030a48134144a4115400d01440a04c07081151034420400209000083d5101a040024005240c0314034064103025080e211200c08903a50f40f0300046400300c1546004030b4021031428040900f2680046810241400c048180001d0980c240c0c4581440b90407000d20181c545803c058501e04280c04c840019400c200300150954503644081202c1c2d1345030403a0035540c0c0d95091070210a94503101d8014202110507000220400307503901c00141c01600046d01700d82015044040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 76493850 1250 76492600 76492609
    0x8090402160204060906060207050d02011e1205070905100306030209160e18060112020301030506191506121d0303131e030309151404080d06050405040804050301050708010f14 77
    0x480700030b54014a040400180d54800e41d01240890726aa025038044641c0d81e02044640c8120010280c04105a882d1001d030b4401d44038001441ca503258104800d121b10202611400c4410446e94000810b03c02c82c0c040c4494504071090420800c0c0307500d0140720075411540420240c110142c00301c0b0980c000c0c1c2d070040c04001e008401c0c0c1c0c90441c0c4090140c03102c4220503050009100400c1c0d0719a408900d0b0181181140c40850085030305803600b00004003c503440d00c1100104c0350011400c5240701a503201c100e40540c80c81c000f403507001400b1a60346c2d0801c02221034605401c503034a040d00001d48400f46462181c1c244808402c0d20342c8000c80701452203401105d810140d000c06051f10441c1c40c42c0d10360b515034000301034056110700c200f140180f0040e40402e850304050002c940c0c050441d941480007101c00180022224130081c104804c8480010906035500d501090a440e0251421104518041403e004504091107441d600c000b440c80c01a401d9403510790790201da01031034011554a6003120030303c02041d1301c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 76495100 1250 76493850 76493887
    0x13140309040e01050a18080f0715051003051002070b010b1e03010603050f0a06030506040b06010e0406030b01081002091507050a0b07031e1a130902060408060f0108060408090402 78
    0x281c014042c0c5245100e03640d00030b00040b515108042e00d8104286030390910041031598a90340310b0155031401188050224994208001c222180320303507014207083d02c50003801400d00a00c0d61204c0311a0b4039066107812410b2500c0342400d568614410b01c2140041401d1281a50469401d014082c0c0d940710fa069403a00c910384031180c40e4500700000400001e849e9415401184581e003000c4413250981c641ca00070a050315090300c0060200d0307208002060100d140542050381140d0141081d07054007201d0004603040e201554801c0e01c20040d00001001441c0c000c1c0090b100c0c00f165084218039200c0c01100048511121741070004d006400030030300b035042040070880144da05400540750b1032245081d0034000c0103004c1140c00c0002c04070002c0110140c0c00142e0080004001c04040d031001a801d1003002e100c1c50b140c00f20008038090742c030b0b0340e500c001584070500140003070720317054003d401d0515100c1010450340d40d069000c580d9540c44141081f01088042e0251a4500380881f4056a980440c1d00002600c41 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 76496350 1250 76495100 76495117
    0xd08070803010b0a180f0e06010e100905040b0303030603121303081603120509032212030c05060709080c06070602310503010b0a0e04020102030c0a0f0308010e131403 73
    0x40c000400401c1100054015003441c00160740d80000f02030303030050607814a4100d03210710703010100ca0000c2884404815103510b503000f9018580217071300c2b40c02d03800010500207541c420038000ca000140c00348040c5c2403a000b40c40085e0020340042d80346040090210343d0394840384043c200c0320000806d0900d0124031441d004001150044c00c1d40352216041a54880001c030700c1c1030200d020802c0088003441d052214002c00e032061203890065401e0400d501d609182c001020f50301c0601410030f229007c11040e01d0410f43d10b110314000e541c2c031415a5003910788a460900003030246014881c480700200221400020b030039100742016101c20391141d20919202020703002e6440c8081221760015a4402c0c00760101b02c652068980031141c2455840d5108145403c81309e11610190300800d11120500690804d0310819030002d2042c4100c0c0d00d000c131031850131801d0648441003200c0c4004081d02001c24107522407800b5025103c5143d4078506400e215000004070088120300414100056004120020040c020303680d008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 76497600 1250 76496350 76496363
    0x815040603030f02014a030c2d06010504020a09050d0506040309120503041509081905011506080c0703050418050a0b1818010618050a0f0504050a170f0d1b0302180d0807 74
    0x610205403000d0b06c500380d1400342c10b00c40f50780040b07507000442020303e0303002c3e1000e8909c098406a42860184406988466080303c14000c4180c4005410380310780900c20750081c01480074011a0610340340c028080741450340090541040109403001040f0040115003c44d18000343c00c1d1418030269006483c880300c01da00c2000306010b0b40514141e42e14400c855024403911840081001013078401c4207000c84100c5014003400031b0001400150500702c034100600166000f8108541040c1da01c10380200a801710780100380c0ca03183c0b01c0062100e4540c1c24080e0b241c00c2501110018011448044543d90240d8020301082d00c0590080d1000e24030602984210040d1030050440c40030003a04021642c00360600b40d6085175903a1405c240302c85101c9880c03094600407070b03101c4098a0f8940355507e68407604070f1a03940c0703564452010030000045003104c200500209600040c0490071500d400b056400302c0d08150500c10900d0300400002d101104d1000078140700c01c80864402604010130309000c0c10340d008a041c001d001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 76498850 1250 76497600 76497607
    0x6100909021c020d0f14090a02010507021912051501030b07080a09020a08030c19020918100603030309120f051b01020d0c03140705040807060815040603030f02014a03 73
    0x24a003250b0481c1c942c030142050300b400b50030251801400c150701c040740d001f00e0640003601e000780150721401c0240711030f80c0014503920403001c10006030b2648403031503404100d030b0814404007201082014003080e0380c00c1c50400da041c030032507145403100600241e0040400c002c010b078000010354180c0081c4d00026205402800114100f070300c843d246503581e800f0a01c42903140c860003031400044404150a4140158040c0045040b51100c110408590810300c202131009e01404103040010324442c840c5000950003940d002c1488640c1c0e050107a00c0441c0101150204072226003011146504402201e03242807000344412814800741154a0081c011180d55418080c2007600c0710b020305a00d80c0040519a1031601400481c1d1640b01c0141c41920841c1315050240e00405030401029005500d00e69015095031700e44014910340300f00240c11901d031500200d000c0381c2000146146240d0910a0034422006032011100c540c008443c0c4c40131641041c0405841e070b411002103000c161400040c02c85e03100b06541d089945 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 76500100 1250 76498850 76498867
    0x506040309050a1406190c0f2907020a11041104230117060402090f060d1e0216080706060b0f0304110d02130504020f03070b04050906100909021c02 65
    0x103841c0507201d10b612802d1003100200d00c96000e0038074120010001000280b8224000b408903c400825000300018003280c00c641402050541a17010074a034030444030100103914100140c0c0e1401616241e10340311408035020031130b0540c1c0001d40f46c08065001610508a01c7da50000140540001000000740c0c644c0401c1c0029894040e448036608000a000c0e90000258958011201c0c030001d400102064041400410618181540245600c0d4409008407069100072808148164081e0302c40080480c0d890b6040380400c0d00300400c014611b04202425860040c680c1c42440d0140f15451010b000c64200003020010014a0b5002030024011025455102c00c07110701c540300c25400c21601602d030104840d040000c0c1d440c10401a2141d01ea004094100080411885200402c070050049030420515948807031243d404000e1000101845d843d01c90740d80e82007409100d000320015080e94051031445084102a03900f10300380031306a0710f04400c0103840c0c036681049034106891181c072019006100059001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 76501350 1250 76500100 76500107
    0x5030c10050a0c02030f0304030c0f020a060f0905010206070210050a02040e01080a0606151e030e120c010b030d2307061806051e07030c051b160605040608071b05060403 74
    0x521442a40000f0082c0c003000c0d1038140d0f1030348214040c0142070201000018002400744601d44003036030040040705446456540404c03104010394204601242c21040c00e00c039055030115403070020b00801e00c0603081a007031000b0702039656400c0d0301c0c28682c195203e0002400500840c0c0c1034400520501d9001d143c5035070740302080d40d207450380705405076074140c104180421183c2c02d00300b160031628a5503540c480d128403c100500010043d41810b10100b5856032100d1043c020200070b040030b02c030b0100071a0b41e0b640843d10082c9003101d480ca000745009400c24016240069004a400c40d406d4019003220801c9500110b0030904c607204440c0d0081c00c1c6c070300d01824265410740d081c1d0b030301891902c200000c101544482080d0303440f85020303009001d41d5441d01c20010309110b12030f4000080b10815030520134200034014100c1511101c11140718034041c0d0000d0394218024001a1040c8020705241c184180303000d050035401404000010003031000d0044040d0810210501070710074003001e5411a0030340e4940d0910b0b29006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 76502600 1250 76501350 76501361
    0x11b02010c02030d050915130b0c010b03150901060f140910180207060b0306040213111b030c2b030b1c12020c01030b03070905041103030c0a021c1e05030c10 69
    0x247c003c43c80e0b402400c0240c4d446004030303201000000398900c041440c1000c4020750707510000c601c0105540f60000302d0510741707013080051001c1a80200400c02407400500e81403c50b0b01581c031041d807007109484100040021410b04440f100001d42e01d00f100740c0e41d41c480b0440440c1c07459000c40d0340108034408840d0001c880780e01519646100d24410b100c281003072002c01d596030741e0a0324013035440302000c180050300d542075502c054a00d1916501c50fa05100040d00c15070010200c1000e600710740d820004440e49000000d1046503500701c000e220b0301d11203481150342c03103000c005075580c030000f419130341c3e41001025a5032a0042440f10001c101120f07100d496481c2c01200d0f032804401080240c89480407014040d1300a000e10030280ca0013a00405006141c450000041d00010b401601c190f10083da05007030700d450510042c19444071800041c802c80c159803043c4880301100c401e92624124089042d000094210418124140070f070040084540c44107003402411445149036203402842042c80c6000944e6064101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 76503850 1250 76502600 76502617
    0xb120406050f0106050d0903030e1605040c08040c03060209010909020a031a09060121060f0e090c04090f0f02031612020111071406180405070306051e011b02010c02030d05 75
    0x248865107810907400b0440c6003e001ea07101091040c0f141c0c50f24180710342e00c808045030088c5800719070402d90045181c1003110800c9102c0c088000c48070244103d007040c0c001c0c15115002441e04500c145010744075400344a203103020040c0b04580000310001641c1c891801080600700224045540b1f05003900702800801c2c180302c80081040a03201441c03040d14118100c2449101d0684030b400302c0c1010300c10059044001d44281481e0160b0710744020802d2003003041c420000d0810089008014184101e83c140392a800c0c8029a22036418500c4d200001103400d5040b10106901c0b0500048a043e03501c002410701502c4034002107294060032000072171315100c1c41c403880410300030b0725254281c4140c0c03010396455180078082c1b10810800a500c288540c00d148009240c060810345643c0c0c640004100004c088c1c0300d0542e520b400080d12580140081e01d801c00740f1340d030880402c9032103090054007040041e10302040c4070180003c0780c0c40099074106590091240070310660340241501c0f03d1041c5840b010700700d500090030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 76505100 1250 76503850 76503863
    0x10806100b1c0f0506040c030501030510020706090812090708030703050403020d060b0d05010531021018060206190e07060f050706020313050607020601030b060d15050f15030115050f0a0b1204 84
    0x745030207590300903c032701d0b41a250410003401410110041c420043d601458040302c0365687ca001c0700c0041303910380018207800c46544c1448040e6003004019240740c512240c10100c0350741c00030409040000d400a003220105c03903060700d100c2e5002446041400c014070412814035009005046507504026042d44464490b030260003000c00304510300c00328881c0c0070105403d204074a561030300d02079000d4600141c4294003c1d4035454154010041c2110242c00741d585035001c2c1c0d01607401003042c0301000d2224403ca800c1c600d002002084551600c420255540710244a24028041d50242c0440001c0c4038204841d00e050b04502c0941d0349041245500580d0092540180e0311405010040b8481610210304a4102c0c1d8000703001900c65251041040412a1000302c203e40c540484044034040100074007401d0b01c102c19a000c80549454054100714002540f014054460f074134000071142500003680d00c800036a0f00603108200310a039282c011944041d60742d006044040008501c00810b07541e2000c1d41440b452040e82c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 76506350 1250 76505100 76505111
    0x20160c08031902190201081503010209030f0d080c0a050d1d010204030c08060705040e01060e03031306030c0e0108010f230406080d1d0f091f0f050306010806100b1c0f050604 76
    0x428080b13510410b9100134001202107010684561058003407102d06c820050006103441e1900740082d152078012000e0346c1e510f400034101d80f503109030803140d010752004030300400074a0205d807058010881d100380b04416512540c2c1c3e840c158010840021880a0182a2402196940e0304d078103111b040380840303208824107441100000390b0050b200d1002d071000c840032844103103056400d1940a80d0485440762072141c1602c403c1c00b84296030461608900020062518001000d4045900c0104049200034086042c00000c500400160031469030003401c4815910070240354224a41e00d02c10799104802c4015407040c1480d001041c14080410b042c0d901130200d855064200000b80c0c12814908940d01165920201940e020a01400c010003001e6014a0122010791b51066142d1014070450702031f00300d5014281142d0040c0110700b0104291405001294020900c41c81c00c1d1403000c21601e0035025441da0b200c000b2504c1c6c01c1c044652045200c2c0008244818071801d41140ca42a000f000100d46840c402d84c14003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 76507600 1250 76506350 76506373
    0x70f240b0d020307030f081309020d0c02060402090a0b0a03050a2109080d03050c070b0103060e1002090d0311150f06010f050702100e0d06060b0d20160c08031902 71
    0x7a800c41d50196000c1c0190400720300d035482c1c00b200f40044500c2a200c07440c08201402c200140010b80c1e00140c0b044010040c3c850041c40000d008449072801e4120039544010144000750361810088ae034810400000807521407120800725447c1c001660005001d84115814407040010403500e411010302d41210038000207800c85012031350895203105411458002c0100072010a2090300b2040d441501c00c0381c2c091a000b0070795501d40c4903070400d9206450b81c80d0741c1e807180c8401140900c07280701c0600301c1070400d500348106580006c04d02c886410b4020705102c0c2d40615600014801d110020038a8440c0c41c01d20014a4416440d204010301141c00c1400548042c0c8000300c2c0078001c41c161034065402610385240342800d10026680d08100c4244664030030072040e0600001225800303207801030681000751340c0d225000d05d03900c0c000b41c980c8146540c51801d00310805401c1d071005801a0781d074a1028807144c0480e803078141400140f00090360072141003804001002c02d00d9264044001e0380d144025400c540c42c1031b102 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 76508850 1250 76507600 76507609
    0x1020a180e0708060406081f110403170306040902100806090c030103081b1908070c0e010b0f0702012f0d020303100b0c070e0f09060a020306100302070f240b 69
    0xd000d4140202907510100d41d603203100380b20303995011502400000725039854040b9585421081c1c415201c004e0440e0fa0001505c0443d8041c01c280129a12a00b40c1400d05540c1c038541c19001c0010b491202c1d02020000940fa07035070302d421405000d030700500340c510308a500100080021404807521406200c070440860b501c200c0310000c4a04032600880260300303010f468564100c0803841219071205a11440070490a1714800580724482940724043e101c3d85da80462a00342001a216406250707801448001002001c0c401030071290400740e95000c4076643d220030b10045e280d44005000c68100c80d91014030395182500c0414003180c6000b411021525208010a403c0788e892100315101c00311128086410064268400080c001ca4504842901c0c1c4268455917507100d8114219808080d040c0444280003060005100b1a900304035100415840e52400e000031401808680e20098101940010b000061240703500034043c40381e078484d81851040c0f103d030b94a201c88949440701e4045503445c045584865250 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 76510100 1250 76508850 76508897
    0x190e150d02100f120204090b0108060609030601030f1a04060e0c0f210f0f0601060f02010e07050d0f0210020c0f03010b1008040503130603090c050f130507090902030901020a 76
    0x140200b0312008000c808004542a0340c408184205200c2c90342a0102c40a40307900182002c0c2c80ca04400241e5000c07a5070004080e000080c11160180310100400c4280d038030007140080c15613400c12a40c0d20b00c20325600d001e07641146115041180b004122007800204100350300300005001010084803000400001080f0030030000c0c9030705c5030380326084012900340d03000150340540d076018821098582401101c40c60a003400d06411010010390480c00040c000c96400c2002c429000c28542b00800c10500d040019503965000380c010244a024a80d00520420103060280c0d499994085d20503016181002000395449105002041c4101c01680e54180c0318181445094040c41006000508222100006588610000e40140c3e000d00041009164100c04a02014000c2001c0e540c0051801041c1c200f4615003011a0006441105444800803040d65030303540030041c00760758100015a603142c2050a0300c659504d070f40804003050010041040d03c1c841075002d030659518507100c41100c040c060a006440300b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 76511350 1250 76510100 76510103
    0x9090b0d02090a0b0402040906051005190e1302130303090506090307090e01020405030d0207030b0703050f041515090209040c020c0d08030406110c010c030c0201020c030414190e150d 80
    0x40000000030058681203000c0307600514810000a109240100403d00742d80c05508400105900d506c0300308928102550560320b049510300d0b03c182007207020445540b0001b4242000e004105010316080030035602c0b41010400095140c40031569400e030300c1c3c0b40c0b01c0004558032043c3c0c04101e034a035000406042050031111030110090241c4503036418a0940c1000703054140211410f59030034000819240c40800449400440c4c507002044981d2551801c11a521001099802018203000500800c80702c41442150810b60104420300c0d0031041c0c00c800e034024001601d81c101114900c00c5c0000310468141d00900c0c0284d01900c0a00020ba2440d2041e40c2d544904a02c1603040307880803c01d880450080409160080d20422012440d4800307003e42d070b0b40e2500449080340c19030359100303801d0547c3c81e01482115400c3c2d8560000b5401c010500d8541c0d1f41ba80924841d5020080b206068100265540040c1d00412408060304100d000d4903010307d646807180031140c0c03044081c40150b041119203407280c030407990305 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 76512600 1250 76511350 76511359
    0x105060a060207050105031017060108060a0b01080105010e030a0b010902041406040509071b06020301060e030d030507020303060d11040c03020901080c0304080403171b030d201e0c0d02070609090b 86
    0x3511300320044030f0700d170b00040450030318400144021400c1d180180a040f113119080d4000c020340e505012a140c107010000d4400d680b03003441c1c071024500a9802418060440c0d40c2402d22140498090003c24100040302a0041407441c2c01000400c050a55601034010f88004265010400c50124240001440341e8058607510021030030025036894880d5004628650401107481c003ca481e0b96102c0382607030402e0700001e0108003498101c0056040822078088600c10798074041c8094106200040e45074400034003600e0080351904c1c000018406400740503510040054801c00130700f40b160a000b0001c2d000031a001380041c2101c0e0100c4c44600c4400300766801150860703641403409203140e844050003222691403050800b420b0011900d1500f00120b03c4026981c6d100181d556244601030710f908032414206102d11019402c09400400d062500680f18a030304650000018203a444060794624043d0001c100c040303200340c0a4614045034040360000866070300c1e45403442456215920078081d03407581180325402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 76513850 1250 76512600 76512613
    0x10207050c040b060f07030c06050a05100303080c0909010f0512061006232208070e06090601031b0906080708070f0f12090b04020f100914031504050c030105060a0602 73
    0x99240c035910204044400510b44c0b40b400700d400b0b501183d2500101d4082e004241c65055a80a1050702d014032a48071901d04070400081c60310071401481424140000b80800ca0719000103041ca038424012a85014002480008550784d2080f5507400300c40760380162030040c80c12002c0354072440000581c1074016010701c05038000c6281405422a42444a01c81540010b144107120900c0d901511004203440d00c1140040b08500c040746140070200c1206a103c0c031026801039104010614010807047d8200e407049030002002d8454100403405010400c00c40c503003c8004000c400c18450b00409100c04a80c03003070703c2c2d0701e00d40c2d40e80b41d000f0f8822842c12240c1d03402041c401102d4142241c0b180301d602d448081b05040900082c40f640701d40004403141c22808840d00c541e09000d0100b07600d40300c5448440701d0340480e609560006014801054400c15100f00100000c0360300c120702c0d49036800c0c0302c040d840d048c003c42550036516290504aa0b11425170051600a510340801704142d030030094a26800e607511600280b91 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 76515100 1250 76513850 76513873
    0x51203100b0c070e010b0c12041a09060d060b0d0b030a030801050105130b0a02150f010605120408090306042d0206031b04080703050c1003180303050a021209010c0f0201020705 77
    0x41c1e660008001c40054010360030041402c4802e544114041c0504050050310b401010f020325203400d00c070200341230420b1414413080000d040728444000310b8200103091a901c034410000410f44a004100001c250700b0304000000c210301803804c001c1e007151814000184020b2034030505058482a10100203800102e0103401440300754042c030700030005001d900304450180c0b681c0d1100403a494014060752401030700308114510b039a403807000c00310f60040b0400c0c3d940c8486514003c1c014200d0b215110060a00503001400102805210002c3d1740c802d42018060f00c0b003070b191601c1d1a8038000d60380030401c8030b820643d820084083d0300c15041d151070f107030703020388418950b0711a00d4100f003140c41c41c12100e100b608410000450300344418004e03000154850030042591100039010030540e015440400001c0500c0c0007000c0c40c1041e41031015070340e42c076058100003480740c03204035a40d0041d102d40c0c2c1c40c10080110f10818000c0110301503000d885486019030307490388104201a0200c1c00c4c4e20030000003a0259020006405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 76516350 1250 76515100 76515119
    0xf010911180402010f031802040e0607030c05040b03040303150803030403050304213e0303090607050708040506030c04030f05060108101112060d0c0e22020d1b05040204030f05120310 80
    0x30740e0942c1061f040071348120a41c0000d0698032095807642280d0040d1091060503501030103481103075820b50500c41d05190503c2d8508102e404002c10143c10182c0f901e1410130010001c00d00b82014254642c26260342e80f03003504001e4000c1d0301c140c2d0201e0704e4902400c80c10302022843e944d1080c145080c1d03035640c4a420301040c070240e500d003c10491169240d040300404e07440e62248108141158041d00007031516032506038407540c14520000c0c083c0051107010803400d400200c9032701c200c40c16550115026512034844010000d6a07001d5504024804600d203400c20040c04000500d5904880005040707540d045007440500c000d0b0b60403003414600c21407040c000140b062182c00c140b183d00090152038080300e031106860390403c9000139400140d0b40c46200051001061303004103407000100348051914242ca0b032542c00308151150410019115903d441040010081442c20b80d4000303150050040d9100e07a200d0505003507240c0c4490003203c1500c01d0092407150b01c120042a40c0c4144100300300c854005282070042c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 76517600 1250 76516350 76516361
    0x1020a0611130303020c090105030a020603010306051b0a0e031b0a050409021f0807080105030a0b0a0509010912020c03010b04050c1903090602040e04020f012f0f010911180402010f03 80
    0x6004110284075a41c0c1c1c4041c06442c480045010341d001384a07a024007018480019010b800060094101815200150702c0c1c060860741129441100060789940d0310307070084011a01042503102d044400900441c000342e000340c104002c1d0724100c086e545194800d0521510360003002c0324954000c60f030100100850b14055009040c943d0014000d0001c1c1d044440303484030328000c194070100c081000d680c20b000640d071340282540d01600043d001000d032981d07a80c8810100d401c0c01060b2440030350315100021403c0c8820340010020700e62011141040301519000692140300c5002103500a61a000c0b060072940b905006180c0601c1d60171202e5407030b041c60100e00007900c43c105c108940034151206c071040c001600b1440200000c0c00110701c01c14141c1098410000d401101d02c4503141048400c2ea101c80c0e010f801e00d1040c1c1c090780e141440a90036016107110590801c400105040c0b0103502c0c240c501f0091109844141c52450000c98180c2c4200b0a401054081c01c04203a601900181c541401c00014030300a9000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 76518850 1250 76517600 76517621
    0x31d010e0607031101060e1902070510020703030b090408210c09090601020a17030105010e030f060a0c26090706050a050406030504020a03050307030903050610032004140c09011202030601020a06 85
    0x15081011a41113590a4901a030700c865001000581000042d03601c44c3c414400c241080c14041d894038042e0340710940d85d40d07400900348504950000350f10003090300a40c440200c02c100504426903c0c40d20b030920000c40c3e040142c0219100401c510008581c41c00280d140d4420a03107502010700345081c0405106844000034080c50551041c1511000840d8059540848a9810060081d604d40c100303000144008001c070b0816000740d10811480b62000700200341140d110024100024080e06900001c551400149004ca071180c0508040c030307402e036045850824401c418080071078800e1a80e170601102d092203000c9403c000541c040c0000d124452086c1c01203074000c0c0c0001d0001c000c06840741c9505095501c400c2007100403404407082002000004e0016580c881400ca200ca01c6440c07441d01c581c0341c0f181102001c1071207910702c44122061555168011704a528a10860b8580c600d80b0744150030b4294409100c407400701c0e00c081c0c20900001c585000301c80c400c01043c2d000d0b0a4505440e5690300150800041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 76520100 1250 76518850 76518857
    0x80601090f0e18100b0f0a060509040b030c1c020307061b080904090c081506011103070807050111070b01081213090e0106150302090405010806090a0f050c0d030804031d010e060703 79
    0x2032107603e1204010030541c8141440c40040c0700c440e16810440c65180002c98103001d680c042074108080d43e04042901c0c01841c05807008590b60001d0301c0064201034261300040d5100c101c0b074000d032081488021135840c0d628400d40031500016100c50060311218103d41200441403205a4401c0000e01440c000e82640c90000e0008241c01041c0c0d624031803a2481504018400d50158800048061a0081060700140203007003010899140b02d41043d2244202040a0035071640041d00d42c08002c2c003503201c880410112010039840300c1c8689040c0c624005d0038401c1c02640d12400c3d101c04122034403801200c42021450808410681c40e2400d5900904402d42000407035540c0c401000aa01e03021500e41103107200903640041c1e9407141401084200e49060b0010346099114508004070500001016045250080301c1790321442014a00709240000400c0c020381c02020070400c2c074003055046004940207038400d844401010110000d40741d440d482d10a40b00380000d40507030405a070350800c0401004420b01924 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 76521350 1250 76520100 76520131
    0x60803030c0a090509160e01030b030d0315050a090902090a1806090219090c030c0306030c03030e062205040506030c01020a03050f0c01141b03011404050c07150507080601090f0e 78
    0x2000a0034405c421a4801c804180842d60400025885406a136011009003000c00c000c1c0b2426011a43d40d20440c0900010b01d40d41d2042480110100d6003000c0003040000c2501c2581901c0d0701010014000c040e008a0250701c5400100e04a4100d0740600d81c4800c140c00050703081c68015881d82c6001d0280072905982140000d4000e6440381804680c0308041c090924004c510400d0100e0000c0c210389040310b802040516181c0140005007040b01410100c0f41c15141c160104c007032090000d00342d0300c1082c003221542d000020b8a080c3c002c0c444110f0b4804c68008640c20070040c1d49075400d050312440d01e90021030040e0899002180001c0c003810107041040460160f4a013000c0200082074211800315074540540c13900a0104041410340c2d00b808188000e9544146055500d0000d40484401200501c0383c820381e02d03680010742040f14201690390a6030442c9810642420100007007005010984045000611000000c2c41a500442001048400c0c0100041d529454002051014030001c0d180b00b180a0300203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 76522600 1250 76521350 76521359
    0x100c0b0f13050d110615150f040807080705010f0c02060306011202131202130207170306031002040902120609010803090103090602040302030607050406110706050405120a1e15060803030c0a09 84
    0xc00108101414a40b111011135210720346051400c10010540d40c0140c00306d0084074803a840398490030341201100c80c3c13025102c0e40c00040107000c0d4011500491024803401800240036040041c035002203030400c1c0c844100b42c0b451071030121442d0b55400c070040d400500c20070114209501c610002c01800b00028801820550440c0102e200d80c0b0b91a88071306008002000f010055103030110207840c1c4401e000004614010701ea170382d03803402d41c0c05d40252845062004400901d494900740401119618100390031075845840b0041c100003134222102100344248043d001a03c01c1c102400c01c50b040e500c4146c021810000460f00440180004000488480380c0a01001006803070400c1006d01406660300c56a44071801c1c08001060321116103405449540320f82c404010968120341106c06448090381d4038070103078001c40f8206181819180004000010b480d0300c1000407140d40d2841c50000c0d228070184000a002c10f03041000760b41d1140140111f54000f00007044070588450700810f035a4405080500000707039607 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 76523850 1250 76522600 76522603
    0x60a0504020f040306230f0702030408060708072006060f0a0306090303050106020f030702150a110d052d041e0801050a0b0a05041503080a050904020301080c100c0b0f1305 75
    0x6000c501c2c2401007410310402580d400b0f080c52504d6100628036601846100c80041c0c40400b411460038441c4003400302d50700f94070a00844010f17000c20b030210350709030030580c20080c41d10600312440300008008094110001c01d8003460b0300d00450105008240d151038450411039411390302045a58040da001c2c100000041d0b6030b004070703041c841c06902d00080540c50300703034040e0810754010800c0040383c000308a03a0300140e4071208080b040d00c40001e001d40e02c0d81010f03881a103c06101030940103c1e481111904185680d11070b0041039841c4103200d9640461084045040c0d80c0d2034040202080e0ba0383c28007003404803014440082c008042c5160b1000407066840c8041401c403101900e80c10212902c84030055114284202130000619003901c04002228143c0c00b000319000080c00024074203280090441c0440340305006541c0207220082c0115500d503910880a40d645008152407405640041d004144650080104642e99904417030201c00aa4504020120456004003030b081024059410740010420 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 76525100 1250 76523850 76523857
    0x61207110c03010e0a0b06091e040807020d0f0201140a02070b070602070b010602100b06191805180412020102190c060f021b120301050f010c0f08070b150405010b070308060a050402 79
    0x2040c00c0a400b500c0813504104c040d106c002012507000c0d141101c14805c4c0c8003004447d843d5a0807603601440501e8441c0e00e800c4009102c2c021000c0c0d401032103200b4440520000ba680c0029580c403d03200c05a00006038078003107901e0300440d40c0880150b00050360800c0542a904000c01005201d03020041c038082090751400c0f82c0c210b003030f0403030001070380802c443e042e25a540344290a00700c0c030100e4600e41003500020032194510410301248003000041c2034190108180c0000d118050b00e801000b200402000360742c400c0d1458011202070352044040c100d803008150041c0b007245c0c640200c40e060500e0209510390251031101940a04950f1141c0d01d554000c9400380c5880075007800340c2d48540c201001d0708031107882c2d85480d04030300383d0100f140420030040025035a44414150540404e00300580c050b00d07582024000e8041042c00a0200d0600091060412280300c81070340c07244000c00e0100c48140248400e10084960901030f00515080411060011070f004034075103548442c00810186400341c950010405981 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 76526350 1250 76525100 76525121
    0x7151a0d0204150e420f0f0306010b180603010302150a050c0d0806012304061103040819020a08010908070312150305010204050a050411040b0c0f060c07030806061207110c0301 77
    0x19030740c59022052000317429002c00c00c00d41c11503010701c01d2050391000d0260f44200610303684600b014007101d24894541640c2125003030f400500359040c5607510b0b030034190541d000300c1115990f50001c51303246030103280100a89050303d030003410040c10a554000c1d010020b6200403031030400c6c80824002c4c1d403512a81001b055880040301da480710304030300f050b030005401d00e41000402c011403006000d9100d08107000f0015501210402d180440141103016101401c510a80e004411356010b4401c05440c4d1403c24001242902d1090316036401039941d62460b10f003259004440100800001c201c0c600120784501480004001c0124000820803901401032050100c0d81d40116005d0350040350403c11480d0940515004180c151b80500450300100181c20040c4114019a02e006802180220b07001d401042030b000b01c0080c0000311421402c2030702520615400c001402c50000d81007500140c21410404243d9a03003044004090a00e40c4490505440d069860290058240304d03030314050855985c240105010714 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 76527600 1250 76526350 76526371
    0x30c0503031608090d080f0c090414070e0d0c05090403091e03020301050a0c0504120f020a0b07020a0f0602030304060b0301150608010806060f03032b0207151a0d0204150e 75
    0x40c6640d100151803020f0041070400d04d500b1640f136915089800440c80c6a00a8011540c86001d907204c00c500f0b803c9028610744140c11614004203e603241801440a9000d604a40c035400d0a40d460340c8100102040408001446054401010070181c1010060140c02511a0501e495203c0c2c07a05040000303586400c9003054030200b649001c10660400b031041507003000c03aa003400d01003290880406000d40c400c502c50310b141e4074280b040311418003408150500740243c1c000e0820a45070382e14020314405c0d4204103c140d104e03c2800200007a6842c0c00402d040480d40300e82c000d1400c1d50b0b030301d845440c0203101c04102135805549400c0c14450b042064048680946929110751001e541481e4a1500d400002010b040c02001c4610440c02150b86c00426200202c544600040c0c81d400004c0214441d03010120301109540d001160031020401300c1c82e03240307400d5103010104101d69405003d1203a284070000f0030031500801c40651030800340c1400c0d004400135041c800d14283d183d950380c4e03402005a150446003250b0f0b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 76528850 1250 76527600 76527631
    0x207030e0405070f270e0a1410080d09051003021602030d03140a111905040f031203050603120301090e01140a05011a04050102030d0b130905060610090f050d030c050303 74
    0x4490300038481a5906440040101c03604922172404060f2042034003070f680c002d0702e149000a0401405801c54000100d01c030369580f50900301240d44416240d458024401c01e40504010342d4a402c0c410b03038615084841c0186030100c1604e004109800070360015003072140084140001c540562010800c804041c2c01c150b0380000c080e0003c1b001c0c19144031021701b01d0744109040c0349034801d00343d06003070a40c3c50b114501803c8100c0702140d1070341658144559404a8030007590f0200000030b010441c0c1103210002000d0700c090000355250010180c45000da5101001d0f00700d024001407150f012682d00c006405902007000181400405043d03aa0507501119803010b0540c44100501184506080c40c080d0005180c041c01d04040c01c2c01c4c00030b500c80c0102410310358501c0d40c0361340300c211a6585602150b00d55680c5c0c0340c2008a10054141030b510b40e001280d0180c000d0900c49548680706114151802c1100c0703880140c0e07000f041c241010402c14801010301502003189501084000c00c0341400190f000303c40110b007003070306e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 76530100 1250 76528850 76528877
    0x30f0d05090a0518060907020a140c010f0503091b03121b0c0a03030c0210030902060d1b0203040302030c040203100b0f0705010501051c0605330405060d12030207030e040507 76
    0x149032009800c441e015110100900d00b645224813100d0780c005100300c070108425913444108924100740036501810190750160b009400d410007042d0300c40300844c00e81e1041186984040c0507030b0140300549078114241d028244511508111801428401d1002030980e2080c40c50f6004030005034024010502c1142c50b00d01d50050301d01c03020400e40c03006284c10745480000510395107000e0424442c505001c2e001e900000500740c0014401e5000440c103c0e07004202d162a8400010710b00c000300781181c4000c5040c16640c05400c1e0081c000030039103049030b034000e00824a82e149001408041d40005c0d252804001c0d00d04008a04140e130a000b82c991381c00384a0202e901c920103401c10a0941c1d10682c00a4001c20303880c440000303000005020041000e8100c0400b042944440144041961980382414202600c0c48804a40301e8111100c0d0058504100c07414030042d2108020480c40016800005289585107040402805d010350080c004050190800d104042030b960301040903250204d402500265001c6010130 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 76531350 1250 76530100 76530109
    0x6090515010206040b0103030e0d0c0611070504180303091103030403050307050105010509040b06100e1f020c0f033d020a03051003020906010e060c0123130503090f030f0d0509 77
    0x110309040034401458103003031903100c41c0074441040c0400307010440e07441400d02040d00c03009920740040d6441316407210115901c0c00024210700c40c1c0007001e0000c4c020283d0000300d6103414041c0e03150700c0855100070a00c00203aa5400d400402d140d050440322000d0107030320005696010702c0a040110b00542c00f440d0348102d01d2903ca802c6072016004a88074203594402d21002ca4512010a9848081501e00000061b078558090301d402888000803070307101028144844202016050717030003212032150204c4600d200700404018809000c605566003640c070032462940f10381c21203134800d1000b6611180130303c4900c502c00e00c94584020b0900d0010119030300007550240b8140e00d88101e644c0504400b4034100c0b01425130340000c1e91600d010b01190b04101901e641000310b59505022100b5a00c00d5000070414005030002e140c0d001070010250340c0741100c0a034002016100064285030119511501540c0f13011308460400c4008208039030300d2501445605065459440104604c2c0c6038070303020b07071207036038a80d1507940403c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 76532600 1250 76531350 76531381
    0x3110907050301060917150a2c030909062403010e0705070f060506030106090203040c05040b0108070503070c170307030510060302070209060f0411070f050d05090f12070801060905 79
    0x5100300007081004000c02035120607154240d0b04922400180301c01800c0740b85142071107050340d4a094200020a0111104040d4032043d05510410120002c07000030f0713002c40100c114803014101d8070713070020459083d075403520260752948054010440305401c00341001c1d0400400b18581504d0340594000014840d9140c00f002e0142c2c80182407821601d001c41c0ca0b9600c0b8003051400c14018107050710780010640d965002e411801c050181b940003152a4a4641030008a6410911400e8043d901d03041e40300400d54440e0250a00c55241c1c0c1e1030380b80c51611080800c442c0741035042d1041c0c42032050070001081c040e020000450207800956404100d40c1402c141101002c0050350009050601c108016001a255241e04035840241210001c98092850021401070049000440d0504400184900812240d1180194124051000c82e20385070304c216030984d4280f00e84500e8640c8081107031403202e020318001c50240c4803080c01e0825149111740e1906454252403c540280c0ca20981302c90800c014851a420314 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 76533850 1250 76532600 76532611
    0x20109032a020d050c0303070c180903050301120303020702040e010203060a14220b03071701050c130b0a110609010b030f01060605121519060e0307060509010e01090f031109 76
    0x3008140e10066807002070340000c0d040c02030191000045031400e101090101202c44c01c0094266507544d01a0305c0d140404003001d01811a803a0a028032a030003642507445526003e55060700d44502d1a420003140c0504100032104c22003c05808210300001a141e80c0201040d0310844000581c4a05100007001505070641d0080d025044a01e0307070107503103076072142280a26a80245e980c0004403010f95140c001900c0c03038004640e018498124001004050070f03260055040c4000020095a00e4081d49141d0760720400b030182d602c3c10020750040c082101c0c40d10003004d1150701400c1015040c0703074284600d801c0c4042154601026591469401c9841c2000d00c1001d41804032030008125490400401805501405a0303002940c0b180c50002040700a0100c4441114030000701100d40c40b001c400c1c0901c0d2030998501403500014040301203408942000204841030320401c1c1c45140c10b241d040401111500c050422040c10001d1498000482c50482405100a103009150713035020001d4220a2010f100c2001e4075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 76535100 1250 76533850 76533887
    0x50408060601080702100902030c030706050301080601080303090c1005090405010b0a020705150a03090309080f101b090302040203070e09011401140408120708071a060109050409020d110402041502010903 89
    0x404c002c1540c0420107200c1c61203e400001010800c0c1c2c00420303c1c20400c802200d40500c43c4080100388140c203c0003440c121a0704100702c503041da884003000b903220701041e03c420707420f503200a02c41c20080c640301043c440030145a10344107041116010000341692020383c01013110010005031200c00607818400c407009414144c40c1003030b804060b80103005243c0b041e009140300705a914402841054850a1188020b2007030078211050440e0410000b0385480a2201044a5902d406035082c84250300716400b100501160b154141c1d071500e15002c0c0006544005e03c4401040321100c904001030303450b2084a0b028204132b010904d5401305000c000741600d10124101e541d00344c070038801045000000982070101d500c0030128952030b0006458921014010010004d118100803048448002a50041d0601c1101c00340d1b82c40899a0f601c1080c00f0840340440d2010b500100b5049402010440061030b6211052010b0001458540d441890501c980042400000140d44501200003803561242c0c654171b074001c0d61003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 76536350 1250 76535100 76535117
    0x7020106050105030f180a05060708221101090b1b010c030204050d060905010b0616030e010305011d090a050307030518030105010e041202010615020c0108090c030c0607170a050408060601 82
    0x2000600f2a0000500e00d00d0240f10441c0060401c0130540510741c0c2d140000011504965164038040b82c42e40c60480e1400000390b10540010b0b0440308440304005510003082c00c8080200b1252102c0c46100c84010020f8144281c40a000507504034080c0184581c1604070740c12000b01d804070307121500f035400401a0004160042c0b10030f00440c0d031501d242c502026800300c00014500700b02d213092030140c148240c080d83e111101103019011042104482d0326180d02c079985115105410200550440e4003e01480c00c032244000c5007074a03c11142024280c1000c411000c88107400142e0b52645d1455009000c1203001403004250b00d00d455000c026002d80c43d8234100c0c0244941c0d81003014225103418010409403414040a01d0200c0d010700030362200e0080d11442955150384141407034065901c9400300720943c00692100c0004a0070312010409014070b1800802910101401c8010001c42e600244c600791108164030600c0704c00e050b01c6400903c000310140c1c035907a444626101c0c407039041980042803c0d06010516 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 76537600 1250 76536350 76536359
    0x1a04031709010e09070314102105030306011d030304091401090605030c01031e060b03190515061318050403091203020606090c0c0a080712021c031a060313020907020106 74
    0x9003c1080d202e02500c1c903015580c0c03001c070110041c12240001c81114030f10070080c00601c170f10200070001038800c0343d10341d007c0158150505180800c20307910007800c0c1da0000d001007a0f0341e61054175041c0042c00300601e003a03a03004800700000d0656100f40d0007001456540c0070030303001d154040c4220302c1c01003644182c200300c100d1618000c01c1d12072002c0240d19040580d1118004005564030542c440141154013080105a4840024810545c003c1d070b41c400e020048000a882d000142c0e00900784203002906410058144110038400d0030341140c030b6040130410054401140300d80f041140344441c0b0036000c001084c10300303003401c02815454140d04490345900d510001c400c0440e4001a4803a080001501c2c964690fa64090059155004407500314070240143c4203994240290000500201c90080301046048602c100c401d90b9145503080b661180300482121408523030303001e94040d204142001138201205240030380020741c0c0303600c03c40700740b0344800c0711400c09415130405645131607001c401400200100d90a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 76538850 1250 76537600 76537607
    0x40506010b090619030b01030b0d05030706020304080c0607030b18160804020609150d0e030405100509030c120d02010c1b060b1206071707020601050f04050a061a0403170901 76
    0x14040c8100003100060000115140c0c803045a2004c0c2a5109038241010300500007000340c025050104d00080c00d040310110245800807105400f503038020011858910141e03200b50217500000d00035910214180100300391504188006d40c07154680d41e0340040d40700215410403c07124014a64820403001c01c0e42080303110a44031803584110051820200d17120b42e1107100240951081c4a040d503000b9807040828008403112070050010f200082c0000d1111140080d8032076528099441525442441e0307101c0680000d005100030b2010810290503602816100408100340c88002d10350821940c0c4800b1960781d110350b080c452520394070640e02d05182d89000341c0c0c540052502e581b11003c0e04d8150344110250165888112822610b041001641d105140550024081034680403120303800016410000e24407510200c1d219050744c00092035a0440d0034494140802010b009000c003d007245e0354800820303030500441c500300811504280c41c540d030340d0540c58055120014030b00300040c3e0010a01034145903030780 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 76540100 1250 76538850 76538863
    0x103080d0c2115090c2015041b030614010302010305060108061e0604090c0c030216030515090a0f05011b0207030f0305070507090c0f08010519170717060406060803030405 75
    0x8288000c106110034022450340c3d40180d60251200601c1c2080b4200d070b4a401c00d51107041c0201d01c4646500741a0700007036140e1582c42580b8001100a040c2000038002203150001c01d6038032044040c18904035840e941c43c0000c4a0744a91303070584400026004004640c1e00d8042e0f560b00c04020f180004960030300902241151a11482155083c801a01c0020298440c00103a800411070315005110144800c00060011401d0b50401e03001070041d02503e1031764079040c03031030a0105e992000042c08040002010f19014500c0940318a8480c0605503c1c0c50114652015a40d42c13240100b00000e007440c50809144020500b034410142990042c8400300003041140c110380015a0301400e2880d07540f2030a10b0024102f030600e400242d6054500501c0030741442d800140c041d000320282d2203c00c09039880c2d00400c2207180c0d1000c103500705020002003d1103407200c08203501c8009582c49040300c3c002600d0b00000c0112281c3c4401001603584844104021301001c0d001e80d200901400001e10f00e58201900c4035501c518 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 76541350 1250 76540100 76540157
    0x702090705181804051905030406030b010c0501050709171b060a2f070b2503121409070603020307050f2a0604030e040209010507110a030204050103080d0c 68
    0x240811600c048680502c2c1404040b01c005102d05016100b06004101a060541e000d90396480342d8203e9018000700c011071a1401600080110704040c40c202089010f040c1c0358450a0400c2070310300104001903403d008045c0508107948620106504210001b034002503c0d01039400198009001c103540a4010250703008650410380d241c40e13541d00100e40035940500100440030f07114041003018071248070810500186081b030311041c4e90103103a889280d0a0305006200c101d00792620f10380342d01402010543c0442040703901c40d0a120210351000f00512048503011402441b0040d01142007200004c000d00c6090054007981c00c00314110300342a04021300d01e0041c0850b0441103c4001351810807540d0441c08152484024194402194074100c09181c840d50103a82c1180855001840307000c90340f03864003c3c0c5844000c103a480034142040c58940c1903c01003e0f0300e580ba00700e4100c05000c4056115401428084c3d4014049680c0d5030003e486c2d100204c6140d00d60748000c00050b074803030200214554000502c3c90 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 76542600 1250 76541350 76541357
    0x603031c0203060f0307030b01090e03070209010e0a060b040f0807050303040b0a0507050c0307030f0b090a0b07030207060e010626010603020105090d050c030a05010c030606050403080301091e09030207030b070507020907 96
    0xe0360f40002180c51000c80c4c01c106030f494407501000004101400411506840b0595030601030162a0307280030b6524042d10342c000758440c440c600140101c1100705c000c0c540c8030041e8076010071080c0c0c1d070380b0700d454045c1e0054101e04800d44a408060204010400110000b841c0582c011840c040c5081806000340c055030000c1000c002e030003d014800d01004016840010400138140da24181e980d24002c00e0044040c4801c03100c40701c0c0c00c1c1c0020078458000c1501d820033900802c802915075a100720807002980002c10446900b80d0301c00c0c042c2035558092080c2c60184ca00c0c1d080d0001c0c030185000704a40c0c50031400840e64010780c1000d80610050342e02c08180c0f004600103481c800c411f0910b40ca466410801c00c01e440307a4141c4518980801130000540143c170b07600c007560310100a03080c1c03600411a854401c42c00f020b000398400700010006c00220341d02c8105100f1aa18070685c88426600f40d040079288074084c19801640b00c0c8100388148604680019040400c4c0e0901c24502a515800301d948640001c0450091 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 76543850 1250 76542600 76542607
    0x3090d0c0b0d150b031501030c230702040524060a0306050301091a010801020a0c121403071805060405010c03110304050d052410090e03040510020d080603031c02 71
    0xc220110194102070003040309a15100c0c0c204200c0e507401051900a850244840400e0004640428038222405030408007002040d04d0b120718019005020407a40031030810011202d180316031102c20120724440c50791020441ea07141c800d4010003040e204064521500c14041520308038598825040810046909076040e60700d4411200c01980108074035440070742c16509000c1d001d81048105590300403080d0f00141354800396620f84010900701d016031800c80300803a808511000c00714005002006c04864075241000503254095001005074109885681c040f60220b079110a044c1580070351038010b4142a61131605252030240000c1c0344200e0b003e4080c003801a0080d07150201c00c41441280e01510f00075003642d5040c0310600e00540d9410300418090741d0030700400d52540c2c1d41e100e445e0701180168105424a00d6207410404035000402860310703618181c1c4020040010103071a40700c045004074280c0e401405180c0c0103940058860040101614401e40041140d0302000c0141c840444208001c4440142c0703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 76545100 1250 76543850 76543853
    0x30b04020d15020a020d030b0d0222060303080a06150903080c1015050a080d0903080a020114040606030209060a0302060f0d060b0f03011e080304030308130210080711030c03090d 78
    0x46800380d20409818040900c0b1401000c9400360002d100039401582201d81c401c1070380343c04404986803845070b680d05c0302c15091054013615262100101100b0603100c110b0149105e000200304170f43d941d5000720b000c940480c00f048900502c1e44650300007400484090000c0328030a1030006d10161643c0401441700c0008030300c0c0c0ca46440104074008000c0c6516000300800304113141c0180d80c0900c10b2140520070020b511000c1407001010404242145182e103840030400d0850395080c503560402d0840b00219035860102550310451a00760b98051801000001070550860050105071103000301158018000d000307003040142c0318041120601d1072940c0400b501c0b0101a01d2305405032905030300525104401140403014520480015070403900c8806141d8030341c800c11104520081c5141c171580d0a1500300707010800200380189400ca900041840e440222004c0c168009002103a00c03601201c005403c5104000e0380e541c00680c4030040c519000021410311041c21400e69480c407030b01403441d00808180c2c04000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 76546350 1250 76545100 76545109
    0x3070309080d1d070801020c070b0703021513060b060306090a051b1201060f0c0503072004180501050106020c09060409170304031205100506070b100803040303020c1315030b0402 78
    0x142c455142040601c0b10f12104884500c0c12040d1424241080c09065000200050140300b211002d6203010701402c071051400f414504550031140042d01580074007400041da0a1490032881e1060310240c800510100c030391700b0300901700c0304a81060342c024a020010300c2032580d104c000e4140d100c5011280400c0954540007a014102c082084103c240d0301d002c60ba002c0900482800f00c4c0c161492135960040c00c4403485c400b1104955200c2018003690010046d40c0080303042d1004882200000c114074a54420381131022404943d00b074800c2c08072806884254208120003805000e00416003072000346850b0b01b071040040c5411101821440c030980d6a501c00e80c04015500e4800c107400c800d00b500303641e180d24290030090f011108004545102078031f450000341400b40002042402e4400107494141880999610455441c3d00503010105100c2c0c140c00c00903c50310204000d0004e540700ba4054072011009005104414059044907003440e420280004040c99181444404483e0032035a41fa07541c0e112400802d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 76547600 1250 76546350 76546357
    0x33f061306090908070b0601090e01090c050405060a050c070e15190302042306010804080703030e0f01110706150509040305180a0603050103050f0607050a030c050f0705010c11030403080307030908 86
    0x890038240050b0f14207004a0340041d16456016640d140c1d5103503a00e000456045590380038036040d05010b003005000b030764616400007240803003600b051460986c540000800c107400086401d00042d00000e0200ca4071001030103403000a10034403010391b580e400d02d040d114a5550172409802d01031400398240300711803d520310045008640180c0200014a00406d0520640200414882c21b28052002045241d4800c405032481150841130311800c1c10f04940d8102c2c0540114402c0c01c8d000d100700c82000c13503e00020b12824641d8624110700d103075a400e40d443c014055400303050030b441080401000c20092600c03035000072580194103181c40d81d61059494881003406a0a030301c0740b43c00052000020440642541c030050603a4017581c12120341c41604403c4c1b80d03460030100c6444001800600503800c109009800404102c011070602c1c50511503950070840b040e4100160540f401d80d110304500308400e402c6901402803059080140d0324150458a680106101c040d10360010544e9030341a80c010300407444182e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 76548850 1250 76547600 76547609
    0x60306040e1908070c0e04080f0711130e0c0d1505091501090506151603030c050708030a0212130c0e070504080a0501050a0c05040f0e0a0e033f061306 66
    0x10301030b004849041116264000340c00450b034550500d000400e49089000c0540d10a5500403110341c41c4c04132840401c0c0c0c0d03a4008010854103601c40d00b04140c41d40e914518401c890b07038415140041d4420100007120329200d45155028011000c105445c03001c900500d03d64184404c0941c800b0400e9110441200d141c44403206440851750070b49030010850301040c0d00094001c4d08101ea030030881402c00703400c8144a00c105d40d01d484103440d00520200010340260090008541141411b0b41420482d4442d041c05074400c81c0c02160665000900c0400356411200598000b0011034011080050075984c0e414900c1442c040c0c146c10003054800207440c603206a085070040e00600381600c08c00d0250f0700d0100c0c003800301903403801c3d070f11402d01c80e501000130b01c0b07501a9000c680c1c0002900e034a45141000d248501c400240c030340004140c6405a0640000c420401001c041425010140480725601580502210018481c0d07482099140c882e1591000d031001894220b0022520440074000728990b000050405501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 76550100 1250 76548850 76548883
    0x915020709051510230315240d06150203040f0e09010213030609021005030610030e03070501090c14040203010f0e07030b0a1203180305070b030702030909010b0307120b060306040e 79
    0x25404810f40d401109405040500d80c02805085c03d440000740090000310380352a050510416194510710742030072034000390046da115450050380fa0306602800c43d4000711b0ba250586885034000c10180400c2c0c656400280c4441c4091400c180c101002010b0446240c81074000a11944002c1008400d00f9411680044c140404088040d5901d240c000050144050180d00c260340c60601c41043d0340c0203000300c0703114060040a109214050502c10b40040041442c1780c000b921040c4000800620b0074403559104500404102080501d8121003243c02c1c480c0700c6000740078500510040109c510000705600c26500202004012030307480100c03c42c01081000c28040e40890203032000a0300c200118070380c00800380a551002c6942050030360843d00a42644002046644103110410140c920f807809190404001c3c4180c9281103020000580d10030020380105180c05000010f1009080d08280381340c01e8044810410700c8120980d00009643e40401003050f800f4503125110f02070030413001d100001d00c0555081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 76551350 1250 76550100 76550119
    0x6051207210f0f0603021f030b040f020c0706020c010c11120a03090501020c0f090a020a1202040602100b03150609060d05150105011103040f061202040503060901090309150207090515 80
    0x548140181c1142c0030495040c030310b041a40500c50045020710425070350040c1112000c002d0380701c207002c644684070381d41508256039180c801449940f035000f8260070038141d081c05030b1284401140300b41021410360000d001c0d54026161519a6608052107404c12504013401d690020500000706004a58203d0400e505009442c40304c000c0542010800d0107031107082c0e00b1221800c4008051281c0d8040300c216503070703111160303100080c0300f00096001010200c140c4d1070f00800201d804c15001040ea001a00101c0158212003083c0c119078045100d5849035200407001401c00700101e28551646c00400713442c2074002d100c540c000444075210a40342520041d80202240c038042102650100c0c101028015540060210f40101a030200000240c40644501240d01c4500780c0c0380c100251203407403503100e0100701180c080c0000211550103004c0648a0704600001080341c0b08940f03001005244103030054200001a1024030200c01d81c001610702c1907810078240050720b6100e030464440380110f5402010303480b14054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 76552600 1250 76551350 76551407
    0x33002060108010e03040303051c020403120e030d0c0f0b15030f0f0d080708010603020d060509040f0201030b0616030503060310090c1805010b0904090606030506100513020406051207 80
    0x40d0450480310000020030001c1902014103440e48598400900021402c0c4003021100710080c401503514032040100502e403903a66581c10040075103940780400481e07041d45180c801800c051111a035804402d01e0b000f8140780c4580d540e029a0f6101c0351000c1c01c05600600064401688400000d1a182000301110096078551a000390b5400482c00c00c0c4000380900030381c0d031b0f003401d0048801e54021907441d11014116820604102d000f5048a514200e1880d25080005034680325601007034022402a034210401e400140005010389030b1145440c3d0085c10108049240c1022400810842e590302d490801c4d42c0382c03030b07640021f450510305600d511b400c11b180800d4071080001042c1704008403a00e001c1e58400d0402144080d5003190001d1049007003440c0c080144941c2032030282e010440300c900c50100002c0094036034850a1a00d00b044400000749844203605109524050040c90012102480107501c2c060504a000340180074425101030201104400702d20340901503e0180711031840d030441c0c40d4280044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 76553850 1250 76552600 76552603
    0x120207030315080a15020f03040f0c03021f0206060307030203190f021207051201050f01060807110706020705030705040e030a05090d0510021305103009051605010203040f033002 78
    0x15000c08881c11051207061117060002c60095400800914a1f0942140e8454942c4003200e8008003048400552890303000c00160f41c0ea0b80d00b201d5080302d040c411041f814038060040e20b0020060561446a40104400c000690b000580340c6040350300300316a501da544107850138240141078000000d40c0209144c04000c8500c5001410000329034080342c2c002d04e05240702d008503080b50010745084a0b041a40300051003164041c1640e1a00001580b41503131290403110012803c180e01e603080940140c1160408100718903003040b0300b80c0584001ca03010000039008849043d601c0c030030f0005620500601003112076403580c1305d040b00c403003a0741c0202c1541d00d5020090195070080d8810107642c0c20385024400c011400d0700384002c220310003414544550b5185029108092079184c10f5000340d1110000401d00c3c0001c0d003203180600d40040740b284006100600d02d0b6030210038090401e03040380b411503005200802182511b50444011640c101010381e41f03810800c40032a07240399007601150810007000310f07502c0e0f0b0241d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 76555100 1250 76553850 76553863
    0x3040b070b01060908060a020307120903210204140d02030111030708070305130201080a0f0209030d050304150212070c030201020d020304080309010c050903030a0525080d050c03040312020703031508 87
    0x300700840341c140da032103540135990400c031809413030440ea00180000310007203201c0d4021600003049017481c030105000515400103940306403008600094003041c00752180320b00d42d6035100c582c81c40c81006500306401c1c9520b0800700c1d4026a2414440c00701400200c0c00c5d500c0070b40c01072400c10905e503042c0340e41e13251007540644070300c805866010009252a000070000e501d6200764041c0298142c0d52203069842d40d540d0070340500114400d200034030380c0c20001d03440259001c000801031040162a2107450340382a05019000410060000d0310890040005c0100380301d480341940c1d4440900d040211584009060480c02402049070160005100000348020301001c000603502c540b4004000348928400d4910498030b60040d2040e030354042d481840410001806000601003c0b8004a1703038103082d50100e441141e06440303215060710303c0100000e2544800c0f0581c09040e520446145040b841c5052a6400819584c3c10f0911020144d03400b05403203040501c250010800d103074414000c94800c1c1c1e2520340343c584448 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 76556350 1250 76555100 76555103
    0x60702210c0d1116050d0b0403030b030f0d0e0d032001020c01021201080d030c0801090e21091807050703140d05070905040f06051818031908070e0a090f02070503040b07 74
    0x441c04080312120013403004160180e5402a104040322010340e5150010101c3c0500210103241e2900340382e0050343c400b04a00304100200c100200980b07880c019001d80701d4034070241814080d03880100d401d00480e8200d0f0102074207080c1440120710002041c0341450083c05542c5c0a880254000220b101d010902900b005068a507841c0907592220304900c2c05604450b5814403035804550b03142e00401040f20b0b15800f54921404031000c2d240509140200800036a09501114000d002c0118085e4103074100446100500b03140211082164144441d0280890240d841c005040082c9002030060388114042500c0324050040010b100ca0b0902c107401405500290140300d02603440c0c03070524481c2d112140640c00485402810901c9003000790301c0c12860740c040c01095040f40507141002160801c074200018078000e40301e0307645c2480e210180b144c024903d1001078118010441d00d80d85c07000a0b03070394a011540445094040006a5401015000300607015401c0041c000b40404200000d010702d080700104480d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 76557600 1250 76556350 76556353
    0x6050109060e0f090705040c030e07080a06050c07050606100504080a03021c0e130c0c02060a17010905010501020318041d0645010b06030406090b0702060702210c0d11 73
    0x66843d010010f40c0b00004907070861603a40050f400b00018149684201100c803498580403a1007900291080d05c0d1080552011495034071941c0c3e01d2082c0040c620440340c011001031072143c5001d04984030283d441070702030701c80c9101c2c121641d51f1124280c0541c04680042a2610580f001d0510900f0041d4645865269942601101404046095204021801d040c07980203080d6041a611807168400420429802909118980c0e01c402d0250713440c1d00c041c01d20b401a0f80d40300d210454406003803034031041069101c46042400d1400612079a0703004000c0c0c81c154000c01c03001201c680402800500648403802280c0d0824034a40302c40703940c80b0401304034603108000c1c00c100702e02001495459200c2020303c003844038072003540f0394000361300c0e500302c5180c4500f00355041d4002107210000c000c001070641d0b000b510b084840c9595845004104040e0a000a5220481d030002c1c02403440d1260340a920303a26062100300042e90080303030300744001d940a0181d51084c1d03140e2007100d0000c90850000f401c8440302ca180060769 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 76558850 1250 76557600 76557629
    0x4050606180112030507022701031e02090a0209150a030f15030809010804240b030f010c080a090821060114031017100e1f020906070803090a0605010906 67
    0x40c52590000705040352603443c08501da90085480448003070f04503c00880c2d101124107a01400705040302d00c1d01c1e480084201511115500d0b610380f808041c0c501c0420381e454004004020310240c0c1c1e80304441c0e41d1003107540b90f0141c2c1d40c103284800640030720383e40201107a9030340010030340e070281135416448080f2800311202e04000c002c818603041c10f598540341c40700610729502000402c6480d449040e501d90410710640c0040d40c51050411450590022030410083d941d581d03002483c40b0385402c210728a05624131000800030581c10303803002002214000c0508210703680f034601807820010030030100ca40d000c2c0c0301d92441807030314a58600600320034002d64206002070b1107602104400752100048074010658401903150440c50440224654407040208a01a018040010310741b401c284c0100015004180045d128924108230404120016408690445c40c0706200d1b0032200d480d45000c85100e15086039109450341c0d41c19016500e4140c002000034001820800002010070a82d080001581e090b0740d6007411 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 76560100 1250 76558850 76558879
    0x3050f030a0e1501090605030a0c090c0207080a030e10050313060216020303120405010b10081501090b0c160603020a0203090f0303070c0b0d110901020a0609050c0d0813080703030503070315030b04050606 89
    0x58a030341e2758001a00140065204103c1c0c0d0155a01079400040c0c40e0060f11229a5112003160500721058002d901088403141c1380003840c54600c0810130b05003114101075081d4107040038011304180360040c2c011301c41c80d4002400190304803410071801503158014200c03aa2107140303101e0070000380000c0d0f80440312036090002c0c5010303038034001c0e05600c003140072903503170400e9507075802c40c10328804184a84990602c0200c960202e01c445da010004c00603009650020603000f07503152490103c1c07508907801002050f00c10b009401405602108860313540380c040351480031a81042d00024298810310600a141c010a01e0001550f00b114401606507880074107004c11480c054045018980c2c401c0d100e940e40144c010b40c02c443c00044603a48400da01c01d0150003160200a0300c1008600b5440060100b907800001c0401c40000d001084d005450113840d900e000f80126030f2540d41d020304203001c0078110505040e200e025180601d0802a03056005607004582d01d800350902c1d0400544440098402c180528000d501010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 76561350 1250 76560100 76560103
    0x31306020a15020f0708181201050708150f04020f0d0c090f060c020603130303140c0c01060f0f06080a090c0308070b060f100e03030705030403050606030d0c03050f030a0e150109060503 81
    0x74841d1130300c00f02003890300341c04d81d884024550207004030b1802004112414440c980300c03014100c400280c00400001e240c207115002405010008242c6560980c0491100c00f2640b00c042c100c1e84805e106440140c0c59a42c040d486da6010700550411880c09407800c02151300d402d83c0010b000e801c403803203114803c103500c1d2242e2003103403071001c9000080d4014400300049019000c40b4090790741c1c007601078507000a4000e1990a01403549a0070b80301c19a0400c004103840411080030b1144000502c450503a4403034040c070345020203401010700d2041c4010711041c45e0015410803251b07088452032030351000c01c4503800c545a14242c2c3e416041440300303942c2d215598002400600b004008d01d2600032009111103000b00801c02c0880703016400c624802d4050100b8800840050b808001070406140704038082e003840c0c60f0481c2414a454201c8902004210341c1e21050b0b80070030f42000465640526078034081d80d40341d44403080e00d0050b1208411243c4c281c401c000e200a000c08110044074140d846182007845941d41c1c40d410903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 76562600 1250 76561350 76561357
    0x50907170d020705150d14060307120b0703020306030a0f06060e060d031709010b18060102010c02030a0503270a0605060f01030b03030306060d09080c010902040b0105040e060d05031306020a1502 85
    0x550143e44000b0082c0014a40a41c00c502c6800c040340c3e9241c503092071401c401080d1610307640082004050481840f00768270341480514080d00b0a025050506412601c400401d402d01412103418198008003050b02914140500003a40e500101d80c4405020203141080c01086e1a119020480d000314011621070310f01103a4660400b030f0545e403190490300c00f513505590581009007a030b4010f50f50ba0b960b5030340c81d510750b90740400110031a242d081440c0c0c58490006801e641c0401a007904542007002071000c215000410f9230381084003540c4e8848a034280454a016103410a50304000e1403080442d204c0400007540c002600c03e0000303075049004005000c006406582c0c130600751650542042c00040d10324240340c00507155503080204003164a1080d030302d0380c0b0070b2035200300c1c0e041059035102c8038034409501f424060030000d40c500b0310302245802e141c0400883e184a015041d203109284120119043c00000c00c191100d11b00c151240f0818642c0d20301c80a9510481ea031001c0f0386084140400c440700561074402d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 76563850 1250 76562600 76562623
    0x819090222200a080702011e090203070b030103020d170d0203150111030a09031401110a020303070306120c050105090d06060f05190e010e070513030317160203040b0904020d05090717 80
    0x8560a00e45207100c04c0d00c0114008041c03104543d0b9440c820b41001c005021000c00c400c200d03080010700b0303102c180141410a00c0c1c0d0f401034040801c04000400040c0c451001580c4065081140b1540303104c0170b2860720000d8482d11511450b81e900204c21b2007404a0000340004643c04262210400d14250500d0182c9a016114003480418403c1c007007040854141c80703c05c031240d0092000080c6151452400c0041134000114050040e4404810851512b40521403280a030103410403500441209640382d07080c242c4c0c0703030060030704008012030082a143ca030030b01403c0300658030200c14020381e610b0709a131000002da103201c1d0b10300c146007480540c00d8880c03507405140b042d181c4035002c84003e42c2c02e080718220007120103054402000390400c814961500140c40b0000510b20036600e40740044c0020702c0726503038000d000e46144840291559403c411030740000443d0200c3d441e1248071610780c442480014001e015145403104043e0034a0100030b1a990003040340c2007039500103404502c0360000c4c1c014491f0f6403000000ca = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 76565100 1250 76563850 76563911
    0x50f030604021513030209070807020f071a0a0315090c030f020304080313050307060e0102030a05010504150302090c0708070606060f0c0c030206071515090b100819090222 75
    0x44a00c5203010340303070081c6420004c00154030501640c90307010511542e0200d5114000900007824020301582c1071018000712160702c0b0003040ca160034031803800e00702044c002c090511b54100061511455000740c001d06480c0140d40005240360359260000c2001c2c00010f2103081c0003c0c540f42d0721417001b071658800c0d64000c0307030003100031400c6a4950701070a00c0d0214904080e906440140603510026029000d400300009141001580701e003001c1c05100c043c0c41040c4c02140c42113048c402c41400c6000c046c1001001c485c0c04554002c1a40c41c0c00e03001d201d2605c80c104003d480c103940050b2a1040c8621a00310310102c1c0c0c003980e5203241a0a448108441c52380100782d0090040d0300e0f600082015152a001404540e800b0726820403008071519520400c035410640c2c5640c050000e28401c200b000420310952024903000e6807505000c07241140000d001103802040d200003d0020b014051090f415944a004001e03400303403802d00603a5828190040d20054a40d4001c1c07601d0901110074201b032085034001c6520100d03440c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 76566350 1250 76565100 76565119
    0x3091707061e12050903040512010606030c0c0b07030518010e060603070504230a1506020c0312040f050103020c0102071202150c0a0c0f050a061b08010e0105060f0703030b03070f050f03060402 84
    0x43d40d401600c405061022a84002d000109260f500c0078507074401c1e5414a000040e000745051000f80965041544400034411040a88408520040e14555001c04503140000750747d61040c840580034605510703a031000350b1800c07a514500d840000748043c041c03d02101200c09031550307030040009079001d40003540002a030300c48412050100c85a178641d00140212004100649003d00b98100c03504154060001039020000401d580c0c1001c1c0920b100da9429005510700d000d0400c12111458003a61003614101580050546a1031901394103641003d0b521038407d510102041400030b542d80c10500c4445c0c0b403681140041500940c0820849482c07030415107508144040b15151581a00c0000d002501d203809491400c0000503031b0340c802d50400e644512080150000010001810700c04140c000480403004140140701c1641c0e0001940c1d00034404040e0300740d540c481032030220054503140b24080c0d0180306a01011402d4080421041d0507613500340e0303e141c030485800c07042540d10482500e0194202c1c883c0c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 76567600 1250 76566350 76566377
    0xe0c130b03090114040c09140907120507050d06021b030703091a090405010f080115030203060412050706020a0302030a0e060f18010b0a0801020a1b0b0109050403091707061e 76
    0x204003540c1e0110004000143c46244410b0844d115441103038200c40791a40c41c41d052040080d03600c5204a07024542c500c800446ca41301c00060f0352949607004001c941440461400c04100007040110090721000d040005d4688007864003402075003040c802d2288800d0300070820028480004162820203405664150f05c0900d13000c240380c1480c04140c9040c0616400300b20450440d01d41e8014180280003001101024500d0801d00c10b0868490080ea08121108a5010809a900011543d401542150030550742c1a140b420580e614400e4000040c00d02d07002003061140c2d20b030580d028500c00c1c0d85003d014084c031420094865110a070480709001ca080c036200108072040a03215079500c08090b1040000703052070104000401c030503415441507080b60b4000030b240c0d595990240540c1c00f007651b00b00ca00025140745030345400c1c0c503450501400042998035000141071602c903034503000040900550401c0804032103d0725688403002d40c0200740c0451610401101031440403200440d00c19080c0d542ca50280c0004c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 76568850 1250 76567600 76567619
    0x201031d03030c0306010302090607031e0302040b0906030a180c0e010e0405100c090506070c050f030102270d020901060503090105010602030309071214010c050c0d051c02130e07090e0c13 82
    0x38241c0f42c1015401c3c40b0f14002504c4034001800100d000781c40711047c0300b91550b25801d082378000d4100c81018010310040200000ea101038801103081100c0141e01c0c0d0b0707590449080200b40c04140e4190b03080c1030101000c24030030f00c4668102601c82d00d501600711aa00c802d4803100a00050710000d000d070b80400c01c0020701e60350b981c1c06010414814680900c501340d0302c4000a560b03404c0000103407116040c0b50020401c500d8869410f490800056000b9400c01c0c0204600c40c0c1d0304c441d400c0008030201c1002504e41d8055944d154445003880e401400c0070002d5031100e9000b000e50700100d50100b55580307001c1c0041841d078000015648210b0541c00100740c3c060905100d1041c41100803c1209c250a82880c2c8505e0702c0001e000b108201003103039480540b2244101840c91900c00403540d84002c0c824200940c0318001303015091082c3c2d0034080100543e5840c183e46040907525442d91050503c01292402e01505650001345081110040110648207807030b10800307401103110345d5150b854900584241002280d50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 76570100 1250 76568850 76568857
    0x708070f0b0702162d06050909060a030b01030308130209040f0b180c21010606030b1f02030901030e1608160905090a0210020313090606030501060c1a06040603051005040201031d03030c 81
    0x18015030328031718025a01e40c00382e03410a413500714002294022407482210b003480c040340ca0303110004451010741d0038a19111500d0070101800302508001074103000038100386003502c500c40d507140c3c05011500c00d41380600b03007691201440d40c1e046594955502c0401c00100000c84412403400d5010301424045080504001c48480c1500c59213481c40070380141c0c9501c41d4000e01c6a0001800e1540380407519440e040e042005554103420204e0707081580003c003440345a0b00005403600142e081c02c0004102003110f086a152215440c0f80040581030040080391010000c5049150401c01d0300e0080c00064517044014140d802c01c45003d20950312460948000d4540020116403040c854010f0380e19041100300d02d48550f010a030040d4850544441c401c211041c1d03d072041e240100b2861500d1202c2c1c0703002e5034404950600141c040300c0181118400b04200f0b0307485601820007581e0060407112550502030f91a0301a2900322020782c00f0a01d040b1074034144494040102c1c9030580020055842e40e920814003e40940 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 76571350 1250 76570100 76570139
    0x60b0304170c0c03031803120a0909050406021213031e0c08091f0908100b01050711010e0303070311060112030f03020a030b09040501152702030c0708070f0b070216 72
    0x410183e040f000740d1001d000510130000c2c0c1042e210f9003150a102410320302040c00d04000c400340303c1001200714150f803114143c1309a41190001003025100c03410800041e010303914004051400060500800f100c2c1045440546ca2094441c0c1c0042550307840390b41036403e10b10710941d001c1486c0501681c0040c81d032100030580f80f01c0003010302c203540c1641511060f04012040900b000305018010038480d4080c02c028040780e40020f10310174050a00100c000174014090301c42d00070031122000000b403007d603015031099a42c50314040c086039240c800900700100f280750000c408100314000e00001140181c912441c81c0000d94160312411202e482040c1c0443c001d510050b44a0205940c1d41c001240543d00e03003084600481c007450010404e111000c0c514000252a42d110010b03403400940401a160000321028a40a1050b0381c01a03d03a80c1d1748122480e103201f0000300500c200800a10102000481d0799003000380c0740245044d080c103950740f08099a454690280000c208002c03034008010180000c0c400306d0529 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 76572600 1250 76571350 76571353
    0x1e0c05070b04063e0901141b060901091a0108150a0e01060611010b030601060206070f0e060c03130b040506040902090f0306090106090b1504031407031e0204060b0304170c 75
    0x4504051010032a007032043c00740312100e1075200d9030048440b107005034404c00c0c4242c10441c41c156580001910488080e03452100740c48000c1000005c03038868000d40c641c8440501c06859081c601201920f0003031006a0080340d0f951040c582c1c040f02407042c1c03040c66050b25500300040000101008862215030002040d81c40da594a0311241c0840000031b004000c02802540c450306010400c0440803425501841442c50103584030100400c01d0542c001b0700b49411031424188101c3d10381d020341080310010600e40290ba0440c0c0006444200050000b0042c47d12009143c04104419103890301c05c1d5003442140700c2ea59002e0000d21091000c09010b0f40204060300b4024100c240248110f408682031010031074003242c0613555a00300304207404c0d0750701446130304150450724800c21819025104e0703091300440c000542034000e0100101200035040140b903000d0f5801c840802d041c80061a9001c01c03005840b90102c0c00380d1b08100c0c00060820744c1c3c3e8240c0e4051548404080c00031000c112a40409400c10f0220710001d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 76573850 1250 76572600 76572611
    0xe100219050f1c0c090503030705070b1309050408041a04083a03050f01050102010606020a1401140903041404050103020d1103010b0402040b0301050901050916030b060f0406031e0c05070b0406 84
    0x2c03a9980940340482c408020881d9044d600c000741020045074007041c001c1c1c00800029001440104081c1c00f0385e0358102801d070703d13842205180c20044040b41c1008180707e141c40207210034010140050320445200c41142a1480000e0f80d02d011140103070b00c5406980d501201c403403003640401c46007164442c20030842e24000070240c54164103019101100c0c20012030350b140113101a1440d0a2089400340100b80001e1207944d2078818020740c1d07440d900c207000c1c00c850066401c200c1c50791002e401120304182540a04012402d20321150b0b40c881e4070038811140141c01c5240300303810b18181401071030f040302d070000d0081e52010f0168503403071440032504030356a626550700c0428004958940c4081c001074594480c1c0700c0c7c0c50f981864144446204180c1000d803240e06903600b0803922860040000521810074075010503101000000705e03450b40118014003926000102d0003140300f030780c10b902000c44035032402d200503d240c1c41d0b240030100b111642070107500047c1c4100702e00408a16003081c5a03420a06c0340303a0000b00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 76575100 1250 76573850 76573867
    0xb01020c03070e040f150506010e0a1503090c0e0910050a050c0706090c0f091a1903021c050d05121513020c030c03041409070e030606121006030302010e100219050f 72
    0x1c800d0b904103006d042040e6034105010082d40e0207984604420b02c00e23142e80d2855400c002802c50a10403482c620010035446203038060404c45000c505200404a80601c1c9519052010b40551246140101c04040c00d01d86800120501c01c1801103601406404140a260060580380c00300a46609401a51100c2503118002001000c900d4032800601388140002005c40728004200a00c112441c1b070705124503184080142c0710700400b503201c4101c0b035040700c5a44510034618040448003610403c081c10901400d0507000c411500480288020079040c0004e0009580d0903001242c520321414001d90000c4408110000b001c030300d5401006c030708030750900b100c0c20003403604600741c6140e206802c00d026581c00c0400c10385490800038050350304412107060042403441184042680d481004140c5880b58484104d05540b6200a128940042c4600303102807200c3ca480e428007901a0202c2c0c060500301d4032500d10070422030200792007511400f091215000e0f4003071a1500d0200c8494000302e4105105000410013880d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 76576350 1250 76575100 76575113
    0x60c07060206010503101104052b081e181e030f0307060e0d0e0607030306030605040506151804020904081b060105040c050c03070204150b0a050d0b01020c03070e040f 73
    0x5004000c154010a0340b0360401040c903060005241e4440b020500f801441c118181d1880c0c19101502c40c02d4079801c80255108090030b4181110054030094103140b50b030820188841c0b10014032881440030328107004030b00d424a0040741407007820b00f51281d064005510b01c40514160341e400d001003c5c00604441e40400450000381007001c3c52406c166182d0001511004024090160a000a6110000d04440c50442c0000b0708400e4002c0440307403145c4000039621040600a61060303000d180c000304100600d103030510b000d81c1d03200302c2a5001006869244c0240c0388920704025601422000014500360300e4480d0790a212003580c028100715400f400900c408080309982041d030140900701301000704815407401c0d05110480b080c01c2c840ea000c0010070400294075800010441d040613a040e100001c4648031905442d44065081c1c1065009a42c0012a01e05a80c0e0200282582d0305803041e0400c0141c9003030005a9490110b111500e4054210f00e40c00c01040446039681d0354810b001300002c0c80e2681060b501c0c0c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 76577600 1250 76576350 76576363
    0x60b040e010b04061a0715020d020712030f110405060f0c06090a06050c0708030f0624040f12050a15092906040e06010b0a03111201031703010303050a0e060c 69
    0x221050303540342c0d80c414181c5024000e0303100900500c0b000d1032001d4101044500d0302e102e4540040c110303207882c80b16030000601690440c0d5040c010341500310f480d8001d500e00003d040180207644e0340080e00f0160958206034091190041076209d02042300d20b410301d803109104403900010040541140c05000c08524400d092042910a00b200d41c0a081c5410203403805404880f8040c000e048403520a01c54030b80007810f10b00440c0e81015007100ca0a00e560344003400039062040401e165188406000d4203910b8007003e070000741007a50b40e00c1c0074070103101e9212801c0d00044141040e016000354803901d80b580120300171154003885c0c500c03c0c8401040c00303540d68540049400c940700181014130250100b109520296141d00d98100008480c180003d1184441c59540c0718010b000e08a01c40341d000500341c8046d4020303880600c0280c0380c1c10f40e5940b1741020038040e001003c424402a6103000021190700d000c024030401700e80c1a07a61544440b030422803280400c44600c110240b100e6040441000000100d070000c0020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 76578850 1250 76577600 76577621
    0xa0503121b0c0105030a0e0f1606090b0903120307120203010305030a080f060901062703060f0c050a02030316030905100c0e06070314030604021c090c0b03010819060b04 74
    0x2241e460300744601070100300685101000d2030382c00000a59900340ea03c00e0840f0381182c16240c000c070b07400103007143c2c19040001040c0e14070103500c1214100c005e200b079034039001c3c000c958042e214243e8a9941e00c2c6401d0103445100351250b8190001007a03c034100708010047c0d600140745251050040c86d0504917402243d00a07002601c447e4404940020810b6001c0155a4004110415080507080ca000490780210041c06541c0c1480000481c58010700c000244141d0900900d10a4001300c55a0b814620003c0044841880301c81303040503c05031b034941c010030172104e1201c203503401580b441e512a106901c12580742da0b02102016112208140071440c200000080c0d1000c5001c00a081000940042c000480040750540110020f0203003d001c40e420a480e96201c5c800000015034a03614440010002d12076019440c1d41608502e6240080c000140d00a2201c180304030041307564207403150064480d6000900c0340001c503601490100c4c00c00e44d1004c500341e1a442c0704002c04a94264084001000c1d605030a00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 76580100 1250 76578850 76578883
    0x12070c080607090f150815030c0d030e04110c0d08070905040e150f0606040e04020d0b04123e0a080a020d03050f070206070507110307030b0406150509070e0a0503 71
    0x40c015204c101041e08002e0140d0786011460981946000c0d2001d071000700007012020100505104a0300c0a002007040001c009128001301c10750361902800300760f81f41d2550b40c02180b5011819104025100c201c07043c0d002142c1c001c28060325600e038116100c40d4012302441c2040680d02d000501601c8900031140c49000c50700c0504000305108800045a540c0207180f010800490424088240c4410f001c95054841382c4020084595030b600205045d0030001c000201b04250f4401003105000300c03452880c07030105030741c0c5c0d4203c0a0585515040211030039144100c0f000071801c201c00c044100c14081c0c4c059494840000c2d01c0303414074551203004450f00048080000350700150002c0528a5041c80f800380d10000400c3d13a504203050152000359513400041c004824041d0001f001e409002101e00c10068003400202225074403500c03440c00d42c290010549080324642d04040003181040c640e0750540058440180c8081c0040d541d45000b02c500ca000454040e1f00f01100c1c02c1e0108090300c051119100071000c101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 76581350 1250 76580100 76580117
    0xc0f1b03120e0901030213180803040f02010809010510090e0a050106172a0103020f160602040e07021506090c250c050a03050705040f060b030708040203061812070c080607 75
    0x19400b03011252014446807280700042e005000690300c091111342140500800000d103071400310000000c030b0850007800742400c5004020030081011000c142802d16100380c1c0c03408041c1d116004c0590030f1b0744042d00c52840d00300080da005d2000700c6280d44400784441c0903104440c0312100c6a143d89003100e400740c00c0307008101f82034441024070801c100001c0e490041d04140300c10840c17010500c0d03a01c0c0100d070f5042c0981010303000520703c804284200244c840452020010340c0981001c1c0c81c01300000d40c40342c49901c0705003028a000503a5036001041898014480041664040e6244c5d0100941790000805005445000303005a840c148810680c1c28003039010004810304918550510700e0480c2520b512440c403669400344103000003817021860038212101601d0100d882c0c044131038000050a8560020307040752001004102545070300286c4c1c103024500076410760b40035460b400300315401c0005402d200d1000b907102090404c0741c0c1208500400c0780c5030040d4814044903403030b070074024101001514500300186415 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 76582600 1250 76581350 76581383
    0x30b0d1223040b16080408010f060e01030206070f0312022101080a0515040c0302040c0215160c0f0609020d03020f250603090c0306020f210105010c0f1b03 68
    0x2603503002202454041c200c10307000c205803a600307032440b480c0610319100c8004580004640040121076221550080c0c0d15a202d5407202d86981c020305240f0b80d24a205803c102c00050b80c0351403408440c1c103894000c0c01c0d05182030301c2a1145440301e407180348100c1c00c002007986055032046080c4082e040030284078548000060f40d020082440c0c2406801814031600030048401c00104001428505580001c080d1102603503141094120100e4030b0f48003a4005080560b101000740d80810507203103215080400303a18a4446442484030410f0020494021441c1e00c00800042200241c0411700207214010100e1070894960100c0c0220386500c0044016074048440d0040d082018815101600c0908403070a03013003d60060000303490400c5100d600c0615a07034940c04400c3c000350603d600d01460b00f15505658841655042c0c0d500342c0c1c0241080031350b951150a0141201018110950480d801650b80310b8124030a034440b00241c0c0360f4000102c030140300e049000d071525804250f1480c0214000d45901c441113522 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 76583850 1250 76582600 76582607
    0x160807030203100e0613050703080d0209131b0309141c0212030603060c03040302011508160501050301031a060a030b0403080402180603060106030e19051e030412080a030b0d12 77
    0x250b03002c2d664a0300744004013421160005216500200000c2100d10012250810600b41401904003030181c1d040000c0d881a0307820356400800c101501501c01d41030b03840100e03088004450a07803980c7e080f80320203540384d178004600c40e03008680c07054040c40d200015425040000d034605a407580b442d03295a40c0400d180d0726400d4040c0300d4007603001032001c0d030b8529616200000030344a840091071484c2020000c130204003418400d50001c0655a031a596030305200e034032065455076415801c103c10f0042200c1c081c000c01c05501c0340054a040300e910181200c0000243c01d000c80481900034503803070300305040c81c000002145001c1042ca0040740a80c88000c031904080c018410186070b020070380311002c6558014040a91400030343c2e0b03411200c00e4500002e0304164a010b5a0a0200b401c1c045105629070315120014002c0c00b09a1000c0d01c41600743c0d80d89500003401d00c0a4403805644290001c05040c4541c20006c00c4521005101300c10303083c5800612004c1c02000900300d0900340000b69068590f085095003610f40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 76585100 1250 76583850 76583863
    0x190b190f051509130227100c2103140f1009090807030f05160c0504050a1b0e1f0c02120106080c0f0d0206190e060906040b0309160807030203 62
    0x742d4600030054a0045250114841c500b03007503000f6212000c4491301310700168165000702206400105050440303600c0c00f10701155007008503100380b08812980f4a82d5009204040300c0c66031129003039040c200001c0d240c0c18054620880041130540b1120900508906680c07480d115204100241c0c4140c1014030951105000790340101000030b02d0b100100011421003400d5800107649403030400f2160f582c142c822525405010901040940c8200c0847c0c1004000307800b1000740c0c5c000b82c0302000b0656500251500703480c4980c480c040900000f02c800d440f41803164030318400c1c414001d03010010b00109000740921201601c6e0304500001d1480c010a0114585103000c020f90030252002030103100c1c20503204035118660a0358052091070941200c83c1241c0b207194424a002e40c0007003a064660200320081e499807542c5807403001c0080c21111103500d03146001c0e03050b60b443d00409010315050904041c0880c15517400074040000301d1241daa0004050001c582e41500684402405460007500e0751050601c2c0a9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 76586350 1250 76585100 76585109
    0xd050403020609060703030902030f010231060c0602120f04050f060114041d0102070803040209010915030212010f05010b1801081e0612100b10050c06190b190f 70
    0x41104101594550080d901010f0003200e5481d42c50385076184c00d40041092400c005e4150107021a100c0e0540010341c040c0c054104031401c07185c451190300c1082c1c1c503c4d0700421402c5010320140401031041521801c80c4a22492081b60010b292946c05036900710020000c1b02d402aa160b03c03001004200141840500420300d001c0004000031350408030300c0d0f4071840e4000082c50040c2c0d0344024003d800c00c00003c43c0300300c00030f540380219a036403c28100020741d540100c8050780103100d0031000040300003d610840000384e8400d00800c3c030480c115401c00541020b2850040d560351f41f196407072030b07031215148101c82c000d1640c1c1c0030041e40c8180240301d443d0300c14002000d090500c15540e0400640d0f44807080b4000c2200110315500c0c0c1640d0761a40000d02941000130407407414801c50480b8801007071554040d01e04407000301e40c0d407408000074100844a9100b201c0880b03146800c4000803441d0710040280b040041a40b0f4900070ae443e00c0118045014100340d001180030801504004000c401241601c41c4050b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 76587600 1250 76586350 76586357
    0x315040b06011e08060402090102070e0408040311030703030903020d0201120e070e010b04061202070c0f030303292d03030703080a0e0a08070f020103021e030a0c0509030705150c0703080c0d 83
    0x18600502800b0700704c0c001d2580703018030740008220099070f10900c1a000a844140300e03940f00f40c1031070b0408002a800174041101c2e07400001904c85600e1900249240449602da40c4031a041d078155070a01503254031065003281070001c03c0c910105042c00d58080e08005030107000042c42e0303142c40c000c2440880441a44400980442040240a05a0300c82400000d09248040140c3d0380c01451508a4803480355034045903030700802c04000300416500d500a1101c09494008004819100500c5400070351507003e03041d68003890a0041d550f00c400e40800f45000d8100c1a0f03101404034508002103401c40c0e0100e08218000303002c03003041100000051080300072070610301d0020554810b26940b0030301d0a204018025000451040d01d40c0c0445e03102e901242c03c1c903a44903886050452155120085540060300c0284036581020003035164584604140c2d519184000c2c0100f0440c0d10380028050b09600c01c00c0000d00ba290100710f5000e07030540410829004603c0f07041d416036140d0f26009110304040b103400b660b2040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 76588850 1250 76587600 76587647
    0x1b0f1c0c0e010e0607080d0c05070c2111180a14100302030a03080a15090b01030b030a080d0207030210090308011715070f0c02040e0609010b011403010e060315040b0601 74
    0x9690380b05030380d2104140f041c0d4005a5901c024140f060341e41c042e941e940c0004605040c0b403501c0069102d005002070500c40c4554a02d103984400346101608008010002d80b03c122594260201346000e01e01d2288540c00b510780d03450030318064a401b00b0440e048804c140043d8499115031a40c04000e1842648402c000311003040d0203003540d0000e500e51004540213010010a240461089401544441400c50030314801d401c405a40d00d607118050090045c40700c2c082840c050911269080224115100c3c5912461140c03400d880300c00700000941003000c1c294214410080c58901b01d9040740315440d80c0f0750003521103982540c5800d8407006140795900c54a4807070742100b200e402c1d0f907280810099400141c0d501303264520403e181021201c2140401010354050b00701000008103d0000c6032040c082c0440304001c1c801888002c00645d1500102d103002000080b00300010080d01d02c0c203c000540000004082d030718518141030100c00c41c08019981540c0608410f424400150303082143c900203c02c803855038414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 76590100 1250 76588850 76588877
    0xb010e06090604060f121a151801030e07031505040b1b0a05070f0b1602010c02010c09030209130f080a08180a020409170408010f1d03031b0f1c0c 64
    0xb542c002d52240e0014085028003494106019030503c00c2ca045c820001003010640041c040580742c4030b449552405450440030400c000c44101c005c540c0c45043c50641869241c015400440c0103184d107e103055003c3c002e000d008000500d132000805240300801102080b0340c141400c10091100000d000d03600c00d2880c00c0c415511080074002544c1c85007403c5e08115445007498100480480c000980c0201504689030400c0000300340741c1d0358034504010b26802040b8062003c80280e00300c1d0f05410008011440280082005103050280035074001c184c2c100c11869640c03030395112032141000741c0d800c03a414800840ca000c41b8592003101141d10060b403422403007401d5511404a520b4804c10325002c0d00482e140c1200c0014407904118481c1110300044003a0b6131260f41701c2c03000c0d00814041110300022410895020445a460705501841100c99000b031450341d00ca011020600e100100089104e191060010360411311644001c0c1c401038040032003546400d040e508801d005c68525100700410300c102001e40c1c02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 76591350 1250 76590100 76590109
    0x10503100204061b020301060512010213050102010614040e030c1e060604050103020904080306010e130207020315040b011e1d0f0f040803011503090524070f2a02090108010b010e0609 80
    0x600c034692050030540f22011307070001c00c3c09000b03030b60011504000c99440c68070207c10154010444444002100200e00e52220012420b17107000b4483c0ba0700040454025072036520b81a400441c41c000300c01e040b03034648640008039500302a19107243d456400703c0e0000010310486c09000303803130b4410340440d41044658110384c0000c3c0c07150742c0600301030300f0f0705400710014840c0e0340204641011000c004200c82000c040b4021a00040e60103814100d010b40254074100020604440700c15002c3d950000c0103801581c203100c0521314005510840d441807243c40780000521a2180c48048182c414000c404030480c9040110340401840107400d820b200c402c00010840420041c2d02524195480c0011103203204010300412001380030107003000742c864082e5182000481514100840e1080c0204c0a488419270b03036140d05030b543c0081b203c400004110a8264000b130100070300d4254038003481c6140841914030042d004540643c800360000c0d001c0b69541d51050802e0b40c1c200000000040e011911a0b19200020000c41e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 76592600 1250 76591350 76591367
    0x9050f0103030c0f2414041104020306032503350c0705060409020403030e03030a0c030e0607140606010311090a090914030a0f0e100c0201210c020601050310020406 72
    0x240401801c440c07281c1c1000380e40100081055004202102c95484282d05c1006100c0803080521155103016034203d06402e100d104a446170b900100001d1030607001909110180d40000c0409915024182001d1111071904101180c0000e1340100c1020036415458050440b00001a22031100648141180e1411b801000c0c1d50f1100d0301c60314400d5486500303a0102901c0c0c2080ca40025902c2000400d01046400b9a94041d00449000eaa50042844920070a1545030302c034007041c40000405031079281010074010038001c0071940c0701414191503d001900d4a04404010141e61200f1fa0820000d0000560389806280d0100e03030f0940d640c9160510510005002c420a44580396003541c503440c0000c00d01c2013940032102da104064042d1307640c62002e03d00060520401d11052004104801002c0c0141e0414941d0b08042403410b455058405015170010356403104604140c42c230841150340181d908081078090b15840c04000e8008105030b5040c0404c140c10100440011142d662061008211456004241 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 76593850 1250 76592600 76592603
    0x20307120218010905040201030b04092406051302070c050406030b0f250f0206010602030306030a0b0c0705070e010303090617040816051006170307080406180506030705070212060402100e03010b0a0b0403020a09050f0103 96
    0x601040dc0460500002618595200650020b401d10139103c0541c000d40041030b074a4032407407111043c42c6e118010002120780340e0001400140110001550003121940384641048c1d42400d4082d441c51000700c040584401710580c040094041440e604604d50100300082c01750145001440c1145002c80209544005592001c0c00b401c1e80040800e008200341d4003210500f54001069680544d1541208000c040c000c1c442100056a2200000361062184200561004154192070229200c03512500c600750440295207125010740c1190100043e130812848400d0f440e49280071803140e141003140b1180b07405400000b621a0003c02aa10000b0001c004403010341d001400c00d0061000e1001040c01000d4880c2c10151304030400005110380207811234080c0414902c21130341917255185024a060300c9210559009411403030410010002e140540c9060100c00d0000d000000c8141e195800651104400d5101c8076a184000a05201b941000341c1351101400303041c00c2c14042410314903000390401030140320 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 76595100 1250 76593850 76593893
    0x303080c0a110607170a02040501050a05030606090d05010507030b0301090c0312180806060907030c0206010e1302060f0702030d0503010e01030305030a02041706060102010c020a020307120218010905040201030b0409 94
    0x30700040403401070004009071001d8504489083c90152400b60455160151007600159000c002400b0038020303008680a885060f5101ca050040c51b1100341c56540020302070b20f038406410302110391076441d074100301c041c05400754002240c1d030700380340350301408413010000070a02a03410a000d01f0082600c1d8142c4e1002c4943c086401c888005c182e404c21141c884100300e400018045511002441600002d0864001c03d41207801c5036144d203468a05904840644000e00096004074004010001c0300021345603020040c04441d15000310140c0c0050a04d92003600c591840000210b130709400e600341040710031015081400c2c80d0346194103040150451079014030009041100000008440320016016140100542584018800240b40032140c4071401180e24900540c6800c00d0202c000b80300266100c0703100c0d0003a018010326070404100d0307a10740b0151802a030300301080b401c12230312041515000c1c500810071180001054200b61000505590103030310ba0b2440b40d030414024502080013900443d180f1801d000303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 76596350 1250 76595100 76595107
    0xc02061210081f0c08071707051b070821160f02040f050910051e0912070309030c12030906050a03090b011202030616140f040305070605040e100303080c 67
    0x750100c5800806401c0401540580032002c2000c00c05407450041041010205218000050401711001542200c550001440c08a4000028454415004e0300036515203003041c03a04612081c114844000c215201c00c550f480414200030224003801300089144580c61218541c500540d030031040f9000c0c5454148000c0c0000e00c0c02010003041075840c1008981c058800e10401c036000e800a80107140444004456010b0b070f480801460ac100d1248034030404402c45054082140543c0c0ea00f0903081c024204d41d200d1041507061017035140c164020f032104030710a03030b1081c1c070b441c0c15868502111005940600820120101e002c000690000704040948040d85409502c4d0040d25204078090621240c2c058004104400003003407100009100c000701c07500903411120340e13441e03030302012008120088803900040e52841c1c950310b4140008006003d0900041c030410f0a0503201d849540c10140503600940104a000408012840180158950020b150409228140e26580300038107102c000030054482d0340d4002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 76597600 1250 76596350 76596361
    0x60607080c0705130b10020f06280e0606100c0804050d060213030c0501020c0f090c130306140414010c120f020d020c0d02062d070e0301090c03020906010c020612 71
    0xc0120a00501c070041c24130701307031407400010b440003000d021045601411185e000d15008600010300341c1d401c1b981a03002002c0a42d03541c500e200c80241c50015030280e0340103500b995814819540112440d8144490160450742004410014114061042c1c4024040d04100d000c0100f00c04100392803c5a00540d188001e81160b490a40c00038851446401a80e41c0508804024007082098a1098503000e800b1100461041d20403c282d201c10420426801803034070000a8014909002400207020f080c1e10310b40e481c2d6100d03582c840c241d5680d590307a001e00000c2c0400300070620010000c2007001960304c40c002c010100d100c2000400284500d084904419200c4040313100041203941200c461080030081117440340240910703640c6441c84415910014440ca4010400c0300441c803007884c000680028400b0390f030142008541e8001c201c02001541801a4061000c7e034070b441c21301444940a1044204050060a41c0b040006102c400b0301541d04001c1c03101000b03001601e86a00711740000310048507a425980d1507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 76598850 1250 76597600 76597603
    0x50a05100e07080109151e050a12111e0907081b030903161707050106050a0b16030e010c0b0c070c360612030513051008060603060d02150406090905060607080c 70
    0x8035400b01e005600310070102c400e0301d0303003558021042d48c800310340d1188000d9503003030040340160038000045d108034803055070060303e840e04c0c510801c01d412402e10142940555070b40001c40111003180d02c10082280c0e0001c01035620802d05100380c07802c4004800c18154201205d8a550301d02038810b4031802a04902d035890140074603014400b00c20501d500322103550384020700d003260290809200701380c014224403c1c0851404160800da9a503030141c5113a2035940d01903130b03d00300d0740158500802414803004003284008601c00c100b1991080552860241d51507200b0725010f8004005d40d840006003025030b0410038181016000503541441c0140c02040341011886c4da000c00600c9240e200794010340385094030404054204004d8034409001d5183c1c100c00ca0396076014040c030221000590800204020006582c91500001460f0080c0c0090942c50b031200c815400b2803c030052150401d00c02500118040241c9544050098064407101c0030501103400d124001c01c0140c0601d03e0b009025180c04510000b07034080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 76600100 1250 76598850 76598891
    0xc0909030e03030a020d030605030f0c060f090904080c1501050915120d08010518090a0f0501090b18010b01020106080304050603041704060512090d140a0201020c01050a05100e07080109 81
    0x70050039680d843d8000d4101175a14501d82e00141c1c0802c0c141900042c481c9404240101d0b004201005030155010383c508200306a44801c00c0740031480c2040c0030660f010344524082e180703c2c0344201080c6030745072141142d65140200101202d0712150740500184402d07215408455006a0545015881c0d00345100010780083c0c00882c29140c50301c00e030484001d106900c0801c00303049a409541d80d000301c1d40d90303070000490141d00b220f460360a503001501540009900f520300c094030314014400011a80f006a83d004125441540c007012410803500800300e8018080c410b0840303616090008101052611810359164004c5211b8107229490204c001004d20071000b40e4113a1024103510b40c80d0352244c40e50f8015215420115040301540510400203900040010b9407560136070440e1160340100006000652071640040340080855409008503010417109009050040d5030100000c500c1e480c0c01c0071019102c1c60180d0010200c6c6032441c090000450b0050801030640d00c1c541404118641e40c2c694000341000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 76601350 1250 76600100 76600127
    0x90f010e01032307110607050a05070c1d1801020909010302060706090b09030307021b010206130c15080108060903070f03080901180602070b0106110c0112090804080607110a0c090903 80
    0x201010410f1421018401c0068811300341502d501180001c002e04043e6508422070f0a04c01040081000d005038074001c03805040010b103d585402d2510352600c298920207810520b1802880448100f482402a03070f500d8400074070060ad030002c41c24014911f000425441040c44080c0c0119800140101405a203401620310581c00c5000121541015142030b0355a9004030350b81c1c0018017489035600403030b80381e103200c0c2011404160300604a54841c0058407025403140c81040b00d0044204d10300249000c101c0002c51003e0341c1d96150b07010550b00d010381003810303c1001051a129604100110000a501a07040c006200e81500d48081103a407500603c03401000f5150102d401500350300003010070005550010072000d0300c52000342500e030343e071160299204140303002c08031001d4000260006603544100c8001461184200b0046101c61007903ca03004c8552042d003204e0161741103a010004040c0c0c11420708250b80007007000500181d510f90f1182168562540210041c46032105912414140328103401040721 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 76602600 1250 76601350 76601381
    0xa03031e06030503030103060f1407121b050901090f032303070506011205010c03060612020d021308030903060709060801030210120509010213050a0302090c03090f010c090515090f010e0103 83
    0x2980302c3c202503079650001d11044075000d0601442c0300b42080035004e8107002c1c1d0004407442d00e01e5203c1c058180c4101c0aa0b100e104075495945404040103c49088414000700e0303ea124076a80d60500c0c0c00044c0420303201d030051411844c621001300006540c07524090b20b0030304450322080d1215154042141184204000985180b06190001c600211052074000a9a100380020068610180710550981e0458490303030002c5104201080c0307080b010740d0001c22084001075801841c110700102c1c400108503598100285a83c000302d1112000d080410400360007103c6414200d8100e450104010310040050000030700a110494100702140e00821050701c519603d00d00c1442189000e05056000390001c503951035004842c980d0010341ca0a10645000591780c02408150166a03642540c10443d44083c1042410348152100f000010b6400e120340117980b2400c1e540c2034001840c2408004003500b2442c5400c0790720f0010040800180c1da0b01e84007200140081c240004441c45010040c0d000f06414580d0f050903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 76603850 1250 76602600 76602611
    0x30904020c10110d1b080a180212030904050705041203050a030905010c0c05060a111207110307050f0c09070e0f0a0b130e010806060d0f05030d0906051015020a03031e 73
    0x2400083c0546103520300c40008000303944100742030a0700c00701e1407151200400c040f000429007032041078022100d0900f089004841201d866400f0403602000e0b409000070b00d810102d9084100c0c44d0034068a50482440d00c2d01c603042c203040207040441307064030f000001c00744000000c0c00c4200754000d4010140b0340e43c00c0030003001a8501a07030080c2c002015038104451901070017000801e0f40805100e00144986910f19403420b100b01c0d50703005c0c460144060400401d0005809000450034810001440c985100e20090965913a14001e0070346000211820b00303100f00e1120041001003644400c100011031402c0f00c11041441a031400300e036402d0040d4102c40104100003072210f404000c2c00795410100d40c1c049418015036a660032000e41c4408050f07038220382c0300075407e0841005c10040c809000c9041d00980a5030300c3c4c00d12101e608800c9480c0410100c1e12291103004100e030031000440d00d0320060040303115101d80307803001210081d21b9031400c1c507000f006e240c1d07112103000640084240641c800050722004000c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 76605100 1250 76603850 76603871
    0x222060b0307031a09010b07020d0c050a18060e0105010503070c0c050a09020a020f061e0703140f1503060601050406030f0605060406170a0e060601030902010507020d0c14010c05030904020c10 84
    0x7406000703d2113020604807444204d010700b01242017034121260840c0e201d051003001e17401c000c03d2035200142550210682c25000c1101c1c0e0340c00c41c90800400c0300c900800004001c141d50403080c0d460b01c3c3d20540007080d04600410103641c21504590b800035261428078000c3e0a2860040c3e4604220303041035802012807500441d08a0595008002032001034003103c149410340e80d0032a6a541085a0041d0742d511800d070390090014076840c0d940c0e0421203038200881c403401445100402c0303007400c0b01ea08a040b00b00381c0a00102e0803980718502494901500a400285021400604244528401c420030580e46520008410b40c1d10350050b8090a40180001da880d81e403411b000b00000641d0444242c1c04442d413002c1024074014bc402c03014418219005402560b84240040d0028213114106906103c8100070500060b5038644003401c0e140d2040d80141d0b5800c0c1070100001440b8000324407039043c17010466000f0045107000045d01d50300c210445003d0313502c1405048940c00c10141e100500c1c00e140c1400c0d090030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 76606350 1250 76605100 76605107
    0x4081e030a060b03061e060c3009011e020703020a0803070507050d120c030e130e0c0102030f030f130807110102010b0402090607020103320f0f01030222060b0307 71
    0x6004020384038041c454603840f0400403a80e07120681d051640310341a030241030302501d82d4200c484880c0300c004151034100041c0000040c00c0066000f0090b13440d45c840395028803035030030b6001c5404842081034801401d1225110028012114010310098210504001450303103610811030080516400381841142ea40c6d1409019a290030003d403c89050003003507404a024100310011055641e00701341d00402d460b6035590b05032079840c03d0032802e40401c00310748a448a2500e030b06807400600740c8111400034482c030b001c0070f40a0a203040038441c54115041044803d022184480a480d00700b07520728100d10f41511744401c44801c80340d5403c0000d21400000c601c150a00030007400d0741990000a0f0020702c41800010100700c120b02c00c4c240342c580d11460034001007002d54801d82c01240643c444003c11401c0e1030020507040c0382003020060400c1c900f920b11040150800030510220303005465845295541d5045a0010700300e90420208004000c0002410000c02902c1e604910001d020b00c40120f980c07401c0102004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 76607600 1250 76606350 76606357
    0xc080f060f01060e030304030f0314030c1c020f0d181b08070f050a0603051503010f020702030c15070305031b0a0804110d0308060d110402040b070b0108120702010804081e 75
    0x114550241e20700005051806500504103440e0018051841d00307085581d9140d284c004804180c0070400352080410700914550011406800a82009522101200aa00c0c040702401c02e4602c1458014400d45580071660800e484540325140d40c0403400ca0240704042c2d142c9003054002800c01403160350b01600e400c14146109054032080c8096889558891404803800b100911999401c8504104100226842503200c9030b040317103e46258843c40301c0500c0010f425603080201c0d6681166001071404218a01042500d002c9041030744c16940030580c00d0b948100c1ca0041405c041d040c440c4c0003000900f08081100c0300d802914980e140c45844900420008010202c00c590883e83c0c1c90444c8215070403454800003800046030306a07074041c81590784405011b010180f020302200c1c5201c04107600c021555441c0058805401010082921600b003400c1c9020760b01410390003c002c0e5045107240343c11899941048036403194081c0bd00c0191915580340041c03840c4144100c4120721209070a540103070b840c8001c0213 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 76608850 1250 76607600 76607611
    0x6060305090d0e0d0303090320030310060c0804060e03240f0c03130219030206031905060a030503040e040c030b0f070e010906090e090a0503040f03120504050f0103090c080f06 77
    0x1c4034202142d900c42640c0c012034103104a548002010f02d41c0000070b120703030403809038240f2070314003001c100c1c2c00a40010301004d150100c81c000d03600301008001c001d020544500b40140340c0c0d403801e401001c5084d11808924800c03801488c041041d0303409800101e80303080029120418240260004c00440c1c41d410000c0c0030400e40d01444500108d401043d541124801580c2c006c518400300b5880e510020b0f401c0080c4401030711045a0344000f80c120002c0545c1e55036002c1d510405425407924020490214040d045407030060900d0300c11005001d080c000701e800041a1800e5511b4111401026110340c1801029100d9550004100c0800001007000c03400340452000c0c040c401544605400361848001034802180d075015810004545820800030703a0510b80e20150025245030a88001c5103403a1110b0f4110380c070540001103808843d000800801443c0c86070200542d51a10308581040c0c18800001d080c0009154035604250f11207003e9801d00682c85200402060b00b10103c80001043e200450340710300d406c41c0d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 76610100 1250 76608850 76608853
    0x102090312040303020105131112011d01020c060c031603020a020c0a03050f060a021c09021203040815010602030a0e120f100914010b010e060d02070f1505180705040c02030c010606030509 82
    0x210f000502c1c01e100108510ba8420300401981b80c0311014001020010741080c0007540d21242c03981c40c8044401d4cd13140303c3e070301110000359407180c0380c0301c0b214680303900074080b40503000080041001014460604852744d224510300075940b843c044008929046180b40141d50101c00c0b60000010060000388203c18081a101611701a90310b820001c4100e018180001600e20a64100076039844602d0307100203942480140000d003040b5030304032601e165800540100304a5805880d01c0b031442d120035002c1900404840c4021860170756010740c001d181048907007602d4010803450b1004010044d05018034820381401100300e403a0400500078803c090010290240c5000e080c1403440f005008040c0101c000d00001038480b5925030110909000d565449003660000c1190f0074490603001441c0c030b90110300844d002e10102900b980412035010100c0b01c024164983e0b44000706c80903079444101081e500b0407290101c500007281040c0010580c01c40c0308001607421194601500400c8054244d448140102502c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 76611350 1250 76610100 76610111
    0x1e010b0a03050f0702030d0e0703140c0109120507231f0f0c020d031b080307020604060b030102090f10170c131a040306020f0c0609011d0a0b01030602070501020903120403030201 78
    0x181c0e032120020545584e00182c104003d01100c1d40c40c95005003034032111042c1152200d07541c940307032800c091211000304103003900451101c4402c0d41c2e20148050161120620280c0f8411280e62180c0d910a2248140301005484243d940e0381c4000c14440c055242c94041c0c1148074966400c0840035088500c1c4a10401192000e20725481d214482d03903161090039805031803201e80d094280c0b03003525a51268044111098450f18035840054030400c0a580145220340040000d401d162074900f058030424151907010360301c140158005130740c0c0c0c00c071501d203860819144c00d4540c40d071076481203c1105000280964101108051140c0c8414100091210120080c0710766055521000c06a40800051026900e07807041480140045aa298018404010b0810300285001e080070b1400e42420b600302d80b5510942d640700d221040510804049030401e010700d00141040f0a1256259402d0030302c103001c0a40303010b6002c03500b64100f040c01d5044500604d40101110700700046034500e10019440741c00214011350074003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 76612600 1250 76611350 76611361
    0x71725180b0408030304150608070605090a050913020f060d1a10090e0c0901050d0603051e071220041404031806140d240815010b121e010b0a0305 64
    0xa00070b6405541c04a4060351039506c8684540d0f0f104802403d05014240e524030700007034002002c02018008064035141d00c0c0d00d0b40c00500420140c2d1595620042c081e140340c60400191030409601213136001d0b411202e081d44015208007181c41405222054002b0724501001981e80c07200d0341458008031442181d056000c043c4184049a0f00b01c0b4a2250340c2241c295100803c030346d00c0c005005072841c81410301d055801e020a04518030243d07580c0758000c6d189508024010b0100343d0091011441c00c01c4040010200761307240c181c060f610801c40c2400a0181e40041c018140305410604c224801c00000805c180001d440d111880e40640034150390490200e0075100383e180c80401d8059030401101d840b80c0302c0314a10009850042c0c2c0a030700554940308090b5440a005c40f640c4803c4050f144000000c003081100749090250543c9014202c030301d5106032051210040052950240490f4803a01d4400842035050300c44104064001342d03803106800c0143c41600c0042088082c4d0300241c15580c1855400380b01a4540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 76613850 1250 76612600 76612619
    0x501140901090c050f010c0210020a150b01081303020718020c06040501290d0b060d06050109021804050408030a021e0f13051207030b0903041e0312020607172518 71
    0x11498658046046030700c40c8000b520b8043c009d81100b0b00a40141c515210451343c1385001c40d650980b0841550783e40f4843d012055900c4545a41e2104001e50b0b0b001080e061b648010350342d60680e2041c0e60584c14640181058403d0301c3d0184c580e18038620080310b4076401c051401c00e011f010301c0100b140d89441003680442c0d110418200003242c2e158040c02100b003194440c2c880a94603400102401e41104d001c00f41140000c10a2003294002c00c9009001a2901c04200c80103540c0650f0142c0705110740e04050900020490141c21a90856246403005a9500342c6c10b1840c003040d400a10206050800850340034407000da000010a490071000380f1298202e626003080140c900c40f07514020190380e114201c140009100742240700e400151100490741016039031710001c80d04404e0540803c080000300c0300b04104208031005104100d04a6001505030341c6003444000f4118842141000d40b041c180c14086161000e003082e400075050020410848501c00c20320010300506c02d02c1196021400000d00c000480d00d01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 76615100 1250 76613850 76613869
    0x151e0615080f0109020d0e0a03080117030c100216080d060302041506050910030e012a08091908040b0d0203040203060702060112030809010b030f0709050702010209010f05070501140901090c05 84
    0x204016942e4a13420481154000c1d0403494061303002c10b90302c1c224156000340411000b2404c91203650303400300c2c40d81440104e50705a040486028425841400100914100840c0074982104620b17001a1070355015000c1804440d2940340262550a000440f0a10340b10640c007c281070302d00989050205903154601c1481502c0544034002c00684140504da81c01c0c40e00021810388101945404200f40700c2030a20700b0708503601d207524514803038002c10420410200003114030700311032600c2c2003040035880c000f151103484000c0c03a074941a000311540c403201c041100c8078040d20094040e076501c1603102d0f61052040300081d801502d081e442442044002081c203031000030885d050300c088124281440c0384a99041c3c42c2e403603000c0c2000409548620f80d6a49030749080200100c1c0303c0d0300500511080e0b01e40440c1c20102c07603001d4003000c01c40e4010040b0303c440c0c6e604188501c0c8400c080d881c216640d41004c0c00e0260051100e001003602c800620010f110302044150054032100340100812584107595808200c0082c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 76616350 1250 76615100 76615111
    0xc12060a15230a0903050615030a02060309030c070632040b0f161b090b010509090a0f151802070b060f010c0501050705070309050306040f151e061508 66
    0x34520150041298850007002d104650101d54025203444030104820450f00806144000915481010020710404001d03031a005000d11010b105180080004280c079401c40300d8019000d40310020215076100c8017041210081103a0a0a96040a448580080410504144680304410354819075400d200d141003c461a01103941186458180740c403458404a410040980000c10024001c0d10080072010194011040c4109009101e0584486038041f05403401d4100ca24003910f000042455a6040303030031201d1440040780c03501099510700f2442c90142004900c0c8011281c140805c03000d0030742d2008c0054050300d040b04049400c500000744504102e0240c0d48010f441642080c000c18130350308040c00c40e400701203010716094107403402c542c0740e1509450042d100c48c00001c00c0083d054043c542e0114069010b8582200940b0035820a611062808540d059010342078a40700208840d428105d03a104d01003c0c1822000700303d41091842c40d00f40104405d04c60105106045840520150301c2000b03520300c40c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 76617600 1250 76616350 76616369
    0x3090709050606070b090d08091c031a041a01030501060311091002030c060c0301050f0d0203060403030b040e070b030a0506030106031a1003020d080c0106090203070c020111070e0c12060a 82
    0x4928015110000d480c01a100c90b4003c5400c000440200360361140d15480303107900310024440c09002c1c00c0c009003107460080c003069a0350007106030310b01902c01c0c80c02c1540d050130320703880c01080000c0c01700c0c191452441a03140c02c0d64400e2600d000c1403211015030a01844076070098070200301c4e40c0c0e69182c05a003075941c0641c2d142515170741044a4242c81c17a0012800000e91450310480e030828245041c030a1400c42c054612250464012004201d5440c0004040038810420384100d8503c41c40c0c1e42c0070950340d000140005040c140c840c11681607540b656844204503042c2d400448101c1540d42c6a0407200f54000d89000d91030908180001d885820305000390812a030340a001c654030300c204400600c0107842d005c1c00391106000d01050000140e5540c10444130303058021309515036a000303003a40c1c0c142140d071268023280300070303006204000b8459045038001c4a507039020700307049014003801500036007001500c1e006401900406428407030401800800352002044540715000c5e9520707040100302000c40d0b2840b401c1c021 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 76618706 1106 76617600 76617613
    0x1b0b0408071404020f0412050c100c0302010b040b060304030f0e0402040308090111070b090d080705010509061008030c06070e03030d14100501170a05071e0e0a09020309 74
    0x10214220343c114682140000002e40a01a51060151401168990700180030003071200004404004220040071205504041c080c820000401d070010342c6002191502801d0500c03580410182c000e0902d41150369595088a04036140c004880c100318451004035000d4446001400c0911310030202951036841c8040010402c05c015410240164000d610400110855404a80c01c10300155000840e6500f9420318038120300c51031500402561030b1400300302c1e02a801183e000d010782000201300c0082c07a51800c0707041d03403070290110241c440d412400201d02c44d1400380605009181c0c002e0103a070308004200b1000412180e21000d10845201c41d2020000d801e0340544050014080c02d0130120b0041d515151249011607000702884101940c8001140e80640160b00e09d2080041d4400b1518415000e5074000389040c40003c01d56000f685a0030010800c445076009a900c07031502c030b10050a0303 = true := by decide +kernel

theorem cover : BRFrame.Cov 76438850 76618706 := by
  have h0 := BRFrame.cov_init 76438850
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76438850 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 76438850 ≤ n) (h2 : n < 76618706) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
