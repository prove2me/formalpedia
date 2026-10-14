-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2376
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:31:40.896588+00:00
-- url     : https://prove2.me/submissions/8e4c838c-909a-4806-b6c1-e0bd423052e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 427158273 ≤ n < 427338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 427159523 1250 427158273 427158311
    0xd1b05090c07060f1e051015020f0601061b030c060b04110901020c0f03070e090f0613050d02030a082208180f150a18050d1103190809040908040305010f 67
    0x70451030203103031840c517a11103a000d02071200400403580300820607882d07041380c00c1c040d09900c0d8014440240030002c4554200c0d000318406002c20a19016170351180e82c0c0341d806403020080036501c415035001d4110542c000030b008030301c41e084460142c10700003900d80e280c00206003154003040d031810100a000c258158250390411814650b124240c502c0810b042525012a5985401e4010300c80601c54030070005081d100c0800c800e0443c6e42050044405500700f034402050804111032003038410b03000320030050494a00000840d00c81542c00e65851056640e03040e81d840d0b0303540e2030009442403500b038000c0c6500441c4030030015040000681210742d440042c10010800000f002401e05402141404691640d0138041c005452064400b4241408007c03d83c00d002c1c12060880c2c1c0040307030300c032178003103042c00500500d02c0f8282c02030301c0168200d0b07420040c018045d031621880d000000307045038020003c41e951400c0907080340c2d420510035445541080d45a41d1a0390130f5480705038121080543d10042600100400c1c03007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 427160773 1250 427159523 427159541
    0x30321230a060e0c09040e010204170d030203090601270603081c06030206030f04020613031113020c0c011d0301230117030d0c1b031206140d1b05090c0706 68
    0x30701080355901d098440e0342d4040c40180441500d120120b100301c07082d01c80e0342010001082c075200865a50b03490307150140901340e4107d52000300d4894403a0341c1d1590342c028403c4034090701c1041d00501d0780381e02c0c0c1040c8043c0160304075055280c40301d40c411011305018290141e50702551181c1941a1a5000c0201c1401040401203c2d24001400c149003040580c40724030840ba0400141c18210000d684c1d180042100c1d84120b881c45c0c03504102c804000002c0c06040c42100400400c101c07290780007841c80d481008145c0c0203c503081401d0f50020300201c881c40d03004d8074444043d24414007440c1d21042c07030040000d003121101c100d080f03040c40810303032150000e00f0411280c5014100c403005068420003071141480d50ba000c1c4560364080640c0e582d40c6808164000c0b0341072004144162415030120040c0c1c600100801307154440d00e40854100740000c145201c481494040e41c000207084e40d021904561904d0355070080c0300166117821001c00314041801d88850304494421100800c01503070b00d80c40e40c6840801c42c1e1140e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 427162023 1250 427160773 427160791
    0x50f010306060c0b130506010605091008070f081b0c01200a0503010605091c060207050d0801050303070b180327040b0108010524030921040506030103032123 69
    0x200c0c1440000d410103c210352443c0c111100d07105664484410303400c000b22011019000d403040034000910f203984900208030001040c0c40c0c0102e5040302010560328940156200004201e00e10525502688100307407083e400000303581c2c0850039200d0b22803501c0c140d52003007205006c00d0351a810490744a0705030646205006401c1c0a10380e04c3d0201f1020010003a02044c0a04020000c0004e60807120781d0f1840e040300001101c2c2e2203d0740150b040c902e0868020760125104803480e010340d0501800090241000d28100e58016000c0d5140124903a200307841c0782c0000300344407500c3e6642e040c290804401003014041442c21214042500e4820580141c00444000d410900c698101200304000c0e0b64406003c0e030441c1c2c0141c03290906d2500707900e084c0d00e1285004e06955844c403004020040f4000000460700c03415a42490240a42080081440d07028840c0340103144e0040000c0004000183c45101c180080c4d1090848640400c0c081d1845281a1807030004030402035001145500110028850300f0758010081c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 427163273 1250 427162023 427162031
    0x10503070f060f020106080715230f0d06030b01030f0311190204180501050f060a2108032a040f051c1106090414040606150c020d0201140a0207050f0103 67
    0x21600003456041d03140180340420029043d4039240d14001d40040c0c3c05417601105403003c1ca5200e2024004c0f11300e15032030b1a00083c03404100801820310031030060100c02c20a0303107082d1030501e01d950200304680c05040004a0180c0d1458000301050f020500710f4042c0d48501c80307030300410501d8180200030076048518040103400c0310101d0b102d4150f071031600040a0307030305480124032541e080c990707242201c418003030140c019401d040400550040c101a40703845080c08076940381c3c2c03039600c0b09240388000402c007500c044207080c20307a00705002c91550005540c0c0121000d481110300c94909400700c003400c015969000d10400085020301c503d1113603270340c014043c00042c0c0744140d1141103c90000c003403048000000c0d04040440c1d1800d00c840c0c5072902103070801d0f503018209020044d1601c1d42c545c1d98040803982910744500e0b09a001c2906000b59468809840542c1c0e04c00080103010740800110000c103207412814001c6002d40c1c1c140301d101c40c02c09017251030043c0c1c01905034149030505004100c44400d20250401d031074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 427164523 1250 427163273 427163279
    0x910080601050108071716110c01020a0813120b040201121413050309040207030509040e03210c1b0307030305250302090a0b0408060a0609020f091e1e030601050307 72
    0x100084581c11240246041c0106407203111003955581143e240d0744000b2900781d010400c41d41148181c0e400088010f9498010b0880d04401c80c54440ca00f4408190060b040640d010012500c0540a0203a041141c401700001598613251b207152000d9410048600300442c00812065681000300c040c44407407008024816141e802c0c0d00c0ea01d140701c0080c50282c82014010b88101404810800e17680c42880c042c10466890855060140440d00844403041c0700c0e6043c0003865000000c0030069800c050415000c500c40c80350704000d2001c00d60300052182d58808010320421803000c42044c114108640c41c507000d195100c0e5513041c020140c52005044d4201d20002c1d200603400d010950303202030503011507803400684800c01c000001e512100182e100341e421481c0400c01048212001c42c1650041d48403800c204184c0c1e503105034a0040e400381d290413480301c030f106000c008070604250320241000e10940c440b00800010820000f041000701c0c0d03a804038080704a0316100c01c1402c0411003e80506811001000d078945 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 427165773 1250 427164523 427164539
    0x506100b0313081b1f1d1e0c09040f051504050303060d020307030b040302061f083304050d020706080613150f06020c09060d0203060103080a0e03070b090910 69
    0x12282c5001441d00c000010b200c0040c1442014000124503070200360351a0341021a80d0002d19622a031906401524080b4252104480d10b485030007282454405440300f24030b50920303038100500e900c1c40d10400d4040e80c60541c40b90f90303d00018621481c8a074511241c103958a0070000e1519041340c100700b0302402e4603410300000c103c0010540e9030200044400722181000d61010904020b41a40010070b60080320041c0010141c010034024880c0725a5003641c3d413802ea0607070366001181ca052048030f09540044820400703008036500403884011245a5520990001084104c00c60744100d0301603a4a0700a0b000c03060380c00e6410b00820000741034600d4200c415007405000030b8030140c008115031004c5503032001700c420000c0582c1082c5006017402d081c490b030704680d1000040d46410300c3d07809051003048110300040d0b4502d003040c94a807040390003031f0040a86a00716a0740d210564080502542481031032840c0c4e8a00d59020007079407010f040f010384403d4035031003004280202d410000e001e55011030603c0710103020203c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 427167023 1250 427165773 427165801
    0x30921020703170408060405030c0609070b0405040f021c0f0507030b06030c071403030403030b0f150304061d070f141203070b04060f0e0a0506090627030d090506100b03 74
    0x2ea000001d01c40c0c01103440440c2c100c0d502c580c1c1d205c1d40c1c00f80645410070080c0880030014000c030b01c0186c0c00369005542c0b400c0c2c02d540c071804c990140802c2e41c8402c0c00113100600340b40e0720a04035000642c1c80140b410440103400c13070020302e09202e01544552100d455000c002d207140282e41c1c1040b224241880b1210440700001c05501000306040c81803140450040305024030340b4000c8610700d00003000d0b20703900d082909004014040050b54a4003800c1c21010006103403c0c224180702000882c44c4150b400c41d01d46035600d8014100c0500d08550b080801840b600406d502840580b00909881843e406e00034a400d1750194502d01003815984540c2d0700300250000c0340b802004070703442c0c81e51114000000f42c4e218035009000b480000c0d82d403540280303045403c0a58083c00918600c0e0540200100c458560390b800b10b035a0360b00c1c42154801030108021704d40b10b2280f0010300208011281d00d1050328242582100c200d0100c03100e040f800da80c3c5038045003d11090102c401f02040151030010b003141e18503c5c00c0600c03c6604 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 427168273 1250 427167023 427167029
    0x6010c02151c0c050a11070b04030b090106080601050d0f0201020c092a070305090d0609060204090506040e060921090405040c050a0909031b0318080c100215012d060309210207 77
    0x4020b46c141031500c50142032100030054490018650340307407034a03400c202215800c21070710600507618014021461004c0002c80d80e0480314014001903010200382d0301c0442c0c0810b0024200d040d0b2240c041e020131181c4c1c40e11750040c0308603421a118194403450540d0403590100381140400030342420002c81020983c0300c011281004801c1e9401880d8040c14501b000003041101c2c80604410b10100d40481c99509035007260b80185411a0140070240319a2442074490300103460981c415444000100a800c8003002c0707800c2d10390345100480f42800d0030000401c00703a8004072021100d080c1c00c04007e110510700b003201840900f03013041c2e003000020300e41e9401801d054081c000015021074002e00d40b0080500ca003d200030400c81c60b0500045080e620400256500080140035108100603407814004910024141d0040d480c0d2007011003c0780d180c00c60700b0509195040d09042c120080d401100c01c170340c4d03005400790b004082958002411401608190260604200202074148002440c4948885c0d00203560029 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 427169523 1250 427168273 427168277
    0x3201c0e090912030c13180509060f010e070320070302070e0f0a0b0f0301140603010c05070b2d01080604050712050c0f01120f0203190b0102100506010c02151c0c050a 73
    0x620345640320840c615004014007400c0c002d140d1640492900400c50074010400240c1f030040c00b440d21110190360301c40d54200c0702810204c40b2000104180000d41d1000d03604065a4103002401c1038190011611404088005c0d10036084001011802c26031304110600043c11000c550000c0e504003510b54003022007016015030300240d19004907031890350b180c043c40302c40c40100030000c00403640c00c2d03106010100f01c11100355219500c0d2141564070540160116402e460780034000000c3e5540d884140b0040d04401ba0340410740c0c6d804500c511000c968405036290203800000f0080866260514003646801850341000171401c0441d40400e0009600007900707080110100c9206410b80072001c01202c120f034039490f00411050600e103a42c60240915801180107a01000503291906400850b05080d20042000140183c1c04144c0c0788800300703a1641301e50303040141490100310103910b9800007840d1400000b40700745200400180d001d0401105000380c1e511141d242001d208041200c0c0c0050668014a030107041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 427170773 1250 427169523 427169527
    0xc03032a030703090c060305090703060504170f0d1107020906091306021801020f0c10050a03060315050f09161a0d1814060606040303201c0e090912 65
    0x8618009512200055040a035056141d14040c90010040e040709202a80c502004900c00310303c10344240030b203902c5400001c0007004045d265664080040400800946100c0d40b00d58031164034200d458000e05018146041d0903860798400c00c1880c00710360030341c4025240500200844001602c800c100240e00c120103c42c00682661482141d0180040c0c03030740000e10951000130030802e01e0700c2d294062001c41e00207038211101e001c1911800d655a10f00d40f100e90360302c90520314a8100740ca20400050040c04058a0081551070340c0e60b076104c0c0c80c01d00880010544546403410014541002d4070742c00e9000907010010072480c20000d24074801041180074807000524100c2d0511500010b240450300d04505a41041040344d105031044001d0174070a8808841e8410031800445101c1000100c403030240200808441ca42895a92300b40d40c07902515158440852a0030b001a59002d0280702c061700c200702e5400c5000c40b0844589004018010802c20640700303403401c0092014000d800100c8910980b0302c00c070056 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 427172023 1250 427170773 427170811
    0x712060b01030209040e0102031b1606050601050408100209011403060d0206161e02010f0203040b12070c120804031103041a03070314090c0a1a030420040609021804020c0303 76
    0x2c001e48503e130a626086814911040c1e40350905500a610940f07603107410310403450300c0000006052084003d140540d05110702d4020120b50198401c1d500014141005490a82c0ea060500e0511a100c0d0507042c0013580481e0041c038558100b000c500000e8100d15042c2e2a41c644080065048104107c029000b4240410880615200d80d01c01c2d41d80305800186c00c4042507211100340041c4242c0110072800103200c01e0117555254000003c2d80c080c1d9804d01c00e580c3c14801a4120b8030903c00001b880202000743d004084408142341011014038541c03075a40c0c0000c1c91420b8180030788044412010f2034685e40c81004204500029548030b0f10186c02402d44c80d42d92030f210002d044001e45031009200c1d100c04508828018030000019a15441a0703098602c000500c0d641c0041b15165007400780352208004041000070000340c44c3c00c0c1c42c40c070300c100c400365100002c500945c085400c417031041e0446c1c2a0a036002802040e00d00008a01e05a483c60403a019407610072042d06660b143c0c0030150501e510405084006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 427173273 1250 427172023 427172027
    0x10e01050a0f0e131b1e0e0310051e160507021507050111040806060307030c12140f100e1b090a0b04050f060907020a03052b0c0e120712060b01 63
    0x2010484001304485032082c40030b0341c4c21005001e000305c40303040607200c0142ca443c03080c00345a400404032004040240c1b208030708030302507402c0b5005420003541401201160300c8000c10512682c2c1c000c020030301e007002c41c4507945100f000440402a0030301c900704226610302c61082da030120489401c5d59066803095050035910002e84114000c8440041181d400c2c030303004845600340303003010300200ca00d4001154a40d0300e40000b815214203280c0000790550410200c28170006202e860700001061043c600013030a411103080e02400d01c80211111030458114031001c48402c0101d002c0d0a07030400c2c8400240200c0e1080511020003011511201c0d03028034204000508a0801640802884c2801900c00d00c0503141c01405104a0304044035024031408544000c904010310000300c4810319941919001e00d40080b22a40509131401001c032081c4209809010b42c10f00206030203040358940d03031a15042c2640203500104030075041c3c1c03062005c40301c0e4413050007040031482c24081d001086400590009444100f8401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 427174523 1250 427173273 427173287
    0x120810180e070512060f181b0d020306010e071808060604150306021204031215140303250203061623093a110f010207180c0e010e01050a0f 61
    0x1e43c4d8480f28101c415581c08202007603c070300c0382040440548180d41e660041400302c155609214000f03034020100b0302c0c1688420a42900001d4000784070b40749440080c0d000a02c0c5c52070903001030501855000c01e218000f504400c3c40b00c104000c0d12038003032900f81000802035981030004c12482c8155221103402c0c000340d401555640265402110556480300d81d040c0b00b41144806860460001d01d003524841e0038503a0b01c0c89440d055441f641c12807840c0c9071400806080349104504000da16000800c01c18004118025054085106031081d41c1400e02c2140105818504010404030a00100e4407504140c03030f903c0200e5810300e0f01c00201c428421317007030520178042c940681000250400340003205600e41c3c002c0184403040524400c040200100c8400c001c00c902e40c4402140101b01c0800084a0300282c80c12480865402c40c041c4102d51344156100409000c41d28a2864003203036a0b5203103e152000c1394054100035030218203007001403e6280d050002441c9100ba8159441044422080241c1c80d5210f114 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 427175773 1250 427174523 427174529
    0x105060d1110180e011e0303051c021b0604051b01142818060e0d0311010906110c0c040614060d060911040602010b040b0901050d1707120810180e07 65
    0xc040c14103a07103501ea13155511000380508101e0305040310306500d58560040406098951507a200d900b4910b507203c0c0300c1c2d50965042068491290203005058080c0c240b91203020180c207812004000300e00302802c0c51801c000660b080000c50302140710340950107980101807410350310204090342da27481d032704100c60b1140309420307590150b45d14200354140822254000da880e0088074400342410701103a560070041e5003509048a0641c0c018401d2600040031038000c10310040c0140101002080d0403c050365107030203c55007a1103c6240356000f00300f08440758000c1001c562004000d071000c1000c035003441c161801c0b1404541e00c1a01c107442c001600c000e0013543c0d030013940080c20700e840c092010310b00310480c00b80d50b904140034200c0103600c1c2410105041c0347c1070042d40030424002e054041c1a134201001d0040c24884600c0a80d9409105184214241c41140c01041c0003401400354012188200c1c0000f0a912800b41000140c840307020f9003400450b00741c0d00e094450308990480052240e00025500c1d0400707041d94 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 427177023 1250 427175773 427175807
    0xa0b07110303340914040f020307081b040501020601050d03020c041506121a0f06040b121b0c120c0705030f06011719021909020705010e0105060d1110 66
    0x120a1094000202d1048125086202c40540910401020b88030500c1d01d44250070000075020342c0304011107107401800301100038010f40b0108044040142820070383e442a220ad40000780002c0400c100b01040c540c80e00c9100003022601440c151400740000c0d9108810b0045c0c41c071500c0240f1203002018000c04c0300a1400c0d00c060028454020b070490907151091942c0709000c045522000002c29680c2030b03210307682c101440720080c80d0031266080280500440040401a00306400300000310320040700c40041c00450001a80002d81b40c6899803003000101d92501482031103450921441d02d59080108552020b0144642c0303050300d804940006030300d031503896480282c05018021012241c058045051410782d00440300b40c2035810340750843d2f282d0f10042004403110300e1104c00303805001072610f0185101402050400300b0b0503d5202c15094040768400c0c4021241d0369558800b61404040070b008041d0700110485501c0c560381c0d05034a42c44c044524440c0300c540b14892004400841502070940c2101c4c803e004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 427178273 1250 427177023 427177027
    0xe040c02071e06080c09041508011a040603050318030705100302190f0504030b0c09060307020d1103090a18111c15270b030d1d0603090a0b071103 64
    0x805020352240020b001d00320100c0403241c80301d14201c10301850541100e905549402d9281c0e1078a05200654000116070b59000b52035000703001100342c0791162003020780742c003c000140206801c40032a1507000021181c0b80240c0c1090020004984048240c1d00300320b8050b09070210060102c4000fa06040b0545c202d20703800b40308a07114081a907819030260546100d21440d1a80b071103184c800030348002c0c0601404000068081105100043d05c20044a4122119065580c01c0c51708900005803075400c1129540016408000411443ca42c8060f04110181000010310300d05012107000c5a40c980e107502070090720304452001e9290800040c0d01c0550381c41c540404054403080c020b11300c580d01f4001800e10b51951410038494407030307132800c02441c081151031651034a61002142d01c4003082c2114014030784443d07250b55202d0f5101544007800510708410f03040c0c1c1e840f91090b400910302411401e244402500500c0280108000301c0d20019054203c6034000340d9810701907840341400c41d29240d540b49451864040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 427179523 1250 427178273 427178291
    0x8371b0902040501080901060e062b031e08070509100e040203040b1e01080d030509011d0106081e0a02220f0b040c030203040506160903050615010f1403160e04 70
    0x3650340940143e034000d036240c20464403240003c038261440c5000f28141c048500c1d010500780c0c602600710606840d0001d800c0294280c5022465248000707801c402e402041246039141409031002404048044007800c08456034148180700803c18061400c20600640c00b400d000ca0b60030740038042200350094014820742d902e150034604042c195000b80e0760090700b44907815501c2c1c2030b403000b122003a050302e168074014a40204074101c200c2c00781002501201a9561321513007a8080f040c00d81c01703602c81c0b2203210300209000b4602101c0a20780080700d408000181c11390f020520a000b0003240e40920150102c56043c0f02c1d00c8260101103040301001c401c001914688160083d81c62030316008a170304010308071802c02c94025050015010392004590081258002d41c0001d1020f06081c410004220481d10b444034000c2e031655210303440c14000741c0d06864180704c0d11103200400e692088841c0001c0003545405d050402d4070b40e1980c00d00d8007000e041400c1c500c1301c06400d005c800c2c4c4070b9041c1040e6202d006200f8000490 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 427180773 1250 427179523 427179539
    0x60c09032b020d0c0f080f070624380c0601031b0501050304030c061d010c05040503070f0302010c110f0d0807020108011a0703080c0904050106020708371b 68
    0x181c41d681040260190107120341c246402142242c02c15504041521143d4440d5620030f2441c1d8001d100040c200c05007805980c0210b20a480780400e41d400100c41501c14026032280445180c506078002c000401c08500c01c1c0498880c00380080a19100d0f04a000da9400d003074402d81002c40c0505170b45401c00703119401c0008240314149060719144164500e80c8904103880300011076030b920086601801140c2d0b6911424002200c0341c0c403580074522001d1a01c50810314a83e00e440c2501c00c20b150500c005407000c00c0512244c90107210b007800408210400345410b40c0785a0011b04141980310380984120714018000f542900c0301c409010741600300902b00c0c2c0609010346400c003aa074100e50401da0008441c2d03800454900030390a80ea01c041400500c2d00b9052030119901110201001410340207410018403500c0700e2a01c450003401e0184c1601e0300038080766410042c1003880c24296102030791611003000345c036811801c046004034800110840030b10101490340d0500310400c0750b10202e550b80002d005840058600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 427182023 1250 427180773 427180843
    0x1308071505040302060a06090614010c0309030506070e0a0807030f080c0a0b040f060e012703050403060e0d0807170117030c1002090406140901140109030b090c010e12060c0903 77
    0x7906e4130104002041d202c0108904903030f01d6009120000d00c001540711401c4d80900c628041003882840c018200580f2550f8083c1172600c00e403403103008140a18010601460321200c00c00180c02510018a060743c03540d1140d02a280798003a0207459010b0000d030b0344c0b20554042c4141c2d20126040b40a029140c24a840c00d100e9444203110b0070303202d01e8035042033724141c1c5006001d07040710700c0707500140001c00c2c0000450745c0c406004111130440621104000000c000381d5140111001401228050b10340c28102110180011000a080008221121201540e00103010f14154150f490200d02d0001c50f600c011906403461251840d60780351172040640254400354103030002c22200d8410340e407e02025540e15078215240b00300194031b0380e0182442005000300e1003104400c0b42c42141c14502050002c1d41c2c5c8d2101050746a0036140d40509422120b11607485e96040820130a04000030b4584250300b4141c6030010f612801d02400400d000c030340c00912603034079540400010280c100803030f55084030205940a03822281d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 427183273 1250 427182023 427182031
    0x804051006060c11030606090f0c0405040501170601052202030606070819022404060c1e05040f05010c02090406050a021c2c0304060509130c0309140105130807150504030206 76
    0x10104c40701000205007004102ea074007c0001034101025a12510a034440300c01d0f00500980c02100c1c240800291595540a0a07000300007003080c1d414103800b0440090b042200c16000b07103000e0700404a002c004124449440c14464640781302c0140c4903120f03400016083d110b5484054810030001c03400c0c650007100640d00c458000080e400312441c50020880c900409003506d0101c6840e1004000040e010540c0780e0030120804800d4901561404042c20500300182059a59400014800b1801b44810b5450240b40005400709081c843c403203104941c0092200e00c030040000b0300d0180c42c0c0c004907142d40b007aa015903c035410100500928020b05c40c64110080050708241c01c00798050310005602c0100e2051a0f00101200d000514a400c0c00c02109036020b070310044400350031402c15003860441d441a40b09034034654081d550042150411810306140b41058144000c980e6452b00051045441c1c11360108a0003d500a510300d468280c01d0400304145a0780c8101305d0b05480c1041c0030807042650203e140b501ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 427184523 1250 427183273 427183283
    0x715030f06050f10031d190b0604020712051c1a0a050d0c030f03022104080d0f0f0e15040303111501050a0302060306270a0b041103070804051006060c 66
    0x65442042101e2058a401d02d2a00b0a07403003081c1d2201c4034400c4d0001d20341c0014107401000f041d8100203160740780091201c0c1250f41d00c41c410047c941009801c140050304034100b100c0650401129480740c2a11050300d1115070240a00080c03081500c5940c2d000403a07100981000422449801d1070000b801ca00c503003103caa200d01c4069601084a10744050021805608030744080072480c15940c0b10001d810006500342c041d8401c59a210010a0009181c0749415040c2d102050702c45203028002c5203001400784006060046e13010840329900e83c072081070001c641c02c1c2c2c0740c200d880071036100200e407045021200d20700e5035001c0014088241034104496256040b580e10403034440d8070140d601c07100c00d800d00780196a485103c951080000d40b80001c040d68004500400c410822000ca84221904855002c00c419000580000f0006490290300c1f03407074050070055030705100000d07405800e10018440141418140003007400810709206042181540101d41141c04102060310f404020f41280710310002115 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 427185773 1250 427184523 427184531
    0x314010b0c0d03060317130305030a2006060306160905030f0703050712172110031b080715031103090a0c0f08030723011509060b0c0303040f03020715030f 68
    0xb040510910400c07040700d4201d03980c07404550513400c0980d000e80c81060f171821803006c0d8220100115400f40010485048507882c0c0c40484200a03d46405600e80700031030f001c254000104010300c1d610042005a07001c0d00313403620702034600b01c5041c00b5030760780741140c2009406205a0310030f21b03510400003130440700b41d0380201c0448802554511800708000c03040803000305001c07802a80e503000082003c001d80014800388800f1022408041d00c0200d2083c002c46800700f10100918080080c48400c46801d40c51080140820300b683d82030000380c0d035943c9683e08c500c028481d215041c00301103510aa0000c0c03282402008030b580e50342408005255901c0d928641038520f003170158000694030081011030412907011354061402e100d21903c030f14201034001c100d80d060741020b10703684c40903110080c0725000c1944074206602c007240b4200400642116981d8208845062080110b803044600010940b640150710408442d080001890220f05003446580002010011280000c201c40d8250308251942074044400300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 427187023 1250 427185773 427185793
    0x60405070e011a180d0609230304030b0c070f050709050a0b010e01050307030603122106081e07080105070c050c04090b1506090612063307030314010b0c 67
    0x1030003800303100f19002e941e000e03442c0d002003203516030103800342c1c82d520b010301011030403130744089004443c013180d00703c844070394911403001040143c2d50701807aa00601d1b025003041440703884000765244110300002d130680d22030300c0c0040c01d0b281c0f40500b00d1f001c1c642e00508420400410f03213007051340e901c80c07800345100c2a03080c00001000b44070244200414998141e41d83ca40c00c80d00040151101c0c0d0010300500c0405864000100100d0080d211803150040180e40c5c0c40a054a0350010070101c410700116010078604214081180280000e04403000038940c2c2d01c0d040c0054010540706151803429844807005500345420402038a80005020740e400d0300807026500b03160b894404100855021000061025802c1c40c00b1503c502044210008400d002510f5580340003030745030020f1407640000008240366000581007144d01d08180e50011743d10303a2480c8000b14455580380c801c0d131000f401c80710700401c1c1440200e40781091510a8000d01c4891119040410007544c452803003681503440304011002d00d1183c010320f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 427188273 1250 427187023 427187039
    0x80405011b020307150c02040606020313050a050904060e0f1506090109050910020d0902030601030c1a030702120f280f020c1e0f13021c020301140d02040e0f06040507 73
    0x404070407a4020302404495003810513500d46a140010b5080c108144440000b00507122840740ea0040c092a8004585560f4030901d4403502444540000b4014070120350104141c0d215004a250010741c04035002c80d41d1090219020710703100455108114611a4642c81380614030f442d120180605402e0702c40606980c1c85010b01401d40d101520035200d240d01880d80307401100748941c0a08400e0b00c020300081403c024030b0300068079144081c2c10584944c1040001005203800b1180f40100391301c0c0c242110303070440c5012180692548084890078030554800030780076847c034100740101d40004403440800c1c1d690070b100c0003c100c01005600240004142c0c42070b0f0b06050103000284500034164002c028586030650324041e40303650902e41a5054101c0340741d5030311a14982e00d44000c1042042c4000c0700503180c90100000c0440008ac41107803900603441040184079800e2a150a18841c101c00d56001200381d2a903c0464011b00240c0540711650003542e951801900020a805004a010710201d0350080c2d12450a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 427189523 1250 427188273 427188317
    0x6060905130f021219031106090a200103060e04080720030c0d14120d0f0212041b081b0406150801030f1515060201290d05030c0a08040501 61
    0x740040040150840051514464800b5011216400c1d5203810103403110000c022142d2480c114042150007411741f03840041040b10980c0325640700014000b289683d03c4140440c40010700c4080d00e00d132058119003e590080e0000c0d0000d10500c0051885881c0c203040c0014107402041080300e00c134412a00f00b98900303900061301c0f500c0c3c6a0050262034602c8030030b07081101665080c0401c50307000000300038030480404141b00203d01f04040c43e468a607990030003c1268100d850300034034941e03024410300c00d41d81c10700e2410900c0c95021b580940d482188880041e01e491170a26203034080103040c4a0070700110351003107880488038840081aa002e00140c0c1c0c5820700c442441c0b101c1c2e00c2100001d900c01d4010008110382100c2d021070a805000351200c03440400403408151018104540340700d02040c10100116035091040701095508a1030071300445400c80d03146a80c1002030b40340d107440381c00300d04980c1003400018070441c3c02d607107940f400b16a00d82d100d03407030312150b241c03c14816a400700d03113401c51001e810859202 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 427190773 1250 427189523 427189561
    0x303040303120f14150d0c03030e15030f0615160c170304080a0303020f041d010609090e12090411030f01051f02030316090e0403030504110a0305070e060102011806060905 75
    0x1304429503540a0150b42950b680b40c10a0740c0912190900c5002c038030300d091548007842c007e03668400406265028800990003552410701d0000007003041042801d10a12950780010301290700441d5203442320303c805201c0c0100e0380c8495200150030300110410408003440b800b00c0c1c2c1600081d160030040f03400000d80341d0049100b03800907a0010b04001000074847c1c0c3c01007a119a0f041943ca0505480b0100d101d102643c0e12000180307200014018440c4680161070b0400a1040d20001c1c40203256502c1c840f5100c440c0700d00d071004041004201018907603200e40000507550303264044140c4918055002140c209000c0c8039085c05683c01000c107803220566150000888400d90300110b2541d01ca040d1400c07480302d8400b60050400c03058400c0070508040504e00c02d030081c3d00a40e000b2a20b410a4101b2102c03c81d5400d0340341d84504100300c81000040d5002ca2030000b1111407000313079079840c0d40d8003005074058050303a64546180b45240c0e07540d1041200071f611100940340a14010040c507951002c0c89900608022 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 427192023 1250 427190773 427190801
    0x4081e04050612270a0609020a0e15010e06160b0403031d03090a0f1a091512060109080c030c040e03120103080d0501060201060f050f03070b1303110d240b0303040303120f 75
    0x179070b9400401c2d0507800a8081501c041d0007040a03980c0d400c40e01440c0d803401e036483c00e403c224542c0000c104e50380c0484100c010300c6041310f440386010349049540e0700102c101000105508400340000701030601035404030448035000001200103e0030031624030303241c2d07000c5e0b4042c0744a8101b060001c200c1b00340710041d00b8240c40850882601310301c00300c0e42c24403180d0484240140d0100d0707620542d62542d0302d0b01018000c01c1d00011450703e4503041c4440050403059040d0001c00c250762000059200703c2d42c1c0002c24032520301054800003071503200c440c01542103105800d4424100291003000004109030310001344100c2c084410100800c0c4d895071801c1317083e01e90a104805503240c03440b000344214075003070590398544d606c01400c95100c250b86a200b18400c1d04000b2081d10240082d1000300b0510046c035a42c04030758181110b400c42079083ca9692000700b41c09802811200d40344035860320480c004d4561104582090007400c80ea216030b0740b490020413201c0c00604105040e0b08040e004261003a060161030902c1a0325 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 427193273 1250 427192023 427192033
    0x1201330506130302030106060905130c0801050f010e030a0b071719020d0906060f090c08040206030a1517061803070f02011107030b0a0b090c0304081e0405061227 71
    0x40401289400000b006062000d06a40000c0107035403d00c0f03800014402c1e519042841403401042020302d01181c0a03220002c0c0c1441111302100b03a00c55407a6064500071a42540c04607814801201c10814207032034150107205890641e024054004001c0c0d118400035500e03141d0044c5130916040352024280c0d1142103052035031603102280084c9402a25504c40a0000080c3e11300194542d03505440c040e900515400100300d506100c90f5480e1b015210314807074a03041c452401d040650100d020341c030005201c001c0341c5507175040360021a00454191b20007400000072084c148640d0f00b128588a640c181d0380c50a40f007465584a00c020760010003500d5a0680081e60454020070980056841078070f190b05004260040610100003c0d410100403409402008000030348400080300f80501003001600c04c149028060003000b000402800498661140e225880e5030218215904044035000301c0c0c020075031150021403180701104c88603043c0c91007010346104150002400458003560b11042c4110b03003829800c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 427194523 1250 427193273 427193279
    0x10504120203190c1a0711010f0b06120a060503030c1005011203020d030e0c1c020f0303070b0c070204140f0405060106090f06050c07080f0a03260612010b120133 71
    0xd07481320700568054180003017291030007991641034450454514000c10560b00d150305540031309106135060f9000640d020024242d503000007401724003076921500038561003a00080d07405805500070f90700815000d800c40b500c1e071810004190b2500320102c0142016444d00c400042d0b071004688280c50415095006001802100341080703001e0411921104842c3c031a420074204036480b4101140c0c1c41180310b400743c3d000b10b04584100003e100c1c0000c0400c3c440d60081c0001d8006c16400a034140c1c0000a41c0c42c420f654205a00c0801c01410000c02d81c00040d01100040118000d00440c06911031841b80b000d486481c0c0e00c1c0c81c4103131460b084500610324808c2d124203007441514012401040d0b01c5c1586004c8400190f541c000d940e1401e41021203003a16904000817560070550010314401600141c80c01e4034400c511411900d400c00303100100541d10035541000e140d104e40c90292704c002111000a00186d00b81c6181121980c00b07808110b145e481c45948440c80d0000b080c021101c062100300f5040510400903107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 427195773 1250 427194523 427194527
    0x909010e040b06030307080403030c0624090e010b0303091014030c0315120303060f0307030c1502060c0405010c060203040f02120d02120f03071808160e160e041d010203010801050412020319 83
    0x1112f900100c0341e2039a030f6a644420400c800c5125484607a031200c6071034481e81002c500600b5584414402c1d41c1070b0381090810316041d5404801e0301c5000000781d400c0903000091703080c00c40d10600c0344080c185107524000203000b40007409900462082c082000b008185a400341e040c001c1c80ca240c0314600020780c009001141080c64000201c20f80302c0030090840304010f84030307100c13900c0a003030651084c01d84001c942640501d0a8043c000c1c182e00100480445041614250001e4041c8042c19002000c4030b0f4000f000030104411103012149540d0068441240e041c4214100750391001002d03070320780152040e10b0501d0300c0c0609500444082407031010081d130440d01c1c1d0803010380d400404100d201813800640c1c1008034000b2400c0200005407691a050780c0d00c03061420080b0220341d00050540c488100b80306100c0206140c01050038031010000769400204509200402103507890410355890003940004000164180150442d038001e41c003a403003020241d140e900c000e80e40c0c4c0c070940030fa0042440341ca00c0070b5152a8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 427197023 1250 427195773 427195787
    0x3060c08012607050103200309010e06010510080106030c0504080607120f091a0601090b07050120070327080d03020415050301180207030c021809070b04180207080909010e040b0603030708040303 85
    0x20700c400c0c9182c01c2c4003c5004801c590b613082201d0701d41e27140e951070100085900040010794014103055072079007004031138140300402501050040c4c0090640301c1c080004660303c503604035801810201d050350140c0c03c0c222401072010b604c04070f0b004001400d0840e1010800321920400f540781c1d502900400524815030a422004a002082c1505003d40e6001c0043c1c1840c00c900113001d80c52080c4000541004601c071000d80215459011404e040700131302820b000a80c0042800600c20038802c9800060307401209418900c044070b81004101c0e01441c6441020203401d50050803e540008c49050540110103004070750390b0009115000704035143e91840b1078198900d50040c200b1038024949018080c5190300400c0885040c55048e64070340e6030110801034180c1060002d4809841e140c45081e1601d031400404001c580700703034011899560390008082c01004210360480d4095400501010095030b034070005184c28410859094918001200c0044d9241c5400f05c200c582c00b0b648810030a04003415920300720340c3c0e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 427198273 1250 427197023 427197041
    0x60703030b031002160c0609060c0605090c10090e0f1e0901091b0306140702031b0705030114090d0c03020a060513061401080f1902061303060c08012607050103 70
    0x2d8050200c02c526500355034001842e031840003486020385001940380200c0040e40c541c0c810030070400401014403a403070b401541c44c1c0c900c44c0c0102d000308a07a1100c1c083d550074000e15486d0360380d11075a00041411910303080013162302121300b504024142c44c0d4170044c01e0003580000302c03031003004405a0028041b180783c2d401d5915030845036440000502e0007843e40d802040065003020700c0611202000b0400410a81d80103100c0c40e288142d1101c02c03a81041c0202035031b2802400b06441c007800f50380c0450300702014100802c000805004009001c03032059410081c030030f024203840c84603c034000c03c81c50342c2185000700c0035130529940c5940200418606912100018940608100540007540b8061404a60b041c0035001007c80f9642c0301040c00c0d45000c4010780b13840140b03901103641750046801008007060409041820319010384c2c030140c0d030720504180b5803042892038000400c80d40c6000a060300065115004c18107869081e211165104807007898200c0c402d001c065604031a601c90003050120b5403107900f0164003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 427199523 1250 427198273 427198279
    0xd0f110a29010803130602030a080109020a02030c1903020607050a050307120b040f320105061e0706140c030c16020103020f040e15090601020601030b090c09160807030605060703030b 80
    0x101e011000c001d25a2494207a024542560010680005092013602910001d112030300003949040e8400e200903000306814403034040c840f035012030604612402401116044600c034001c1e81c44800707640d1060101c440100c0c00c2680140b0406002030301e5070b80650b0454060b0b9110741c8030542191780740c41003101d804200182c2d40c0140da40f0703130b0384a4030303192610700800c90724038101580030400030750311202c0640c0940c102d078000844607142d0842169070f07807811060f070341918806e84506940310a414030712012040351001102c03100000080794030520041d9400503c0501051000841c0b0740c42e0701c130100c001400103a03002030b200750041201c0131a00c841d100304c203000c0300e00c10b0501600700a09143c1030076281c1c1140c0d01100100b02c0d00810442035400c1c0c02075a110182c03084070248554281000001d642d41c90500004103140c0c141400700f5400003040100a250b030307400030402c45042c50301074a500c1340d03030b030401d2400e6000c0307510000451020f0340a8000d11060750005009141440c4035a2002c030068941e07041c0e4250 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 427200773 1250 427199523 427199573
    0x11010c0c060507050c0a051e0609210c091e10030206031816030804150905220e01091e0c0b0408030310090c1407110d050d0f110a 57
    0x1000518400c034010040ca07140d122140ca80c0c1d0325080140c144014041940e12460030316800780050364030f18500c91100341980300e94250781c00450740800c20034403d240d08140e2244911030804100c1e100d102040354011110300981d804540313148180301d9141015121113502845c000f8900728540c90303052459078065840c800b10322845959402151880e4000c1d10300700101e12800d01580d008280800c43c43c80781d9a40c00c5224003a45207152140d18030382c080c1d4010281c043d10f4420f0003825452144000001070301d0000d1801c12030407856a61401d48000c400c408075611410326504502c0c100043c800c035501c0d9900040c450080205064510a00744402c075400c60b14181c5954011503180b18050141000d00216401556242801100c000510a16a0000500070705010740c520030a640001c580798101d0f8161012921400c813450a03404040c48208115000008900110140100065549604031181d1078820117000d5541007261402004440c401d07041d03101c0300340301d0000303441140008411466140041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 427202023 1250 427200773 427200797
    0x3020c04050403031a030f030703180f062c03071502010f060305070627120f02030307030c03031b17060303040f0e06041401060206041b090c0305100f121101 69
    0x9012280180c4080c1e00180e902c107a1740d86868101c0413003100400084004100f03214006e9803450f40d03071244e4280142000541c214062203a420040c0d20310250001052241d11561180d500500b107074003244c1200440c030030848414401c40c907502c80c00d54403802c02a01800506081c0992034140c0f44441202c42c0440d9070f0ba954039410040c1e03500c179600c065031241025005803840e02100a00340341e480c040d9003d00f410320344151503d4505604244084441c400c00c403403024500b50500d900007040c41e500281d003601000618004041e4041500350060b48261810410000405228010b019582e051000031403c8a10700d68034049443d40d01a60120006045030b140c030b900e4220705000540e4136400358030503011100c14006030303180901030300e500041c1c116070495241d0b141030380081d5181c20240c4047e04089003600c98000c3c41100d00c404001500003017005000941c500080100141404c81301d00d8420840c50300d000c2a81240b0302c150740d04a80610011030042c469070b40710310700100c0200800714184039083c6c1d40d038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 427203273 1250 427202023 427202029
    0x150b0d0c0e0a120507050f1309110a090b09100f060e0604050411040305010509010b010f0e0d060e07092324031b0405060306010806010612020405030f010b13090809040903020c 77
    0x102015140f9041069402489072801d40d03d0b0205a070460742c400c5c04144980003168451084078140120090b001051020712410700703503083d00805c3d00d801d81003626a0404281c3d400780390009000d030181900c102c2c81d2503440f0340d1244801c420300c0c06003a40140201c0d6007000343e5441046006141d480091640e440c084c0c2c2c4000180440300003019091030080702050030810f01c8401e200c0d013030344040000001d02040100c003000800e08964131a0080c244440e10740300c2c03e0a030300e81c2e09070410201c0d403280e404c1140400e006000c60340d4456901c24090080d08240050500784803910b10f03265028400755000c1c0e50f0b074840f1100c503181e45643c0c0040011003194030300c040b2400c2d81c040280440030244c13260b4190701e194241d0705200c255140144a540254441c10040000c0c0c2c0c80002c00c281120003a20341b0790704100031485c23244081d10803030b444240d05115003002004c07540010f40c004aa6038108440701c804001d20802800203581c0a1200030b07110031410711081c4101d0405030003c01040f40b0900c1901e107006d01c6a000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 427204523 1250 427203273 427203289
    0x4150201050609071d04020a020a05060126070b0f0318030d0b0f04050702070b0c030c0f0303090f190312090203030706200708220315050a150b0d0c0e 66
    0x4010040c0e45840c2803190314188540c280d600424145000821802d841001c911029400d556150185a0000300c0090040c42444100f606d036901c02c082c1c0e240741d42c0d01c071208201d10710b132504001c69840d640119081e2100c00000c050040b108958606410052080d0f001d140d150001811042c034001c030351224030705403c1c1c14002880c4103415003000040048422042c0039406411141003805140751100f403180007500080c111044a2803070a00c50398a42d07000444c2c9095005025801d030b038600c6441e203e444021404405584982c00920456646e102031fa20404d42d180380c01100c40346280901c60004010030301c00c42410002c0d600054011850b44d0300359011a1039980864800d5035080e40d690803541e21112000c091410f078400000180342001d8298503002c60601c54251000740c90401c10304440720001004050b40b00941d00600d490900c150b04c9440b0401030030046814200d05407410740710400701e1140315a0390050350301e45001c00c0e003041c807890700c4400181040c005880500035903610401d1035540f4181 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 427205773 1250 427204523 427204559
    0x3070302090709090f0c051903021603031b0305040f0305070615060206090d0e0f01080612012d0c050405010809010b1203180604060507080a0c1b031a0601020714040204 74
    0x40d80048a518200016040310300b035092400c5c04609004181c003481d13520001380c6807065003400c0e00c00450394921106600900c10742c04480340b543d0f0440820350503d60141d014007107a00031079400008005003020210210b510488008201e803d100d00480d011034454030203080c100d0301c01c6800144c0d0158155504182807040d0b8400c3c0d005034400c004000380e04005010742c90451034107040595141480d40c0c0041c61507400000700c18104000440090301654904403c0040c40009000803c81c0c0d8105103001030a20403000780e1480000c00c2184107202c3c110551003075001b020340564030f00703041c6802c0c4001150701325406803031f00c030556403030300c909080c0d643d5080951610403e9560085030b0300c3c603803901c0740480c45401d14401403058206220801685030008201d501c01c0b0784c0881550794400c1e50102c180c8088140c0c11b8050b110030144040a2030700c0c024030680106980c0240154201080f4682c0c4c0d40a0703950040300c2c070f240140c108001c104913548039a10b05d0348031000b000740003600b855203c84e01540d11610000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 427207023 1250 427205773 427205777
    0xa0512040c140901062114040515010e060d02010c080702120d30110f0d0203042f040b041d03040e010e0405030f030402130213060908010e1b030703020907 68
    0x802c001a03070558248625020064502c8020b030342c9016030141c80000718011103c08040c1030503414650444607800f041da9104401d54900450500742483c42d07a99100b071209030394601c00000003142c3c003043c01089a20032240200070003c0518aa401180c00d801d096000703e4510f02c0500034540140c0d070303441100c0700410050008250681d8200401403800311070b81b81125580084420380d1103503501c01205013010039a801c00104800040000340c5107a40700318001c41c90350200205c1c00d40c01c0c0d0041a00118052400f60048140400c488401086461500e6001e140544030701c4021580505058221024400b030003000041c0c0a889031100600100f000c544818103900002030604c500384031010014050031400882680529296407403d035070344141410114002808000241103541384070410071007110b500010b40d2910041c8041ea2201d403003a000f0580803a0100d01c02098500713051141340c5410042b2001401004a4503207440c0c010074014441139054054220007001685501c490366006222a07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 427208273 1250 427207023 427207043
    0x90f030d0e03010c030603020a14150307030c09351e031207020105090a060f18031115150405040c121203150501080f060d12020a02040f02030408040b0a051204 70
    0x20070070942194188841c41082c10702d0603800303002584500318988180d42c10700d0412404a42d900000a242441256160031102c1d0004208144d456140d0012000000c080c1c03203040d0746a031540c1c21500b00401d501503d060b00355541c800c01c1302040c0f1081650011402400a8842150302da031904050f00107202841c1866078000100d803e81c0190003031899070301a1081c0300800080c10b05800c5103840b45131405001c0c2c50b05444540c01c0304980815445041001026400800c00c489180f402a203003d9041200b44400c0c028050b46984c04c0e8149001306c2e01c150034500b0b01182c1c01524200300070091002401c140d4252031003203400b2404035a500360b04076180d80100c00b400c10a0307240800080580704812004a41420341034410000384c3d030060038840e04900450802c0c060b81d55004040b512010008002620038074124141126040d0003240d280c042d6070007501c0034815154107000000580c071050318000c00c070300f9080104100800a44002c4c10000049203001c40c6422143c80000106030801d40b02034808a1031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 427209523 1250 427208273 427208297
    0xf030905030a03091412040b0307090e13141b10050708070c03050f01180201080a1404140c0f030a0204020708070b010305070f0914010e090a02030102190f02070f0506090f030d 77
    0x42e203909484180c54100040c1001c800c1e1481c20b150307d003d2849811140790000c0045640140100000405040a031807550507503e0311140b6817000d0700c912001960000a5009010801080031482d400480168008142d1080c0d104c02885411208010b0369070070042d0031300584e4001042c4074000c000060040f4850207241d030560034118102080d0700c150284c00ea14240b820040700a408140800454090038070b0585581e0306203001c0080c1c8a1b2002d5400484240020041088010451b050708444460101c0c1c182e49481414049400300441401da0f06900c80c06514005103010b40040441e1481452075a0804280365600e4a1000c0280c104892a41110405201030484142c2d18401010303c04020b218096481c255266400e106018070f071480da001600142a40350204138160030594050002c40d510b40c1325002003051003c010b905140003030000c000040f0814400140003080d00c00700e0034075840b0300d0300c1c000800007a0380c013104440340c11143e440030038221740d40c05100110503a000e07615000c0760228 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 427210773 1250 427209523 427209533
    0xe010c0f050c100b0607080a0f110114060402030405010b0307030f061a060d0504060605060d06050a05010f080a0e0a0204060909111504030311010905030a020715050304120f030905030a0309 83
    0x4003540d00d03902002410b2240d007804040025440c518480f60703440029030041290041440c0388101400582160b000142d07100742e041c6e00008640701d42044e5598040031203160a411400c3e00d2840c004030190200040104400d441c181d4000c64000d0710820000074145501c102207800c1c07550950055a510080780500400d101c11340c01800208040441c941d4031010703a05000a003640a072041c1443c074036566000080800107150311002c0035150080c6016200c0c0056042d0101401880c05a06d0050354050400035041d40185c000303200c64261340d107078607141d40c0d550100304004100c0004002c0c0307944601c65502d000368480f440f404001d400e410502107220710480c14070f030200d41301c00802d59024144004850042c401040242c8003504c1d071521300010b082000065003400b411030004090b10500000480806103900000c4040440d0148003002641d40f07440d05c015030340c0b0f00045402614450f440c20040a00900c160070b00d4110401600700003d0303141c0340752500341c556084816840b003c44d175610740d0501445 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 427212023 1250 427210773 427210787
    0x3020601030302061e011215050c0d110a02120d0603020d0807030807020a240f020c030c060106110705010806010c060507020f01110415050a120504051e0604050a020f03100e010c 78
    0x440e07100d1813113003c0103905d0054221090502c50390a102c011030368514100030402e40078590a1403022414442400e200c290024554000078855040510f066001c418071030181d4141c0c4d0450718640c000d80340e145603505251880da408440c00c207824980e1030001100596032200b015902c1c3d03000f104050f841d43c1d010f04c1e029103603071809400b40c005c2d5440322014400258104842080e0103030008dc180c9541c0008200308000f41400919011000b0300104d007911452100002428109174000200d40099a0f1000c05503000c4040c0250603c0710341207504107229950040b440c003604202c0601d020b001c0187c40c0e0b11000216441074800c1d0006820006910300700d540d090049515600942c0c8100d854039243c280b0b580420745214150400313101c404540070f0b0f0024003030491146600a041002d001e54601031404940700c002010030f4900305490240300c070308450800540300303101d168040000c120880e52034081200100040c0030040e494400d22140030b0541000c2d0250700d0300d230302c1104008a46850104005450302c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 427213273 1250 427212023 427212031
    0x907180e31020f061c240608012102010915080603120a05030f060604080a0b0412090b2a0102070b01150c03021222120b0903090114030c0702030a0302060103030206 72
    0x50301c420409000da52a520082103002040b00d07425900c0e0030a0640c19848040e10f0130003402c0a1a20310621a004400d0002c0010926008851030070140c88000680304c5410a00488210480d00b481d0100c0348480505d501409900504100b03541c5980c0350401003a204010720780600054410060005908003044090301d9124164036072402c250010301b0050107400001d003a00c0d03000c500c0b03002007201500c1d80d000b2a4007030400392040c1c4a00781c400d1b0805e00c1c104503054a08881c00d81c03103058501c20061168141d081600c40004101e80b50011082d5a90100c0908401c0e0380d402000403079413030142800910083c40b6440c0724024019003585404e808a908900c0b100302c031802c0c032444602910000b5408038a041085004001107522000784942c0c0a4401c004500f01690f51001a00c02103080c070390040f0041d03041842001c0012080d59624a49500ca009885c1c45901062101040d15414866030303002c1c65005e41048485400e006040c1c00083c5004c3c040d28007074015800103c018010315506010359540 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 427214523 1250 427213273 427213351
    0x40501080606060a081015050c0d09030c090507030b1c2003031608040509010b0c06072a080f04032306010302010f2114071d0907180e 59
    0x12071410302c0c00704246108035400340042200c8400001c8030302107900c0250340944401080c10048002c5a08003500540c4041c2500e451031145c00b200c00340280c4100c02c6c0e0340c00e883c1d01c030b94414005464626028082c0c200507004900b4951110031210f45502e4541039180c0d081b40e03c10f00843c542907541848402040c1009424022407000600300d500ca860000071948010b0f0018002c406d1004941480101030046400c100c3e84000624000130302180303001c0152103d0002d00d03090350581c2e00c5084080d1002c034081c0c0101e41c0c915900420303040300d201c002e4001c1c1c00483d0159000500c0c101c410031013409180d0041c0c1007103491031171520354452756030802e030a50101b00c246140140502c4d411500080c0011041d11100707803c0200244001c801041442d07281104681e80d00c3c3d0610040034000e000550110b4101d41000000d200c0d00317141c2c00040c01120401803a0a4060240341c03071500c0b8114221020041071620902a51001c40d000035844800150391303118182e400c0803d0302405c3d030b2809074200c0101540001c51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 427215773 1250 427214523 427214533
    0x11100c0912020f2116030b0c130311030703050114090c010c0c12060f0504120f0c11090604060e0a0911150306012d050403051c1e0203070609060b04050108 68
    0x401a100e6190304200d038503003103468548603d2007008142c140c404c80b51820700c6500401c02c1851281080c082140242d0340300e0000d050465542a22580c0203010f94100340300c070350b0401102040400d42d0b010482400e03a0016007a40c400d59104c2c1c80c1d070f82c00d40700650050030400290b2401c10603c5001480500b04c0c00c042440c10000c2c1f12201d031140003101f28a4004e1280705009400c3c01c00400180c0c2d48014060007000b0310620131464107061048440346004100350204842000e580380d080c0c402c06a100440f507001e150512082c2c001d20030b0040655004103420740003641c5410114002e13130608681d034450402c8400100b810f40c040d10b4810260501020302a01500c6d81c003410300c009410f88400e0b00d600070000c2c80c01c031343c02900d4025462030300d204c84400c00d8114406410742c84c1c039480e80200108140c900071400c8034a55807a00c1d50080d41c6074101040000011003100708041401d80310000034003503c0213481180d04002082d100d003011140b030b100e000c841c440c0d603d015034042400d060040c0c9005100303260144c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 427217023 1250 427215773 427215809
    0x1b0f2d0620011d060403030c0e0a270608250501080a1503081305120a02010e06070501021306030203040302010b0d120c1b080309011812080a11100c09 66
    0x54580c03508062205101c114090303081800080c01d40c403d003e902e00c1030304a6540049020b0342075881e00c0e8156000e42c0040e0400603290040e034041d001001d10301c45e0203800403a0841c0351120401303460045450301a15001503030b100070810080c0c1d000b481d01400d144806012a0f507110000100c604041e031111a01d180800c0c001009a40e0700300e00041d0713001c81c0784040800d0031484000c203251140440d41000f400f190b00030036113981101c5040c5c1e8803410b448054170050841d416441e07400d50784100074140240013030103000079100d031130410f030016014151040c400075042801c40080318039a10b180307800c03400c000703580482080141355090003000b29981c0300340c540d82c2480d40c580d1103120340480e440f510340042c007101800c074404204020000350360b580200300d080c2500ca600d461116840c3c0c7d0000c49004c0c0010421075444640c410304590641c02c4812007019146005120303581c10b40c1540000c09048148001c0304041c00d0b003c00d09006280a2504040001400904000e00034003180c441d80c00c403131002d4042c46204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 427218273 1250 427217023 427217027
    0xe0a120503040306020f09030f03041d0105092208040303030c0e040218150c070305010209150406021c0c02040507080a230a0f090206070f120807020a1b0f2d06 70
    0x1c80589030850009030340c5401081c01505c1038810070814540600c514421000c0c9c04801202400980b64800c0c0401082e80e178424030301c410b0036004e010b6103074444401c001145c445050380a415015462101601e4685801621141c45503001540b09402181c0c444a04401340c41c0c1c458241c038440c441c201e07002c60600000324119402e00803d6000c1a02400c0d00350041c07903901c400a42070760050a04081120900c0c6e8132480c0c40350207500542d10712409140190016401351401070281c4040d284260300502e0f003050a91403038400c0f21100d860082c24002260320381c20243c0c84a00455215017031a441c2c0788c6040c01c1034607110045030103540b00b0b110b8090740d01051030288011a16005e802007100b030004030b00c1c02211940c140042440c040025400140090340e1420820101c004425081c0242918805c0c441401c002b912030035001c03661a40160020b20301100058000101c0c0008001220003d0001580791401058202d2050700404001903e140e403c26401662903181d1403d454101d010040745481c203c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 427219523 1250 427218273 427218277
    0x3041202190312090302030c030d0605030f01020a0f1407020d03031406100e121e07080c01080601080a020c07030c06030b0f19030b091906060e0f0f18030c030a0e0a120503 75
    0x400403a115000308091620070820340d0710423030000050380c3d50390803529081d40061000c0e104050003070040c04024041c0ba40d040c820b503440c004058940c41d0400e0603201007200d900d9101011802c0c1c0c107205100340d40241e10740300b88030034900f4403a441c0020070f80000400c041d401c010080007103100b514840010b80c001c561102421814120031384a4411606001044c1d5040c00c0d5040303a0112407840001080b003001800041440c00c859107007050b075100c4a27181d00115010b660440c0d145000c5005c10f4023242001c07111342e0003000907460000541d0840b50300c82c0c0da49081381c1041d03804800001c0e16102107a249240c05280e008408004840300350003440006501f0054402d0f41c07002800d5030b01000b000684940c03040c003000129a031051560700c5081001d00c2e0490080505006d40c0200c01000d02c0055016a44016068041e60303800c100114960358844c0c80035500285016401038034002030040c01e0712800208050701d600c0c0386a40303c1c032202e40840403e00448441c198005005a80c0e05a00c40000c0351010003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 427220773 1250 427219523 427219547
    0x609010807061b140706090602010212130f1205030703060b030f04020f0d0506070f0306090212150307050d06060302090c03040807080a09050306040b0a0b01050f0409020d11030412021903 82
    0x2c0444881080110700903c0d904848406801d1280d0480c0c1541c00400c007003050020782c0d04640351134458a8807484100e080780034040d10358001602040100d440c542a00a0030380119214000031800c500e169a01e480100450b000d408010502c003100344900d403601802801d000c0c021800d9807d081d1300d005805200c0d10341010300064001c105241c42c45900d03440b9104103c0e403054000c0b0490b085c900740910020190010f01e807000c000070f4035000c0b0100d1103000e11300840d08d0072911140300080940b9400303400702010140e01a410382c54802c3c88000511505c0720504001224011178000070a41c1c038600521030304034001051284086030810400001403101c3d0150b0704419007005045848801003d025140c040c000c1e00300e00c0c4d0522401c010002085091a50381d4482e2803025070501c543c0ca107036001503c450140d040c0165203200d0510050014035a958003811520440716070104800c031a40c91b40070540d600a40e030a4604500c001c0c0b00208040d0100311481c2403a603054a00322070210703e52801080030640076 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 427222023 1250 427220773 427220777
    0x1140f06010c170a090e040803010503010c080f0f0601020304090f1b0206041a0604150e07120b010210050a0209040e1b090105150703020703021203040306150614031008190209060901080706 83
    0x1304000150314403900c0e00e5406030890160880841c282070405401c1e5400c00d1050520a600300301e040f03003072940304210050143d00304000c1804680c07200340101d04251070050080341148424000007415004a0081c0c00c2d41c0014030f03038005180b01070b09002d91402403a001c2800e06640c0142c00f40300004010f000e2407903040c07540c400000b1480d215100010086c00346a518204120300305000424181c504486c081e00690040d1202d10250501440306420340e60000401809030f001146052420344081d00031651129000900626000c5104e00280440c0c40f800101c40071303540300aa5441d110b2641c08502c61950204071a0620a90b15000004919011516440d40fa1560101e00981014020086107015645c002c0070004042c19960469560707400c948015501c0c1c60070074641d00b051504c7d801002e0180e4040e659146c603c8000c0c05035000d03545d440900485503180d40c581e0b000400c03a0040c040200f8042030100d07040180d40c4140104181154054030305032181010900401010600241c068200c0e80d980c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 427223273 1250 427222023 427222027
    0x912091005120c030a0e060f2403070308091203040506030a0e0c03071e05011d042f030f090c030a032a06021317070e1801140f06010c17 60
    0x1080884060140722040c2021500d00302c140844000d0000c003461007001d05807020084c1c3c1d03040901d0765a80b202c2c292080d801c88503440b40890344e03504100f101816124a480c0d240e01c20720f210341000c2850320a042c1e0080d14510310110f03c0b48170610301210034a40c403004440c011824941018001506444060480121780303179100c403100740c0103070140500c00300720400809031020701d40e4510403440690310078003081c90300c3c070048400071a5540c05168143d00f0000ca0f418044590042a000e10008020200031036003000101d24400078410404230744120b8141d00d0350030054503030403e090b150424400241007800103802075200d0800a0f200064408a419014a004504035030300455550030790700d604803040202e07440042c000d0103006440d0000e000285041e000490346a0b5110b6070380c0d90400c40b45640011a03005184200320040480b40c585822802c000c840504c40c10700160005e00710761900d071300407004003c0301c0c0c20803200000310048603500c05002c1c00c105a101c026551100c0900038410010f038049040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 427224523 1250 427223273 427223299
    0x80c0306012403091407091503030c020418020306132001080a0c0509100c14011e091106031609080313090203180d08040606141c03140d06030b091209 66
    0x4203420010110b50400304600e00c4014001c4d039607850b0303100e60183d14142401d0160031901007130800c4234001225015980ca0352014070f554200806402540045100c0c0d444030a440b201580d0300f80a011301840703404000329030842642c034005c002c2080c050070040900080c0401c0c5a8980d0300800e0301e80e030000c0081000145248400004da540b4010110b0742a000319069540c0c1c0c0b4815001207500c0d142600600c8151541c2c0b0f8080e2015090f81d60a411000360402001002064446107411080b4075520940f1081301940761900441c1d45a081120001c018100b01441100081c2e0029840b401818032000518070304440b01000460400c0c4c51f114402085900200244101c86007600001e1050605001d0b20045980d642c4010700ca200d00b40d8080c0d48e20b44c64500d000400c011450b09107681c0e064083c100c4001c0c103880b0840c64a4540090509406004c0d401080031600e0011a0042490340b6410a00113002401c5081084000740000c00b84611507000314030b40e07100e5000311400d035103440e6800c0361485e074080d403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 427225773 1250 427224523 427224527
    0xd15180f140c1c0c1809110a12060b070b01051306080607050c07150302130803090f0d150608011505031612020d053007020f04020d090b0f01080c03060124 68
    0x2010070f10031100910f0315120100c4940d100c07101e40d01c455a00c1840000840e25602c888049031000140c0104111080003001519405800c15901180b0f0190001495503698003a0f2011030b0b2100030129000940040180118941480c1c1c2e014900c4944070b041114604089009a80f500060b00b5075045c00000320f00380b440300d031082160002419040040c0030054811b280b0260294100030800d0b442c0145014022420b89000000da511441d801004c121a0305086d1043c88050b4010780015100840d410140c1c40e0101d03082c0c042c80001b000b1040000400b00c0d00c14400620800f10fa4010501c030390802705949c00d060316080c054900341d90140808920803182131001440302404200001d1050160f050004c2500503540081b1407000403180550f45140c0c031001d442440f510841700001e5020801c2e04c0d46111030705003a40588140341740c1040015407515961070380380c22410100c07035900d4000b807560011300c032001c0d06000c0c0c500ba4a00a9004142070b505158101030980031303041c007480c0352045a45045592034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 427227023 1250 427225773 427225807
    0x21905180303040b030403390c0806041a06030c0109051e0d0503091c020105032a120105040c090e13030c02100806091b09060d15180f140c 61
    0x100207046941c0e036561903403000c489420403034003640860004200c405000045010200d41001d04407081f1480171a170031244052039000345015101004218808540b46008005c420300580c01b41c80401001181c000c0868200b040041446009401c03245482071181d030400c01c040d09544003110301e034ae00305070b0942400201043d201c0f08503900c51003c42c100c0d410b01c840400180f1945c04162008111070000c44c071315007126040d40c0300c000d001400400002e0001401842c11484821450901d80940f503035045080b50142c10800b0710541074020300e40100b102d464680300d0062035201c00c0c2400c510705443c2200700d541846000740102c414881e1031a5110406103d0740010385115030043c092144150008402044281c08a6100c2e008200c80d1003c194003042c8404001a40c50310452800d1170f2052110601c00f903030300410030400009031a08810754442429580b0000500071681641945005854078002903030034a00c00050068a42490340042690221010341d1050a030a0b5207659000c0140f10b14000c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 427228273 1250 427227023 427227067
    0x1208031522060602030a020d051b0114040606080712060b010e09010914100302030a120201060e01230301050405060a1802100203090a0b090603060607030e030109080405130e07120f140a06060603021905 88
    0x16510380014040520741010ce0340e4011409442e08106107130b10b41540550340e803218051000304400045500340000c28a400541942c4018900f17403c0454a030b2010071842d000c22727003000c1d10301a00e503000225818140700c840c560046920202c21881455500401d4540880c00c001505030013500c000002400e0007500550028502115984480d40e501c4000910340304205248242c20841c3c100c00840901d0b050250500483d080f5003e000c281d180c01800d04000d0000456030382418000c01c071020056503903004070440c0c41003103070081d542e103200c0342040055543d0783c0d401110000300180401c1c511511b078602aa540241c00340d404580c0c9001a0800703a48804602200076410b6003050744520400403080003400441c0c000b500c102804044150504068a03c03102070428181e01104040080202c1c041100402ca03001d641e05e400c200070141c4848080002d50809100e40360720210f00001001380500c1000d0081c40c0c1480e00310f080c00100c6041460b404540030f0820308111000c192040c00c4841a00d0603406 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 427229523 1250 427228273 427228327
    0x1030509031201030620070b180a0b0a020c0601080601080a120306080d0c0507090b0303250209070806030d050304200109121a010f1208031522060602030a020d05 71
    0x202e0740e50b078500100988482c0c8420001d280f9655a00c40107090750344255034000d5405030840c0080d55a17201c0f55054603840100c40c410703c2c440d52640102056100007c14081e0181c2400965510800f40b405480e15034180c0c4109800d0707218000400c0814030116407420425400421500c0c88224404220050301060308840024000d801c080e0041c0e45c1c201c074818158038401d02c01c2e991007580e56014074048941c3d05442d1501074000f040801650b8a00c42c052154000b00758118195018864001c5128050102c40d0840420008003c0c03154600d01084548074522940c50420b2442c6000e0f551864081440362000091a2480b600d21140da0300800121000c0c08001200400120f1070f403c003d82807480085051a04030517140020464030303404402103003a5041300303d40c030301c2c00d0a485d518442e01307a000030048010048801c44106441c4c0d2581e0012000783c480b5585135451103001000e0750201d4605600404c103560082151030b0005070085600e13003881030a420b00c1502c4410740c0c3c900050140b001c02078458 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 427230773 1250 427229523 427229557
    0xf0302070f080a0309030306140d02151e03040b090d0c020927100e0307020a0608040f0515040311010902100f03020d06080a14030403051e1005010e0a1404110103050903 74
    0x2c1d80342d140c1d20045e0101c0c0a5035003480390300d644001c2c03d450040e86079002e076004004c0c850000050705001c0004107402d4413003416a441c00d49200c0d001c00c3c051002e2989128601d400106000a000d890900fa503040305920f03025041c0703003650040281080015000007030140b0f03014000141c24205075895603508003001d8040c40000610b50490b41e071503518000c8441961498555201003e01c0d000040e034010590260014008a00b480b8059800440040045462074076401d10b21000a8081c418208100340b480088911030074140f5006d0580054107000c001168503209068000d607649040c42c00d0032003050f04046070050703581042140a0b20600c030101c0c2c0f98504048001a8603040015410b108501460008840e01d18500055840c0e12940c4070240482d4032030880c180d4842d0364100c141d01d04100038011546000601008081510001d9100d40f84254020b820801069110302030300803140b80044030301984d03240c140d607174045039040c17038200741d04140d55200041c182c000b041086980f244001e140d03040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 427232023 1250 427230773 427230787
    0x1b0b031b1204050d030635030f07030513141e010302250b10030302030d0b130f0617120d09060914060a20071502040b070c081204060f0302070f08 64
    0x503034039143c1130418000280342c1200058010b2100e106003401c40c080c1688600c2c1121102801400440408040c83d030a01080094265080c512130003400642d11917154551241501d41414650022652080443c28606004d4000507680c11004440f8421159011a4004000c5004070002d01800c0c1442540b041002d1008508a43e01c9028103103251040803203524a503500801c00d50b182c00640300040150f40300740010041c035511a0400403000c2e40250401c0303c3e130a078011700e45085e600088001002e0aa40d0801444240071403409101c4051101c0c006006607030003006a1003c0740f0a140813608402c2e650901081005a02e8204000c0c072500010910175036402c10202c02d455403000d4424139000c501c0e1100d10142e161414145400400c00c2440b140e0400307a40d03071240c40020800312079200f03046500b00000b044040009001d8070480d8099490f851007141445501072400c02d095202d4500720310300380020490940e0221900380349000c81d24015844005520b840040030035088001081c282c0d0109460b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 427233273 1250 427232023 427232033
    0x90e010203150303130e040206120106081008190303050a0917210402010e1c050607020a060609060f051e060406030b0301150305070b0c100906091b0b031b1204 70
    0x1550190202841140340120100b040540e40e20034496000405042907070104841c0c1c80e41884680d10500180c04207191510b08084186444002d0708503101007900e045c03e000c00d55000908503000342650500601c08440680300400380c913811440000c04044d00c1e507000406a201c07641101c0f00ca10303480702c0404501c6118085404280d00007140c81c8180580da02c800c9002100c01c04502809550180c60380c01e440d041e10014094240d903085072503800c64250381d1400d030020b0300800c0440c0c403500d000e5001e085404614501141503034025132140c1d4002e0308146d8140a8110f05828540032030314100e5841c1402c02c412007210f401e24a00803540d07540280041000518160550441204044110f008010821171913005000b8a20507001c0640a03501c0b0240501400b1841d00040070301c1070401e003c80708540143d20b00c5a058585030801102c07099201c142030407c00005101031481800c414007003803600750500384c10000c0ea000040403000301c40d1981d911a001041000211109440d05680441080c40c1c90300f44 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 427234523 1250 427233273 427233277
    0x10b040e0c190509072f0115080102030405030f1c020a03090b060d0f11010504050409050c0316151407050303150f0d030e06180303070c1401081302010c0c090e0102 72
    0x30150085080b0001600c5150341008000192040145100361503201d948040703d0041000c0500e8084402d0008901490021300c100c3c5020040c104002040d065202042000100502d0b884810340d42c1c010300600c4009038010050b90840f1941148082d2900d0440d0380c5043c0d001c02041c0035200c1c26100040c4215031507071642000c0740807809688800c880e501e80d00c080c04034070108140c010f800f00121203e00700c002003038401d510000050501d45141055159030024086841c1c001084401c0d901541505180e81000d1090b5401080e00740c42910005103004072015503100c0e100c00342000c100e0a0900e8800300341c602010380302402d820a044a40f40d1a200070203d03554030010b208944501242a02f006803443c00070451401c2541c10780e14454009604070500603580c00084c2440d56507580158111443d071001c1000d0004140900501c50303100d850070260444503d4118130090401842c14104070985103894050b98401e42e081ca4407004180b16820300d03440f407140070f03042190300900307016000d2107100d41500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 427235773 1250 427234523 427234543
    0x8030d0605060a0c0f24050a0c020703020102120a0201060b180a09060b0901080c0702090f0f070903020603041b0807171b0a030f241407080603100e010b040e 69
    0x40204030494544003004141d00442000b48005280002d5240c0040c007078402400400d4440c03040e1254a80078840440d0360494510341c0d04109607070f10350410020408501481c482e1821600117003800e2421900002d4840c0d06035040c481d0910000640030042d24800d60192006250001c4056221aa200010750f43d207400c3e4034602c1d2013070076030400c042103200b2103101c3d0800322040e03030100780d00d80000c0b1401503965a50082901402d14001d0000c0409070f100c805403980300e441da0f81d28200c0b15180071000c0075040711014100d00104201c030a0148016103a0104890304607070000e01c11601c202d004250610718130195005070701180151000090440f010030000c144c0142c4c0d000035140d686d10300c4515000d1310400e030400b55510501c908010000700307884d08850404c4500031104a216070001c815400c40040807480c5500106035200340c041202180b440003140c2005c003c1c80c10859500342500041c0e990f0504031a003400055072851b840815600945c002c01c00010b0141042c0101c0b099040456126a0042c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 427237023 1250 427235773 427235797
    0x220306050103031205010b19020717250e070e030102070c0303090f060302090603010b0c03040f060e0f090609060405060d02090109022503020709150b0d0b040e01290a0f0803 76
    0xc10303501000c4c401c1e0043d18162240940182d003031880ba1903050700004200c3c11040154018072501151100000b00c0741980d505120f0000e05266101c9805810300100300c16841264903a0780b2000c0c070106049403030494008400d4603103102d03480f1380350000034024455000c3c000d000e01440d003000410140c000c5240e0048a1405c81c0d4540c03182c1c0d03502010b07001c1e8864080d5a682c000010001880030301e91580141c400c03e1520411281407984070400d00201809940022000c164000580102450030315410280460161010011414490086002c0341c0c4040c180c948102d4440d0300241150316405d22002010390028206030b02c650b5540c040c8002503120160b00504001d40405040340141900c1882c980c2990540c000c1480501d001c008800500640c040c0d103101221107040018002c4072600075055490b91078100141c03041d0030100b00310803100d0030b0411840590522070b00d8040b440d02c101c0010650801d0814050b4404030030000501d0f120310700d401804148405000102d40c0c0c080c000081c10001c0010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 427238273 1250 427237023 427237037
    0x2041e0e060301140402090a1d03040302240a030905190b040b07030e070312030f0507260106170907150c1e15020901020f010606020a030e0f0f0622030605010303 71
    0x103400b03160a0312003035031248003010314080101e001420b01c00f545a601201c2000e001411940200c0110700c03849600786442c2c1c0e1075201003828000e500c1c00c8044003104101d0598010203031000881030b40b4041c00b4000d6101c003030540d6102d55405120041c04450703000c042d80140c2c011031098600d440c18034001c058a099400d1140c010005651a00034410802071003044802069018038681c1c0b5150031164030940003040507200e056070340035141d05024003401a100c685403040e58610074140711410480650300c00202000402c01048616049441c440d4000380030002c48030310384d44044002c0c0c41c0070070b5a030041079211011500c50009540c04081444024807030f030050f48051102010b21000c80200b07407005072049009108413410313006650b00030508910180143c80c0c100c06c0b802c620740d0840d0115801a4090b8004120034003c0580c4403a0070210781e041280c0184c440c0d0300300008180300c4105003079100d0042100064050025410308207030500c4070880945038914540707a01c0c080d00501028403003100480c120b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 427239523 1250 427238273 427238281
    0xc0312060b1309020c0c06030702010e06040b06100f140a0504030203100b030f0604120f03142805160c1703040c030210030c021c0513080105100b0a0e09070302041e0e 73
    0x3090084905c121400c00080c025a80c80301c08004844c0d0015101d182559a658610f4103401424480782d44200e01408011183c0e15244081c010000313042d651100401c80e18482803140c81360801c109050603e000c4a1503601d03000782c5a400e0b41c07030744116080a035052240d90a0500344c0785883d04054195101941031b54034052002c50401e65442c1d00740e84c02007141003c99400ca001510490240b000503010b8980402e04400840c09029001c1080d200c4e90301c0740f04815040b03004125201440d07004000b180c44100b0442c03500c10804030082c1e0b1010000020880c00307400c07010601c4181d00c0700c401c550b08840b0065590b800e151030615010001031008a010702c0c002c80d004c0075002e02a102c1c003030850305141c01800c008010540412040d40b228554002800014001d080e11480060991000707803e5003000010070b814425484920000c80d68813a24001d0010803480008641c003548618007004195802c03101070721240c1060b0302a0080da0004240458411b00d1a120715020712601c00c00c5030394131502e040003511 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 427240773 1250 427239523 427239539
    0x1c03060b0f0307080c04090207050a0c060c08090405040c15030606080f010612052206021305030a33020c240114060f1b06101509060c0312060b13 64
    0x650360740d540e00640a20003e81000e00a1002c181c0c0280c408010038901610741240d00103d0f00072480c20307541540030f44060350170003042c2e4400c040070b40100c2c18107811002d40c03650303102621712545480d10f0086844d41e010400300404a00520b0240085030003001202d003000303170000d00a00051107980002040d50f004552098a04051135043c0c5400d0341c1d030400282d2003401140042e00c000340c01150010740640c42600d0101d000542c20544a00c264400340c2d48042004462448241310b401061098101d20a9540081c0e030582499003040b20f500842c2400404e0621404040c2c3c90300c021000100c1d000041c84108480c000c501050082c80031000c0509404460010140e088800d01035041c04a070101c011542908e040b001901d0780004c20a0a40e10703001c940042c1e02044003a0900c0c4d00b400d9801a41403000b4248440c0003100500300000e00c0502c4c42c2c035a5500148050f00c10710400301407014141c800301c1030602c60060200d400c201d00d00107002156450103010002e0303110540301e541c0003448540c0170501745 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 427242023 1250 427240773 427240777
    0x405060a14060d050c150c120301080606010f090308040603290a091a0604090b100c020108070e030c040507120b1903030e06040e01150e03030306010f1b051c03060b 72
    0x811040900056030baa90600c56215202c0d40142c50911405a001003a81c0c0d038424441c5440e082c010a060b00e5540641c032640c80c041d214200e20020310002d0006000c404030019a00e0b40c80302003480c1a6070403106921050782c1d00240c0b034002404090700041c0120380240c0507040324607010b8216414603103e00d5a441d00c06004030b40c80d014507901070301d001c60801c107040300da41040065102242c0c03900c0d60340341030900040d516171141c0d1041a039103071145140c505034a410b440020ba120f1107030400100840e1144d000a02803000140100c0510a0340304041242e500d04010900c5519070141c0108080e003496807018000f00500c1c0e401c4003203e400c180301803259003032011041c10484001f0030810b01040c00e640d82560100d0440366a2a0402810300c030004454460444040c02410640c1d0342c0303e048844018000c000c2000f2001440c0603030300c1002800860313684268115100d1615207401009460008110300c1c1c00c001c90b000182c068820084240c00900c0403072024400d609a03a00c01b001a00d0b07860310241d8840c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 427243273 1250 427242023 427242041
    0x1140610020601170712060b010807022103100b0d14071404030809040b03030d151406090108190e1605010207060807030c090b0301081e06060d1e06140405060a 70
    0x16000100100030404c580080251410303070140550f0303019500c0340c40401d150408068251243e50700d80d4107018903541c0101059410203824406081060610303594607806601c10941c0c002001c0307000001846c802c1400b50b00402401c440c900080c0d60310392010308400900214214203c5440503900420f940ca030259814410301c1201d401c2d41c42c01e041c950307102c20265030064031055402c01e803112a801d41c20f030382c1407008007920f9002ca80d0004074071848510f0807815440319040b504401ca03000c20203504640e1520181c0d00a80c5007442e00310040c0d0b58440420101c1d0701b00d43c400780c0c0e001342404d1000c4070080c400710300c030603410641402001015a555004a80e1020a032040b007001c80c0c180b80200742c4841c86504000403084050401c2d40b0300d5a528241f5809551090f805040d00340c000d031103081900c050b0049101c0342e044071400103003490300700080050240602c4c031034024094280c008116079030250070011455040d41194040014681640098040004c1241e0482e036500400f000201120b80307612403c0b007a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 427244523 1250 427243273 427243277
    0x301050603030c151b0705030d05061c0b070324050114070b01030b13020901030b180106050f04091505010f170319081e010b0405030709060e04020f0a080106030501140610 75
    0x241c1d07101c1404203a0080405001c5515052003545101c0d250080100100005403183c0d0044d550780600c15a80d5080321005080107102d902080348cc0c69003241c550004440f0f80390051141d40c030341d84070003006030f00038580201e94107500200103042c1114a141c6003200c40441e030302038940640030550f003020f203541803050107001402404408018804a201e110000f54041004c8080804220951700000e62400f0268811241002c0c80c0c1c0403c1100803a25441d00d0822081c18000d100c010700745000904030721f07005c0414900a50341d40000c1001c0c0100004103600745044034104000b0b40d61114181c0290364005d00a5408803c00302c00500314901c4e000003200d0880f0741c04001805040c4004a0031980d0810282c8455880ca00507072451f0880b90300d484e00c01d4000d05048400356034031890042414100550b950008042a2404004101000000c200c2c0c9034003e5049554207031801c1c2002c0024a80b19090700980d40d42c0d0719010001c010010f055002440310108008400b0a543e20ba07010032404042c45008100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 427245773 1250 427244523 427244533
    0x111b01050c031302030f0f1606082a220812030f010303050d0905030a181a03130807080406020714040506180411280603050601140c24060301050603030c 67
    0x80703e4000d5090b01e501a480202650000040d555906182180d002d4038003003503821414036030188824440e6010010001c2d400d00741401e15210b401c02030060100443c602d00d01d410308010481018010040310042d181e00300702c1211001415241141030115402400780350b101c0d88036207a00c2d848035101900d100c3c09404c2411502a0b083d5502213926400c071510320044a91109118000503005102818061141e66036201c015181d4000d6504141c1c0c041d40702a44c032404034442540203440103130459502400071202c83c003202610f440c20950600c40e500010b0444c007408074010440b55030225280f41261318460340944540010700404c41101d8003a244582c4c0040202012a503c058542102c3d600501940051000c6c41030503001c02c03810140c1d0501e910a2441c1005060361184c0200c0c6400050718880c03508200c0c501d0f101d400682503041c003800d02ca100d040c010030038007949030b41000444603800195811842828800c203a0644118060707511501c81e50811001562a081c0002520f002d51501da00600b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 427247023 1250 427245773 427245781
    0x402060d02070201090b040308070209010e060604120809040e1f0606050a0c020f0a0b1b01050f0c030a060312080601030b03060606031f03020a06050705060a1b050319111b01050c03 79
    0x200254400b031002c078148601c058000400a80510242004600a0710084c0c1d6608182c0f04006594405801500c810101c0300280601034035140213440c1900e518039880c00039203216050500d02e6014041b4115170041c1032916003400b014010803042548051642810080b0f103d29220400b40d81440c0940c10005009101000786244952100c102d000d00180841c0103d51240d8041460072010703401c4a40f0800000540702516040400d5a10501c42070b103000f0403090920000c4042c06040c05040314130715100210200703a188400354403102c001c0d50b104114076007070303401d0039000f4200c60022103405000c6480c00e9507803100c43c1800701e18280300302c00040c000c03451981d03440c030861440c0920028032020410442c00200050f00c50b040701ca000340c90b042e01c0d03142e21650030717181075460000c00400c1100e01e681012070362604605c00e41c4200091140d5801e2082d1240d40c1c40710440d015030456a4002e140d0360400106841c006950790003010340d40000301050304510555694942660015500c003d01c41400304005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 427248273 1250 427247023 427247047
    0x60a051b0c310f02041d090a030f120c0c02180f060103020d0f0905010603140a1203052d0f09010b061804110d05060901050a081b190303080915040206 66
    0x81e500481c580c402e2040008031502c007084505040760841240d41c005001d111660300d4510b03455400034500d0320f40680d4600414001c1d11009034100080a004110152184590059819119162042d1010084541c90708002040c1d443c0c12074069000c0d02e410600505a06c1540b0504d41c07282144a61040f841d44900c00110001d601c04a410400280d448008000d000028041c140c1c0460190b80085031035401e41c20540c01c0c00004011610241d0720040901000030511804603000c0401c070b0500107600c0d40c1d02034404030f04d00f8502c11070103c00c1c0300e40e84441515016010403a40078902030b69030105280e0382c1c41001400c840c42684180d074801024404100340a2041d4032644000f4009000441c845115181140807500080d01d00900280c491003000f0f03040c28180f1106005000c22100b6000d0300d8a4100c0d456100d41c1d40c0c42c410200005204c00d0f081c800c0d1110809001b00c0c500e042000c0032440c2d03403801e00a1000e4800d03180c002580c05580210a072503074040002c14021a00104000c0c5010000040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 427249523 1250 427248273 427248319
    0x20a05120907090e1f1503030309080702090a050a0507092d030615080d020115030204020306040b1f080a0507080711150103031205070c03120c0509060a051b0c 70
    0x103080003a1080c42e0300882d071000b09000f00c0880218650003015040c20750740352412540d030341c01803200000b0b151180580400381d41311051303001c880d0541000101d0400c541000e0186108141e00613420488000610802e0800c90744801d2003580e40703071001c10107511031803403c031281100e912501142da840c40c0545c514030283c00102074410400305500014081d9290307902c1041d03031111194031500a0f41d02c0002c0000d9903090105003411b100d1840208402541840d045000800c580400390141d0350200c0010000c2d2100d60240c1020350005128030342c581904213515000c0c0903a00603a1002a03e000b01040b034030000c500400c1d00038550f40c2c441d45804c0d503135500c0440341c03c0d641d0300d0071030418480c860340c0340401d181e0034281078060340c0250740e10614220481e2201007544d00150245040000550078030010960142906d4209004014045440c4020b214211054007a0b508440c0e0300000002c1c00c3d401240c0c00600402c2107203141818004c26140400d0f143c0d84a10800d60f0744c5400c1054400420611400010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 427250773 1250 427249523 427249531
    0xf041502160305071e0206093a030906090f120615270b0a03020607050a0b0411040c020f0703080c0a0b151906020316020418050703031206030c050d330c03020a0512 72
    0x803a0032079035400c51030488500709d00440d041101040e03160203a03080c180d1100400020b81030608049069915100c00c0c4041e69600e481001c130014000c88100701042200d8000307040350440f10a000404640f1041588810728000024402400c2a220350710070030303480c1d0700170031074030300c0f0014079403200b07103203580c0903c00306502c80ca108844070301451071044002802c13203503003d006500940e44100e804404400b80030844001007440c0e001e55104c84001e4455050004038081640d42c0500c61070b407190980070030780c1d1501c07180c0c2c0030040c98400e00004124004d42da02c240b17640556000c607243c0b06050200500c5510038480340c012080143c004002c84148800c8a403c10846c413407028000145111044250440c1013180c1d06084505070400380c002c000781035100c01d0402d94007484c4441049114610390b10007120200b1482507500900d50400d189040c0036150101081100c4d802c0d001502030106001c9500e5045040740d0583d01c41c51409050b41e5000748284240c6459042036204c1d00d183c6102c490f41341c3c00c0140024 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 427252023 1250 427250773 427250809
    0x10c08011401090f0603020301060e09270313080a020a060c02010206070509130513030206160c020904260703080a0c120203090c12010f140f041502160305071e020609 73
    0x3460019040340131030040c10017041c10740c1d80180c8a505010005007a4460702903130309d1003424a101803249161510104440c0170141c5078030755100c2c80c1c40d02d13140c60640c02580c8990070500e0000c071001070140780c042803a586192086688940183c0c42e00700c1628005072091019006a101c0800210110b015600503e41000700401c56108140109920360659200302d80c0d00041d00714001d4000c04041e01000225007113122510500001c41c02c042004241a4100002904c42c5a4100109040c810a01e40c600325011100c00740240040c40800554030036404a40200c3c00189001d0001d500b0902e14450340000420550b681850311400c0703040c0e2070203500040c2500344603018810b54400241e90b01040e0550301001c160010032200e003070019100481e6920748608030104400010064401304070340c0d005034840d070b02c040316148940000c1c241c1c00090050400600781040d10701044010715800801030300c40b040c891288000d03600300c03000c424600b0400451000303400c24818040c10000e8a080030412051404003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 427253273 1250 427252023 427252037
    0x303070f030e0a0804210201050f0d091e17030603070605070302010e06181002040506030f07091a040e01140d020f0d0813090b011701060c110306070306090e010c08011401 75
    0x3100b4890a190305074200f190240c100007810081000980c00740d180ca4000c2c42c98410400009400180c024441d10131100d00c201000284003210401e5688191083c94001600d484080000f1a101400c5845900146c3c0c0c00381000e40d0751501d500122048030b11034074002d4050040140b8044d8180c80603040044114151b5484040446404c80c003003003c136228002d11000c466500d180040c030241000710001081c51224010001400183c50380c104503900a200075030300b2302c00d070ba80e10401180c03c07044036003200f240c0d241058030910785441d81d1009031050b9409074070781c01c496903a941c92900d2006504400d043e08028a1100c060141c40d10302103181c410314028140b45002500343d90348070410340c4006a4251580c51a40302805448900e10078405645d41c02e007051030031441c8420911040c0e000c140720307060410044e1300c0028104030030f140007280c0c504800b404450440c2030111001c2c0c00b0300f009010360300c10341d850a000804041c4050203410b0106840752110b556513401d20f40304802d007120301c1240d00d044c4804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 427254523 1250 427253273 427253291
    0x906010320060d0c120e0a170c0307050d0c150509100504030504210506010e010e0c090609060d0e01240303050c1e100605220b0d0507060c110907020303070f03 70
    0x1440c000c05181540ca9030f030340031141e05d180014800300c406645150007240e000e9400100001d500e443c800c1e0140c3c2d50030a0940c3c079018045001da1862007040ca000f00180600310a03081c02079000701340c41544074801c402c0c01c0c044060420a0104451040341c2c01303070741540a490140c00c0b5880551003540c000d40286002468030792150f03440768040c8139035042ca00c0742c408074100700d5045c000140a042d01401c81d03d00d14145551400208039110031003d010b2901d409000610302d0025501d81e030444500d00340140402e80c07582d44240d80c0308010f00416088990b41c2d400c1c132240a00004200f07148000c0c8452400001030a01e0440e2000c0301d440d0003090710850faa2040c1444c01a1403074400c80d44540300c11014008010315000e246404098030f01d268009401147c4545400c0f000c01c100440c1101070f80a40f5100041400d490b4000520b003101c0d900c0040e2003400f0340030020804581c003c011000c1c0500440c0e40c580c0c0072801c072080c40310301c03a4210740b0500140c01c04d0001c06c42c680e20400e00c001460040740713008640c15030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 427255773 1250 427254523 427254547
    0x60f0c0507030f180f05130506030307080a092303100506130b01140d0c3023011401020c0d150903141207140a080f181f05090601032006 60
    0x1c04d5400419603c10702a104101d1480d100520007480305098009002608080b000300b9901c1c041e85400a20160740440c21080c0c29216440362001482c1c4203a001035044001103c480e04d42c411101d50274020300503c0000000c005c0d15000340c60044001610704500010903030341c004020403142e01d6030390400011181860b400350020010b000701da4002840000c074110451800340400c0703040c03544c00180551810318030401d10782c409070000c00048014000b180d240174440a0070110b0092844961010340c041001049180d82a000c0d405200380a80072114540180810488c2c0e0a0310030303500620308950229014601542e82e08003c0c40c01e40719041800d841c1101e20005d10b4280c1020055000702e501100400000035400660710030b58003902e100d2a8500000c0c1d01c2c0060503400010000c0d40c0402c140c40101d560300c8094502e4207211040d0301e01790341e41c9800c1d03d0400b0703040031070803442c0684403410f03c00440c4810b0070101e11141201e034411422560b49186104000300ca504c0d400026601c480c0600041d80506 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 427257023 1250 427255773 427255817
    0x1314180c030a331b0906140307030b0607030e0907050f090f01090b0705030a0f0c020603042006040b1e0c060f0901020d0c0f020d11030f2206020a060f0c0507030f 71
    0x10b0240e8000b1030094400d00d801d513191000c03121180c04000c0440c03001c00c44603400401c01a94180718103002640e907902c55078198043c203840ea80311508001e000400c5024546d0040020060850403608000d03141c4800004403841d00031641c548d076802d041000010258034104860310b80841d0107050034403c4560f01d0000501c1500210003c0d509a040012100c00300b540c000050f4040d81c889007400307041e400140d000f05005002c028070040c102c00c5216400407440f41d844c003d04a10500040126a642c0d072a40d13107294141c4c00c40c0108100d61200c8070701035142032000d03200740c50200427140c2c0105042d81d15600c40100380301020700800708a55081207907102d1400d86018003880500c0c85e841c0c907928042004002480c0151483c041b00c1008a150f400d480406c8000c012900c00e220000c52071074683c0c100c00b907030004407003000001c624840e480d12000256180c001c62050b40741800b5100412210f10070080c031006a80b200e00d1100c2c0040c81c04c21402c0d0000740580310f80d01c0c440030076140c5541d81019500182c00d1507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 427258273 1250 427257023 427257113
    0xf05010309260409050709031205031003080c030d0e120702090718170d03050709050d080c06010617070c03020a060c0314040b0108122104021314180c030a 68
    0xb400c40014140000c100c070b8060550005000c3c94003c0503d40f9589030082000c180019103c104a00000860341d030008d1002c05034040c54000c91200c0c2c4d261510501e40760707668010030b02c0a140703d080c001c0c0c503c0c034520b01160300c50b141c3c0102000d0602c0d022140e42040003c41008201c441441039503501200f100d1026a0030344013900090704a80f10701d40c800c2124620306101d6403074480405080c0001c01104030340c0401a2411508251082070b468109468142080d0103030005001c164440c0a000103000341c3c0c0b00c403c60240d00318030690104240c403101c00890349541910b101501591103400d20800069195010b900c40c20031920300040c1a0810720b0041050040641d0199240c00010340144482042441100c01d0f40d1207020380d80d480d10503001c0200d0903491040700048270401d0326100040940d1034415501101100c8420f00300b00b40344100b5031020203102c2c1603030010400c24008200b2019094001025106038600900a01c5840c03182e23550080b100f524400030003c0048418040801c50807991030348040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 427259523 1250 427258273 427258343
    0x411040b040f05120102090a1703161112120f1602210d0c020d0f021813030e01050a020c151b0703060b0301090209191d030d0606090f05010309 63
    0xb0703d2070841000b9800740c2064803103581ea4030400408507107544812200080765140302d105003a41001c01031a03810b600944856164004d4480c40c914100290705444d4500417100321220020f550690110f503a44115070742d5116803c2d64200000303001802c49501800191445280c602801c40c0c035070707010607203c0000b500101858031501003402486101400007031181082441e010440e04c015400045c400c44902ca0050311520034071815000b55100c0c886010810680f80d401d50a0302c0c00c0c02c00500c1d42c0914041d5082c2d0009110f240300075010340c0b041003101c25000e040e500424501e0400c108014801c9890807010a90750410410000079065810400c0080341c07011020b400c0007031550809105031000c2203c0284070741d01d07260024006075940746184d030300100c80e02174180e081001e201d0034000038008440c00c80c410242d9000c4100c08200c0010017031007022140d00c0300b8010130b95070300c0040d030b060030b014001c07074400f40b4414000348942c3d44a0382c0f0802031940141ea41c00d0b00b0110f52100c0442a0000c00c0303803204 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 427260773 1250 427259523 427259549
    0x3120604090213090c0506130504051909080a020c0402120105100917030a02070902070519080c01050f011e051f0c0c08030a021903080402130e010e010c0912110411040b04 75
    0xc180007100844038000c3c00c080e5459894807108c0075100381d1303400990041c3e030300c1a5503e41c0400c2c649051841c40c800000b10103401000422640c1c01e000540f504005155001803040482415050a060090b80c404d190f003080c16814030b03402c2204006143d41da0030494000c101618900140b040c1554010f502d041c4500d4014598410001c00001d0070004190401c481d81c50042000e000001d10008a21101300b65084103a1350f51030306880d02d1a214442c02c1400f814940c00d01040c80b15002d50002054100c0c0c4c03039481d20002c11010391109a01c5d0101071322a0315404100e4280102d04c0c0c4045604410359403a003842c0c50f0403060741650b074403003c0f0241500034140503031003c0b9003040d40316010000d41c650a080d259095a240758550303401403001c40f00074070090084520708002040b10910360800317803d240c000c1d00207211509589042d54000c03d00901d184001034903a1000058044011540c00321203504504841903026881c000e100c0034243d030200002d06034104000004501da514400750020b0700c0d44114860b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 427262023 1250 427260773 427260791
    0x512030105030c0102060f0a05071b0b0f0708091b060d140f0916051c0f11091b04090b06040305070308040801060f05090a0906024005010203120604090213 68
    0x10329203800f88001c50706544c4442c041c020000c003072501c4542c0c00040400007103101e6032901d4044031a085450203440c2c083c1420481c40c005c100c050010184551000380c0a51025902d60300c007203510b082b05075001c1c6140e802455941c500d0312240c050826944e103024000514020041251500f1910b084200724825801c1106200c1d10380000c0140c5600480c80400410303408042030720020740f680c1c49220f070074414008210b04500c44c08074028901c84450304009204445050341c140b51000c00059940303640714500d02070014091240e0744c0240e413844220300c8049400d1070705101d80440104450389250768080e030113000c0080042c00410015001c0d5101d507070b18980355403400d8041030035a04203410450000100c140d0a00442c1c07641a5031700d900c142c0c000000b007400611400e045009110318081007200d0110704040701c214005141c0503a262401c4644d51f011030121074826900c5110107801882e0050b0010004c0300c5120440c2c4940e1604000d00510001d252400e6500141070401c41541940115440704180c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 427263273 1250 427262023 427262029
    0xd172710030e0706111005041506080d211503030c031d010e0603040f0803070e0a09050408041701021315080f070806120c0604062a020a0b030901090512030105 70
    0x180d6001405041c140034080800d00303001d40b152030500610040014030120f03004164420840030710030310801e0204005600f0103041c2902d03d056101c00907240c85062444c001000180042c0200200000365958038036009240d0a5800400161344030089803074a4503e6451040c0c48030f00341c0401075200c1d80f5102e4203c075440c98003400110080c4580300c01070310883c0000c020b690300b051004201c0c0c00100c80c110740e00e540354588000040445003014140035000300400c0101b0342c010707280c0000c3c04001c40381e00c0c601070368621203102600c004940040c201d15083c03004100307081c082c108a4621a00400016061800205042e52a803d86510603d86104281010303485181c00010840d045a01440544450700d092580a1300b6000050045c0340030303d0700b92002c0e002c506000c2c8150004114010002c0740d03115a01d000052000205004015070469909030b1405504000e01310501031950203049140d152f45058048005a040140642e00e99502c60090310009030041c0016080149801e40c1e1a0b22941800c082c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 427264523 1250 427263273 427263289
    0x606032a0a020f07170303040807150903030e1009050c090c07060f020702010e04020703020616110118170c060406090606120c0905071403060f0a0807060c03021501050d1727 76
    0x101400e81780b0310003e243d507914004000c80c0d070303c66048941c0700e9680b2618a048104407200880d107038036080c986000c5808056051304020440c0c0c0c04034003120212010b901512003141e402c1200101141e1049805e02454104606260b81c45045585200c0c10440d00d911a44161703085e011543c03003526800a480f808541c2c00100114005100b83c804500b052100d98000c0d42d2190007610006400112240d1007120600c180100da8100c1c004800070700602d00d1030b00a0303000f0510310300400c880c0040c165001141420001080e9410012010000c02d0282c90325124800101101c03541075589a40307640f00811070403413040c01440d0062142d4045841585019500000c40c1c030090109020001141c0c005a02c01c000d1409907500306004484000d00c9000e8103000a404032032170f50000c0b0680c00740610010303065411401c10800f40b4029001d41c1d1380c2c005e0320910004c0071402401020750000540360a00e0202d65114503c00d15903d21a000918041d2604a810011081150101c3c022700452084581905011034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 427265773 1250 427264523 427264529
    0x30201020c071203050315130f14090316030f0215010e0412020105150f03012a110d050723070b04050f030d05040302061615050114090606032a0a020f07 67
    0x4030344038400920350313001002444007801c001055400b9040307810907a500c10307066000024200c0003c020111020400300c000e131116586d403204003034041c80000c044850100803250f840b0000c514042d1802a103640985021400866120440c40f0b0241d401d0002040039003203601811010100c00340500d0305107040607154851564450859040405208038158401003038070084a0844d408400000c1c1800403d00408501250090901c802020003840000e000c403d400118015030364011050074898075140c0e500f41100c00c80001900070008800410390506101c03000081061090918641c0e0281c09807814809411141141d80c0000e81003029181203010a4000e98044c0c0260a0702c00d9849009007050046d884046d005850015203405200d6200c921030301600d5001c2c0c051201048074444002c0109024082c8080c450105c128204407443c007151103a00c03a0301c009208030320759903d4001c07501e44541c507081c00c00a4407a11042c0840039416480c0541040c0700b155004040655000603060f1400e0702c107034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 427267023 1250 427265773 427265789
    0x61203300a14060d080904050f070809010207050d0804020f04060f050438190609090c020f0a060c030908030f041101050304120c020105090402030f0928060509031303030201020c07 79
    0x3982d5a1456040242c03480d800344046440000981076810400c4c054400d501d49645e0083c580030400c850780c0c01c1001c1e103601908141e41d0b143ea060b075884055500f03d00c250b51015209a02203245074a80c2c511400da193388c4503101804ea102c0c41204034021900340da04030780106610f80c40601303062005041c40e109144000324002c082a84041210108100f003002c00324440c03081f0300c0c3c00304c000b00c4180c5480c0071000d10000411003102a19945000080a18203075000342004982056500703400c0920000d0801c050512803009800c4400199540b58000c0400000301c0303040c1503c6640c60404255840c0280d0300c1a8004104201c5a00c1d0074982a005142d900040c1e034180141032040c080454401c10070f04041d0a01418030140d06880d030b000580700c0c2c2c0918200c0981c0705000100f044043c43e00580340d075004860900c100c5427520446012454840010b5100b5a803440c203251540010940b542c00043d0070120002c00e0b680f51440404200400a011340c00560150b034000400c852088410014140140080c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 427268273 1250 427267023 427267031
    0x24050601051303020d0201030608100f0612050316050c0d030809070905010305030409150f0305010903030b012303040602040506031614030c07080a03061814100509061203300a 77
    0x8242c140c502c01200d0300020b8018081c0d01624821a4007941c48000030301250030407504500151601c200280c0240c1185518140c2451000200680c0c2010603000c860340c0308001d541840d1403600e10545103a5180802d80e030512441d24503500a464200885585502941d18114113151540c2c044e40380011540c08040f1711454400104049100402503a0640b2104000890000180301d2800f84214141d04804103901c0f000300004100f10056000784002441394070f00b84a024540e10040d2401c4440e1031141d2541608402c5802030880000000d42e400b5109440060a00d510362000ca0343c250812144080c400c00440389120f100b0742c002c44816203049022403181d02d5854070107007441d058062100c004001c0a000700310348803024000d40021010701b0761a090300c54002400ca40b100041e0181103061000301d60600c001c20448400c2405902c1928800780581c0580d0b00e52505105d8102c0c001814666103000c00e03c1131040400fa100c0c0c114141014420244016030f4427502840800d030300c0036101c040b2040c07030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 427269523 1250 427268273 427268287
    0xe0603190e030403051c03090c0609052e0302070302030705010f06030c08030c0c060703020a02031c0e030601120318031506060305130f03030e0f011506020601170c0603132405060105 80
    0x784804c81d01b20130b8807003e80001d032440d015405424483d0340282411800040402d0795544264280100c803400c580d00d010740d008900b001c03170003001040204180c0c0c112407410107101500a40003002c0d505e1203441100e1402546483e40342c2100c01c040d080b481e409884000410601130303083c1e041c402030100c000c091403510207048150f41e5105071400e507540c022a00032031407406041c0240125881c49070003a00f55545817035884558001d05820100b004d010900c1e540c03543c1a0b6040004042d030694248400700c1d4552000b6072400d545080c0d58907441c1c142c1c180b226202200066201c0032210f07104ca80f6075804102c0f18181030021381074840c000c09844040392001e07811000b2948148543e10f40e142c2504000030400309003160141011010091480c04c1c0d0309140309641808641c0d244802207410507400da81c621790b04ea03020070042103140319400429034061045880280f415030010340c0c10000c0000a11400c4801e55115410b0000344002e0048030503015464903103000460040a62202c0700346025460060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 427270773 1250 427269523 427269533
    0x19091a031606030f0e06130b0112051e010e030d0b0a091806110f0c03071406130303180c09140a05130803040503090409140f070f06050a0e0603190e030403 68
    0xd91044a0030552074022920400070b043d8001c003080c0841c14159000c030b02d404211507203c40c0c07043d40c003220000c00200000488294ac003410454043d404000380c800320704540c02c8905403480e901c90001e4955a146081712500d14200000c1560a03042038000c600c4000355010000744000782e90001c50b10ad800c0c02401068903180040100a16910450018843c009550010f00e58007400d0341c0ba80244000107002c1403d6030000010703124251082c6860300e440045032640a40302c0605413013030f41c0b017032078096101c2001034043c0d00140c1d030740d042c41e00100a800e480d80c0c803010b00c10071556001c64420b958641440e004400a103810369400b2099050030f121904001d604a80b15000f5140d019000380070120204003008801e00441d80042d600400078010310794142000ca0216010303030710741b40d441d2091031901900010007140840840340c00c90f4400929034900b90307080c2c4d8a6440b00e40b0030380400507105084a01c650b1418003039030156010241800c44020400301c00000c0707550740c0c2c681d40a030f60300074001003002071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 427272023 1250 427270773 427270813
    0x7110d030b010c1407030209010b0d0b10020d0f030b0d03200c030c0d1b0b0c0f0a150506060d0e0304050a17060c0a1b0506070e062719091a03 62
    0x107541310a90300d1000102c40c08035814400745400080d404450140001403005414014052200401d6010003000c46d102d0104200d20722102c6141c00583c0200100340110b42c040c4400c50700300840da0a011030828201c400080d5004c010355802c80110b4500380341201019007010303a2640e400c0c0c074840105810348070f18000070b5581d90414121071203048440156030410802d294000926a840c143c189130003510f41c0d040c0b03036442c0c20040e03070001c1c81e101d030b200440c05681000070040c0d11103410030204004032070745196400181800411550b000641000118058942031041d41c2c3c07400310402c00f07942c5440c03c03c5d04100051b0342d41c1c2e001c101504880d0748000c0d01488049003003034101190118560f5510034041041e624070000c5161490340c0c4030110039030801d0250214455105140d20390b1100d1006290000f0061130703009110030703900c443d1901c41c4003840f580c50540c0b84030840c031002005c2d007158890105000407100c3d002e8000b404403903168140303402c001540021104814070105c001d080302600c2d03441d1811801b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 427273273 1250 427272023 427272047
    0x507120c0c170f040807080106061106100909020612090c1207050603150102190b040c0e0c030402040c120603030e0f04050f1b0f04030b100f1202220507110d030b01 72
    0x4100001d00f8034001c8498412a40146080000d851119136280100382c001e015a01c141c030041180181002c3d90248080346c1980f26140e4480140c05581c1820300c1080280303880ca000b2a00318804211960030010484001da101e1240d50f002403030010010341c2888001080341140541c030341e20000c030900250350b17044160b03580000490380d06294106c600340100d242051400c1080c194401450300d10042c8120303e00382d40d220364080c100c02c145440d038840d40002c00c610304a480482d503023000c0c00414014982604080c0d8800c0c0c507454142c01100648120340e0468140c0d510807008140705000c11015030412034511900504200e07070030000c510780300d4403419034420010300c1c1c0c169816070514800c014480e80d0040c0d03521450380b111002d41b00c645030710f4a01c0840505641c0f0882c60960480002034030304440081505a800034a03090080003140d5092080c1c40b00200e240c0344030040d0010032204481c640d0700c00c443c842c100c59076400d100140303562046810030708030000740001c160900d050a000360360002e04103011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 427274523 1250 427273273 427273313
    0x1020a030c1b030803150109150c06060b1902100912110307061109210c040902060d050405070302120304060903080f070c060e0f040e0a240507120c0c 66
    0x355000c5140882c030310030040008410100c40c1550200134008900007444c071440020780070702074121043c4015500348440388103c00000e079200e0400789075070f40710388402e2122910580021a035540c48000f100031581190844040c90b082800350804001c2d4100121866030501140030010326841da15200004e52904101c0024410302d034440d404103000c1001111120b81e000b0208000182c3d40c103000800c42e40c070520a56125600f800c100c807071003c4410801c4411605020005c0000d107008905210140c007032104103a130b00c4401407100c0c0301a100140a001e03c070b00e01c160003078000b0034114810401c0e00c0120180c004080c4e44140024000c0c3c940202d003541c183d82d00452019184c0c00110a0f1400c10f103e040e80041040c410307042d0014065402492031009120101c1c0c05030b1424000c3d0040c8002c4075811201c03915661300031940c41001c900f00d8a000412000744038000e03088100515000e2040d588142e40840000b04d511b802c1b407511660520841260751810b141000003c4029115001d1b015201d40590310 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 427275773 1250 427274523 427274537
    0x509010308091f020105012606010e071809061505030103051218040e060907090c020606060304030c05060f040b1005010c02090a0623030f010e0607050c03070c140f030c01020a03 78
    0x1c26943d18403814490000c2e60302034954402140c0e8000c0c045e1800303210b078080070030b0f6440c4e0700080c041c1020300c4e40c1052200100149403503880d1100d41042e00501904407014800e80104080c02c2d44070654120001e42400c580200ea4540b410f0001c50410070004d030302c4810800300740010710003d100400d010001c03610540b1910b46a41c400c0851103400c40c2c140081d242d01602d0245016008031002c030b0158410314040d000c0d111001d503a41d00700c1c030035550640c483c04016006500090b12600c0d00d040515001030007490810b05007091aa101417600c0b00580d556810184442c04010401286880203a4041001120020001d203444006800012044402071049500d0000240c080c0c241e0782c8058020720701e002c0e942c1520280715904607115412002c1240c024020402c407070b008510140128a07280586100612060781c50a808440320b070400485451107010401203400425075900010307000d06070500100b402c0c1f800c41804c020485100d40e041134040c1d041030260803020b80e00031400400994040c10301176 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 427277023 1250 427275773 427275787
    0x90204020f07060e0c010503070f03090c0806090312150f01030b01140f120f1017100212090c040507020601140f040501151101111b160305010c09050a0509010308 71
    0x50180c0101c145201c245000031402609104541e0003060744220f01000b50b61250b800c5600440e6a4802150f09a0100e29140c402c00c888034131070fa0000490a0264200050140d25088000d050100644140e0010f600c041a41700c615544100000c0c0c00c1018519031194400300040401c154400c0d40c50002d0500d41e0f14038040700584d02550700d00207880d20481001e03680d40120361003054603401034150300d0405500c650015004007072030305109000e060b000c20009003036850705041c0c403209510607400810754001c09207a105603c40d14000f0302500b9003014551903c500e010101c180c41c1041314581d0750701c541e0829083c004000d40226407241550040890071000e1903004011401d080c004581c12030b0014680710000450704401140c150b110102541c440301311440135a81c4509a030071074024220041c01c03c02c1452180e0114000e1000340704040f000317a0b000e09401c4982111000d82a078420350380c80c0d450301d5032110751a50165038030020b000200e13540032070f942c280004a200150140001000c450000481c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 427278273 1250 427277023 427277029
    0x5010921020d080a1709100b120723041b1803020a0e010f0e10051309050d0801050a0b1602040b0f0306042111060406050a0e0703050105012102130902 66
    0x25189040e0054162654000107242492140d030010012030001020005181d4801e40c49a07120750146440c0300080003507c5802c4800c50090020700c024a03449204207008420700c000034403542c0700500c5c2081d0b1119602d201517048220101002010521592030046400058404a0000e83c50000d02d450506285e04055030090705500c2540c0010354008281032000a4488440801c14180d9160181c00355805a0381d500c0304c1d1000c1025500c22000341c941c040288120b0900d038000941c01c499050000c2981c070310a84411f4208002070b079a4400003510140140410705202e42003400906807c400329140c0120400b1904000001c0b6100034401d94854403002440e0395200b5200c0c951a60060503030784641814540125a10f0308075072018800b00400814002150044401c00d003060640006045155a5941c0d50001807030003d0084680075600c0300440c82d003803000c1000784082c40c447e400002e25541000520b06640803034190745581c100380d08000c074005882d1305098180009260002150f01500c2c0e01c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 427279523 1250 427278273 427278329
    0x50d09020a0b0c0708010c0212181903050a030f0921020a08150a0c09060503010509090a060f0b1e030703260d0207031e082403010507020d090b04050109 67
    0x415400080080f460400781040403490700110750300d280c020050a1a1400282e880d452200a00c042c220414000750410305200e41c180401180000e01c0c00c10120140013002480a41e690000c1d142c0e603002ca00300c0c800301a04101d4600f901d1246042500880d460402e20028488408450440b0700c41c1c000d6118045440d00c21013040034180d500140c62543c00007190300e0400d030804075502110941098614003410340032700c5188054683c5543e0386441c5030700b44030030300c000c6d5500a80440100d124001c3c8150100d00184a9061a1401200c0201da9a106101044640441ea40c000c040800010310500210b41d00014031030200c0b6400000d0302c480400f158510703418807184180c0d0b09482d6100084004290415074020540e0b24881d40f562003400680c42c03c20540319070b8111084001c034219202040c600307841e116080400b004c5464410344c11f540070310701290030f40e0800e5850402592000d6403070200c642c0c01c40c1c07414000e402c0d511801c0d401c00d880d02000034811442442038000b9151110160100b100b0f807604 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 427280773 1250 427279523 427279529
    0x20a1706101211031e07050304050c040e031e0d3801020f0a0804050a06050307091a0c07030f020301060e071202070201140a1106090f420601030b040b01050d09020a 72
    0x3c91103459150820820a1103e030090440740d00810001c0001c0e00300380201c0940f030080da0050300501d00e5401c800d040c800103249000780c0a41070b110510501c04142e04070042c41c103074541c041c046d40f510340300c00c1c8002c6401e8a2150383e46034400b56100313228048403000e0481910080240350041c9540810150040c0e06000b00a20104018082c21040d5402c0c09040c10080041f26010344204058594618049490b4081500e400b0b0004a62150411480c401941d01d803049400042a091501d8000305003186414910b0b030080318041c510b00d45400561a00b8814440100383c0501c4030355142c83e007048010a809803605185080c03d0340445c0b5135055901c206440c074041c90504000c15501e0382102340140c0b42c681480e2408256102d50342c00a800e0300808540c02c07020102c134000601d400d9000b4a1b0f2090311441e0360781280001141c6c0302d050014803c8041c4003011b1044d8801800e0036a09001000500b5601d0100141e4051b50078200517100c1d82e40d00c6003c40b030000340b03641d0000860030a00d10001342034a0040d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 427282023 1250 427280773 427280801
    0x4140618060915040f0f150603020315090c010c0303060b0a020717030f0a301d0705030309040e010e031902010b01020a0309091508030c0f0625050a09050a09020a17061012 75
    0x1001c0c84500358032079440308c4280c078001c03002c07213000c401c20000d030b04d0b01d191044071104180c1e0442030341d4100710350040f010303030162904c40c2c01c010840030745039040700c0c0164015800400040e80580010082d101c0c21210203400c0700c01c0200550310700000b490a0f80d82d240702d515603c1c420801c04200d2140c501440c100c440702e030b17013040401c13000d10700c681840ca000141c928801a4121603034943c10303100380b0a400040c150704803140500a58100086201040010060102c050360380d9529000303070b10b00000d424401040800d8035944039201c441c414100081c21110101c0185040d5070002e070b0401c01003a0088000c104030b5151301d00110b5280308006030000301004641c400400c45c840880ca4031040707180429211a10b0303074004200e881c03903500d04858245410340c0c40d0a00100e01030502c441410b07a0b01c288002e00302400c103810070001c0b055840b000701e001112664801407170964089500407000d07500c034100d41140883d400300c140c2682403041c00a441e400b1821088410712103801d50f0039060740a60703008554402000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 427283273 1250 427282023 427282043
    0x803031609050409080a0315060207120813170d050a050405120109061109030c031203040206160510060e0f04031205150402030a0506040606020d0206060904140618060915040f0f 78
    0xa86407001040c0c101c0e82140000c81c2c00c05c00503952801110b40e817002249c2441e40101129458106900b42d180b5000c48141e550781c00c01c0146048613861000340e10b0061869580841d0f103507022691460804040b50304010812004103d485c5566a01105650030ba0344111002160b41e00020075140c0100300521006007480d043c0740c994618180341c000070b03003207080b000d0303040e1201c4416100c00c041d16150100d4242095040900220f070142c10914003031311740d0190b08420100da8120310303150345140a503036070b041d4600035031914410b010440310f0b0106990407900d81c0c501c09806051555015150000704a80481c03030703a079204000743c1503125108042021b4440a402103641e41040380c01880a000c040301c450340264206076001802c90b200046440034130b800d0b82c0c0a852240c469504002484402800035109048050b101d00103040051110f80c1c040d40c1003175030b43c3d0607214070030f16990b0404030f006000c9501e5800200400800604021100d81c0c019071140601000050f6450312030700414010802400b01074003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 427284523 1250 427283273 427283291
    0xb010305012f030c12090706140c0312040c0305030706230403080403120b04090303060f14010c0602030411040c0509032506030e0f0703080703080105040504020a050108060111010213030b0901050108030316090504 93
    0x1045c404150380c01c0c0d0f582c10800601c1300e271100c0322a105044035414150b00401c07020182c036140140781ea070000c0c070640c0030b890126625141c0724550303048440f00b51040c1e50b8803030250030114450b0003525034000130034034002c6070303403800c5c0d24044c00c40c140082002d0140007e0300a40b00c010001a800701c0d803c03031401030080004100c1418018000c103010f000d11142009032101c0800c3c00c80c0365010707504558030141d544a01040d00760340d50300060740003e031007116000d00b00da1419400d80d45a000e003107441403042c2c0e501d517107501c0c0352010940341642c2c8000148490004c0381d05220640c100f241c008041d40c0040c200071580ca00780d0079400703250040c5c07104072101f00c2c080c00c3c4001c42042a4440189000744c000d41e124961a602c41c1e00300011101c0946000354410606103040090b94046ca000070391200c0141088441c035201c40c1e80d51826607019518008001e20a01c8042c02008000401e81d0782020003200200515070500428590740c0c84041e003c1100520410715005002d44a1038050014001c05002071204440c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 427285773 1250 427284523 427284541
    0xb0307180302041a033f0909010b070219050f060a020708070f030308180307110607060609021b0a022b050106270c09060f0c0602070b010305012f030c12 67
    0x4240d03040c0340c420b008100004070b03e42c0b1001d148a9446c10840c40124158001c4075401e0082900c1c090003201058003844004030542e2080c41307140c020074501411603520301113071040108206000c0c0381410310a05d1103400340200d407545000300c94410001d80340e2607601c1c4a00319099142c480642e007c1a02449540800300300d50003038400c00811688692103990715a22034014140f00f1002c4080422502c6e4400d112030808107000c00b05440c406030b0040c000914016051701c41805540080d088018000c6d00001d9201c034072803807007071440009800c0c00c026003101016940042e00c0320304c1c10354414423a00701c0507040300c02218501400b1044168024001c104841d600c625180804d4030400d09071010390003e0300040021029030113240c00c1c0d55044d54410f04154280f40c019200d00b03194040a004100040504200150741c5100900c0c16500408108030190303d507203071450070b41e1040e01100c030700940c1c1c4451001424007038008005a80c0c50f2038520507240d90302c1d80c0c001080b501440b44101080b840500a01030020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 427287023 1250 427285773 427285811
    0x7020d1b0807030f030c030504050405090703050c030111030a111b010b0901050621090f0106122009010b16020901060809060f0c09220c02030a0909060b030718030204 73
    0x203080c00c00c0c0501100d80d6642550340b034440034400642545500030328040002c1c85140e441c90030034403074101207040940303410204040f54812219410281d01951051051180800020302e001004074000c2c80900c0d500c4051604030301018041030f45043d240c400c2c8000824000d02560350f1418645403141c04000003440d8a030190628400d40d034080c41800001050034100f5004850b00c100409400d020328840700030009805c40c070001c150f2185405444a2040148400c0c001e500007070080b4452602451414103004e034050389521031045003c21140d80580c000e0700d0390200d0074115102d003a842131701c0d80c0103900d11404203504400001c0d40720003054008030755590400f841c2c3e4001c4100c4030407612030f0340d5494078115403180c0c00c6c2c801401c484014840254940381a01118140303c10b1044840342c104460041c01c001d0300c50318040030000da0000719992600030390003529480200322251050194034502481a09244005005c003810803510118090785100c0c1c003003d02005544c094010098003a0001d4900a65 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 427288273 1250 427287023 427287053
    0x9033018140f1003140a020403051209030a0f1b1206050603011424100819020a050904091e051c050301081c021219110102210a0207020d 60
    0xd52000202107490060100c111a50700c601401e0b01c0b102c03001d00c0007080807120002241408060300c034034450402c91138445086000300841440540c6550441c039296003030844100c0c09003c0310f04240076115182c0c0d00020303100304003a000100c4802d101c2043c1041050b00d41ca01c039a4101c5562940c2001500060000000152074090b0304100243e4a95000301403d9801070b640d0780e01ca50380e42d800880c0b52b44213515102070b9038041c58146203001c029140d0201e10f13440704510b000c0c0302103540c4508006502102851524442003908021031408003612400b82082c0200781050b405159138945000400c80e0f40003206d41252450381e00000e0040841c03074280d41c0c4445004840011b41600d004010b08a4090b00699042c0c4403000c02074101203070650141c03503641c0c486011110861240326a0700382410000e4008141d603c41e140412040480d60007000f41016616401c0640142c0c41007101c68a0075201c50700301c1561001c44010940540c0350b0130b0381070001c2e00806c0000f0323501c094250751076002c000358069884d2807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 427289523 1250 427288273 427288307
    0x717040b0c0c0a0e060a03020f040b120a0209070809060a1512050a0606290a020a0209070e010e01050406120b010e03010e0705130608030403120504090c0f080c0a090330 74
    0x90716031101144000a0704c11385200ea004810168148010b00e00384030651004940540b000496000110025004500158018020380c2242c4c0c41c80e01503040128030154400c1c002d060010080c20640d01080d902c0300000e10584d8070954030b113002d1701c01081c1d00000100400c6044140180c40e0303440e0602c2d9032200c100075012180146805c800140520003401c850034100300d4240c080030100d0130130a00e04090740c0480390707000843c096441c0030001a540d000c0240c1c05a5101d0360b501822015010000d49004480c20400d81407100c240800c104a50b8007030b5030a01ea43c03107008000b144032160000185e40080c40318100960550030f10340703a6090004001610412148100d4040350769140d0203850004541403800341404ca80c10400c001d0012072555145000310f11428523060703142071703914860350040b00d590500000c005207049403490a0345600c04103054001c0c103501c0b15185003a60f030800140898505210080c4030303040c120200e040e400094207424406031908001b0b041c000c00c0740803004003415150700b01c0541c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 427290773 1250 427289523 427289539
    0x512210a15060c020301021e04030c05040212011202030a0501060612110c2505090106030603020316051e0102030c060f04050d020109020d06050408070f05030c0d0c080717040b0c0c 79
    0x120880e54040c1c91840301c0115488041c103414034004403203074034800358141d8140d9004c009001002d4545190a02000e090802c81d07900d075411442c04507040155070b4030440c822401440f211024040341c1c840d542c1110911079000951701c2007403012070b003000e81b0f0ba000038085500e81900003035403541010400321203011203501000400140000c0c07900d0360103415018113865002c02090031405844c1c44a0781d0600305018881400140d0350000285500d000741c01c02d800080e1074040800850400704040c0c01c00c83d400b0703034503640070b5404c00001c00c030b031084902c1a600c844409000040c001e82d0003881114001c060201c150384481c60042d0108011130000e0381c00700d5681c45102e000c00c0390a44103114070510964001c00b041150a0191070300710140c00041c00560b6030340c10800c428000159280304220354688140013442d2079909008a070303400c10350769400709014011844d60750300c0015416003c8070b02c0d5952200002244040b503218a80390b9008640040803405400146071115071070004203a00729070012202c8072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 427292023 1250 427290773 427290781
    0x1110c0c0306010f030b190c0306090506040b130b01030212010306063803280903091706010b0c0c0d0803040b0703020405130b0103020904060e0a0605011713051221 72
    0x50b60342d8424450481c0d881c20031403092000a04580f901900500800300114525040e0032441040701e0851500d100070a81d600020000b9108030300030030f80c1c8038401b102c00300140341c60080451584c442000460004e207680b6521007246030701a41c162a4181c11000a080711580c4910300741009126a010350600c8143e46e001840d00621201600100c0100b01702d00740070301e0403043d503c4804580016001083d0089078084011400c446000403030800d84000078003251402082c00c0142c51421140c0041c02e95521040c04440500c0c000580c0604580c0f200421540c1c2e000407203c501c3c1040801810954040101000401802543c1c0040e40c041c5005921340240c50b2104807007a0201d01c601d100307a42d0040d01c4203000c0c86007421554850395481c0010b040140c502159100010103c0b001ca4002e8030b140843c10090000c0b034070641c404c641c043d00082c00c101d04481e0103850003002c19400104103100c50105402d0300e404000c410b0120000c0c0c45072068003651902c0340641ca5404041d5081107400c01061158001703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 427293273 1250 427292023 427292029
    0x60a270e1e0601050421080a02030d0e070b070206031902030c03090f062401210e07050604031a091005070c0b0a091e03050c1b010906020303070e040b1201110c0c 71
    0x11800b4480c16102d0728030f03151822400140178140c44200415007414139401a000c521240014005014030b54007455031202c42c61710007000c0740c282c1030043c85103601000742403101104090860720303929011120306480f690340307003c69040441d50f0b003152580f150020051105001c00000954018a0b00d01c05840802194601c00381da281000c44407003070009583d855030140000c68100b000003480c0180b500c5d4a40701e8904015403003100810500134150707543c0d00702d5000f0990080c006074001c0c0204a411619007443d5880b40c1d0500d00d801840306024190745c0300401d000038002c100c0c0d440c2032003032000180302d103262144020b040031415641c02e681c22500c0030b0000d00061218429101200c0c1c0c4007101340c4031122400c000d4500d400c2c3c200d00c101e040c0103040200c2d001002040144c0c209040d00001c3c24007541e45c0d1840014108905d543c011003d651050081c0b00e081504400070074a4041c003640c0024545040a0014030200305841c81441c01d54079014980b00d01c442c804008000d40f52080c1e04551110183c5814 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 427294523 1250 427293273 427293331
    0xf1201060c050a060c0c05060916050a0e010603020a09180209120a0c0e070509090f0403031401081011040315150b070803040b07110336060a270e 64
    0x1c01401500103086840c0010401d5001701c03041000351801441401450761403034901142511600069407009081100070252228150094807080e1901544149442001c900c02c5c00103000d540c1c00e0503008100b440da02c034800c01d40e20004190501804138141c14011403200203500c4500100c0c052030880c4815502c03070400107510000c090b444010b104403646042c00023040c28101401c031800f040710810014180d6610b12010714000c941d1241400180e0802e481c0290861703980d2402d49105058050040140c154003007414502da00c030008000c01c2c40e00c2000100c68940c0b0494200514014031140105001d45c1c281c2d01480c0c00c10320f002e615440998559102140324011420002c00704503013000018001051080400d421500a0034038a004107604698542113421080d0b2a404048484259501c00c036000c0342500a0074a026080f00020780d92030002c50650b01ca01d0400d0818802c1c4843d40000c41c00a406107001d149100d90407444505841d400580c0071244103450348041240d40403507011131021030500d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 427295773 1250 427294523 427294547
    0x80310140f040c0e0415090c08070c1101030615030b1e0a031509050f250e070c140d020109031d0603011503020c010213050306090a03021e0f01020f120106 68
    0x11039540510380000412010f03003000c030110400c0080d03c0b000080c2c1070311035010f010b228244003030000d50314030b091480941c00c07518030030b490b0b10410001909010072035412000810b0740d150000381d48140d42d0784003c0180c0281002d5480480421514440f50b401154180d0002c003240c1c1c41190842c60500c80c030005413802c022900415680545964000c10008060503840880303401c03242804240845d540d00d42c68100301c030241a454158000f1000c0100041125840ca4441c51500d01240b49050900800d8400c10100915600501c50070341c2198080c00010360000400c182c2000440702c05981080b0001e018002c00c0c82c0480100d80d02d08103428041c03c0401940440345400b03484141140c0ca42a50b41005944c205005d8090503802c0028800110080c00280400e0f09100f1303104408500e00000d00d8039090004000300b006030000548000046e0f40800c010702e0a00c1c241180c48103c2219251540c2001c80b2090010080d41c0300198105403580e084014107128240d80f8103120081e07036100d005956002c0300075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 427297023 1250 427295773 427295779
    0x20304060516020301060303020304031518030806030c0d2105160206130f03081902060402090f07090b04080609120307170a2405031905030d0902030c0603010308031014 74
    0x840144a010701c140302a0600903400001003007895400c2d0003090841c2d103540c0095005801c005014001e01000741500465148405000c10074481001c1c0900301c503084400004007000645000b00b034440ea01007041641000c801002c5040100c2c06290840c444901641c941c6040c005894130b207207001e070050f015510b03144116610018000d40d0351b820003e0340d81c4003802507030f413040d14084040f03802d2002040c8100507601c5046041e54072002a01d0344115103441021070411540704804120050325440c2401da004514959050401c1c0c543c2c0400342c901c0102a00141940741c40428001152000028000e0058800c0001e44084036000c18844029110444131040410303c82e0302070242400038540c24550104030203100040c00110350191f0140790700f040710400d1003c0e840310300c14082450140000e141c80e407038961034800050f11907601e10b61640140f8004243d883d03510641074040d034506020025403041d0040c101c680d2582c4034a4034007403d810940b2000510189048041004400444900d200032801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 427298273 1250 427297023 427297027
    0x30203071e0f0906053109021f03020909090601361e0507020714060309071203120c020a150b0d080a0c03032a0f03110301030b09060708070203 63
    0xd900a180030200d081d645a034030380d202001030100719a0342c1000150006030804601c40b8a02000c010300e404044890403582c2c041c5601c032911030080307080841c094201080c4089085085400080c0d009103084c4507116442840503d0394903480c1d450b5009001e2070008503244a0940c50301d80c100756540030709005081600607184680580305142d01d014002584106640641303800c5c1072494601516040700b0443c10750202c403040e017845d0b00104e0050742c0d0b00100f244000d010540c90203407030061003003107626800e0007000004042286502d040c82a5000b50000d031a5502183e03030340b4034004041d0880064141011840c11480003815440400c0d40b842c0c480e00010165101c1c5144c1105d0401448442c041380d60082c107892401001032640005400701042c1900d582051040c942009426980ea07641c41c02c404040008500801c1072081002c0011400945406400d040f4500f80690042c0442d1850361482e0300c01100000810022054180c1700b91140401d6441e6a100d1160564060500392a04070158000b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 427299523 1250 427298273 427298279
    0x3191e05060402010c14012a0206060a06050d0204030b010e0103050706022b021c0305070e09010f0b03040302070e0c0a0f032903030f0c0c030706050c030414121603140703020307 78
    0x41944050703802d500915079001c00c034030080c10390747c2150924101080084920269800344e4071040360032524512890028000b81e02c0c001c000a4080c04441c011102881000b00701c00d843d00c85654180c0300a10f6005c015030859584072098520043c40920086039648034003100403407103620100c0e04004002a80094042c0c1841103400c002c59281c2030784180007144264038019000d0020401c0ca14004c1405480c0020035007031071070009142c0098105c501d40181401e5004100d1260820b400000f21407006410686a031204d140490900007154800251501d03554140101c00c03401c031001b803a210301c240e00c59400c1d044a002c010743c1524481e207843d140c004907004904000c03240b032018001088a000301504d240200390211520140c02030003d0101d0799021600411540c1406c020a40291440d0b0806c141072170b40700c0e03c0c2e0303580e2071050b0301502c1c40f030040101d00c0030300c02c0c1c032080400f4030b5804605055500b04007c0750804400c81885200680369403042c40f22135200b0aa000c160305042d00e070040e000d4050760341 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 427300773 1250 427299523 427299527
    0x203060c0c03041706250e0f0d050105160e040905060c071a1e13020f0d0320010501091410060e010c060c0807080c0906040905060d0c170c090f0105100e03191e0506040201 75
    0x21800110b09d81010324241400d001540170b00c2140c0c0714180402d5003055110301481c0050481d07290442d403900651601d0b4151000c2140016455403100100c071f40a60391704d0461900c4e0180340381510400400c040303208180000300600840641088450082c000c4d141d50710b10400c0b8810881d12003000e5001000394890710141d00b8100262080d45010f8202955240c14902da030141e1008030000b0124213940d02d900500c10f06040f4000c1040c40d43c800d0084070b03094100740b040000241a20702c20300c4140b08445900c006164011000c1ca4000c64205000700641c0c0003440f805000d4030421906040041e04a07400180864008429210386440c007a241d85d0400e400c1214400003041e016242c540e100140410840c0010450189407001d8a0300d03001104035030f4041d44104c0d160241c0d50740150f204010348010040d14103800050389045500c02c0720208030540003510113031015801c40341d015803d4001c20841c6110441200d4202d15124807409e43c648003042e1402c4100c4601890324801840354001e0001304000d0341c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 427302023 1250 427300773 427300789
    0x1120b090105150f0a0b040906170604121d09160813030905010f020118080c19081e1612020c010318020126010f1706040203060c0c03041706250e 64
    0x1310140c103c1000d59181d1040b4250b9400541c041280d841e2520f40510840c006800e04464802c01c0b030b0300130708040c18540d079003103800c01500010008014186070440e050740f4220300e031880e40d20300244c0200c2c860f050503190446248020301c01d00d404540d1441c0880c06120700b0851307049a0380c1d019914441d00340c0c1850011a404261034200a0441d901c9003100d54418140841140405101d850140e07968009441d501d410320409040940c1c040000c454001d000c180340804540a00d60207190040301440c29140784203407800b54500c00031442c040925282c0401c41d440a42510308c60640e000c460300210840011000c1c0c2d04030030308480d11744444404240055000e080c261665040400c094102c021610415400780c2409900c00d00110b07610190030000030700c0c0792078050101d01150b40074100c603143c54cc0100c0d030b40d084040c190303401982c000662043c01800030f0055a014250215090107490009094680d407040140d61b98400f1003410b072001e142c0190b5001c04040b411075161100d0038040c1041d401c000c551 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 427303273 1250 427302023 427302049
    0x51023071805120304080d05070b1513180c0b2704020c030f19090e060f031009050708070602062712030a15050301061d0c04030b01120b09010515 64
    0x41c4141000700700350781d031039900700ca0f185a81c500850b00c40c0c2c81c0070012494090600900d030203120082100e04089040c11091a41c1f10000710042c040c200800804681280300c4214120511481c3c4022094540b203220110032081c2d00564040544035110f1518840307500c25102c00c2c05103c1520140040c0004014141904094005100509060301c00610a0441e84401002440342c0c400061802d0060003100e00601c4240540c40c1c06a040c900b080c451012420015181c0c0e44101c00c50403003021540d40030407c0d250b0f0564130040030300440c0d00c5480c0182e034071011406415542d014000002c1800d1f84000765081c440c00001010b80d0301200480180e0700b100403403c013040d0702030088074010f0509080d401d0085018412504002403050340c40900e0440c1d403256900514442d07410f1080800ca200c66520342648100040c0104010079242c0604464a070f10503640000c00141a1000010703115080c900c05011070b50141e08d1058444c0c0d21074201e0350880d2000c440c69507060208a000440c0c600301a4468000d03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 427304523 1250 427303273 427303307
    0x60a03090f0c0b0a0801090c091e180605011106100608071704080c0c01320405031606021b090c0d200307090603020304111909060305102307 62
    0x400241d490300007005490f03802280882d100050b004c000030b64400b00780303801010480010004d102e82d00340000c04510a82c0324902c921449104601c01c02409101407400074107045801e405502126510400601240c5c0318550110707150300d44207010044082151441038044610b20187e060406d0300950f8a0341000c2c20400401170010125480090720711003180c0118041c1c02442c1c0c4402003005e6030343c68142ca40001904000c1d4442c111f050441d254025900690340a02100c40e6012071800f1341d8055006030b51025604d481624000d4000c081d0700c4000b81d042d00c00c03e50036101e00604021001341030b15010f100303940d0490f252070001844018140090308040440c21404a40c1a030401c3c61308216010001461002440c00814004200c0e0040f8451000340a0b9040c19400c40c9041d40310788500001a100300c602402d9140240103201a001c1240c0c2d001d8030301e0680030030602c0d45a04007103545840100c502c507065850000c004011801c004e400000e8960314007102506955641e500f29100c007882503040d20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 427305773 1250 427304523 427304543
    0x15030b04111e04150804020f030d170601021207060b030c0a12030f0e0d0506090d020f060f130f050303071d100e04181b0902040b0d1a0904080309100b060a0309 70
    0xa50810b1000c1691306048103558518041c1040c2c0100090003003c4400d00b8800d82c00100c0380d00b03e05402000c42200c0c8011140b041c030082c0c1d00d210060342800d00c0d10000d4681076000103105810428543d01c240303a42170040e400c0380c0044004105100c1c040c0150300488100302c0d20103a140d40000e100d0044200d44410900c0e202800c401d01402181020750103c2d411a815001402082941c000800404529002c42d100910390030181d4001551100b0016000c1c52150301040000341504500b141c0d4078880980c80616402b155400c1d052443d201e400544483e400200e0b10035090f02618512004002200350041104410f40c0ca00300c070030b50743e20350500c00e081e412075110700300c0007658860b421100203c80d000300315090092080501c51640c01ca1b0725045000e103a44140410300020010405641c3c0090b1941000114110340341e0344004144c0900100d40d62102800081004000660b40550701603501602242c13101d480d1080d801c2e0640d03403c003000682101b014050340020500c01c1e004504802e02452002d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 427307023 1250 427305773 427305779
    0x409051906080609100203070f14070b07050a0909020708030f04150203100302120304120222050a06090b01090303020c01140c0604050c0102210d020c0c0a15030b04111e04 75
    0x503075081c0c0d80010720680203901003040d5800207001442240c4a820403c42c6145001c17400641060166190314040001005410340c600030008112200d59401c413405400c145020007000f401a440300841400040f071981700011000f006009a82d08030b540803c0701410740d521601915000000100240c41594110b411500c0d5680386200440c000c0503a9a26902d4250030350040c4012036140035491200c42c1e000300010803414915240540e00160304a40ca0b55141c640084803842c80c800030b1350b03500d0b4901d240106200e10003403140d0041d42202c0c031080090094440351030045da00b942031840060007580003000050580d610403204403102c049903091483c204030050b0b2080d0701c0e2486c12641290298801c244180a03580c0400180c0e100d040c440c480741e40c0000740340c0c80d803a01c28082c08034801a102e07008601d04008034018446045142c1006d4006020725944031b064050b054079038580200420310b4580c11181a042a0154164008484000390303d09401c44540d014034419032014040008030600001c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 427308273 1250 427307023 427307071
    0x18120706020f09040f0f0b01170604180c0603060302131e05130b010902040512120415111609050705090102070b0702010e060d1506030b09040b0603280b0912040905 72
    0x2070707662661001700042101d61144480104d03801c010910781404004641e181100e1103152000b648000260750201c0c000c0e491a4001e9204c18154100526102c0d0204000c031701c15505034005411a4000c48015041d100070204035030881d10002e00d00070002d00110401c0e64161010f03002070350808564103ca829400c1c0c40e0300e40e541401401e070800c00b01190009410025407404a161301301c0d018440004d0102040c40031f420800600c9288035800510400300c02542c00365008104030541d44c02c444d401d9034035001d810f03007429814100300d000318205507141c08007041d900d07032048042d15190300701a001010300754241031f00603a440d004040c00301c0c100206820780c02190744980d00136145481c1e185c04003080d4020071310700e43c03c0d8000c0c1540211080624080202e80c655503612269500290001c0280c030594541001007403c2142c0c4104800140c1d4881d110039094600d410105182240540c0d50389d080c540796580340341c0e100d07444140040350440080c070007030042851507481580c01a4071f000710641c4401c800510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 427309523 1250 427308273 427308281
    0x70806120a110a06110304061404170a0b0703051303120608011803030b01020a021021180203011d070303080a270501240b0a05041a0318120706020f0904 67
    0x10458030540b54010a05182c00c10300d50100c050802030030050351024036907107055628080c3e40705000030020007000c544151801d01085901030104405004d400e100c0c80d00c1d0840c0d50707521a100481b0500318400c00140c07500c0c401c1c85a2400744030380c00c189402aa8803038a0889690340b00702c0031410015a1a507000504031070034400e040c13140c0d0028580380800089400c010f8100c0b0020301149055410050b0f0103001a0b440e00e051080d0700e8050b0401585000e0510b42010001c0c10086c0100c1c003140c45c1035044540c00b4030050681b40e03041e108500a01c01110507103000c0519111403144440300f98041d40042c070010740940202c40d8000f03880d0100048421381d00601d0540000e00c240e6214042203110448414001c007070040c0c440d40da503401d03100405a140b42140c0f40002d1101e00c2401d00c2d001b0081800b01200788100200d40c0244228969103a001d480113108a0031a88207481c15134248110b1a0520a1001c0c01f194101400545442d00c600344001a11520080d50045078145a0003004001e0386a01b50350f2442 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 427310773 1250 427309523 427309543
    0x12022b0e01110307031e020d080c070816030302220315050c0d05040804030c060f020a02060c0109020d0c0e06011d0f041427120711010c0f0803060f0d0b07080612 71
    0x161b00c80d1104c082c00103018a03e000351054200315041000c9140902c0d0300110b895402407203500c1400c0d0703100705a007002a601d0050f904c1039043c81400c0304000d014141e0503005031607c5000c100c19034141c03848903000407800c036843c2d02c0014803400c80c010040c4200382241d03210940c01044803c00914060710b100600c0d003200c001320703811a00e01c40c02003414418080c60242c07440c054105410b00304081500e142010355281310800e0002c3c8189000506a02d00a00a4210610040c0e0160005080d55020326001aa0311000d000d544807112180f030000b036180d881500c961411a081480300c80c4d408032008188503ca030762440d805030300941c03104c5180407907031001d003800781c0310f240141c81814008003d603000c03100e41203001ea242507055100034800c030150a9001d0407034013142e91128000034030018120040e2401e900e5808044c10040c1443d4829080c0600c0f407008502c0394038100c4920306070100d0f00c0200300c80003882100140110f8041400074040c00c0c0160714942d0400402803007400ca03c52404501031518000d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 427312023 1250 427310773 427310777
    0x31e120f02060711150622020705010e030403020904080c1207050a060f0b03121c061e08070321090504150321050f0d06090912022b0e0111030703 64
    0x44200002035414005240c020300a49007079984130761004070540e540e2940c41c81c0d0900240da61000310b11039036210030041000c4004807001c540001510303006100250498407003a501542012040c05010001008039001d50354014000440d54440703071100311064000394981d282500c9144200d0701404030001c041c02c0c1c1c8511480c0100000d007014034054054032100701014502c6410100080ca15a5003c104c4c90401d610385600c054444140b040e2080c00c140c1c030a98800b045500d00b40d030108005480b41c280e41c00314881060341b188c0440c0d4440040f9945c0d003451001030941c48540b400107541c1420303503449481942041c41c01070189a200c000180464204461507501c11201220803c02c0000e9034800c0c50022441200a0302c9504c24404042d01900c00e500d822841601e00141c000140b8a069020b4009010501010030000b030552030b0240601c85680d00400140c401c0c160006043c41d100130922100764090752007100008101c440507140c0170740346a040c5041c89039440c0e41500120040020340a40750182d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 427313273 1250 427312023 427312037
    0x9010b030114011d0402060d0902041401030f0506010b040e010b07051c090906140f010c0f0510200c2523040608030a0813020d050d02060619050a031e12 67
    0x240060351075031121404c0704580000c101000701503130f998030565201c0421481c1c0812800250310020300200001c060507055401c0f40000442032080030380c0303103054561240080f0395544e41c07100c0c502c2d0440d020b03d108415002c8404001881240c41c800b0107000300500c208200c822000c1c02d44444407a54500d520284001160b02e002001b2610740c2d1b006540c01006292000c1e4001280301d0f020a8000c8050b010325414070140720701000030010601e085d000c00d1a00141a1102c0c81d80980c4908050144000c0f600c5000041640a807848059801110445840c7c540103225601c4840e10084890401c200e92844040c502000001e41506820340d880e20b010365122503c50407080d800030001102d00c11342117440c0d00e40c024040b01c0091500040000d07000f8500718511040d0941520008c0d00c0d02400050090003070003818211040690001802c50003070300121005d000c1800d074800080b90f085068480c15510140c0c4035020004214050791802c010907100326290189481526100e0030310b07450120050001d410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 427314523 1250 427313273 427313279
    0xc1b010c1e0f0e1c020607050c0a17062712040302100302041d04050705150304062a211401030308100b0316020109050f011d0a0c0e09010b03011401 65
    0xe040503041c0120003810309040b0310001070b1008194092002c0d105018003c64201030044411150040a0f5568020b1079142d03a940b0074903050b6160384845001501030b0103400d10125802403443c40c000c0c200c0c004d03c4018055507031108050540f000c2443e4040e40401c88065200075024010b02c410302c0d15890340d407015662a4038603c14031441c0006e040510041501c144818070200c2041d0311b103107150800b0480b500c8e001e034503141051800d0510715401141d02409001301d144400800e01d01540c49140192420801c0c01001e0201c010041442c410001540d244046406900c034000e24440030070610650020703449200008280003100c03d82c0019482840d40c01004104040d8010704031544820074030007200015180074600071741400040e152040155038004004035251003540031558182d003020031079030607074a0420051b00800c4142c80c03c5881d4510b150610050300c0000482c7d00602c3c3d1f00a000e566042d1400003070701100d43d00904200030035500c0320000c2d03c00399400d001d07a04104030000c10034821545 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 427315773 1250 427314523 427314557
    0x7170108030a0801150503130c08010f0608060901050405191a04030203120c0c0304030201050d0915020d0609090b06040b0303070f110127030206030601050d020309280b0c1b010c 78
    0x90f05a0150300c1100d828030780c81c401e1a500c401540c1c0c0101410442101c20300c02850240303070300406504100400d600c0c142241c1c8030040244c20002c112640e00069039403e8540d0100d0a083c0c3e0022600540f2613031007140112540080c0c00c881545c03079070040c000c4000041140f408809211420f840607401640089191520b071245c0c20802034200101807074551901c1030501941340c4a01983c400641444000300c0c0088070800b90750040006a0351106401710010b10000703048000f5000100c0408400e41380c0740c00480c1706801c5101f20b1404507003182080c0a02e03625181040041c2220708802d40e010f0009008120000e00010f516034042d91042940103c15440200010b104000c042c00040342c0c81c5540b40c4c4061080440703440d60050f42d4054031216525920240181da0340c0c42044900c152541c800401c001144401117510f584c4249450000f1003086410759803c19a0402510301130110076001010072100d0310703410001e24144510861041c09280e91060540c00c44030201000400309500c030324003150f405 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 427317023 1250 427315773 427315787
    0xb0312030a051303020d1211070309081b0d0f030c052a06040e0a0b031612150b03031204150204060806010e0a0f0612020c0307150b180403030507170108030a 69
    0x12050958040c3c0101403502c0c025502da804046d020184805108151010842ca0b0802c1c48410000150280e4400d16803030000c180d100d6a00c5108241e014240d1901c04610480111401104d0001e180681c1e188050321940000c42c2c8044049003801108119900010010302001015a040982c03448641d0305c0040030052200d4aa0041445548108024040146042d602642041480800080701100c02000c2441c105011070110501c106211000690450f09624941d6041c80350b0102c030282e2030f20085400a8600c55110958150000d010303400301242044603159205d4000d84521140100c1c141e242412030f402600301e8400610054100030706945c018071b400703100d064242d42d09500503191851031071104401d800b490303040003400a070326070042080d9010b5030081078880065a96803203840c5000d105c0c20010039110740380399007060030a6103245081910340040c42120304448a41d659079940c214010305002341082d061000742c5501d400300818050006000e801d001008658800242c10050061 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 427318273 1250 427317023 427317031
    0xd0503010f120b0414010b03030301081e061608131a0601030b1005030610050f030129040305030a051606060303050408100902150c100212160c0f03050d0b0312030a05 73
    0x180029a0007000040007401043c1e0312680010300001c05d01040c03445540501903035a00781e030789440b0200012070345400124545200b00c7c504401c00f4030740150000110b44480c42240c04040c03015910302c0303820503c0e001e45500c540c0510707c00e40c070b060350304496510303000101c02072501c080103003101d00200041d42d60140314a80008000b242c1807100440e894100501c80c3c84000c040600501200d90102c0140b4084d205a403424010f890141c1c0d2603603103859141c0164501e00304862603019100141d40f90545011046406603034108010b5440c012040c5000d481030750012550301c25424050000c000800d015101d058003861003503950b15510b0740361141d058a420862240944014546000380c0010395030920a00003078550600440d844005410240341007840c411041490180002a0310018a5007100028410041e40594a0450000c140e003244c3c0f401800a0041a0011400141000c00d0052000c2c0c08120721443c80401c803070651a000c64200001c83c800f00038059408000e0040440c403d000e2a940 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 427319523 1250 427318273 427318289
    0x906061706011805100e04140702011103010e040809060408030c060a0b0612010905091f050601080f010b0d0b1f02030909010801110f090a090507051306020d050720030d0503010f 78
    0x803002583c0802d01403040c14425540310ba01d020000e01c0260740a0003088024410042c400c000d1004000e4111005200448000d8015464940c460040300880d1042d00e041c1c5807982c03220f414a43c0d81e961100c074164072613402e02c0d0340640d05000004000004000400c04804480042c005504040c0c0c010020795001c0c00c91544200020700c4031040c0c0c1c40190031140c3c1181e101d0600451243c4900c0c94441c109440e41d007800d05210190465040158a1604418080c200030398403a8203d644104610b880c00b5820301034510002c5c8108817110300fa18854200700c808800c0140340c0c213a2100100c0310b0705107407a034103040f8202581020034001450b14140c05c21a00500d5918000e0103456020302c02d181041c800c0440c0d101817460301103205c14072529122008001303081c038000100018240030401600d280c002410865098050410100c0c41a1000c20844040b0615481c1c0601342006582c0709101c000134544542d101000991040b2078a07034081000c0c070442c030040d0f110207aa9506222170000f000714a5040220 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 427320773 1250 427319523 427319537
    0x41122060813060f06031e0b06060304030c111513140402040e1306020408030f040e071e050d090b16090602030304021003020c0309030a081804051005100207090606170601 75
    0x808052494219a802d0390161001600d00302c52040d5070010201501701034004a801c1700041c11000fa03880e00e5581c903034020651101c00e07076101c10400c4850710048400500050b8006162400540034401d0080d00c0c03403000704004220100304810103102d8011540c040d1400084a400f000301400150988036145826a420b500d05401c0c03c0e4000d030700c600e016041700c83c540078241c000801e00846905a50140200605072640c401c0e4441d0b0503102074105005030300c0803202010100e51118002c01940c07540725100c0300c4030098882d030710100750b03001d0300200d03092611030303859000040005010120f13480c85034618500c0110104904140107203160081d07080003082d0340c070400038080503070b4518a00c0d082c00c5a441c030b00566160909140a07045004006020360544981d40d0000c0402c1070f2080034203004288800c5c1e41040820480400c01510400d0f04e080a4151848106004905000c3c0c02c1012505007401220041aa03403602c80c03040700d406612041c0041c00000c030000f4080340d20020140c101c642460103079 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 427322023 1250 427320773 427320781
    0xf0302011a3f07060804060506011110020c0a08030103050120070809090402041e05040204110a05040302040b060c0d0e130605030d0f1b03080a050c160807020411220608 74
    0x8601018124458280001040300100c4a45aa500c0c50740e4030030486041c3c2d01d0080d43c0352805070480034140c0703084528a04280004d0b42551240c00350348100700069004026204a946a0400a50103420301020a00a000400c804100117200440c001e6110b01e00004611503d14413030440084582042980c02e80d04102030341c0030401580070b0301c41e9010215555800c2c0e032550320000300240181000c19110701d80c14400c1e95468035a40d80a14403840c000d0307605022103102d56500080724440c01c541c05003c41c5003448188054241070340300410308840504202e2900362283c200d40c1ca001c007161181000030300405200300e600c0c105080c0b40040c08131628020b004860503c00000c3d141c041c5038003108104500d4030002840144a601c00503410403854244280341d0b19241070040c003418085a07881032007030070440807544044840003199440c1e03070400748520007018181e95096181e80488001ea030300984039412040003c5445d402421002002d0034424070210710503500003244242e59125105020700c5500700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 427323273 1250 427322023 427322059
    0x501050c03060105070b0c1c0c030b030304050a12110418050f0105070e0d02030703080d020c0f06010b070b0c13090e010f0507052b0606170c0403020105040513090f0302011a 76
    0x385171311950040781031602d551600300d6443d0600508d0001100c00111000c1c2170b0f03155515070301c807030102c2a0b03e58081c01a08851000d16a40307200b2072040d107411a00c845030411620300d9a18414100c1445501100109585a80001e040e1510180301c0303270300008190480c2040090811900300d001170325030000c0c8403c2c500100301800b010140d07102c9074001c045840c10441107507018449030003d144e20284441d194988210542c00035001009090428420a0706045209030001079450480d8144966a8682400c83c0d5400000701d0700134001c1800b010051020320200e487c0030780500050098480c00103940c0ca2000c14503400d403038200c0e080703018651500c0140443c0540c080308440f56112500c07107003040d0f80d800303904c15203500701d030180001c41c03191500308081078141d0700081140714100c0780c038245c80d0182c40b0000409401e103c0d92000a0204408000c00c03c02802e200080c40340c02143d42400049080301c070741300c60001941c01401200180d54401c0900d17000d28605280105902c401e880440101e401c1c0b05030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 427324523 1250 427323273 427323277
    0x61103090904151b09050d150b01050415080708010504090201270503060f040c1e030609030c0813030203071a180a0f0303030c020c1c0201031104091104030501050c03060105 76
    0x24034081d8004800107000d00610326501e45110b02d10700820450350b09001118801c85180da02d40000140c5003100c00161844c200c5421382145030032031940c50b152280146013800a101d1813662505024060100007440c5030231a03d0140400c50940350507150f803400c130700003c00c004416040280f1840c901010080540da0007071945081d414403c5403695111850513503500040c1d4241c0c4400d0303062141104108102c10164130580c012031090060010494a130400d4100b0000ca5052035115034030700d80c01c20404604203401a92019000781000701c02080c59071650b270401c1d17003c0244204803e013031020070030842c2030030000b100040510134200480f10400b0b020f654074900c15421960840707030036030380141040d40e80e20207101e000b04004113421808541d81c0c41c01601a0049640300030140c011095064842d0901e000440c0e800d06032440d2002c1a07801c6940150010b200c622026265001c0c00d0001040c0c501240c4200341c8419440102c071500c0728a5480c01d5825200010800d41c14501c1c107106110441e600501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 427325773 1250 427324523 427324537
    0x10f09030f12020409020703030e0c01090608042603013203070b0c030d0501170f0a0b0601080405120f0d0501050307050a03020904030c020415060314010501050316030608010905030301060207061103 87
    0x60000080c40200ba502c4010b40103a0b080220458400640c41d02050b42507030003084003141c10020344121405610055680c5151403190a0200d41c1d0b03074000400242002141c042c00403041d1050348001455a040d42c22590000d800c0171120406015003041e00c2052800c800c0c00004c001c41100040c0c2103c0c8011945031000c80c0708080c5120400305440320941014010b40700b42e04c9500208005039a9a800c44144180740020110002d0080019241100c84041020003880f500514040c01c19144d440044540c010018010382d154001c000c600c10311807080750300602038134480d180400e4584c0140b480c58411110180e000c10311aa11071081003003d500e40b04500d80c1144d404649086850f62207003426125040f10f40c0d0003c0d48a072811020180101c580103810003550a6076a040104100300760060002c1d007004e02405001c240c040c40021018007000400d00151120b614002c200380350750b460a24255008500200c80907040800140421641006030f080140020318100c1d0ba0307400002c10031500e900c240f030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 427327023 1250 427325773 427325777
    0xe07170613110d0206070f0305070b0903190e12072405120406020903120f0424080612011e02040e0709031104020304082b0e160e04050726010f09030f 66
    0x1403d1842959561000d40d1100d40e0414501283c4c2440c1c0d1a000700680c0c040b010451f501107203000071030801c1030000709407040007601c0070101401d038828107000d66842c1e101c0850a035000385094620b010f1014284071001c01080d14005402211848110600000c4444903244c41004400e12002d94980000d04600b904242c002d10016070340c00342034001c81d05148180e0210402800d0001d00c0007840ba004600a00407584003001990302065202486021000da00d440080081d00003c0414614a40040c500000c0790303400000081c4260ba107404116a8030072045180d2400390b000c2420404032024480d081e500100614203020803904542e1101c0c80010403180711400b46a0100002d0100802c4504075002524500c0c10207a442c03400b5446c600c2d2480b600d00d04841014144801e4229012000a02881c1034a070880344503115401d02c030301107541c220010b00c25200707442000030004203400240005032100d10310184214569001c0c04080f401d40d1158103140c840306240c8101900841e40c01400c0d8a2400214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 427328273 1250 427327023 427327039
    0x1030f09020f13090503040e0603070f03050604060e03040f030b15122e05012601111806090411040e070212030106032a0201020408100b0d030c060e0717061311 70
    0x90040d01d0300400b00b804c40200a44400a40851900300c6500843d1145c80c0440c01c540c6129242c1a0b02e070002085440020040d50010012500160032500081c00804900c422641095078038400c0b0700b000c0c0ca841d0300544100c3c800030140310303604c464000c2c4410590010340e0182404036180249542e202103012800c40960810340910840c80710309103100d00d078411110f40c1400340f941c590110302101445412a540c03018403540240010000c1070299a4280c4000c10415082c0208001d4103900800000545d44c0e00c207404022a503d180d5480c4200e403050088240c40c19240c60500000da030301080090140c070705544c000c1e06040d4143e90500100d9040d5040303440c010401c602425940c04480001c2500c9114010503155100c03216581503029004503950702007100d81e140300c50754203e4100c5444014141d00300c0e03c2041800d0103c1d001da294454460f105110002e50364500412581c20581c0540142280000c5004c0700c0031100c2c01001600d420a01c5000010489002c9641304442580b141400c507006a1391 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 427329523 1250 427328273 427328299
    0xa141912091b081b0a05040b0a0308040306050430030209011707110c0906030c010f05130e06010311090f1c0f15060b0a02070504020304060e0f070501030f09020f 71
    0x2a04a22107065110794407162418000b045280c1c001d0340b0340035284091058161000c8000300d0001000042e40c07000d8102400e450502d002e00003e00900d82040340c02c0308404200000242c2c14900902c0114054000083c03603081524201d08078412180e60000c0e080060200361001c0054404400d0704460035060060359090002d00689440000002807403144074108100b000039604100d590b070310080a1303001d686140c5207240c20403002c020b054402c903800d50302002e081c40695015283c0d8500c200e040741402c60400c00c0b512081c1042c50050f411104242183c90b040c8012941c00d8082e428500214080d00c130300b446801c801050800e00c404d08500e100300800082c1d503001da01c0d1552400d1103e07821040c41040e002c0e6600740f000e0f0b94524070303020320300309460003900140c800e155805640f003804055010382030962800c401c00c4065023025105650003961124024039030398081162440500149019140081c81c01700054201d400404030000c040b801c2151100c01617070303406a070a076107040498842c600c81d61 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 427330773 1250 427329523 427329557
    0xa0311041d360c010309030e04020714060103080a03050c1c09020105090d08041e030209010605030c1611010924050d3213030f0e010e10050a1419 64
    0x24034109101d5411501000c032002d4404002c0d441d00c1c1c0c40002002c42e02c01184000044040300d904500281c001054a14025080e1170701e60010840c4e01d0080d02c0d1001074400103802c01d41403510a0f03000325420200001c244e007201c0d8242c0a038a80c0b04034544105820120f22250700702001d02c400b0010780b091a91091084110382c001c40a5507054003000e40490740020b000e180c0009558440c6c0a445520150940140302040110a800080d6903000d400c0b110f9991a0802c02e172500d07040548608086074045c40404200b0f10700703800c80b83e03026014109004105194900140c0f20003400c1c0c006403000a030f80e01c43c081030802641300003000e1b8059031170042c1d65003c0900b0740200034400ca01c600e039402c21b801c0034a080110403580703519564420502c0c3c40001a1900b0101c105040d01d581c4006010900e0403040d0b01040b8061541121492018107046000705204800146194110300d903032004500d0200388102e00c180d103c00000308452401c00d15915185614400050035002d00c100b501c100108840c117107040b08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 427332023 1250 427330773 427330801
    0x12100c020303012313020f0405030c0402030601140a1103070f060b03010606050f09011202071a01060c0312091b0801020316050f0706050414060a0204090b040218010e22020a0311041d 80
    0x14a4031741045440756582c81120b1025489441803902c284075801414042c0c0c41c0ca4402c0368020441610b40020035003034101c2c0b082290f00801004e90601c100f0f01e00746141604c05100814030307144500b4020f00c20740041d2903c0d1049446840c0c0050080e032620f1801d00226400200700c458900d012242c10352030701d4204004070b0b8514004400e03400001e0000c00c0510421030500381d507403045010101207900036031f00d4400440395100b1201d07020300024280094440c0303410b001c1c1c0c0545600f5002d000c62840f41e4100706200c0b00d418082c0ea01500d0180c2d40041041070145500002c62160790349840c0940c41e0031110151000140141e10002c1d14440d42c8002240421030001e2112400c811014145d0300145001412580290400d00c05e082203207081080c100c0d214a003900c00c48440d00709149042451000c4c4500444d2003046030580d15030418075080000340c24041c0004844090300d1000405a501c00c0c010307800038165002c20009110900c0140402d00c81620018540080040c1c1d4401c954502d948038403602c5088 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 427333273 1250 427332023 427332049
    0x30f080c0d1d0123010302150d15031103031c0f09050a0309061706060a08060102010b03032206080106050414040f050f06090c0412140a0212100c0203030123 69
    0x29500e455512100318600000500103002c0d100020800d03402c0800740c02802c80310708881c00034150784010050006151100428040c102c0061034142000014610701c400c50310f2403800405000e1074414100b04100261468014044e001d40165003402007040c0d00281504940301c11801ca40c0e1200406491840300d070b0b000c001d01d00d030010f040700c0030082d2070304000d460b6400b00d025200c00141c20384c0060021200c404042400346a010708071034504000300c030045510000140800c3d045540701c0c1d5404035640c0c1c0c204003800544290b6010000650418024052410f0740e91707000710144181d8500402c0059000300a81d022244090810080b00900d04001002080d03000c0340d03044480d29040900020440500103a8445c0700f05850501c0180c850083c804024003a0b8810300c080089900001400510410480c12504a4000490303035400d2090780081c680305903860300c14410f40d0010318100803030001805a41020b03c81070010b035203154113000f0504e50040070707200c202c441c0c010b0500c4001c920341c40c2d981d510500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 427334523 1250 427333273 427333297
    0xf0301091b090b01030204050105040e0601180f05044a0d0e010e0a1404110c0105010b0c0d08010e060d23030408070801050c0301050d050a0804080c0a0909030f080c 72
    0x40700354044015070300000e40d8090311922900c0c00c001000d59501a00c00c132030a40c0e105031251820103162000c10524070718000c0c901d5040000c10034080c41c100c07650400000c040c0410a0501e036545003007006200466142d070522169469000c110b030030031031200b110b10340203880300f9420003807c0310300703500c02800300c0407284000051510a21540350055a840104042942c0c1d00b66101210351414004000701d583c0d46003d00b450780c683c04420307004245400c1e40309c003100100c03099080e400c0003d13503100c50f421514240d00080c140400041c0e1039100c20001d10060b086100c26081104865050616000624800408803805401e0500081045c0108283d0742c0444013078490351818001e41001700691242c0162086000612a4007408160103406004851207103150580d00c500b1030303291000b00440d00c411490256a20b00508a07102e021460010041c005044090010190000400184074030310f8920f50008000c58684021540001c0d840b52040391041c106c2d1030401069110003001000e54031690044180c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 427335773 1250 427334523 427334543
    0xc030f0528090c030b0403090317120f280e03070506090111070b19020f07030c020a0b120a090314070506061306050609010c0809030d1101140f011a0706090b0f090712020f030109 78
    0x52000901c00902d251852800607102c0c0351120307440450ba84100343e9070a100341e6903c40dc00350319202c0c01184007410214021000c140900304503510740c1541c0c0031500546d40350300000300308000ba010034042c1d542d0083c21004000d181035015180c90044000160034060b149000d05050b03541201c454041e6810701070180c03803441e9255035902e4003034180419800100e020740f04030b1400040e06422002035071010385c1c180350591450368030010354500604041104406100c40410320f28495690b0b18082e003820782c8250014003d50801400300a20490300c1401c03410790341e09040041c403103522030000707454100200307007040203191007580303030024050042c0803000341c05103c0c01210803003055001c05900850100c02e40200850311070b00c100640ba804085803107042e104c06190040003c1b41c10030b00c02022240101c0216402c10078503564550a03980c1e411811703982801c0e400c0034840c5c074110055042e504010f00000a2440b5071610740c03003107000c5080d400060300ca9211903402c50a261403c0d04003401455224035810f0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 427337023 1250 427335773 427335803
    0x11d01020705060c030c0904090206070615170c0f060304150f0b010810081e0f030301150f0905031905070302131b09050d060c030f0528090c030b04030903 68
    0x14001c1d007003481c0039900c0c1d100b01e03400f182d055125102205d00410003940e07402d1802d15a0000e11000c0c003d50b0710100d07040041000b030b180101e101407064694204550103001001c3c4d1410107514500341c0061000d94807500403282945240d03503900e48603e0008401d40e02141c4907a1036040000d6049100c1c203540e180c0c075003402d05103c0052159444011941c100f40c0307600301980c03204503441c1d482d40b029001d1104941c1c40b0b02039420b100d544400e40c2061505a680c12124111240094241950803c0c0e004d2103d0b481d19010f01c400c0ca6410100c81e4041c2484c0b440c080c1019031420000965491440e01550400321144200d0b405121091040202854000c0c011241207031407802c14000800f8000d021100160003450042c44442c0714065507011114001c1c10038080040075211a4020103c400d000707014507903076050b02005a40309000341481207031986280c3c61025401100d041e24050f015140300c441614241d80000015441c105020a803500301c485a4030380d40d80e600d408c1c2d4030054903800290003541950088 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 427338129 1106 427337023 427337081
    0x103060e1905150a0e150703090549050a0e1c14210c0f0709020403020f0616020f0102160602060f221401 47
    0x55216100c001158070344448800404039890703088016000c006146080c81e00340d100c00c02d04001d005191611500760785030718050554400c1b5140e06000305180078460360210304d419520004807040a0702602e81c1c00342458100d1002001004148114040c202207600c04c0910780e0750303e544503a0b000489610688040d00881942c0c4104046000301d040a82c0e03501c805401e405c44d1022101a83c45a541010b1030310744400c41c00340c5660741c019862160140c0b0089200c001c0640c0080700030b80c941c0301c68001c5508000d00140800d00030b21540b03c01252124040d070003001280c2c402c803002546c40c01001c003400704a001d04142003100c80a401421005070800c118245d00d0600142f05031860515500d10b000040503682e006040103a0003d42081101004151307001d400034508400080762015038601d00800c5009003100074142c01d403140814004e0f040c250442c0090300c1c0c04079070f04d813840b448840780 = true := by decide +kernel

theorem cover : BRFrame.Cov 427158273 427338129 := by
  have h0 := BRFrame.cov_init 427158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 427158273 ≤ n) (h2 : n < 427338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
