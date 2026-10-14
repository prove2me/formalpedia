-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0123
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:57:32.484958+00:00
-- url     : https://prove2.me/submissions/9e668b78-5838-4658-b8e6-e2a4b08cb0c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 21942452 ≤ n < 22122308 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 21943702 1250 21942452 21942457
    0x60103020105071209050a17120c1f0b040212090609010b06030402010809010603080324030102091005030406180f02040b03010510060e01050906030a020406020f07050a03020105030a02130306060501030b06 90
    0x280c060b16001d25040d841d03500d42c0a00001ca9a8020610003041c2c0d0118081e01d8a0300c18602510701d0101600c0070524182595140c040b8400c80031800e6601004035405011020511140d101123040c101c507c1c02c80d00001400140c4050361020790401d01c08650010b10803800d64095000d108d810080e0303002d0382c0782d0640d0740f402d0355080440304d5000307401000490019442204100d0380800c000e40001030441e01ea0b500e81c030140e070054502203851120440d11001103000c02c44100045441203000310302d02020741003c6800891a4501c850034810084001418811241c024034904000280c48210400191506500c1a5905102680658a4402e080500782814828580034880403000ca02c01c0c146080c10480703410f10000351130b40c10490700b40807104850301c40d540514015010300300096102c0c1c2c2082d82c024581500c50040500d55440340e031040140780c440b01d02480940c0d4080c600030b9034940d00d2884040c041d20400301000320287c100440082404515800039040e280d0981e17060140840366400c1000320b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 21944952 1250 21943702 21943709
    0x30c0703030f1707050906160302031306091d041523010e07081602120304050a11010c0f060b0d02061305040b04020702030705040c0e060301121205040305060a0903020309030a060902090105030601 86
    0x10101c40000c00c0a13103000340c015000064004100d00e2901c0d280e40780a0100405020b03040f405070f400400da445c140400c1210040113003d0070301e401000350b8031f00b0344401e42e22528062a87c05101e0310f400800e091210310582c1c5404102d11500c103000b40440c00c2959001c10100d80a61000c120f070090011071200c40b4844128040c82043da034400b425212a0f04005200078500b030800c007903200d01c1e401da00c49140720700c01942c469030144015003c0801142480c40044003181216030420060900d400002011071181988298000d5000103840e545000884e524003440680a03611940c08100c0912411091480c0e2095500555051103801901c074140426802003d030000e516030400101071215040ca40e0126274100c29a103041c9054690090211b41958000c0e00608005001070b0341c00401d001d854000034101c06281e29003145028a1a29490340b03c604c0030741600c0b1780c41e49491081c0c040c54420000e1320f0040e180181a100183c0e95464030030028000ba0104902034029800001000d240201d85213040f03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 21946202 1250 21944952 21944987
    0x20301051315080a030504170705030d050309120d02030405070503010501060e091f080303010801140705090108040f05010515030c04020403080a050f070803040c05090a0b03070612020408030c0703030f 88
    0x808100800501514a08206018510b81c010b40040c0505080221500c50b500a40f1295030b03881c200702e51420700070700808501a295229460800c4140c40003c1e502c050300e4210700d404c81d12529405929801e00f4940e40315841c121102080b680581c0b1700a50007580076500c00c6003116100744d92031041c14240c6100b4890100071a0548680812034184249803070341c0020b0145038288080c1c100c01d61064000000d4010000c1e40d44080011301c8840d0007485111441d00e8104c3c5d0485143c03a02040040492040c800c030581045640c40c0410104100160144440c0740e00c18002d1180307103456200c088071001c20742720705c074405c0c440d04d105c110103801c0c603100315420740f40c210804074a0b008004005031740e594403100000380c00200800c416000718030280c02841c0120300c503101c42c0c0f2040c2e1400081143c2c0380009850406004e10308244000160780000303050044407071a050900e0b901c2111030f500ca00074010740d4440b600ba401300181d8912158404900314043c1c038401e03215030380c0f40301c400c41c2c00703c510000e210f140c4400e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 21947452 1250 21946202 21946219
    0x702060402060a0f05090306040c0f0602010603020a1206020c061603060506070203030a0e030f0d0e0108010b120105010f02010f0504050a0203060f1009090809100903030e060a020601030f02121f06060302030105 92
    0xd02ca4812104c182ea01c0c125403e15a261905400100c1e19060007150103444161440c03005000d9040020b4540d802082c083c4000c2c04440d045d50001400f0f441e10f80f040d40d40e950200143e0400b00542c94050700d4003040028142d401c1854032601d0300000203110ae00b0070340000c0c940304001c10301c1d00e0b15006072035803150040c2c029801c0800000b03098800c002d000d441990b040c03245005032903e1101c10001c80001200d583e8451828298803400540a17040607001040c940c10107100700e002c1c0501701d089042c111142440c09031074070050117030142e005010041810160600741000c01090100028100041e00d01c01d40480e0180d40e200301104050702030554603030702c000140201c00c200b0800715402405246029440c3d2501c2c0492441c0040d555003403400b180781c0800e904460030400d01d50812500d810340d05064a215140560007200207444040502008ac59094594092020354551290000e00a10a00704485c40c1d00c981e05030500e03010b00320507900404a41051b4010400314440d0082e28100e0f90003400e00301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 21948702 1250 21947452 21947467
    0x50310060e18120a030213090b030d0e04020f0f032202010207030f11041a03070605040f0303320304060e01090314030601120203160306050301020a0f0c14070b09030105070206040206 80
    0x10340360410744903490b00d44a2003c0d8811030f001050020550454543c0b401031395681c00c0b503060203060020b9031003a8a610b2610050a51540300400c5030b072034074030707503454030924580c0301d200010000d00802418030340d2054042000041c0115520085001c0c0c1c60444580c4e0b040c0f034480c074042030411b60074030000740107802c01002000013441d402580b0440c035100300044801c2814450110f01260f03541c1c14455050710080c01d034000103040a00200024040a2804c00d04c2d0a09140c800c00d1054171603c00102081a00000c806115180c0c00304503040c100056821403c6005464002105810070788041e07a2403840e185445195280c148110b81c0b00c1d07603240c1c84540001c032030003081300d1250700000d140d541404410b40c641c6190444520055101e0b9200c2d1b07071528054201c44000804445140d00168001c0e88100701902055400031401e0101c9501c1e480c0800c091107880c58440c25400500c2007801c414401e492020500102c01c1c80a070040d0082a0001c01495440035012a650081500e01070740000f000c01021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 21949952 1250 21948702 21948721
    0x6060303031302090c19030207030305060d0203121312050c0325030b0c070204050405160b0403150e0f0d0903060e0a0c0e0702030909090604060e030a050301120f060507030501050310060e 82
    0x100d40c1700d1055082182484058404c0c1d02d528898080c031500001e03400140c000c109030701485096040001a15180440291940030981c1c0d81c0810040156501002c12502c01c2c09884ca05da0402801d50905d9400400345a4a4046c0d56503408a521034401e009102c6c02180358414007407049000040d4000003655030341b45484410b02644090030a0a21142c20007400025898a0080310f004030b1040e0001c22a9200c640140c1102d03a4240e0421646528100806c04c007251105100c5001d0741000c1600040052500a0007840e000c081e00d51021540290188a050300d034105d080c050449001d0f81e01070050b413402403041a00d0740c11100d0000e2071100094020b0003203281c03030500c403988460203004480c40e0041e050006100c81c0c6c1c0440e0a8480b0354000f004100c1000002c1c0100140308080000450600503041e2014009000501900c5045580501c1240921000e40510220f480c1c010008204078101014000d0240c402402020300a01c9410244028450144a914115a0020f18401c540e84604005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 21951202 1250 21949952 21949969
    0x705060121110402030408041d070207050301020c1c020304050a0305010b0118030201050d09020103110c0106170c030a0b0c04150201090c0614071e081603030b010806060409050a1103011706060303031302 89
    0x1900e47c2e020621011440801c000407020b03010003480000585440c02e294001c1c0340081540205d4000d0340140031382c00126500080712580078480c1c1400050070000b41c6002c900d180950381c82680d100c81101d03800020700c101075001881c10742003030340c49142d07040001410289001040c40300900080080001d0003490203a540b0520110b0320516010540510740b188010f2950818006034895954454080041100e00300c043c102c0b000811024001c810491000292150140100076003104c41c50f1000402c4812454112406040a00803c0304144c105000081c004d0001030707030440f009040e4140105089000d490490f114a00c13449001c0c0c58000166241c0819190132602c0201c1410211004000500448c01401d074400200710030401f9810282030080a40743e81c0280f041c1801a09024040c46481e50f07400c8a05031042d80710301140a41351095900010595074103400c18100e40800041707041c0c0c1084404801040c403100854440b52202420982c507484182c5401e14100d24501243d001820075250 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 21952452 1250 21951202 21951211
    0x40302090c0924180d08032a040306140609010f0b0c0106080303070314010f030506070507030507050609070501030e0102030c070f030212070602070209070c020d08090a0308070506012111040203 85
    0x40020f00901007440401d45844881e50340229080422044c40c615189001042441021914050031170580d440d11003803888098403642d20307100d200d042c00e888001d148035000040755035074004aa07515582c1c00c0c40c030010302003038502420010000e408101903103010400d19040e54500b20600440c9440c01559070345592140380d410210b5500c9000000e044581031000e1440703034015403408280202d22004010034002c05801c10500707403400140c18400b042000825661080d81401c6c1a80c1c1d8650030b050179105801a45002070040c8240801c01405080c08101001200c2080c4c030b003403016183c8008030500f030780001c44d488500384100f40651030204503a800544036240c0240141c4258100d44c603400c43e40b59002c41c5090310841d8000601d0411070801c450900d90105152400e100c1400c040c2d40010800e0441d20380151960702c01003001810742c1d5420a109008540c010304940d910881441c02940386e400134440c0c001a0324404c08550411425441400c0e0042e50100103024051070150070000203400203030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 21953702 1250 21952452 21952459
    0x3050906071220120a110a020d0c0c05040c0e040c02010e0a0b060a17061b0306032e090b090606030c01080f0406060909060905012d09110409030503040302010b06040302090c09 77
    0x7040c41d54100c0f8200001c00313244000309101032403450200451416111903a216003407106041010131481503011a90054002192411200d001c0542c14441d080c2e004580001e58003e00d081d071081040350b00021000e0100b20203440901c5660410300b000d83c200c403480030400055800001c0c40307400241c0303086142030780400c0c01040611460380b1000d0b290b030140380e50503820078294017a0040c06801c0c8001400c80702d203007061140007842c600d808408240c482c846040691980400715044403c1c80744a8040360b10002a01281000788408504000c1101d03c0b003551100702d02d01804001c58620300307011801104032101070b150445151515800d03003980c03042c010f00540d4103e41c6c03141e01003042c0d5618055480314078040c81c40072a2904050500c182140d81048518007800c100e00b110a180d108488200c280103904c1d0200022542500c1c1820005034000d450342d140e2003031900003c00d04050300500070f0b41c000d038060b600800000d41110706000d114402e50201a40c0300c4000c41c0010100031044c002480c00d5980039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 21954952 1250 21953702 21953741
    0xe0d0e031506040906060e040c080610051002100c0e120601030503030601050f070b0c0d1d0619090c0603090b07080606070605041416060e0406050a03140a0b0a060303030509060712 79
    0x2900c8540c11203401d6004401551442814231092128101404000e09212000b506d01402c000c6601900d00e2440d12a2602880c04035003a621024001d110180140042d60310520070050950307002800042100082441109114040d901e403000c00540b40d8140c950000007980b460f2205001034400d5001650400a4550100220800218496880c41c0251100100c0e581c50f00c02c48181d6505590042c08004040000072860240d100e400161680c0c01c51156400c0c5800d4003000c01100700501100c01e00035040138001d000000c2c0090303041d070001000f00c4c00b40f034100c0301070b4555401c111f401c4102640c11a90202d010321081000c14010703030156811a10403822049541c0c1a00c030110308048020060418a8440c40300402045800008031103d01d0000c40d410003126040c4130000718001804c2c0000342a6660325582415061410444072600310742010171200c181c600700300044d000e070044d4042100000d003000082000f4000000d41030380540040c0e25080200440b800d6160000c1c242c15800100c01ca940 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 21956202 1250 21954952 21954971
    0x4090822060e030307020a0e0c040e0c070501060f0605030109050c04030506090a0b0109090c09090c05030304300308040209061c03020c10050a0801060f0905130e0d0e03150604 77
    0x4051030304102045400c0c1101030549010405042c80a21040c014020703001003001c1c60041c0e840744084400d50300442c8414031945c0711a50b0f401070b41d00958100c41480070f403010030f0250b4200b5030070141480e1807060f00240800c90300c40c0a840100f80c554410034002ca03005000500c8040f401d034208550000e814990181002d649494075840c0100c20390704001a608294071807000d03c16801d0702240035040d0b558043c800300d805640c5201c04004a41304002a045d0340d16a600104a41059a6802044000c084945840e100e0354680780001590700342d0200c0780c0d48e82104d00440c4400f507101d0304e00d8a4041c0c0303a0040647c1c4680900c500e00e1001001980d000c81407020314640e1000c10080581400d000c1d9008018800380c51050203505220010038006100007405010b0440d60b00440d00d5054407114589210a485908004d580071105d80e0402ca5204d0b00f00c9508010840242d406000c10f5840442102cad00702111071000d072002071022030781f142c0542160340a9541d01240d1b2001c150050b10107400041d90400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 21957452 1250 21956202 21956227
    0x4050109150b1203040503030403060b03010b0316080d0806100e01030902031e01050f1b0c010b060703030c17010501020706210504060905060c180405130c180e0102070809040908 78
    0xc81640c0725011540e1030150341103d050148241029180c110f009510b020b0038480002d42d68026488024484c50b1110110b0701981c400f0340001c401e414014045407484104480e031080f10401d00e00401209200d40144003005510031823403135001c0d0401800404040c000c445044558504030907166052684403100c000060300d003000544001c080380f0780001000c0c8040d00756142520400703080d030303426001c24000380480c110100030308180c4424034000c0d60380e65082d0001458058182100719070391108008c6610720626805801104915510703690740c00285a001c0386001c0024030a006650041e806018280150360060407540342c8052000015070800040041d0311003980e0040b07808a5081da1198020b00c10171108001c155000b118803403189040030000c40151505004840708d052140d5151008103595003540e40311100040c0d0460280c046503074031803000c000c2a10280310300440861422804003a10501031098030360341070748141880e01e04085030081001030400840196a0717841c04100441e684603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 21958702 1250 21957452 21957473
    0x7091404090c08011a01030b09060d020d1709010e04090b0601031d01060b1306020a03080412050705060901060501080601020304050306160201110a03050f0105090108030a0807050d140103020f0307150804050109 92
    0x205070f000451907542d030490300001e0151040840d07050609142040d9900e0b900c41804990250081d0b51290080000f03000141d102e5030800000303801c0d500462903e00d2150340c40002020101020f0701c5d100c46424040b01444100c41a003180608a051108080b99081d84aa0080e03c46d00b00805035241032210401429800c403003c1d80d04c40220381c40000f84010140d59800108030041842c4d0000d0a0050038584005e402032030010801406081c0300c1403000c8203907021310309403002d0303982102c01c6541c0c925040400c14000e005d2802514042150f150000e08550702c0001160250391f8041c2c040c00407134569400811008034150703042c0c3c0943d501c0780310900015800c04003414406489507400f08043c00e016101c60068481a000749014a8244c0018030459400100712203942e2180d140800f003130365030100129441c2c002e40e001d511240e41001100d408079991f080c4018141c038000c072403510001741c09c102055558a203a11580301030300406122403441500070074189a200b8041c1c070022600806a585003414007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 21959952 1250 21958702 21958709
    0xd05010219080a0507020f060714040e240301020901020a06020d110f070b01080c0d02062101080a0309080606090402190806040c180b060409020702010908010504060203070f050307091404090c 84
    0x4182800f080020400d5004540c0c21441c94005081c080001c034603050f845040c01413061044c0b20307914a0300b080c03034008101180c00512000c60514901e061015403940101c1d50300f444c0002c1400081c10345402442c040c400c07641403403030507001400c610344180d0b9048040e4210341d51030001c142d41e0301040b250310030350400208035900700244800c1e590640c0d0716111004140603002541594400da9510030140c4450781c904582540403980c1a490b420030701054503c024a025007512286541c0000013000c0c2d1000410020444c40703900d400300c800b612401303030031742e1104d00304d0b100c3d0750081d01440850007504045240440d0082140d0300c598443c0d40b203040346860104282e90131541030b044001d0401201c484201109034208042c0380c14004100828000b88050181e0702a840c15680e002662100f10382c01010044010080c00d0700910aa2800d030400030300035002110003402080300140c1d08206640300d68222071250f06140ca0b9040058140080a0750001c0201840390b00940e48180c0c8002041604034010001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 21961202 1250 21959952 21959957
    0x120b031c080a0b03070501050706020d0903050a0f05031314030705060f010302011416030e040b030109060203040606120f080306210606030c0102070303080105041a1801091404030c020d05010219 85
    0x2030441038a008011200080044035038501d0691448184d07034010417520100c0350240380c40c940700c005509205000740304a031801d4a00e54641101c40c0101a0071202800380c0318420780714034a051050a01c1900c09100449105d45c00805205001c800034030b6011030540501801e408682c10803c07246e0315113103800c070f040e98480644100e00c4010000c42d0b07440701e1400c0c02014449007840c1803800d0340900360480304802c01c00409000e159401c1d019107840e50741c410b00b004240240240301600031390034800025070042d6002c2c1c50240c2428004200f402d02d405900c8850343c0d001c0a500d05030308581d22800190b80003d4402644400c0c07643e281d54071842002e008044a40746c54001d080541002001c240c074100c0500103403410340d08100010800320780c0100c0102d04403a01500c002c0799040d081c000c408080401c01920360740c002503a96542210084141e800c2d4160744280004000c8442d002801c40d86801e4200d0380200005d40100c414801824443c0306035140902c43e4001600f4029014152a000000c3c07400b110300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 21962452 1250 21961202 21961243
    0x13060e06130207150e060a0902010203071103120406031a030304050321041206050601030e01110d1109030d02070602060603011407030c230d0f050906010618080d0518010908070501120b03 82
    0x10001011b2100d190003040e0300b0340401ca050140d500107500c030700601703402800b1080750324600f0f030f06501c05101c0c080110031107a00d001d540d075813501c0e0054001d201580003003001c5400500340c50300c43d0500104035402d070780c0d0040050200e030340040c0701078000081071381d05296054014800000c1c6145024000c1c2d030214490003020919181c2600010102d032290b2281001c0c50b0f06001d190380040ca12802140c803080300d0000049010103c5402420a5100300342419030144241d90740301040913408100001910b4060b8281d8402d85c48540c1007500b62850703105040e000c03d120001181182d070003a44880f4030320003a420580000420440c42d421030343c0049500c018100400a01010382c0911486200c09000808008001504024851642c0c03158140114001e00c003943c490001000c1e50b4605940082c0240000c481c103c0d90117090080a07500040151030300001c2c1c029a135000d030740c010118401030325410360082c04c0c11441c10f001120456442203a000744e0a45e1022100c0c1191414070010141000d21030701e948 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 21963702 1250 21962452 21962471
    0x603040606030312050613200d0504020907020604051b130903020d0f0513060302160804080c011e08220507081509070608010b030a060e090c13060e0613020715 70
    0x802030722000e00c540413000d01e06000c0200981e02c4500019000a0000c5c0010321010607a00b1781d40c1e60560790748001c14107603000c04c102c40e0036500c03500034a01c520703c02e031011401034440260076a92600e0540c4c00074801c0e00235544102c3d41c2d800d900c3c205400c8203801403050804018610141085070b00c140c8007a40141c0140c0070886200340c001c019032210f885a868141e29001160303115000e42c610714018913041540000d900d07070498001000c141c0000d03400200481d0340300d903507500d810f039a030101c1101503000c500c41a100041110084400c00d10454090311000016562400c01d00c18440302d6008081404011034180030128034200070140241a00d0001801906070014040340711410040000301c20381e024000074001290f020149504483e01c0031469612515154892000761410307800c20000c0344a034900b00408202d00080c07a10640c0015540e0456102d41e80001409031042030141c1d441003896200403032014108203c0c042c24404019400506101050399240700c0750141035400814240c41d601050f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 21964952 1250 21963702 21963707
    0x1303020613060807112112131101030e0a02100917030405040f0213090b060f0307080f070201020a090e060d05030a050c0d02010504030f030e10020301060f1107030f140c06030406060303 81
    0x54104c145400c08040ca400716800d03007951110507411080e14165000111100840c185095401c243c0180120a49529000c00400c84c050f0101c90207564080802c40788000c3c65000b40b041940c3d800f8850302820598100d5001d000c1072400301141d40040102110b0000b0751409544e0040c5100314015000d16596881c00e0304010a940030654000050b510400003408031588114000c01142c1151001199000c0503400040ba0307070041c14840da0034400d00104000d0700b50ba0110907140300318a040102c030358540f6200e000728200e010348081240032035903d920900c104031004243c103a00c600e0003410710001384c0661380c40500b142c100c24013107000f0603004a90110714800510410b40740c590648000c10051801d43c4004012200c1d44040e0028140c0d41c080144c000300007400011100c00c2005410f5589503074400e0300401040e00213500300e000800421a05030361004c045008401c80c0d4000407280e211900170f07102c020945000310395140040c0705a907410303409601c4200245200e40d015417000507a4070b2039410003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 21966202 1250 21964952 21964967
    0x9030c0e070903120201020f07111003050105100e030f010c02060712050903090607060b040e0c0f031203011e080a03021507033303050304231002060c130302061306 72
    0x4030305000300e081010155005822208494000381e10102925050070180d00a02c0741c0c5041850b04440007440d2018451200d40c0300d40558029501a0607a40316004100c0440e8001e008841d44204612050302904d4412100c00201080080c00c1d02d5400c4409400142144d40d003802c0c0d180503030421810002582d402000c1c09819000f94030b8107010710b2600311141038030380c40b503562058882c3c031004ca004000d00100340e00071080c103800a00200300c0e01189840319030f61810303100d01282c42a0b10820f03908806080110f460901a40c003a9081402c40e42400ca41c0c401c1c3e00d00b00c4205041410700c6640004001004010312004103000390003a04070b04a10320070b0381c1c804070002007007502403504100f00c5905081d80513031070703884106168142d1100f1703519100c50902c081c0426031026020b8480480c01048140420080071740010100308030301c0300680722200b4031450001d10b1510102603000000080c40d0002e40341c00a000f80ca00d031800701c80042c6c0e00d035800516950072440b1010344003402c0307000c140882a0460700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 21967452 1250 21966202 21966209
    0x109050108040c03031b05010e10050901060f03080304030c02130501031203061d1f0803031602060408030408090402120403050a0207060e13020d0f0203091f150e07020a02040c09030c 80
    0x81c081640d1800b03856202d03080340e25102c01070400c000c01e082c0c900d035003d502110824155210000780290180180306955403022400c240c00d5130391034240403500c60041442000300301c44c0700c41a102c0d0100d2440d103c4503036540008005130184100c07007001c4001641d84a081e07084010b094440000d00354114100041100202001e22040c1481d09400f440883c14900080102c8050091280110b54845000e401500380100043c00c0c40700243c000481c1002000c005140b050b058050003d80c3d05c0c680038001c0f40d880c0030648000c3c1c034102082020401044010f00101003030070003d40007515128140248000d1150121400d90016902203044041d559050100b580201400e2130201d00a070390010000e81c0c4151484440c4120660002c0c10300e01ca4820394004100b000341b0008210340324139142c000c568903101440780784040f00e640224004017000c8a4495a80d8055210b50407060040c103110b1b241d51320400181005040d44102d4094100583d550b001d2407a51614955078503103140c0c51880c06030924a003941 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 21968702 1250 21967452 21967457
    0x60103060c030203011208070f120903110a0303090509090a050604080d0e070803090f030703060603050d08010b040819082205030705060708070803040c030c03030302041403010203070207140f040f0b01090501 91
    0x4002e0300c1c1341b5203900c0d17000c02d4004a1141d80c2d1002c4c1c0c58016161440d0040090080c1855501042d4039a04500800c01b103c0c051a280c0018001c00c10804c58403052502004003c181c0c841e400707101b0390070550089503004920b5000c8851080c0151909450840b044508681c450f1002a02c80c0b820202c0f030050214640301c040c001c01c0034a00304280941c0324000d039844540514510810759605031b4007044440c00031904800100b01c0145c681c200161204801300b000001701d8190b0b000065001849030072074080300c06c20b40c0940b038400100526046002c4842001741c40400d001d00007407050110b0313a0841c044041c0312020081ca014a040c0500d0f0501c005540021b2184005221650119054004039580303568407405040d5a9511881c14010000c41c541019001214aa60100c20160558014025245a04020300c4940c40d007104140c02e0b0301c012030b0b1200058001d003008002101c0313110903d0392654001890341d14203102640c081002c9800c0c0300e0304c41094940307a100021641d40c0215042d4094202032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 21969952 1250 21968702 21968707
    0x203040806040b161d040c03060302060f030f24090703020d0515040c05070b0415061502030d14090a0204050a02090301090302010b150703081f0314060a0501060206061018080a05060103060c0302 85
    0x21801040a05c603481e10060041e500c171034002c1440740c400d920800143d40d001344800c0d151040100c03042010742080b41c030070000c0d1100101081c03d000c20460101c04840b5a0403900c100c844200c401d11103885005001c15052503000e1090324090301480c040c442c8208403090f40070540f1320f10581000291103007001c462050240030000403010408080c00154030603008141c45c03402d00300c0c00706038400a1250f50f01882c030380c1c4104070815180702c1d4003000a000d00201c001c0c0501034444041c2d1081c006500641e07014111781d1060141c500141420341219a010b50240c100504002c05007010a0940b0100f61044006035598203a05c0071606c2d08803142200214030024090410b40d071039501619541020781a2161840c0038501c0c40311540c5c00d0242100a15440703070107074501c00030700c0c450990f4503941680c1c0700450504060010411500c00282c0520801008007018401145004d040d030300c640120f10420040881d5420114040c40c0402a40d0211403240c802025250700d18105101240c00600d019000c05004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 21971202 1250 21969952 21969977
    0xb03070b030c0a080603070504020c0a0311031206010309020103090501050c090a09140402060f0c0129040c2007030c0b07030f03020702030c12030d151404110d0c0203040806040b16 79
    0x1c880555120000f507051003801c54a650002034a005025888107500c40d00018064404180c0840e0125003284a529000e00c0045980c02d074945174046c0c0060920003070340b0301c07001a90641c071079002110f2040c018100000d10082036207640342940e4080b130300c400314064000381c503401e1760030b00703100d070b1130041149240400c0040742c80740480220b150007410180c0701d4a40412110ba13400141012149490040e0000700940c0802c10010502c0b5000280c006200d00c1c2d400b0344c0d910046c1464051200d04902c180e03030f0076603850702c4451030921468400180c0c1100d0b206180e40800000c1c0448000c6001d008018034054440d07080d454020200031000f804602014014045840161800100c0c2c01e00014102d4900a5070814041c1d0a80703140a8450b01c1d1007a03a080000845950702d4030080310341646d82c5c0d01d401860910000d4140800c2c1c82c0340c8230000c51849020002c1c1440006580d02120b401e00041c8150fa00c1e09540700941d40c07070003005a405a500c00020414400003c11480a030b0411141e02e0911500000f030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 21972452 1250 21971202 21971221
    0x603020906010807111504020111010203060108060616170d0605031501180f0207030c020103050a060b0d020711060706020a0315050303070311070503030a02010603020a0b0c0703030e0409020907030b03070b03 91
    0x8010381140c0c144400f0701c02213902c0c80d001e92159039410020200721441000080d2080300288000d0f41d0a034089014000713403800030301040c000c580c820281078403071010399169001400782c2c1d0307401060040003802d118184d070317000290300c00d0b600d99110100c03200c481d496035414040007003283c3c1d40b5841644a9841490050950200305040c0d50440d40511040441909140e200c5000340c0303001c21030230390b0301440095103c1c03c054104043c00c0404d07000781d03030401c450b80e21140d01034100c45690040440d00c04c0300384440052046a80c0090a055101e440034125807000d080118480e0380041804070760850300030410407020f03541841441c1c4803c2c41c03541c442150078034040c04a5205d10a01c8000b07030401ca64264402d40018042011070001c00780907044a543d600e040200030300802103400100c2c801c00e1800c00008500303000e00290782c030030347c60340010305416031940c0d07000d40d0301c1018038140d140c2154841d0014030142c0d48200ca1641703e2010380d00c4c0807070021410400c060500000b0b070001c01e00d44206105000502a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 21973702 1250 21972452 21972469
    0x51003020310090507081f21050a051608060a06050117070903080d06061b020f0909010f020d0203160810120c03140f10060605030601080a091407051003060302 70
    0x45641001641c81e100c09510400c42501600b01440d440d040c001800310a0394440e4078144210001c40d003542e071206d4500c2060b48464058801c3e4903030360310000062072140c2d14115142c0c0341540b1580c12542e03e9026961242e060036156905c0c0803001154403c20003d880301840304c19840480000e0400c0581c0c2428006012074520300851201140c103000000c28003802103403200c0145820261464550210341e403200301a08a9010311000101390389035414850b0f0715200782e01900c0758000e1680c1d03010014001409840b4100400c4030601b59211a01d4042c6000700307200038144007002c05800b594a1600749034400d0021420303c500070400483c0010841d008101c07030758107070070f8441d03007003c0555401c0c56062075408a0000d03040a4907031786200c071251060581c0010f00c1c0c0e003000010401d450b10503001c4044001142d5042c80340002040d810400502c40e980700c1c240e002d41c44130010b6400035200c3d03099100d1200110f0342210b144c550380c2c030400701404580b400c01601a00c0481070720b010300c806811503000ca000d04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 21974952 1250 21973702 21973729
    0x3050a030504060209090f06030c0a0b0a080709090c02010c0e0d0b0414010b0402030a020703021606120b0d0609150b1e060f09030a06140a0e0d0c0203010b0a08030301090e0705 77
    0x5955101140030410f59404850300454018100b104078186070071010b06800381511074030310920482c0c209074440c0c1442220003048035031485549040200d484d40544511800030000802c02c01950000710360000b591007019001c1c2c105900008055a03000720145c04c807101c0408251060075844030280016222003059070b805170780302c600300380c89407590103845014140c0d108100354001e001104000e44516254064501c0d01d00036400c95000c10651143c81292010900511000411404030a40d1030030756904a21000710019000544035859600c07540e08540101c4007c0320309440d00303d01400c3c1c20003e4001c2c0d1555241c1250b0b03042d820a110b50301e140c000e24031a07180a0103944085910a000c00302d0340c00740d8020341c0c80602a41d11441c03540c94288010f00811042001803010074000c626245e65520800880c40c0c003100c001d0640c20803865055071401008202240e06648460070300d43d894030740701c80c4030004281c1503008503107a5040c16540001da981b028410165503101032410407680d40c1d024a60103d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 21976202 1250 21974952 21974957
    0x303030a1104081509010506060a0807031a0a03061e05060a12050309040203010e1b12071805060f0c12070f02010804030c05030a3c050a03090b0906040201110a03050a 73
    0x61080801070000a02640d448808203009441c180c4800d425041e0026120b204204020881c550384c46040145134000d50342c40c3c01c00200c416000440030f46c003a6000401c542c04c0c0c155480c54699603200046d100e145150800c4801c541c40d01104e002080c01340070002c60640c0030507018800d500d80f060208440701c009201d41204002c0700708110050040500440300b403044064004c0d07542e0340c0c45582e1046844e0080d124400d40b82d1489034049507058804041d1801c200705110b50351484d4031800c4044964501c03e0114801e09404001c0015990380e0b04002003442c1c03013420080365120740001843c00d0914151140c020000c0030704110f80800a0f200c603001c1241c43c1e03130900304180d241e11076007403c4444036243c0800078007600c400280d80000d00d41141480101e0440d40c07500306603004941c9803c003140380801589611060000d00e4414003140034102400320780f12185030000705100305890b0110807000070340701020f80740c20007010301055581c8006410302c0404200c004141a001560b0001c042c0e00c20b0004480c01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 21977452 1250 21976202 21976211
    0x804030c090c120e062e08010204030c0605090a090c031404030906020f060c0712021606030212061f0807020f0a121404060e060d09080307030c03050109090b0103060b04021204030206010302130b0303030a 89
    0x1150021b0004165091640c66500f840060b00d810929001b9031081c082518000c03042e4030005011445078040700c524100103804010440d1070001c40305e0203044415804400d0540321001d460001410070403152280d070080d56a40c1c1c420307150982c042d090200e10b003c07280c0795820220800c411610740340101c2d0101d540c0202c0800c0341c00c840000072410083c07000e8100b0302d0740008010000300180d1680140617034055002030003080d500c1e502c1c00c00200c0c0c0d6008d01d2481c220807080c5140380d01240215443c41d8000450300540ba420900000d40d40e0a002c2c5810088403c801011044180303554006a001050700702040c40c540b0341800c08001a140c11007090b0000e02c03410740040c12a81d488019048826400d5101e0500c07510b0f42403240015000c0c04841840c00c002a1a0100010b20f5000500405546640010080d070031a400d40d10744c180a8140140c9041e0419002c001171294055402e5841d44180d01a82c041c042da03504510420410450402c001c102060408100c1c1803a543d000c412280c1000181c1000076 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 21978702 1250 21977452 21977491
    0x50624040612150e0609010507080a0203090d03112a01060501020f10050415020307051206010e010e0607060209030a03050714060402101101090510060303030e0f15040804030c090c120e06 82
    0xa132005507400c1c2480c0c01103205001c0011415041395010b402d46407200c000c141c1da61071000381280011030320340302c00340c0c8100310a1100034042d60060302c10b03060040750300340f400c0303003962210001e0300c0c00b090703c200381c0b00016040c425842d50a110307e1001d044240301070510210b88038401d6503100307140c00151b0703032071940d0b41c0101301008004102000c0c60402604195100c0c50840300103807464100e071040c2d00320950903000094144d8824800645503010584031511000504000d0042942042e101111550303820082d807030050ba005c101c5043c0140c8a5540c9982c4e4102c0d9140080b16812840300880240d4023103814040141d070745c50400c64107a040c1d482c010960503041402c0ba40500030021000e0a14001d011401080a20f02c0d04a1420359000f40c409001c400301c070384115035a400400d01001c0c41078014800407070444120b50a0150824002d090076801c1030740320786501001c05c030a68000241e1641e1802001c0c1c40c25048204006d0303d0b150f904040000c0004400400e496038001400d20481c8940410000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 21979952 1250 21978702 21978743
    0x5060d170403020d030f0e010807050a030c020a080c060910050910090327060905031204060507020a0b040b0304030306080c0a0302040f02040905130b010803040b09010f0903050624040612 82
    0x1a002140c005003110342c04801da04000c2c294889106c44400040c8540385000440d50040c55a14000d280d41c2d07540c14a0300b41030312001c9000300f0603400004214001c0500f24001700780ca00780075101482c0c00402034102410045905840c103000082000785580c108001c0208034500030586902d022201d0a0119801410b071600300c980414035042d01c0403060f00030905e0100b002c2e068003400103131902c0381c0350a600c480e26902010b9940710490034080390f115040005115507172180002e8000b0354406403401170419101d258104254001d0740100340001c001200704814075074180510001170400a0103808072549501c0856036000150101a000319210b4250240d44425a41110003c01d5801d0041002d41007100040307822180b0030b6030503070340c12002c06c001080f0300502008480c11201c0c034201143c0313088040701c0150741481000c00744500b4001d4103800000816024400e0701e11826240c3c41c408007540750f2a1032618010b064100345400b0350300c1e0100610000c11041404505290400701954100b03e40000c903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 21981202 1250 21979952 21979957
    0x30609100b01120504060603030206070e0a0314070308040b12010501140306010e0a091a100201050601021e1018170306010504030605060301090c08030c0613170d110a200105060d17 79
    0x20f989445103000100000c1c064950b02540c1564400d60a50b111911030030412a44041003e04099200c0c0b850401040010415803a201c80c61050070143c42c40d455880d00c445a0036002944030f0158a000002c80a144005429440c1d0145c1001d0810b500301c504170400094041c007008090070f05005001c004103009036a0310002c1c000502c2402c0080c0020200900c1080c00c4490600301607028031000c440e10700310580107000301d41c411a8181c1c01085004214480c00c00b500e101c404405109000e1280a16941c1c3c0c0b0074041e04980034100e007a035249400203458080c081c2d1407090000600341c0002d205100c110380e40f00307003181c0440303070005803700707a603120b031b400090040000714001001c4500d8404c0020300030310b010003d41401603c034019605190741e010602d000c080c044d490002c1c0600707180c140f6220b5592402014000c0340c100141c0002d1003146080c4001d415a00c820080030100c1e1241c4540c181b04442c1d25511034007a05240005e00c22410b106001c1200d28000900042495081032620107848400505 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 21982452 1250 21981202 21981227
    0xf03070e040f0c020708010f05060d12050702030d03050f0a090809040c020c0a030b0403080a090f0605180f0f070819020607021302030403050403021f0e0907020708030c0f0705030609100b01 83
    0x34200810038000b0703c041d54510301e0748a203c00c5542826007a202280040c0300e2603106420140c0003c00c40703e441e40d00d006c030426002c1e4450090040503c107040146c0c030100300c0d40c1da20034807549000669080c200381561900d14000d01c820201420b110f000d10001d0710440c15103400f0b04003903e002c140340101d407809a0400f0b036410800343d004030741d04c0c0d000000c1c007040031000c0340128002c0e1948240f80d11804e1140d000e549100340c0c040c0418500c14406d800055081d0712940c0e1003070241103036094503407244189505051314103e00513124ad000b41c0c105941d508003801044002d0201d60000c040d402411001d421080400d41c0c00a842071002040000a40d00c5582e04003540d074032400c00855070b0346480d180103065070300140000c1e070250030040042409150401e90707034500401c0c0c9803560f41d05ca000710000c000c00380c840200400214050304600007035030700042001d0702c40c0550035806003407440702c61080075107800600c1c1c0c8294031a6010005000103d0008940c0c404c2e04e560084010035802e00880050340c90a10030213 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 21983702 1250 21982452 21982481
    0x6041b1e170405060f0c0a09051306120f060c02030a091517160306140102030913020f0f0306041803080a0e03040509090d08060103060f090f06030602070308090c0102030f03070e04 79
    0x30100000c00c6400300301d1912034064416861740d640c80c0c500003c0250b0080c030042c0b1000c07501140040c03100f840c7c030b4882d07584442078110022814a480c1d202c406a110b405510480c2c0f01545108070030308000041c0901d04001c0c00c02c1c801075040035445d000043c5951014800c0d000e0000800c81e403400c10b584200e45d500600d60fa81c144003945070400c1000484003140700e00d03c80b0b00080c60800085a038140d00803002c1c0040005074000c0d801e01d110304081104110b891a49110060741c2007058400a00c8882d01500101d100800740580b00d2030800c040c8829504a8031202c100b14400700c5600e400650130581310b80e0040b20310301c00000d003482c8a49031a03103148181d4101d2580315a508042040d020130000d00382d11411915524030051392280d40065080c0e4500d405401080b07524400244809000d99201d150060820500464aa03540e44c0302d0702d080b61300c40002600014420300400c446144200191442a2801c5c4000c6182c413084a1400d04103000c098241420030a00000202030303941c0310f401401028040c030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 21984952 1250 21983702 21983747
    0x60702040209150a020d020c010f0e040509070503060106050403060b09060108131e1101020d090e0c13030c0b19170a0207050109050708030301082506030203060303070b0c0306041b1e 80
    0x10300010b1b40c0d5009003142140140700315142c6e41d03410b501c588241721000c102920340e851050016010407014003c010300b024080d21070b440300040e01d5642000624024002907d070f20341d9a900350301346441911084480b09005422030380a100b0300c1c2c5d0740001c40070751080f141c03040c1001e204501c0c41d0071031400c2e40da00d103101e5882c141c440da241c0a0044100c240e000702c82c0300741c00b10303a00d0341809403041d6410a402e22404400d4034200c1e0004d020070000390300402e00c003808038040d40745c40e9403030baa00c0d034103110442e8108461600b0040b40381010b18030780c88501c40c1060110704050702440100e0038600d40020380103010103c4036030042400c1c410001e0940091540d83c0e03004040e00c02c1c980d00d46d06220381d6078009120300c0a56100b6005400310030a8008c03120302c1d1105502040c031075154203109056001c0d6201408075a050b00c070800c11140490300c40c0144500401e40ca4020329a241040f00410080c4c0b06045042d2500060080300c90038540c1c1c1004404118800007a00050340640c020030648514aa81c1c0f81903115000c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 21986202 1250 21984952 21984967
    0x30903031801050f0c0a1103040f05040605060c0d0507080403140a030219050a060207030e06041409010e010b091212070602130803030402030703060f0b120109020112050606070204020915 82
    0x10015500c220303410304121801c0c0410790400e60a0f241c080e144541d02c0e0054102003420386000c03a00a102040d1981854844030b42e00d02241441d6500603480210300b2030924205000741d18241c080c541c000c0c9000c55200d0304003d444040c07141c5818040d18a0402d000c0002920301c00c10143c01c0a99000316044101d120380c000c03030401e40e191105008401240140901c0400144115071a2240503500760031500800301c00001d80c1e19200254001da0040c0d052003c40181e1002c1a55404002c10203890b2450341c120742c1020140c01d100003e14180c02c0001c0300a02c4000520003210f00704103680340702e2402c44400702120302c5c00e034846080c507081403d21140c1c000c0009004044c070100d60020b108051158001404583d81d443e07415031280020703100203505412054041010500c0c40d08003004401d1031600c00240030600f00006000c21441e141700d00d2059446124200030b56800040d078011001c20600244003a141980000e0441e01c940d401c002e02c55940410601c500f922000c031285003041c2d030300001c035a94480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 21987452 1250 21986202 21986221
    0x702031204091d0f1510030c06050c010c0503010501050304081602030106090b0f0301060602190309080601060c030f0f050d0903021608070510020a0b06011d0907051309090203030412020d05010203 86
    0xf00900416540b64120310320005040d000100346403030748002009841d6030f03607090480080040f405040c40c5150440440080041910094044001d00c401d841d00c5039a409540d11203400e40744882004c1c0306001040c0300410207a600305044036072241d4061240365586484415060280c0045c0780041e40540ca8080c0104643e42c4c983d100f01c0700818215505000e07000c540b0201803d842e007502860b8010380200b102d6400d0300718480c052044240c0300381001c4d201c4640301d001c0c152501400b41e20082c00500304003421004e050b0030110a0190b80540e10344204251241c80000d0500d200c0c40002c0400140c0e54030034030301414402e00c64031034404c4100310303100020b40e07807070160030f64076040b600a0610941018000c0b07030340d1750300008039954051f0380701c0c041d0f446543e02c0c2d50065821182201580c2850000c041d41d401c0550b0354141054414255521090384130070100e401c0f448621520b800900c401d81c500000f0b400560790000030f032811540c01d4414141c0181042c03020421203109030700000c050f980003000303012400e031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 21988702 1250 21987452 21987461
    0x10905010614040b0d02030907090e011a04140c0a1803050c100503010f0509060604030f0308070f09050a0b0a09030503040e070807030603020619050c07091401050402030f0705070203120409 83
    0x8403242d507032200c100981d50810026110714881c070303845200c0820003009070762666005554070000c03182c00d54007290350380c201000560b9120078002070180d40d80c4060138103500c43c401301c00010300c405803420410072400b40503012481c2c0e405006050404030219140400030310508000c005c000554010f091460380c0c03442d00c2580c442490901c1c1e441080d58440b19040544100280c80c100d0710074914600e0740d41c2c946810302c104460080c10450700118200404000710fa1627604204065119550710503440c9029103008181c0007208044500b000340325503040100d41e43d48030742d072070941d841d004030b1340e0b40c070035003010103a600075519030008103603000110f80010312100314420107200d04159220f107507440d601e60f8021011182079004c002c0d0300240501c000e01403800300b005100b0900c40e036428294600b040e07141040340307007501990001007800c1d21074860800b90311031500c0c1140180700a0b6020f40c02d5050407005c0303080c541c0d0006d112a0820001040400035903804000c1c840b40c2095508036250f485458202c240080d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 21989952 1250 21988702 21988709
    0x10e0708070305060f090703060b0102120a080a14060f01120b0a0b04030308010801051b030402040605060301270506100f020a0606030c050301050601020f0c0609040605060a02070e0f01050109030b040206070b01090501 95
    0x140500701c000780174199890302081c41500c1d020f025040d002e04550714203000f0641d090b140c50441c8030b0100e01c1120b032406039004040981407a200c0510601d0503840c20030507100304c1c00740c51000d041d240041c0440c13034580340c4041969045c02d080084445c14914403140081c0520f441d1540e02200d102c1c40040c42401c0c00c4007c1c402e69000c1c2d40c5600d0640c0c0c954030364a00707030703941607070880007070f01c0038150740d1580d10004800745030458402000070403101d0340c403c0001c18980080e0486249403070004003509000e00803c5039501140440007052220780b074408002151140c480441006002c480e1840e5060f5034828414160b010380d06c940c1c01c114854a03801d250300c0e00c079003038002d20f0301039880c11001c52410340c000503040310345d22103100c018521980114240805500300620941c1c006407070b42c4002c1a16a10400a00909420b550080c155240340407500105004050104900011303803800602940c1d078415411001d40360011005215600c0c0c80c400b24845100c1c000002d490302c080c180000c01d10f1456904964101c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 21991202 1250 21989952 21989963
    0x30312060a1203090b0d0b150d06060905150a0908010e010b01030b1804060209060403050a060b100809030409020f07050a140c010302270120060105130902010c0212010e07080703 78
    0x46515a10502c0d1000803611019021405200c820803030002d8050040c021440d4490000c980c0401d00710200c0c0f040010001251005c40b030200d0041807110480c821800180828505404031078a4200403030302d2501d0648603400121800142240014011a5110000c140c80c0000b0001c3c40890740c02507000b4060b031911240003e00380b0100300c11918140702e41d000d4409540030340341029103c907620300000b5446051301c150042c0080c440080840c40a00c105070983e80603a0000c500190f62404007d002d8014401d1701052000903001d00403c80e0001059a05a0300070f4030006076281c85202d108281c900400c00010705902c41c015440d402c00072a07000c592005000c43d03080395064100b210040d0b01340d00520f0380c1d540f90000c418038030007001008001600000707041070401100380001130030401011800040c880207241e205200400641c14860b94080c1d01803003100382003214004030360000b40741403080d1002030b10031408030060504541c4290300c00401080720104403400a5501c01d0f84585407201c80c401503c6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 21992452 1250 21991202 21991219
    0x3060a14160816031107050a0c05040204060504030b04050717010212010603020a020c01030504020a0302090412020f030403020109060309110415030615030302061609090f0603121812060b03031206 86
    0x300c41c600e030302022107448240d00c80000980d9000764000100302900f046038109511024113900e214850700c000c1c00124040c42c00382a5134801d40c244880d0b14012680302c50b0003288104801c0004590000944054a622451910301905e6074201140b50010a030041e030114042d03201d100c1035124056004207a1102e4a106040c8039a036030341429022405480c22200260301328400d080000d611980c840c613801071004050103c229120340204046e24405c42d022034001d80c4c0400703002c0180750100603460160382800c0040d850308d82140d00083c28009030b8450401807549884140d0108161140a80a42580a0300802c50f0381c0b01004c448000d003036030344825602c551505260203c83e81242c8009819260590014401d0b61034285800301b22640402c82001000020340c004588546107025000c041c000d00724000c00d0311030840c10f001c10102c940e800c0c40300a0128100c0c0752501c0b00700391180c407000c07079126120012a0b200681816070181c203006881ca60b041c080081c01204032914414a035010302000e1700c1146 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 21993702 1250 21992452 21992461
    0x708070b1902060705090609030a0614071704030f0e041b030b040c09050a0308030c0d060f03020f0301021e091503090d110a050709020d180f120207050609060a02010b03060a14 77
    0x7030f12400d00361201c0340001d80c20000102242015001881004405011102c02003000d841d004229450b4100144400107044184081240d110f1307041a201034514132011182d0409aa02030400403108011030700f03110f000d407032142007981d0703e6002803003004482c02022001c2d600300c0c0c00200204803100e58203101b5883d04440c0808140f140e5082816250013500e164283c90030b6407102c00c0550401401c0d0340110404104100644d0082d000d010001c1c0000158061014103610402100240c02e54080d070190b803040c0300c503078103010b03100600e2074180302c09040017681c598088022544248074045d0860b986007001091103100440095041c480c1f042c02c2d9150803c80c10070f0030390b041e03d0f5100c0071006000765011606c14410580c45078000c009000320081c00281c50150384120401003e048101074480c01e4044c50300d0401d004c940b10a0404994051002e025102d00b040c0c0041c1d51800b030704006900a200104141030301c10700035405000441b0004044a009190281d481e03c042c1c02400107880e0001d40c180c0c00308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 21994952 1250 21993702 21993707
    0x40209070e0a14061611030706050c0a120c0f14062a0f090a0b0d0b0105030402010f0f05190203040e0709080d081909050c01020f0601290c010e031306020615060705010908040b07021c0b0402010c050708070b19 91
    0x4b101030422010525040b04400820038446801c0300302c150386d00c503104008103291503482103814030003045801c140340d4032142888148001c8851400c03421341400010000c201c010303a4801c45501500505081c41c221280c03102800300d83c10f005912003c0300c066140410000e17041d0300000076008640607504029800c0e82d801d0070481b4440414425024503500c44c001001d07026000d004100d41c0507030034041030352100c40b0b0300803807105075540c2610035191600545001020b550741800300c9440503500000a0007103501d440403900982c0f1060310b009844020041c21100500742c0c09044861981e004002404245402c10709691260701011082808405c2050001100c6001040491040451000c280001e0032000c0620403294040e41c0122041e540c2c550214000070b850001400192000108542d11001a441070281c856004100c0c002801c03520002c1c00006a201504c49034401d90a20700b0ba8000c007030501d482c030b142c10301a030000c0081c0d00400b1300104044403400c0203441d02c98010a94450140c0e05032005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 21996202 1250 21994952 21994981
    0x40b0303090105040b030c09030706121404150f0207051b13051017101e0b030a0b0703020901110106030308040209070e0a14061611030706050c0a120c0f1406 69
    0xa400f08906000c100400d58025020b035602c40b40805440340f4190079a00080c1c14050980c2001006c07a0910861815441044c8103003062090302072000321341420591641c001c403520070801c440303201c1d456134030402ca10042901a0754607107a0200846010550070304102a00010000c10036004082c00b412103480b245043c0100c81c090304400740c244221500304100d000703040e4244045541e0600c01d0f5610802039600500c2280550244040010f01c84140d03010303c00117441c09409003a01c43c5c2d0180141d403011034880c070061038014074142070041e0380b0484800103a802c0400502810b140703500e85200041456040490144a0740c8200c0f81c03a011070303582041c1174400d00c0e0301d112000e811a100c41c200740300c0302410401c440e5850b04002c0000b4100141419104039802d800c02082311480760010096005007400c12010300030b44210300b0038604180c0a5448580d87d0f0750b1003403000d010241c203941c400c0c41080c003c1070385901c80c1c1c0d0014104a1090b0035810207150410741c0009185c2c2510540780082d5400703801111 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 21997452 1250 21996202 21996217
    0x507080306090705040b0c0106091802030309040209010e0a12060b04090b060d02130c020708010b03060c0703140d020a0507050c01030608070e090118050a0605010605090d0f030c170405040b0303 85
    0x9459055444940c00c2c8000403000408150038003c0402000c00c000503044054102c00705008000704116041c40c05a0342500c041004815585036103114100059501005441103400c0940d8016150321301e10004842c03c0041113034442d044405000d000c0742a50f4034050394800310380218420b00840320300d40c003403004407242030358094030316000400070801c545403a0440a81c66030006040d8585031020b59805011142c14812160160740455410400c416081c00f4441341440207e0280416142070040c88108e031041c030400804104100f0040d120714003606045d201c50803182041152942403011001c0c2250f8800c400c281c48922a501800c421903101e8082d510980f5030346800b61911509d007000ca00401c07000a803010100355241d025480180c0c1c01c000030411014001c40040801001d581415812107806030020000c0100420120000d81c0f60302080811542d44000300c4a06513005041c212040c89007860010718140c0640c0c4042840c4100d2000b07442030329422a070410080c203040b010075a07284a20903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 21998702 1250 21997452 21997463
    0x8060d0b04020105090409060c020a030e040e030f070f0602030a0b090a0605100c060e010e07050a0801022503170c090301230604021605030c01090c06030506011403090705061207020d0507 82
    0x40c0050015440307100030340010b032406000031408030304555540702034920668140740180e00c0820150141039025858a000300e006403020021014240d81a540301e01c694520398005110001c0e00b0800c002c0c50340000d04249420840440d100d003031008200c000341c40700e113101074410417440c004120210707200e108000c210392006003960748440c00c0407025103545078042025100c0075a41d07142c0c110005428015184401200c0d07000c2d02c4800e0400301001000c07803140d00710300752681c0306100050481c466501c02c5550041903440c002a030700f095240c101d44403110380780074881c01c030300c074009014001b542d03c070187c9818402103000340404040f80154880021481200b410000354100c08038646e800c25600414040c0b03a0f00d020313002844495151986035510006d1940340350fa65660103201444080302491014000500d0306021320304103100001d0087c0300da00ca01c41c015201c00808030f01d240c0d5041280100404016011989803851100d1507990105c04546183c050b0042c2e0740c100309070a03c60000c0302c580f03940c400d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 21999952 1250 21998702 21998723
    0x30509010c021c030209040609060e0c040303020d05031008010c0306030c080c090123030703030509040b100807080a0204180e0f03030f0c03060307090e0307020102120a020706050c0c0a080d08060d 86
    0x1c10040f04a00c1941e2100800d01d582042500055140c81c0101e40c05001e8091012900302c1c50500d170f0303404072040180b045460130010b01052002990219212407641142d00d490f80d00ea489021103105844100c0d8081c00341e541c0303081c0540040365019000742e4100c074015151030400079035a4054036100c000000b800d035481850b4174018040c00b804098642000d0344400d80f45004000400007207403804000360405d9011031004180e1034950710345401020340c2c0c2e5105075041d940141c082d0070058000c0001902c1402804900c00000d400b0b410305034140d800500a0072529140f81903018641c400900054000010307502407080500d060b01c0000081302c2c010150918011016900c03100c0124150300060015a814000c401d80001c0c0716466000c1d440300c8403800c501845c1c1e248224400a4500030120402c44200d99050105030242900400d07180111030361400c10355989d40da044041c070705201c01688100e50000e000c040c0402d00c4034001480381d1400c9010388805200c1c5d00c0320000c200c2030031003c0b80c00401803241c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 22001202 1250 21999952 21999973
    0x150c0e01050c0f030408060f0c0723010b0306010b0a09140108070f02101508010b03060105030c0d0c080604030c0506070903020604030609020612011403100510090b010903080d0c030509010c02 84
    0x140c80103002503244401940c80f540d050140c55421070b88a988042c84960000040c8000130000030312050f008407403120007a2070303c0c415569014600f000039441c5000045801c104030580c1d0300a41100824201c001d09031070182da1514030318032094000d8250762000558001c404540b180801c0e80d08849614140c40d040450350799210700b00c52483c8503110410444c01450a42a0440311a014281c00c0ca44001d58041c881c1c1e0601d5481421200d0010f0290f11a510101c0100701c03030348000c00c0e9400c00c0402514a00c1840d40300f41420304203115558400c0300d1600c40e010800043c15440b0007240c0b40c0138452401e80f62961140b9108680742101800b020303601038404c0200301f000030525404004503e00c0902030508103d100190101c080d81c09a0001042d0900c5003c140c2c4a0b10b0203105142c202d5250000802140c205465050b2804c2c1c9640103044042c0d985020508280e8020b400807001968000c80321070b136940c01120103001400340c024504001c281400040342807000c0601500c40c04d08826802415660031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 22002452 1250 22001202 22001207
    0x403020d170121051507030603020f0409020a061407080c15070f05030f040606052e05040308030f040203010207050f01060806010f0501020303070807200f1228030b090103030309150c0e01 82
    0x1a800c3c0120340c544900c1d07034808000c2e461211803034851090354030300041c058514014007910071080c0d121076105900e00011007005a8a41150740c05a40052504061940700f22200311101d108040c0003900141010810400080300010fa40c01c0da2800e6403410005a19250002c0c1c84d080800c403000c4000c0346050000544e00d074099001e0580c05802400d000c44c8e01c40c2c0d0741c0c010400c0070740c95040d21400c88010b840919923100410a210300450359030320f4902d03d05455511011250300010f01207003a540ca86202080c195502501514403881d0004151440d0b40381c522502070003010b242c400c5140a016070f000014400190200200803100181c024620710f6a41070400c55150350300400744030600c500e5140082d080711100036103855070100c1030010f00c0c110541c0f00c583c601d807201c581d286180d010000c001000318035210309901301e110408941038440b46045820203030007602d1805643c0342c004a0402c000400c2c154544c00c82084c05001d11a16802e0003071010344101035409906545001c03513080842c0214551 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 22003702 1250 22002452 22002509
    0x130608040503040e01120209011e0303050c010f060b03011701020708070201051b030c101a0d020d0501090206070b0114030c0604060c050f071401020d18030602090111060403020d1701 80
    0x510680030b0364a402c0d22500092a0208203801001c0e122800707082540031400d1065046000d4012211002069008001901801c405a000090412001040011041c0001d412640d840041d00c1024041e07561504070003d02a04244103240c10601d1210145400440602c00c581501d43c0040c0001c4c5070015a40054171207900c1040c00500890f002d80700f001ca551010b1002d845502d5400001d000c0c000440d000344400c0c1e03042c03201266545402a501501d241d80c404214102c810b905032011650003601c1e00741070340100039484020350811400500c03681001021144135040e5555800c42c0c0704112944001d1603940c80c04440d0030354021008000c140000c5000e1a100c13640d66104e0012101d001c08000559402c00020f940094101120035070418007968040c080350041c1405484c08600c510041068040301260a10028050b00d60003d44080da40e4410600c1143d101403d0f0200ea14070b081c2894000c3d0f43c0e50058100200250740410f20007410094510f44604139a40c05200b0300c1c2800049034682c0111 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 22004952 1250 22003702 22003711
    0x5120306030c1c050109050102130806010b0306040c17070216090218040b150c01050106030501050d0506041104091406070305100e04020f041b020105010f0f03051902010219060b040f02130608 84
    0x1400c204268001413024014014140d00c9100050f84035210140d0206201001350800900f0750440303801401030141003401d80b0342c0800c04940c04035076600e80f000180c402c41c81822411483c1c0d8408000c0045d0b560b000181080c240181d030082003034035541c40c032458089010301c0b444100c0d00c480c00000c0d4981407a041d000050304d10f0004200c400e4004140180c0fa0890b40f040c5a0514641d4440004021075601031040900401c0203903815865210380303070389030381d03d900000f40002d01a08401c05822150f88940c0e103d06c07002070784041c3c09d042e0701440c5103401d5a1000110341c92380019060800103000b82451074225800c03110030600981c800c0e10780e40d08129107a5006007070603400994802c007030150f100c1c0510f810891000d15800028503541001c0024140c0b410582101c0441c200ca0001000010303000030f0200e4040d0126a20308200c0409480105c7c204031004106114005002e070194060003d29030140d458040d0464042110402051840042c2c5c09007030280310045281081c1009424010583d16920 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 22006202 1250 22004952 22004989
    0xc0307030908090406030f060509070b0a1805090702030c011a030a0204020d150f080c030c010f0804020109050a08010605190f1203050405090703140f150f010909020a020a05120306030c 81
    0x8145116010904840c0d103541b0540b0a91050044541441150310901d500a0100406000b4050500c19000c00e144244001c02040184011b20303005000c1c1100c50300006000c000740304034401d080a0a0007562900310003810a07403540313845640040c40b040c12003907210240c0d014029101c40d50b044e4003008000c1d00a000b40744070140c0c40d121100341c034642c1c1d0700303002c809030841916680c0c00d5801c1001c258648248214468045d0703000707038424140d580c0c1010104110848618040361250745510040740e01880e039600490f0400301200300031274494810b4102d00150b030026140380d03a401590302c40001518400b44a496070060041500384076031051140c00100441c000e0406600d419900d4000c81c40c250030031118140080d503036481c009003444000001c2a048a02c45640210701e08000030040d580c080000031052282080307140c113541590040650500400040404648034120750300069166121043d0840b424018007c10210050102050b2401040041c00810b0440b895800307002025000c81220410b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 22007452 1250 22006202 22006207
    0x90209150907031e020a03021201080102091507060212090f190b0f1003050a080301030309050d1104020309150f0f01050102061b090d080307020114010914060411041e0302090a050c0307030908 84
    0x300b107804c1c0c0010f10a0540c6547d005949080301d03103a10680140682100200383d0042003c07000d250740e20480c00c406174049004e41c5903940d10500d0200d0091040100d04008030224104005040d14041022992114500700f9264548a00740080d08100030b000001001c40c82884089424084541401da5110007228411000715469440322403070f0017030029003120283e00003c0103000301175002050030001c00003a01d04841c4002c0b1581c48508a14041a10034003460740440040c1201d541001a00c20482901802102508201682c019001003c03110660070804d544000512940b0000c2d901c1d1103100c81c952424580241640841c15990209402ca6401551449802c003c122848010342c0501c8031380d00005910b0342c0300700c568250410164481700080386011420b001e11101c403c1d215901c00c0e02110001466500001030404c1405643c02003401c092809402c3c080300e2035107540907001c1d20300031190804c49030785002162043d1791044520640d141c0c1c0030700200c1d030f0b85030082d0040d0100c2d5108081060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 22008702 1250 22007452 22007501
    0x5040b010906060203090105030f130b0f04110f0303090d03140706020712050702100311070602040b0c01060503010605030307080d060b0c03180607110d05210a2007171f09020915090703 81
    0x2d8cc0001545c0c82a03040c03d00200303000c00c000c0343d100040000c001c2030300da00288081c160002034480c007855a100d1702442103c00030904052003040c04003418441c40c1c1c025138441d1000c0c1441c1c0020740002d401101d900310140c0c24003020b28026001d0b1030143d580244056620080000200c0140429003002d900302c0c1401c3c0400d000040301030001e00060600c806050f80c440244115031030940c0d00940c810b5010b0303403410105116a80b4007008980c422500804a69641d03001510000000c24442d80581901040842c0800e803e86020008159180e18100c8850305020904108036080c4a41d040c0101a284440780d184e0036418503070b80001000703001d0320594148079150095050b1038043c440070300c100302e9800941c650b02c7e940c022003021448248807030340c004490b44203480705a440c8400c0c052602c0040400752601d850b00d40400c50006500305203508100410709605c11107003e05202c020480c418402e18000a509425441c0c5030312205000038503050035900c0b100001e030000c02c214410000720681d03202054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 22009952 1250 22008702 22008713
    0x90503070b0619030b011a04030c0803030619080a06180c0807080d020708030f160602040311090a1a060a0203130e040501050f090c0402090a050405040b010906060203090105030f13 79
    0x300304050185907856000e01e0000104100800500090400510b11450610220300e6510a59055841c0130103401c4441c50704000360615401241c0c0024a0000001d2000c0b41c6280040055409032101341c030070b0f407944c2c43c6000c042110480c16004000c07240d4000900100480c0c0c058000c101101804100924080c400b81c031580c0c00c0700381a4004e4141a07105580400c500201003005480307000c000d1010b04200b500f010541a09c0348105c0001040780c0e03c011503450103500b005407031540125400401107558603070300e103040b4a19400c3c0d115214491040c030400101d4106040c082c410f28100e46541c1c510f2107140540c1006400d40003c1540803c51105019240c10050802d880308007400102828400a141c1882c1c0142922801000349501c2c1c00f001c82030000640c030000e41100c032a01c080718050713241c5542c10003041c20320710325500c00c3d07500c80d0421083c07105110100c0ca88074160340c2c21007400e0098a03211102a40e8070b10510f0030351070010320200000f030300600034030080b0780d082610400040a02c07006034558 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 22011202 1250 22009952 22009957
    0x170409051806010909020901030f020102031201080c010305070302040e0a09080c151b1905030402040908040608040309080d1706030309150a0306120c05040f0b060d020403030e030c0901030f06090503 87
    0x100d01e945101e8541818007404200c06401020291024001c0341c000ea80469036a8606200090081440ba0014421a8003e2041c1c9003451034a01e04c040381980d4840e41c15654001040c9603e000c24076180c041031030780d4807038003c075015544010422465511000700344001020404010760301c41c030042c40f5000600c6810301c143e500e911600d0759510b105003808004002e12210085030a05104810041140c0341140c0e940c200305920340c6418115100d40c0d0f81c1c0041009044030080081482c000011701244054002ea80d15003e24040e580d50744c6001e840b1104203176146d07003400850740462007001202903401480c105407603008001400396410306402d00c012171494844128100500c030804200100519418454440141401040803d00354040d48540020810900815008035124145000c150f10550000c42c40c00c44090101651541980d100d40000e41040c0000c0b000a5580031300c0040b20b21740001e0603908904010807000741e50740f9668030454042540c01080704c22946a01e242ca010440a001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 22012452 1250 22011202 22011211
    0xf030f010b01080a060f05010809010e0102030f1602060708060609010905060a03061a09091305010207050a080a030f0203010803030a0c02070e0c1b0f0a0210030b060c0f0105010602061317040905 85
    0x8074580c16590009806141c0082004120034038110042001c90b4481d000d1800b215400c0c01d2840954440701c0c0d407603002d070424030500d00c003541c0000140528003c0d19601c040c403600c2a51014000311080001c12a100c49040d6640000640c00201180c0c00b450240d004200eaa10141020184165144c0c0070520a03003152480101195861030104101c01c0c410f14041c200414054113141b9001c0d00c80002a4500d00c00340881d869404514104020000700b54101c405090304041182c0769020107103013010181d07001d543d400d00000d00705980f40c2108016802660f040e80d1100b03010b90700390354860544c1c1d80100345807190181140700d5000e00107036100389a462075000d60300707082099585110050100328110550251544a03900601244005160105480c4030403541190b960b2500803a89404901401802c0d48150344603400040144403a50b000803544030913199600280401c1c3e998000982c0c90b950101d031250188035060003188001030322a100e44441c1248507102e20f043c00c0c0c50b54000c200f1180100c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 22013702 1250 22012452 22012483
    0x801050702010b0312030a0c030b1801061b050703020f01091d041106030603150603031c05041104140a020a02030d020f070b01050a180203040807060203040302030d0c05270f03 77
    0x8061120300c0341e0a000c1e107800102d0503001000d80c14a8500b40c0c0066102c014281300c41c00b40d80d031400c126458420b40140d594140b00074080320b104001404070149105080c49401e003c1140e06079201c2e0651000c0b044504c00d641c00901503c0380381d180d902070040005a01e207407079040110304000814a8034548158100d6080c0c1044284034500e07003840d1559408400c500a00d103d408184204420340d0390004840b61003002000f0110381e03507250507001ca8918050005110084001200720385e4000700ac1da4419481940200c102c400074060300401d1000b10ba515a003607212500d1107800003040e102c4d0039002400c3e40e40390b80c41200d140840540c2102d049030402c6196450301c040004218060203d2a00303181e014100445400544a10b40301c80001a20003181d0034641c2e0b942c021000600380221401a0745006800c8001550f480c9820301d0000e40701c0d80400c3e014101301e40b6003205160802d12450030b0720306142d00c1d001c00c610040050301e24000c2a4410000860b4042123085084440351010b20139403a4900604 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 22014952 1250 22013702 22013711
    0xc18061407062a05070b0612010603060c020c04061d040305030405030c0a12020d0305070207090f06050303040306140f06090f09011e02030a110c0c01030905150405060106090605090307050907050705070801 90
    0x100500f441e200c80c1031200020441c05204083c04901e0300505c854004800311126070f90000007984d1280900713003941c000b900d030903d4242c0d045002074010510041a0004403400c0102e5034890001110000c01703c4140600d1100f082d00040000340584011a0014094022070b41007001c42c00c607580c030380810030b5022280c400e4540440c250003a01045410701c0b40c0c459040600a624152200a507611003900c074400d420360300d4490a18800d1132551005010b0400601601e036030726141d0608001400145526404e1a00c8102c00a0f2050703040002aa0041000a240c3c80854642c0d14031081100005001d12075255039a1040440710f030032101c0c40d00c610a550344005030b183c0c41e0024101f03044511114000c60422000c10619103868804a84091014401d003030020f4144080e041082c91301c10f104c400c03110781d890a071040c007041c0040081c00034100c40b1300e60341329070390325444800c200c0e4180210703090b07990140e01206090100303142c40c1d48420750003481880d00071f0a102903511041e162203616030158180d41d542d03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 22016202 1250 22014952 22015001
    0x61104091505040b04050f0f0c0c010609050121050703030c2906030c01090308040902030c0c03030702010603150207021f02030f070305090a05010c150b040b0619030c1806140706 78
    0x1d0f0050310054030307040741c040141d0f182600c0241ca001f0390080402c03800f90886000030305075001200956070044c07030550003003042d07940324400100141002e00500900b05508007a00c105e404076940fa0104460b0b100016080c203c0c0781d41d605031100c010000303080362040920140a00c1e03a03444000d40d4940000410700c2209070f400d01406260a0a019801c064100440c1c4d08050002c14141e030201c1d001c0350341038a40160f4a541c0d0031040b805d00e005a000002c410701001091000c859415085181624080e1040c4500c60300c0c10141e2504a00c540d040c025040059070300440d0f1103000300e00c02410b00c807a460041c0c03483c0005008100c5015441301e0000c4020034004540b5a845040401202025180030309020b13130030103103540312105140f3740900001fa5240c1c440700340c1c12540d00c075a04541501e480c05401d0603200c502d0780d00749114007181404108002840c10000c2c01c00d203482840e8801226072515420392809042200403900c0000c1c100e0f4440104404101400000e490b40c070070005000700d8000008001c204c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 22017452 1250 22016202 22016209
    0x405060f180303031b0304020303070c0b0408011a0d11042408150103031403180d090602010b1504050d020406031401020423030319120c050c0712080304061104091505 73
    0xa000c002e029610502c03c1189104954040100c103440c02400c50f6281d50b1644002890f5118810300182008201200000e45680f1400a002501c02a230024440c000014409403000807440e42016800301c868038250300890800b441b08a451031014202151030048545004400c2d502c20000805440d5618020000c0510074004088400d00d8503038491041e51460314000e000a52402c1c94044000c800801705807103981002001c41604206002c0c0d0ba02008000d0002d041054240310b00c4025508042081456140c01d605641c1c40c180b01c481d405080500f00801e00c0480102d40b030b8100c1c2c105603a41400700110340103002c004001e40084c0000740c3d50350304002240f00b064205140c031070586080c4420484140c2d90201c2510302107064082174840f4202c03c0303102150b02c1e6030000088481c4915044d00070301c04036400030050aa83c00f6000444107121f541d040d020f10f0340f00d40703032001a0a4800610124001804507003142c0344c10391845400c241441d0b120289101152201c1d8801109603490150803c030760f04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 22018702 1250 22017452 22017487
    0x10c20010e0303071101030b06120906040b07030513060e070503010207110414010b0706050a1103090a1103070501200a1a0411010302030405060a1e0212010e1015050a050405060f 78
    0x281c142c0c00745041c11615a595a00450008521814181c1b40c102c2c03d02031f038a420b02030341c0c28109951480681400c0c40c480440d100d10b802e81d000c0d07491400410005071030600038010a80039008c1003011041d541c040c1d80701c04000f4038244040b02d0960280a00004d8181c1c0d0900141175068056500124800d0041041004030344000704148240705001c001044409189015244050b030024004120b90392003054800040c07401c500c08a00d010408030900403c100005071400071244591000304c00000c0d803004050b039034030301d0703118290000b02c41c0c1550003050400f295002d800d81c041d4004451220304240d8420f00c007000e021861500b8180d0f0380d803c00003800300aa6120303038604420300f421481c500309626501d840c2c8100515110b910b03078490410402d440500c903d4000c15400c2040b0841d00c03805140c40720301c9644000c0c403c1018808001c000700d0b154984005008045030310928070317082c110411740402c0d10103400c55140841809414000010544c43d9600141060340042023007541d11020307a124840c1c4030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 22019952 1250 22018702 22018727
    0xf03110a0e070906030c03091205030f010b0c0a08130e0103050325020a050613090e030703080109020901090e100803030412020115050f010516050a05060402010f0c030e010e010c2001 80
    0x840c404400e1108083c2c004410030142c9400d46004909040030700402d0b0090310708040001c0c000d0f007019a181546d41ea101014500980100000002c41d90b40c824012050303000704100600c0300e0700400302120010360520000c100071046a500c01c1ea04980c0c1d404003a48081090344180c4280e0400111003018001c2e003801202d90030442c01c0502d040500d1a0041408030007617000301401004002818105000c3c0c080032000180807600f0140120118440065103a40082d50300710007180940002168040c424000d43e5030707410b0b040c1d5032031000381d243c800c944000ca41d02610b610130100104502190102c41407004510460050f51522010800c040000382100e0b0210b11325448050398010602199540303e80700d02c42201c003440c20303d40340c2d106000d03d2846182c0800000f0414032403000304a0030000003069a900c01c0d4000d0322155290318000005803100c9030054802030000d055a407050f4107039070140c016004452810b150070135117422a90f8070380d00400ca4500c14440b045000c04526022580d001d003008114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 22021202 1250 22019952 22019969
    0x30302090a09110702040e0f16140108130204050417030c030103140d080114030f0304080604030201150b0703050a1b0606030209060a0308090409050319080103060506040e0312060a0f03110a 83
    0x10303001c0c5010183c0c1c640124200284515210500d601c0c00f60003c02c490400c01d0116010744600504000455181c50503a2144080c0711251b00030040d510360040880621840c40718000e00c0e000c02c6103600300002460000c208469400d03403943d20100541d980303406140308112400e031195032035045003064285441d000c10b00e003034550311003800c0941103503114408034111255110038061032004000024207004e2040c0c2da0018501c4045000160315000103040344c0644d001c0d07002002015240601040708002c1e40c0151320b00d60380c0c20411017002a00c07442c001d09400b182890000c0c0c170b11082d04015503d521f040001602c46c29107440007402907180c202d48454109d9011901220b009140d644c800c101d5000b8641403601c110707902d0f00b9035030600c03905204444a02d2640c240ca1400024040c4000e04144028001500c9c1c0920707180c0040c106040c00d104043c026200007004500b0032800c07805a2180e8000140302c10741007281d14000103601d850a030310032005180701d8205203100000758800d000d080126035000031036 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 22022452 1250 22021202 22021211
    0x604110310020405010f0c02120a050703060b0301020a05040317070b0901050403090602030309070e0903070f0507060806010903020603011e0302030105090d0806090f0403050309011104150e030a03020d050d060909030302090a09 99
    0xc1d82c0c1206c01d10b000203003d810080c51800c03560000800e03c0799402c00f8151180030750380b214000c01c2000316801003a644568020040c6550401c2454200e00a00c071703078040890307401c01080c07020464040c408000240703031060031481c1200c1581e90100612007030b90591440d0703450b501400304054103e140c2d480030300814402181076141004903150b40d1700741e910815916010140108400c03140500858070500d41240040120340c0562926654481c2d05205000c0080c010780c02003419580300d40c44c21001c480c0c0042c0128110390a01006001d1007401c04000540310008000010060b2028082c091140c9240d50140c01250b01d00c1c04041d0245400038040f61003421900c040001c0b0132000034080741c000d0f4051130141d441e5a6013480c081d00500c1503c0c504400300e00f01040000740b450840b80700402d82c1980d60766012050002000b41565a208418002c1c0581c00045040040d02e2107080540080680600007044040c3d07200b0011017154000238080e0002900003610802c80e040480d4140024501c02e0001c11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 22023702 1250 22022452 22022459
    0x5060d0b1f080a050f0708060106080106050d0b0a0602011505090405060c0306010507050708071d04030f08060a0906090902040e07140f0402040801140403120212130303090506041103100204 83
    0x82500c008012426000c012410a9940c00c1c0500041c00a085001c00302c83c068060703814000c0da9092031064200c054800c5100210b800c0c2004100b0a040700c4840d29040010317401e0020586035a007241042c0042e49175280c145440c1c9940b0003410340010000381e000012603e8503500008204c000a40045014250303000c00c0c440001c0300021a00d61184440001682341d44079000120b8291103040c40c046c055220311400800c120301b01060781011244100200c00840d507081b9004080c515044030f010340401d07544000755107850b0040340080c1e80010001c20a5415a4491416004446098001c5000035075103202200860900b03108007410421084001c000c464640b504007141064541c03501c0c2c0c0150340f1490040345076283c5070181c601418000009001d50904e8005980304004211016400600324101a20bd44119403080b035a0b4040902c01121550b03940c2d50308840d034000310342421020541e40d80000e2021032402d2299078021441405014984446c9604040c64030003900060114140704200c01c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 22024952 1250 22023702 22023713
    0x8010c021f02030709030c0308040608060d05150405030d1401080c0f1507060902120c03060f011214071e03050c0103021305040504150c02010c03180f030507050c060a03020c0105060d 80
    0x24030007944400009a074a03038403150308a40414841d031004101d074802c500007000704000c000180c03054403c00c0d951b820744c2d1346d107690400040141104024000350440d4682403c150791051711a54884c3c050400c41e40781c15040b070188001c0761003e0210240e640303100340c01401201018400381c20b010300200e0301000040e140c1c400050f0880c0c110714103440320f5140014580d017081110b400003404660000e1028814500d00c00490740c61310a040010383c841c0c0601e800044c80508a80550b5050300c1c18800c6918105d04683d480c0750400500d810075031510321800b000083d03084402401040305010b01c00e084000c01d40303545042072801015000c814103050040c000304044100503403c0c1021950129000b10744d545a900700b00340c07410420061440060b0514141200c42c68054121040c25200d0750780400c20720100c0d001d4501040b241c10340c001d1484151800d505d0219100300040e080280c09681555070088054001130103550000d1102004207401148140090740280300c3c1550001054070854000d40040d920f9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 22026202 1250 22024952 22024993
    0x4060803071211010b030a030c03120509032a0f0703021003020705061501030b0406080102040f0e0103120309020102031b07090501170616050c0a0f050d02070803070303020901110d0908010c02 84
    0x2c4200030070450b9041d0000c401350400384038418042c0584d2414a081d042c014a46280410b040e00071902070b4404218501d410b218140c41441e40c4c9001e14100007917400003a0300c0103c05d150444081480700c2d203030443c04100340800d91039100c0000003030068529620500a91403500ca58140078988180303d0007010a031702145a0f07601042d00c410034005c1180c1040180d00802603031a9054000340303840c1d00458090300550061041d150f0304000d07008a9580c900714280d1507d42404000c041120640c8c03107521080c02500f15a400f0ba00c1401a05c0c1424030305048040507080d00c0340d01000b03591007544200801d10980c8141809400451140034040c0010301000b0740d0350801810040801c109e40618a02040c841c1c01a40c0c00707050b611040d01c2d03420340c25042c9040c1c05101c8a5043e5400e01852002144107400010440c0c00c581100020754103011030360320103500030b40101d107003e810b04c80d5080710620303542814404408500c04076207804801c1d42c1004001800c503007206d0b42800640d4001c7e4081c07150034580712030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 22027452 1250 22026202 22026233
    0x50c0721140a0c0204110f0309060612030903100b01050408030f040510110a0b040203120d02090406050a0e0a02030a06090903050c1005061809070b030c0c06090a020901030b0a14090c0406080307 85
    0x4010514246c0c0d840c40c000d03540b15014104040440110602481e1140410042d01424003144c0c0d482004005080c015100d200342d801c40c0e5030cd6405560351603c1001d56410a0303200801c1410140d0a195444080505580c81a9820070514038002000c0c44a40b4006402070001301d803525040198101404600d40e0b90146c2290107001100460002021550f00700a070201c44101426003030744070b4109840282c065000b1910052066050000200701402c1c003008900440b41c2a20080b002c80d111448040020750000c0d24082200b07071200c2c2c004c1250142409081d410074802e82d03230650341d04000341c9200d04180124542000303050900080c80140e9a9400940d400e007070f0031004070020ba480da20030440c58001d0139407041c405110040200601c80d0b000c40054006032a00005aa10301c0c0c0c1c84ca0b20040d00d0351211607000358403580307501c0140041212142145c0d032100103008002640d40040802d811149002c5034540d0140d4070802160b90b0380d040c01e0150700d00400b43d4000075030500000b5035800c180141080c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 22028702 1250 22027452 22027459
    0xa0c24030203060d020a08010e0f030309030f03040507120c060e040e030a03020901050c07030b040203060f0603070b0a031e051504140403050307090f030821130303050c0721140a0c02 80
    0x1050441d0355403190b09813407036030090100101e15030390310103240a8860310100f200740d8010050201401840031003202d10995424003c1d51400980e540e000006810240081d520b138403075800302154031a811040301a140f40a05d8800c600245440c1e40281000409802c00d40a50b0410001c0c8050410010135030b02182c40a00700561214201c10048502c3e000e60382040b1124440d18100000740103070304200301c3c05103000b80d0580c0e40503070b20034604036202d40068a2941d0180c0c8503075002c011800040018044100380c9140100303941c1d4162200600b4121140c0214044a82d510f0070f104026080034840110702c1810f940902c031449804180c9140810b00910140601c6000800580c042c0d10401144c000f403c107542100403403035100c0c24a45400e030030080000a40da06901040520591400c40251041111002204c030002d12950110041c0c840038020032010340c0c061000301c00141d5180d54903500b114041d0781081ba00812688001d10350210000314042c2c5000801007060202e91188400983c0b94058 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 22029952 1250 22028702 22028707
    0xc0804021c05061302030c01080f010b0d0603060e060105040605010c050307060b150d0b04050106030501270b100c0507050108040305120709150806090702030306030d030506061603020a0c240302 85
    0x610700603600c40c0301c010050550040004024030085559840320f2007500035021101c501c8036001c0152210350702074482d02c2004015000400146005000030301240d001c212010491582c1c1e0340d46d90042c0d500224003501c00703400940c0144120700303052289000405092078040ca111402c2d403507a503200d11919101a10380c0d61904440300d220b44494996040c038040c25855903076128100c1010790300610420012512407424a400015418440c1c000e49040c1c0340d200030301c6100220b035030306040301100041820301200da440c0e01480c8803a55030950720131300001c40b5440b01036000f80b66140c52824000309401207810310003100d09000200780d000050b02c40440e50104019840d41719480191031059041c2e1151200c1282807a400d600c540d44650410300640d029503003003000362a1181c05980380c5c04100c40140d00741d4070540340003508034829004103400000280030945020301c000ba52000031007002c0720584c0580d0000c100c01040142004180004107080203802005400c90401550080c16142c3c0540425801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 22031202 1250 22029952 22029979
    0x30315010e06130b04031704060f0507050a0204060b04030201030f06060203190909050705071209061b021804060e160303090504050613050a06050102010c0305090601030b040302100f1a01030c080402 87
    0x9880440e0114581c0b2800c4003c03103980c840c000401503200e0302040ba03900c5e403040d45d07903514201d02200380d0b4207480301611b0703003010007280141c115403981041c101070760035100d24005480903880d540b081c400940314030040d056035181180009030548540070b0b51941c0301c526090b0104100c6a001c02540d0406001c0d200206a415a50b0404c9400207a10b4110720f120519000c28801c07481d41007001404003a101d444411141c400440059070b8140d441d200d440041b518810305650b40c00c1da20202c80b00c80318402492102140d06c034904503c403c107030880e001c40c0c0d032541e00e084614841804100e002100d07003040341e11500c0c1c1411a90002c0410b0060311500b4091520341d03020074016550701d0000007030705000001c10400b03131805100c07000207000244103c9000d546082400c04541c0e12901445102d010007030002d050503461a99144c1c000f5000070710540c118040c03100101d80485130781c01003980098103084082640043d0004844280205035083d0741030501c5c25040b050600c3d040042c0d03661090301240c80d884043e90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 22032452 1250 22031202 22031209
    0x60f0105060c072403110c0d080907032001030608060c04230301020711040c030b0d150216030306030302011503020904030807050c0f03120609060a1202030c0d030c0b0603030315010e 80
    0x8683c02a03081061004c60141d4010f0000c805108150078a613001c0c040001040b850090364401c1c1c1400100751b410000400c82010b0003041c1d03907900952420200d448040d035980f5030f081045920b0038195038015401c0107500b840d60b41401076501402c141d001400d61401c00904941d22403080b486002d80742c103201d644451440000c01c83c482c01e00580075009560320201c501d450b0741d00541c03010302244154035200f50002d4440c0300340310f200d0704090041c0c80b400000707005841c2c1e0002e55104041c1140da0640030002c242071014a0800d40740143d00c83d880c085040c030305514000e82914414400f0a4407180c44804c00c10260742d0300351300c940d003054160070240d145849124007280e080c407541d5201c0300248900034403542001c2e0000020501100b0b05403030101d01e030702d07000c041200c0c0c07103400d1b034000d43d010010640031f014071080511101c40d8203100404507a596482100030544111454000b0790200d49a00c51030b6060002e03c000b11940010100c001d0f51451808010341e0f40c410b0201002141007040782001c0051031384 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 22033702 1250 22032452 22032463
    0x301060504060608090708011a040b040b04020f040305070503011a060304050c03030f0d0f0905030708030a0f05040f030f0f0516020109050a08010204080d02030711040b0402070b0703050603010b0102060f0105060c 93
    0x102078400c1c0b11064440c40c0282c2440003e40d0307150541d00ca5410002101c400621449042089070700c0f00c0003400e000380040002030128840700c190300c25039a001c01075260b90303644020102c008802d4501503c0e1451410224201400f907071100d802a411700c07591030040301d02004c0e120320040342184c04035202e40b100d040141c80c0a201120094040c4400102103e4803600d600103880420000703001402001c00b4400048280d6a0b10a001052580184617100000e4502006198085035881340040c03071103020002c02d0244e03242a01d003540c0414084c0208806e059000308010350f03034007050600d59204020380c6030090661051885004410171464420740c2168400c0403000e008000003804500080d40f20806107000b075000d48100d01652152208078001e141c004020307902e00540004450510b50003181c140b00150145202c0694016800c01c26040020001c0c40094041d10350350340c00040514004060508499850400c18155801300c020401e00200e0654000d06540e01626410344940e044482c045c9010f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 22034952 1250 22033702 22033709
    0x402060d0b030703151805030307050703020f060106030b1e09060906061e0406020c0a08060a050c0c0109030201060e01050d0f140a080c0a0b060108010308160309080a050303101403061302030106 85
    0x5001e01e00000091180304400702d9000c10a2810411810306c03203001115040d410800f00400369042400001e03c020b01400203001d100c1c1c083e006548408400410590030008240c0001c0c02090b17035655a01400d040130185075611011030301e0220480d5040c0340001d400c95000404545c801d10305040040e40b0790322034100703460b401013101c58160920060902070031419040342c00740800511072106806c00b00e00e0030440010407103103101c001d824252a030311402000b03000000c1c0140d101d40300c200308824000341c0034417400c604140a40d000154803400d00d55005014071040e404144180c50920340000455000280c410410b90710491031990a0f841141c014105501d1417000f41201c80041503030240f15101082d61040180306414900c200d41c1c5190040d00c0410084c00068105c403014410101c10703019408034910058000d007081c80c50641d40d001850320b402c011610860f010f40000c0f06001140c3c22340003643c009401d030540030703140d400a0b40303003c00e96a2800414071400200d104910400795102075110308043d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 22036202 1250 22034952 22034959
    0x60b01110a0b06090a020301031a07020106030c0603020c010501080d0f080a111201090e0607050403030c020102160611010b03030c0a080d0e0102040b0403030834031b030b03240402060d0b 82
    0x100450804440d10b80d403c842d814050010380000840c204018400c40c0d06803984041c803c20480ba4009c0200d0001c0e400500407800d541d61f03040040040740000300e0f99001000c4030380d00940d0300c60800b40d40ea42980d9040e808600981c3c007040505181039001804d00c1c03030601d51883c1988440d9507200303d01004d0100e5048528007110001850b4040d4101c001101c0d05807004d0310307014481c003228592810b030344510440780d100000340d003800700b0b00c000383c8a0003421b18102d00500c1112a405001000a031a0100c41d074041004103881c0607100200319000c5c0100c40a0180482c007441c140004140074603280c2250301c000605000c4000307444400d40748683d111070883d1018400841d140c40e110650062141c0c003a00055020030044000910381c5109281c641301c69039280c443c0554000c0d241202c00e02680c903d0110001815140c50b214241c2010780e00700d115190516a07404901080c1c100207050805000865115000b420300707014003141d8401c0c20005e40c10650542d1400d540b0314441d00c01c00000c1c604c0f4030206a2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 22037452 1250 22036202 22036213
    0x160305070f2d0207210b010b09010c0204050a0506030c01020f0a08030705130f051302210901090204051e060a030809011202040b070c051905030a060903031407051c02030601020a060b0111 82
    0x8540c0c0d00113000400c1e2403042e4480c0002e040d100e0302801507007a00e01002803901480c4401400064011400b03083d00d1101810600c801502640c0000c05507041124094102079445042003007a01d402c020081ca545802e0019042c11200507256a458580034000a040c021000001c108040c3c4214110785100d01c4450009a41d01c0c3c680b940c1c298103640074803030390340b14007140c1c0b5810b580f086031482103c02d50402400405041e051040750f00102c2d11008010504655840f00d0241c0962103e0240c030b803003000f142c1410b40907400b4801407200d00000c003811880c0288601c0d01c09000192440701180c080c1300c401d00380b480582202c400020047e10583c0c100d03216401e004103600b000c1198903010030058400403903a4020040c640700a220707020b4043d2140992540c415012003010946590005107110b00030319021034180c00c44c1c80c0c0500d00385425191a0009040010748074065035800f401602d02201c2c102c0191f00d0760802c400000d655921902e8003401e140d99503524172b0040ea008580ba0541c4114020507a20b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 22038702 1250 22037452 22037537
    0xa0b010305010c030b09071704170c0102040e090a0b010909050c10030b040c1e0305060409060e03030403120b1f020708060108010606020708070807030308040f0803010b03160305070f 80
    0xd02070040c9845070f0f8007281c103003910030200346450101280b0500c0e15648001e10301440e0352250814007005802524200c140914400f00005024002c15145e0441c40025a1b5549440b58801405400810b83c60042d000080c810001500b034010150440d034452034041840354650900303d0034000001c5050b540000b8503100308020a40580145503805d404a5007000b94a105803001d489001d0300500b403d0b03100641c2c00c43c202202d80030b603000c1504050081c10004880344565941800c68200f00d01d200c0c000e41c0040100070426611001c043d41d4001807034420f1200c000c3d00c1000c290058201c504c1d400d201d007480041c1b84030a9208202d400010840081111102d580d10401c0341c0c02003145015520060140d840c02203822a00050b201c012181200024040c81c0d1079600c040303840c402c0142c400c85d80c1244000c0c1c410041038000d0043c1d0b010700000d10201e5501d04000d441001105c0d110042d817414582000c080180c10782e042141019581c00358106140c03045840640c2000c28610a4104000424180c00c0340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 22039952 1250 22038702 22038713
    0x312180705041b0f0e01020618010207060207061401061b0b090c0d0309050f0603190209011704060c0314040302060c030709090501031202060903040f14010302040503011a03060601050405180601020a0b0103 90
    0x4007240c600f9882e003d440b08020744080b941c4440b83c00034180541c0c00040403580400105940c141d444000900041c24030460365a010282e0303000800030740c2c003aa111015002d101030390310302a500414035814050071185100031800e0f8240400130001e000e40880400003120fa000900c207000080b90001c000c075110501c1e5103400780c051443d80c010940280484080b0408604018045a0103034440000f501000206c02e01d20001a501c801d5402d410040110080e0b428200e10703a9590b40940d11904001c00c00098424004044500400007001010380c100180b10100350049841c94014080c1c07481d581c4c2d00d6a07606001e440760342d02980208c009902d00300c000014402441440000504182c0c00e032242901c0e9098000c1d41c82c06503024000c0710301c0352004200701c10807142446252000040c10054105503503880000e0071141680f481380403e910301c1081c5203462400f40044c0341d001c03409090550a00e424034002c100c44d818504511000d45000001007611a8001c0007038031481c41c0e000161855542e100d00c2d21 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 22041202 1250 22039952 22039991
    0x30509120609060c090a151808060a1a0915040b030f010e010b0108090712150e0a0212010606020304050405090106120f0519020904020112060e0c0a11031218070504 72
    0xc100090050700b000c03805084c0340c5401c82c0c0c2050802404486440e040541c0e0724040305445504500f484410a41c0c0030500050200480080c040d0707001500540c80d180c4044020368240a03850745007240004402e2000396160550141c010560032048801d00e64030801140c02003c0d58200254107203c0c0d0a00c03401c00c1c400c1500024072540c440c0e40248403006c062401560488402e40e0360038030035089648140204078010003401e105070301518540c445002e0003080041220b10b40030781403505800400d810010f40c117200c0050700d4295803030002000424a000070007074983c0075a010301c034030a948400c0824000102500402c010b0700380c0b031441c80e0842015141025144400c000126024080c081725104900500c42d8452030050b00a03040c507079150340b9a401122000c50b9440807103a055900c00d00403441141c0c41c3c203620b1156203c444050b0344c540c44850054080c00c00c5000c0758080d5403003080741d20b01c06401c82240d00e801c0072100300b0715a8003044040708039081104c40d400260b00702d49020200407800f00e5a008d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 22042452 1250 22041202 22041211
    0x406140a12110414240d0f1a0306060307030803070f020c030102040b0406090803070804050405071b030206090114090a110303070b0f010314150c0a1403040501021801020607020a0308040305091206 86
    0x103d80f50481d2109040c0505007071451154604401c00c0041ca4900c000d55400900100c0c16141c3d002411990790700714101141c000c84c8c14913010005401500c4146e00381004500d40040080700209181461070707032000d0845c0b01c000c0188041000c0100540c1d5094000c0003020380c8140000c00a54480f5100c3c1c0c00020507420920400d00001d00380400080e0402000c4121100280c003c82c1c00761070281014140005810041c4c0403808010b001804000e4001064902141c110320aa02805039030a0003244030303094801e0200300f0305408880344148100c5280009084101650289403600c07082200c40002e400d5000e074940240000c02c44404001d81303610182c9034107058a201d4881d4030069840301a0343c0759214402d52401c41d554030103d011840c80341000001d80302c109a00e2510784036070802550045110780042d2000c81c0c2030b80d004640c0e048a2100c104400200070802c0c4000c00851a10030030096882c0020f6038058140a41038020070207041c0b04008441000e04041e11086000c40d1038030003d5620f4404a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 22043702 1250 22042452 22042469
    0x14070f090e0f071b030203070303020906040504020307020a050606030106080c150c0609030406090603020304050307030c0c0b0403050102090a08010507050304030810050a080a020f0103110d050a060e0c03090105010b0406140a121104 101
    0x1c0c13018a210441d203c3c00600b017605680158102007080c0d0b0182c0c002d60040d4031580e40710b00240000500c1d9521400118440c80440c0c1c041e205148030303881c0482c0b40c08405003459100f039050010511142000007141c40f07a69200f103c0f40340714030011040c000d01a220390840b201e014041d80c1e040208104000006004071091962a4403002e95158821012400140c90041040e0810400c2c240401c1c0b150745069001800b4050584906039540501f42903503000c0d5104a485075004a200005850200600001844501c0c000e004d549005d00c002001840014401418400d4a00104000e20750960004025260152281c0c9901d6150145640da0351a1540102c0c4100300004c6400e41c0c6512a00070541075030707440d0310b006040001075a88080904801808000ba0907541c0c9400030f042480d141026014400c02840182d403401c0c4502e40c5801c0d200145c0101455031420807080002581c810f00340400840c0000e04161240011502228a4942c1d49110f240150801c0a1181940c294000900071101d800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 22044952 1250 22043702 22043717
    0x402300106080601030c050a050703140a0306030614060102030702280609170f06060d02030a02030d030207150203010e130609170a020c010804050c1002070b0708030f010914070f090e0f07 82
    0x3d0011001e035146002001c0000701c051042c0c1c1d41c041e000310080e00440340f10341002005006071100d2040a031700002d500200003901e441c03041017440010f1051421080c0c000c860048030341340c2200081e56911078040000d020b03a643e0030b9501c000a400710407844403001058142c003072540e601c000042100c0e03e18041e842008002d000404903400c1d001928100041501340501020342e1210b04200541d0205142681c05002c0d20421400503039060116600c28240790314010b07154030050900c5003000c2d139011020880144104010320080c03541c804080d60001814840300c807103c1c01d5180440c0a80309211000788007800e03104030628400124005014909038590031240b54200e41001100c25040c19200074000390080040a501c50406004121104030140100c804d015940e0010080960001c003054902c20004030078801d4503005c46495500404801fa0240400a8081581151410080c0010f0140042000d041040900510b0309500820f00000000d40d81d10300402d1491040310110380d8a000500c01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 22046202 1250 22044952 22044961
    0xf08060103090c060809031e0706061203020a0204050a090f060e06150d020904030201020f0a030c0206010e0c090405090c101e080106021b03010f020f09040506010518040230010608 79
    0x244140b01115400403541e41c880d514080307041c2c1e0444800b9100322003d00040181800e03241c11204807078002111800000d54403503160601c2c20072100380d03030072503104088800046400700ea400200c88100700c2e0100d50000351600c1c1c101040c001402140c03801840300c0001400710301441000c1d4010945244c2d502d058030801da4a0f00d0b10b0150b04c03a04482e84950000c14100c860002d07042440415038007501c6070000500e84060000c100209804c8a030049000030348a4068690042d414003c1e17500400c001c0200d41c1981c1400240d013202805000161401540d480c0005549207204100e03d1581c0c810113009000d50100c6441d0040c52080c1300e450304030101220108407038803640300e405490704a48199020701030786038214145900b4540c0003141d940e81503407101241380000500d4801003070360007a046c1030166142204003e00003620340040105041c0102400607012011065551032007841c4100d4006030380d0392102f11010300c4e054801c0d010f440007085500c45807880c0660400027505880040d1200c90701a074a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 22047452 1250 22046202 22046207
    0xa020a1707020112050601050d0207080c06010305030a09060e0a0603020d0b0603010b130b070302031603032406080718050409020102030403060509031c0b010f0f050c0607021b0d0209060603060a030807030f080601 93
    0xc0c00d1b18258001481000030111a036034590181031250b119901840c074100c3d010454600d8200c1c203800948080e04000380c4107503040d410415913401014541050b4601d111003900061000303106118074018113400250068440890341d01c21003000c0802400c950b100d584516203003d4a4003c003401282e0a4102c04000c140d0030ba081f025500c1c00b0350326070700a51900344014407001c0d86c00100c20080702815140d120381401000400c80c825510500c08560061407440c0010040620f900a4555000d015000380854607107c070700c1c68a10b0035110700307560104401e205440102c3c80c43c421940f02502e03891800040c070030350180200081c22210f2204c20b44541c425400c1c0e50301c1d03040303a4940420302d02207130440250660040c000c0310900104115400e10300c0c2070440b014400340c1403003411a05400142c100004448003142070112004114800f615810030000443d13011034642e580103071505114080100000d139040e075980080740301650381f298030592030380410300d009422462003009a0300070a2001d00043c12651 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 22048702 1250 22047452 22047461
    0xd090b090f040b060d06140f01080702070501030e0c03030705010209090606030f040209061503070801050a080309010503010e06040902030f030904060b0c150402012601030c0812030703020a020a1707020112 90
    0xc100921410784100d1800c100401400b510360b10303d0b0022000d003c1010310084600c100801030a5081c03404101c0101282001101e03210407081905024801d002e00c8661070f03001489005503442828000380270305605400741c0c80c1c02c0c083d07010181e00d840f002407840700b04901900a008224400c0d40c1c0c8a076540c540b00100b0040d40011100d98003500c04110024015140242130160088000307044101650540c000080003623001711440800f1403030010040081e8109002103200414018016500702011080000d00600c418031850341408080008900305e0f6440d5031112120b16070050441e14041c0c1d480300b2142d1250042c040032440b40346170403800078021004000721103020032070b000904500307400c03201d0300ca101c0d550190040c2d041120003031000d420440030a07025014000000070100056241d807501c0d40600610b500b06c940c5940110381003054424000090742d070401824240561601084c84089103881051a005030881c28009101207003444401c0052071002c0c002e03620008810b00140200e0700340e6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 22049952 1250 22048702 22048717
    0x10801020a0210090807080406080f0a050c1209011409150108071401081b04080309040e03120708180d030615030c0906030b01181d100608010e0406090c080d090b 71
    0x140c01c9400d080744010724552045040310305c101a804d0405032141c403a501036070455008100450f45000920500c0340010700c0c55544460416020b02c120724240e21451403501400031a22101d01c510004542c403c1029040141810a494051410b0341f030450b0700159a6501081c4c071a25140f045000824080f40206400d82901c89440e0400811a002401151215070040001044a281001c0d4900e54254440200020100600159206e0b40c0400070132080318070144032444564001c0181103c0185aa0844e0b43c6c000014100f00b100c0341d60317010842d0200e801e504c055180c40e0041903102c0c0c2500e5010341c04a0180c50081200c0d2841030782d08641030707040701c10201107100400da0000e01002800c0c8207801c10b010080e018074000e000304510004a11100c25190401070041c0890a10340d601e81c0408400035910410300090b042d1000c6c074000c005020a68180582d140802544002400b4402607801081c4001e03070082416030002c0d921021542c660f21540418800240c040b40c0000741a001d0500740d5649 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 22051202 1250 22049952 22049957
    0xf080603030f030c0c06090c010315050f040b010504090504080403290a02091908010c0f050f04030f0f080a11070812040b070f02060c0a02040615020307060c02010b0a06020c09010801020a 82
    0x203059900b4000c0300c03180c0008124400b400d008028140182c0001e1160301d004020b844002d101e04203120b030000d030903603013000799202400f0800c1404015654919583c40311800c425500080c1401220b001200e8912075500b0203011705051902b844108183d54004004503401406203010b000c1c006803500e0b48a0500e20440c41d41d013040a004030340c688000d5402040b240c140100b5204c61520712400c0c403013040314668813036051030350344408209030690005540c034140c08181c50942e250000c85030030480c442c05039001c0500207140040c401c0080100c00d00d03800740703950b03040391001d40c6401565400510102501100d80480d0280500018020100180d100f1890001e80300740390a090078002c04845075000284240d0742082403124441c0540c440c0e80050541c2110b0202a24840b9014010702040e5a800d9000a1041001d58610402e0036808410350700000d42c0100301042e10714404100324050941240c207030750300901c0745900080550300010120f0541105584040d610ba0380c0c3c0700510300700d01500991001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 22052452 1250 22051202 22051207
    0x7020303040b2a0301090b1f12060e090604020307051005040302090405070b0406110c0a030b070302070c05040204090204180501060f050304050f0303010905040201020c0d0503181309030c02010f08060303 89
    0x803580c81595600c0b038260703001c62412202c880750f50f0241080303103544040281000401400140018002c610301c3d0382c8140d4006d82c07028500c5040507200d1129207084020000d00d81803610245407590021001001c0021010702d1a0400c11030540c2c90780020345080b4402c2c881d4402c00641c0d41050b00b0001208015a240c9509180c9103400340550900e00030000c55090041394000304110241d60050000341110359500d00185030218805032400101c1c844640c400c0e00308007020800900007022403580b01c01a4030300940c0711200780c50074421814054100c0342e030103070003c2404284850749901a04c2100d84d10700d250030040b054104c640045402c203008100010310407e420306250f038080c1008540180c800e400f00c52038a00342d00100350440e0001e030440c02a0a0300c0354148001d560f410072480170201c0040702c440c1c403080c0d01aa183c5999100751400303030401000240c41201d4503030f2500d1400e103c03005002000c3c080c4038403924009004915812089001c42d40c040b0011070854854019984a1a4003400551 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 22053702 1250 22052452 22052461
    0x50703050f180c060d06050a061b060b01020c10030c0306060809070501080414060109090c1e0e22110405090601060509010e0609031507140c10090305160308010302031507020303 78
    0x42e80152110424881440f41a4082c16681c980400a2078142d06592000400ca82450200104400d05034805802c0118010b04060010303c1c09a182c0c5084d80c3c046c0b0001901040d50005074145199241d060f41c0c0b0130000607541014136015002050350b015941c2d003c01540b6110703002928074900035140400640d00000c010310855000b403551a40180c010b46000011900900b9120320300b01c07090b0001d80c2d5144d240c500100401000c1c06404015006046400398201250006000d803407070a032247d1400f40d0340031004145900d0142c20002a40c00c100c8241c8442400b645c00d00d01040100054000e0207640343c000003c0da8610081003044c1a00c441d91b89051401e090b07400115a00c80c14480d503039501075420420090242c0e4200300d1a10f800410410802403440e21004c0035143c2514080c19003801c1c14100005040c141c0d01142080140500d10000648000b40d41070849840c000c5202c1640780c001920844020305070031803aa07a0480c0c0c800c40881380c0403040c9004511051034140c8900f00541c2c020310114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 22054952 1250 22053702 22053721
    0x109170901030914030d0c050903030a0f0504050d0b1008010606050f03190e0c011107120201120e010213031e02060703110c10050909060301181514070e04050703050f 73
    0x4104821051402040c000c2c0d140c0c56544c105410108030042540c80042c0c000040302690080d03005040aa080003410030324841e000c65141d12903590b18908004820181041980c099020784010380f034003030446100e9003080d15003007241c44010317181246604000000019510380500590096460700da991500b09103540d404071107940c002520100111710702042d031420300c6040d4800c00100341c801d04020000300501500150603107442036440d41c07031900846024400d55500069600c023185d0f0a1030103140012090b00503100804035001d004a440d40002010781d540b40307201e512041601d001e46003403e15807000c4460b0079000380145000075007100c1e00744440300203c5e01032181404406400d6094030300000906002440d124446240756000c1240480d582c0902c1c18803195a07540014103034003c003c110600319500c18044036402006050000388070a0381c915002d00d40001c4015441da108002aa050080024202004098803039000711b15110019401900c280192402002d60301d504510540b11104030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 22056202 1250 22054952 22054957
    0x6110307091707030512031e010e0c09041803110d0f0207060f031506030203070905040902060301090c12050903030138090604080303010e10080a0308151206090a03020f010917 77
    0x200281c50040100000128805021200c0214440b54046c0da5a00d0a180d121590021004022401081350310050002082d0044402d410446a101064031a5407000014005c6c085e01d10428800444e440c030000c0400d070300558804c020503092400d50b0004503180008850a00d56203e000005900c02d010030804140505001c0128040c1d6240115100d170101e048074040903110b9000c4400294004100003629500c111003030003800c0c0031107040c00417492a80004146000c10700819120540d40c5c03030304103410390280706154903400c100c1c80103008901e8011101030300c0750824410100030248201d110f108911b5089083c10b442c2110140c900c3d40c0f6448070341050015000400320603040380c1c1c00c01001c141014100040d50080605039140c4442c0d252034a62403408540a510031181903000030301060020340c004040a500007407040340380020300d24140018a90911040f6600e10324000c150a0080c40303070300410800c44590107a02210103000c20300c0d81e151b080f82d0391040301511050004600c030302a20f480f03030300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 22057452 1250 22056202 22056239
    0x60c09040b010c0f03020c010806041808130e01060305041e0201021b0301060f2706081e010209060d0207230a020607081209030d06080102131202130c0201090611030709 74
    0x141000701c804650b55800281d0a81e440176800759000480040c029a44580c0103640800103403070911108803411041c548a01a9881c0180b143c2d8011441c000c1803140e0300e030319000030201c00602d521256540d10010300181b005550655006244000c050b45281c00d0303130011b000542d411390090205030b2204a85503083c950101545074075540f40c0500042d0070a200460002500041807a54046c2c4400e42c0544582e062100107220210b082400811070300c40085650b15903904e139a0b201040c100c1c40d403443d0500a03c108161141d0294001c0303141c054503c0c1e164051300c0440d204100f0411100018030441c000f080c0384404400316644510f00b000014240b050103803001601c110300c40c40c10000340142c03e851000f0b089400c1c2040d40c0c800b08000040d4980c90041d28005d2080d01c00851504480f9403a12030104118083c42c2c20750000d1b100da0f1003c40d101d030381d0f4581e01840580c02c00c10852000c050000d0107020703544026519241881e04880300414407c040303a0003910f00da2580c5404030b103045186001c82c545010f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 22058702 1250 22057452 22057457
    0x902070b06010806010e032e05010e06090417030c0901120b0303040b070c0305061305070605030106050d090203030d06230301060806041407080304120c0b07050d110c1305010801050108060c09040b01 87
    0x849840b247d141040695466a440b040e0035004411202c0b0b07882c5652140c1d00300300074540c200030040043d09180f40030a45c002c42c0c2600d01c83c030180d0740d504025a03415102c2080080e81e070700c0001080a00040d01014000c0d0710340c26a108056019055840026501800700460345600b003000204002d1b600c810082019510a25040400c940d8a0300c03480d05000044400f06102514400f0100400409103c6003020b00000d05209082d941030410080550294040e6040c24541c0d0720480e6041d99010025600f000000709010300c811515038000107009111908040420002c86c900c0d010360340340600a050544071040f00414166845840e00c5c01c03025091450300700503005045c80070500d848244002e00c0a003c0c60012802580342c1c0313141180041d002603001c1125184103000140000d040407a0b04c021843e400d00d070104203e03856040c01414640e58503000340c4c1c42034910740e400f0b80c0c0e689030380c002504136202c0c200208a10fa136074105694542c6800c0b20070714413415081016001c0c0340340c5540850080d50b41071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 22059952 1250 22058702 22058717
    0xa030902060d020307080603150103080f070b0a0e0c010c150203040804030c0806070216030803070f050c0304080a05060603060606120a090f060b040507090506070b090c0411040f0902070b0601080601 87
    0x250040740315940020510810b80f50000100444542c1040c0a00e401902c242c1c010070225031214407112075294103000082901100283d00244d01c02060f06440005401c88031182040c1001c00340b03c0c006041c012032a0815020b404421101507014123441c840300c0f030f00041200c03200f01d040455040254401081266003110520000c404100d410b1110400342a0b00c1c0010030240c02e050002a203851401e541100079540c98401c1400040c5515050b41d0f04042a81080c9500315907000040e9120302510b40d072102d56200c0801c00040c00f5500250651000c1d000d80261441925900245a210f42d000c9504c1900011308004007a014003012080c02d6104c011180300058000b1283d50711075895855a205030f802503101e0a44081c585003511502c0d07004410340c1031884c0c1d0f16251002041960141c00b402406e80c0c031119001600c0c2c00340c103100b07107070304c10320001d0041060321405055074280b60424064030005000c400c0380410a1000c0e40f007119221a00403421180c2c5d942d4020045450100041c002410070002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 22061202 1250 22059952 22059971
    0x5060906090c151908010e0108160308030709210b090102030906070f03110307080103140c100f02010e030f0403140303060d020904050c04110d0b0d0c151103031e01050303120a020a03 80
    0x1050301c402d4507400381c2d03100c5d82c05525060010203014810382004000d03802241c40c200310f00740305a081004803a404000c840d125a1450000d03182030b11250302c10841c2c6c004a80922006141c18006401030b540b20711905852611210052400c03804120b81b048100d602440106240034060381288214150515001c11010162089016036420940f851804a1002401441000102c2d00ea6800403603120005005c00088040003440e0050110b44000038003a04d002c0c1000440e00c00e4200c208007602c2c0e40c00f2a13564182d85075070072006610520044d00d40c0c4101020266002c000441141d0007808014072030b0b8501880340d000c00220b14000b03030080762a40b04040c1c041d40152200d018007242084400417241d100c403a8001c18106940300760032814418059071031a480091003a003800ca0503078140340c03080080b40c034082c0001d541142080c0600b045900c008020000c030300b400c00070484040401030b503940e43c00e6641e92041c140d032030080d409048102042e803000035070180101d50241c95000e8040c600414a040c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 22062452 1250 22061202 22061227
    0x10e0303070501060b1306020303040314090d05030f090405060102162705070903020f01050708030a0906021209100b0a0803030a050c04050a12021c050d0c030507020405090a05060906090c15 83
    0xb0903500c21407082d038001ca1a0305840c00041410b200801d1640041c518600d400c3d5402001820200007003424dc03200401c248400da201c121141000d660b02000f201d0b59070041d0411384155070801243c46106505000004889500c0466810b03200c2c40280c2086034140e040643c035a14074031034140c40851444a4124001c0c07141c00602401d03020f2089500d541c1c00090450050052590400840d541442000c21004000a030740d042126031003204054009000015442e08602030310070b1000022644110405110a950000c81c14801c80501310400700300311215803091000341c030002c0c440d03050590820310018021301e00c0e40c3c03c02a8440da441e09514909500c510009450030041d0300400580d03030f00000010704508100d81100040d03105c40d000128000c90917030b40ca07913407110f070385216200300940c41227030700304242c0524161808998014410b00079498a020982c0d40c4542502058a41d4465500801d03201e07840820003900481a00e80a01145149d06080c85041e02c50510b42c803120b42000c1260041164 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 22063702 1250 22062452 22062461
    0xd020a0308091f0e03060a05010b1602030f0106030312200910170a0c02060f160c060b06030f06040c110d0e221509060b030f04020409050106030302011b0c020f010e0303070501 77
    0x180d40340c0e040300405040500d4074081d002449076444504d014014419000c00001f4bc400302d59080341d90f02030240c03452000c03900f40324460f80ce1004560808801208064100030b624621003d00340d0f040140c088005240c401110b00700c00514808101000307081110300341844582404000d0b810405040002128803d17054502140d03404046652040c5080c01e2950510003580c10000c0d840500e43c29091840d6040d000510036a91078003405149880001009800e40004600801c01800b01e0740701c0c98807064111443c081141c203203124602e44511007100f580260580a45071520000504012500380020388e0680f0740c030074001d0791040c6500c072041f008100782002100c000400000200b21041c8000f641c80d04141c2a0308449111400d1860900c034515114080d01d601668580220b0019103031070001c180281494031020b446942045c001000345501504041807030040701d01da6480305075100d1411901250f032002c00a40c801511030030a0720070340c861207000c00b013010010f083d00d28201280c1c0d900307400c45 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 22064952 1250 22063702 22063759
    0x5040902090607050d020f0d0c0803011203110102070c0608010b0310150509131b020712060c140703080403020c120a02040b060f03040f03021e030904050705040906030305090f0d020a030809 83
    0x6a00410038580080808d014180b8403c00354101000d00180355030355491640014003a1035080d949005c650401c2c0b42c031a041c00c141c801082c074000c650b204501d082002140e0290b009440208086100000b80035580e0030840b0300c035600542c540340c181410018498018007041c4c500da8100306c2c052209030038640d1040e8004840c2403101c41d00050a4a550301c03183c02c100c004001d2407040d9001007104000850b100030030380c41181e43c000b20000d10032407400800e9404c0c454904006162110204203041050f800c950460701843c003130340860718546012020000b161200c0c0381b044185800000c0d002005081c9504460348182d40104401e0038000000380301089134104a130140c0b001280821004241a014480715081d00e11605400b00c0007a40c0c28800d50703a078412540c3c000d01490b95200056911803185d0141c8010300541042406016500c0c140142145c1141d41d45901c5801e01070300055461801c00ca40c1c018032540604800049441c50b1a048959000700410640140144541c1c00100c1015000f00300705 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 22066202 1250 22064952 22064957
    0x61f080714030d03020403030c120201110307020102030f090303061c1106030420010201050606041e05090c0c24131b0b0403050f0703230109050f010222050105040902090607050d 78
    0x42080360010146004100050710f01490310400c014000710750b01078a2250700903008110100340b280440000c83c0101b41d02c95840000a102005101c000c5506400540c01043c2000c070b0982240c4451904c00d4803440140c03011944050b081920b0715500032103071000840c15024071040030201c00c445002c00c03201d51044500302d800410030403500883c41c3c0c1d421415400608203100820217403030504041203e62140f40500250700704003000e4201f0040030701f03502002416020f448051142803220f03d8003056000050580750358001d160300d04c0604880c403105240c8020100010f8195600e82c1929a030401030000801c0c1d600881d19803134243c4000c0d0040c0203000800e000d4000694507495400c001d802c00f8410940b0308400e41007440200045280300c0b8800300400303070703501200c9050409002d4983c018140800010303c81c0c0104c10300740d2aa40d4040d030240c12003a00484007001e4100040e24605c0701032101d80200b5020420500040c405040f940e4062301c80c100c1c000d4a42c41c81c100180d2103903482d000949070101b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 22067452 1250 22066202 22066229
    0x50604060f110303010f030f051906050106020708060402090703020306060c03130306110304050703030e010215011d06100801090f0609090b0414070f030b0901060e0c040501170702061f0807 83
    0xc0b075216400d290b20310078200243d815541441c2c02e6206600301d5103c0901400d07040d440240038004180400303442141c8000b20903c40400b04d00c0c0000180c242440f4500241c050a08001030842012850754800c1d58010030440b115030381c61100390002e42010f00104e4002c82c1c14005942440c0d02000201401400340705001111882c5244c080e0a03920103414442580005005000000f070000941e1020399505040448020025000407803034007213410240300403242c00c4d000000391f0013110071000c6000303041b0f2042041e441d910581402a0400d1803051030002480e8040101310702c80e202e07030000d001c2c2c0b1001100800d4940d96000d0210680f0414041600c0c0f502002040c00f00304170f5000820702e45000d920b0b019020162038407051858080d4240700241c8001d09210020351103403020340c021405040c0301c0b115541e40d4280313510a0170050f04140126404642d02c03804200c00c031044601d0a52003000c007503006101c103030f6901d02c070242100700310702500000b80610240810244803e0000c00c02400b40da020b00b05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 22068702 1250 22067452 22067477
    0x40803010f05060405010519021002130f08010203240d060207080a020601170a150207060903020a060b0402040f0b09120d031509050601020d050f0c0706080f151f020705060406 77
    0x52001c91103500c0a441124104020091a44c021058030188840502c2d0811082a203100985c10045642c0d1900e201c1c510004d004c20382888429110702c01ea44074042403200050f16200c00d03034202d11055801890301204150301c0b100f40300c0180365001001002030018900012140c1d504003d03038000900487c1c1c1040c012803090030142d4104844c0e801850091840c501800305103480540b5402800d101421461100f0b11200c01c404a6404807540c0c50f9001b8001c000d5540070b41002503d81503c1c54086444505080c605141d5203468026102980c04850341403035414030b0200c0d0213066511a8804680100c104480f002c500d04062100c6481c043c2c19450100304085100c0b80a40d080b020368014071181480c01c401d200050f44e0000300380000c0134480c2410750b91401c40001090890040420100d091312031405c002c00c02da0341c04142c0f10701641c0d09544030785160b20b801580301e0200c4c0d071510089400c20103c030030348030154000b558078030562016030041e6400b1503141c1001c20181e5010f9000540401c0300c020488 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 22069952 1250 22068702 22068719
    0x305041109010510110705100305010302031608030d020304060f14090d1106070e0d0602032a071106090a0801090c030c060f090b0f0903061311042c07050904080301 72
    0x4034022400c448440c515030408000070060719161840c0b030b0800c0707200c0d600c420850104021031000351100906440d4000e09000000700030701401d000c128001d000f0060490411800d62540000382d4054001550030115a00e6042e4001c0d00300038416103003c1d85441041c3d0190000f441800c0c0300649c20364140d0818034041a8241c60440340c000c0c020304000d000790320109080d0020400341d0708080c2902e800c4480308a4840060003a81060f6006010300344000706001425070041c0341d4407498514400d082c00c418071134461a40d00c0d0700801038080c150001d85007500916140c044028140b52400616224415495415140c01c507884000d003107450f4010802c0a105005000704000003c00e110301e0003135240c50703041034010300c000c070a80702e901005e10700800d4074045500c1c00f80a50710010405411178045d03141000002d01c2585d0140415114428182040a15400d0030b00518000410003a10502040420444520082e04e0604100308600030340201040340d640300c00ca1140118000d1440f29120b50400ea42c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 22071202 1250 22069952 22069973
    0x5040b01050a080307081204080f0c010203010609060903050c01030b13020409060302120109120f0507120c061103010f030206070f020907020307030206060406120303090501140901090b01150905120a12030504 91
    0x103c0f8480d40240603040c00160480d040f1a5010a0200c0740c04c0b950b02c0d1417504803124020404100130809022440801108055020314102e403003603a0340030b003a15070b94641600d1101044c0000b0b04103400000d00344070786500980040d607007000007a020609411070200041c0880e00550000030405841e1003041080d450000c6001c04500c0d10034008100504041d07076000418000011070300e003400b80756410500c0b514007980588007503035000404201c8403d56100c0080c000307021800c04891072840c05500c0101c0712030300015a41a170340c4540300d109501b420741e000c0202a4101070012034107800c065031080016261140c5840c014003440e001152a440e681c5406400d10000806041c003840c17406604000f001040c000e4901c00c2a0103040000703074551035083c00741c003404c2002e42000c500441c003024001c6c41030b01507100702080c5008009003407259032180301024070b0400c6c0940d42000190703100070070300c02c0d1301e40f024003422107000c420308031101484140c3d51340c0300d22080d090381d020220750b81d03c00700414881c0c100b24 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 22072452 1250 22071202 22071209
    0x204060f170609061c020301150312030608070504090c090606050310080a030e1509030a0510060f08060103110613060e0f01020303090a062c010e0106080a080a0c0204020d05040b01050a 81
    0x1031003210b0724000b004038581607401080c0700e101e003d00300d00340700301d0140d42c115180390035801034000c1c1f10705c0e00640c20414007200c1d14803040301c12480d00c0c40c144084610074840c40d0195060400505102c07885e0504010180146100c1510720443e9201d000410030301600c509002041d050b2901501d82c60041001e0030f9444490b80b000d00140c200b03c90702c80000b54401d0b04140080c0c0101c50501000e402d441100c0a00c1c0241d40710180c01d80b1451001400340540050b4510303440c0300c68003050201c980c80307610120103045244a04006540000c005200081500030b06140020010b00b03030314208136824108a980354a030754400c40c08510044100c2c0c1d4030303041c400300406403130500380001c0d45542066103400ba40c6010030403002c2c0c0802e40e602c04000003010414014100c100000780c441d40c520b41c02e101c4e0b01e8001c10000c0419441c540c609003001a20440114182d100079402c0141341d81401300b41e400603181014145800ca81c466400c000b40c2c403d2f40401d10540d8002d81c09030103044482c1d070414042c09903400b490340 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 22073702 1250 22072452 22072487
    0x3090105070809150c1c020a02010912030902010c110301020f03070509130c230408010617010606080402010915030b060705010903030c020303011202040207060209030a050a0303150506030a020c0a060204060f 91
    0x4c040349042c14100f01082d042203940b40c03030f250f8600e5400f04005162043d043c0c6880302034000110400c80c0c50381500b020142502502c60700c0389d04d200281003030f002c4551000000f808200c5141402c8007145162064180400002d40054585655180741c0d0030141d10807034941d404603034041130f00a203e09100700201c1011040070f008220b40341400b04080c0c035034584819402415007a40d41210341d105e0a60080d64000c00740d0600902805844128503140240d140d050181203600e401800145544610542402282c042c0c691103155070a041c0f04802c08240203d240080c1920381080b2503450701c9510083c50802d020304c000003070101c0c20385001400d6441a009000456100380010702c01245042c140040387c96040b0384c010ba80e280503145c841c02070700030f1000c202d03031501034440380c2401d100000c00e48100d540e01ca41d03010818151414410780072200d03a8001c20360084810b0001420201450f8020041c0d222907400300c0e00c5c600d6143e944c0c002640d0042e00540c00203210500c5491100d5003200c1c01030f42465055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 22074952 1250 22073702 22073713
    0x5060a0b07080f0a090e01270203041103073201092607060c020117061302180303040306090b09030304030f081302030d0f1404081b060d0e01021809070c0615050603090105070809 78
    0x21403d043d23544000700e201560550010110301000081140c902c4da80c00003800341e50340e081d030b9a21000344005200494800180a100303a000031400038000c16161024143c582d2913201d400c00a0141e00303400e4800d0032240360b540840202600f104104201c100a05803030303540303030600d813410b100040114a0f001c2c014085a103c00c4148603050784c03003a5144942003034540005858020403404900380c800c440f007204d601800f0005001c000d00c1200c2e01b040284d50b001c1c914841c400d440f11b445041e6a8442110302400003401d0504140e24a44201803294000d1318100c3c0d5481d000d8001e80010b0b0130004020b070aa00450342e40c98a61581c103410840d11000119140460382c10316103040c680303585900700307445840c080260629505505031307903400c1924040c419683c1304102401c5000c40c207500070b41c03140501031640804000c1c88016843c0540c0c115102e4092581c0e200401080c075514140581074808442c07880c04600c2c040860107403101c0003d580305200c1300001203003606080c800541001c07c0581400c140d40c000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 22076202 1250 22074952 22074989
    0x6040b0d1101120f060b090316120b040f0501140708060406050108130501060803040b0a030501050603130605061311070b130203070b0d1b0302090306070305060a0b07080f0a090e01 79
    0x601a40d004050081c00c005501443c5905520700800444010514a1340340c070748041100782240000c2c0502c0e101c00e9040714800b007481e41c1100c014940d148158070b614202c0d0360314200003030481408503804c244524080e00503030040e07507911400d594042c4010301018160004010203158030403941030300403006885c1005400c2c103020000f005218000d041821103903207240d5072410400300f540881c0080c0f4402058070740f102e0321009040051750018a140300000e0400e000410030349007002c200c03400f40034000748007400384039180d40701000783c42c0040446074001d049071f05a00400c10f0074054034005042c0c841d000c50b51180249451070400c0d0001e02100c01084403521130301d0060304d001a03008280c605c42c50403a0b84035800388213100040c1104100490640e400c2e031149902894060b005001000400c4090b42c01c55a14407408404583c800c0702e8140d07100d40340c0c080401030f040c001e900400c0c25030f0042100c80c0c50204000b82c40d5150768413422180e0005079a00718100109011025158050181100c000641104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 22077452 1250 22076202 22076213
    0x415090e2d060607030302090604030c0323011103180f0111040518070c0206160206040303080405011404030f12020d0504052103040803040212160b130605040803070807020a090f0506040b0d 83
    0x4d56800600385035000031250740329507840c410f590003164405185082e054483c40d00c00104070415150020300080215940021041801234810000241c46a2403c56865140042150b07120709000000c43c000c1d0101010b01600a00910132041e54085400d95030314600b40601c00000b4451401c2200c1c1030b40101807103aa151b002d5101900d940d01101c80b580ca40c4820802c00c20360740c440d141d000358041d0001074008105908102240d00c04c0d8080c0c0005c1002c010011a080d8200340e00f200d0040000d80c50880e4407181034003410243c00026101140181088200381d092030880d81c0540301613500703a11030087c0c100805100c001c600c8241c155007812608505045d92500a00e0001030402072240d912215290700a003400c0003d50355004454401d000300390380d110f100c624990b0041e90240b00b02c2c141550b01044d0580218100c504a52002d0010752810200d40c0700d8034000e0f084003078103c1c4e000f200740c0780000b8148840c5c0503116a40803824000949410b00d0802c1100f1150090800b85c000c141107003e4801040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 22078702 1250 22077452 22077457
    0x3220503031206030f0706031505030d080406052e08060c13030b04170d1508030a0207170a0203070807050405060a0e0a0908190309021002010603080415090e2d0606 72
    0xc030700c1c2156180a0f1641000a4109030321601c100250303100706140080e240390325800015140008454500b400c944a4040c0754941c90408030031400b00d0448004034000031850340c44180d00c81070402840006103c001001c520400c01d0100000c101f060045007840010800e1007400d07000084400380c2c501c1c0018070302c1c0d00750445050344406000c2480500c00107051002c0e9001d1440c0700c0c528079001d1079441d240008150700610741140031a01c0f900d440c010104001200000300c0d00109980e03001030003640d00e0010b002000c0c03c040c04211020780035251001d00182c03010850a00036000040282c8401c1d800d020501044400c01040140b060000307041c10485841807007000d580204014101140404250904008038803c031a08010030201d0501029040c5505034400300540d41300711503000301d1011602d0120300b681d1680c00b014018510800040007a41c0d8040b4620041072032a040101c22644d50f03200500c501c06040700d40c540444230340881500004480e04e009040308419419001d59400e00d8408180c490 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 22079952 1250 22078702 22078717
    0xd1808070e043e13020f030a0b100e0402071b170606030102041805040c031502070c1202010f21020f03010608091203070c02210102070308070c02150702060c0f0322050303 75
    0x608800c04a0456101c210303100c039007a20301388020355036181071a907410b246610440394121781d60314042d11807440346040981020b0b001c1e1140d0300d0421000301c2108100003580a4401125003c0c2d552009802d0805c04070850700080c2004410903000000f1001402c0c202400180468400d9104101c01d02c000c1800c80300c031000c1c0c4412a000007a03103503243d24111310400559040900f40d0a20150202080785450b0014001544201a10040a6991b02484c440b00702d19580080c0800c5265041600d19132050700121210407040003032442e410203c00400d0200e0b40302c1c651030b149044c000801804403542002c2010f03044102d4000401140e0440d51144c0d109020103803040c810006110b80c41415903a0340040007038100c05074211961860459620745000b584024000c401040070070340080c809a0180f0040000360b0b40151031702c60006103080c0d000740705071321803a4103d034004828001d440c00584100103107103a000290b402140d4800c010903c40801b036100c0c400c441c4002e09940c1e000d0145807008410389405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 22081202 1250 22079952 22080053
    0xc080606030607020109210e0d150b030303010302060f0913050703050105090702030703170603100e0d1704050703020d0305070506070306180e120c01060e040309050114040303020d1808070e04 84
    0x6401060104696209809081607031007080c030241036050204540000318012b040c160704101c08480b101c141a140c3c0024400a5030044060100d961200400b1008101e5018002c0a01000c6a120342020302117520640380000025903607030041c4410704252030403541001c600d000460810f40f656800400011072899401c030301e5604d600108640761030802c000c01c0380c20398190050050981d045800b03641c61200d05032110000304a800100c1c00508030100441c040c54000340681700c1c15040d5001e000180315542d4040702040701c2004000301181d003c4c000705000380e00380e60300030a0561030104075088022210034001e503014130740b80c40000001000188480400315803141192905410402d003801001990300c80300d00c114141040201b010750222421007a61000d172200ba022a000340ba03541954065800018050382c000ba0b4101201c1d4020300101c102841d030f50000402158458100605106450b4005a44030040390107200801c41004401181d41c0c0488403441c0180503040c2c072145404c05d0700602c1410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 22082452 1250 22081202 22081253
    0x6100b07060e070b070501240501020d0516020603090109050105060306070504030609080c01050106120507050a0c0204050a110a030905010e0f0717030d0203280501050f15070c080606030607020109 86
    0x1102c503400e00c401c100038903210081a880b2030305410400c1c080d01441c262518040c44010032101c18070403d000c0c0030291003042e8010704000401003406d0fa0b05078401001202021140100080107a6500b001544154090300c00419102501e28046094070405020745209802140400103040d9002c0c00303403401c40750803000c08601c020590410700c1b001d12420100d000d565003040004a041600304014140040080c1020001951452030488040c00740801da100014000f69014001d81b50a80150760003050b5040009906000800c1c5004a030744024580310109807624070100602c442803181c0314030012080090140d41007050010b9403542a035004035034a0100c02d003003030a140e42c1d080041c2c0d120001c02076021581c03402c00503031030010303100d605581200d44484201c8107035102240e402014103d8002030406103444601e9130400041d260002c0c4010020141809060302284013980d0420040c0503c0010300b00741d0034010306160810000509078010b41e810400c42800261401006401017041012000c8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 22083702 1250 22082452 22082471
    0x10c020105012106060302040207080307081608040b06010e190609090212011217070b04020a1215180f0b04031701140d0204020417070603050108120306040c090806040803060306100b0706 82
    0xc00810582e01b0280d045440421107004201c400c0740158042c000c0f9894500300d0365101c00d2140c07690410182c02c03400003214440840c0000f100c045015030011014103000c00310051100c08030384403080300300e900103008514040402c41c980c2c0014a520103003400e04015413601c901908480e03c010710601c1a00002c42d000c00d032603000d0140a56490b25000c1c0e07061881c559914145c1012a12000160b030143d12541003002c0001c0c0700c00d410703428512190ba00c001c81c1c4a000400924a10080c0003032020740741896119180e00000510b44904d02118603c00c00c000109410310781401008010702c2c003401610111200c1c010710840d02e40c211581c814003011180d40941e1241d620201e400b81c0195401a85820003412542400d00c00120b4035509071502942c0070041e0741c0e41c030b091a542e5140c0482c1c001c2a46d40042011401500382600046600c450340d040010200395a6003d00345068030484c0d0541d05800040184035543c5014049076411082ca40000d50704e0909101481c6000c1c8a40e0000a26007586ca0b261038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 22084952 1250 22083702 22083713
    0x70501051804060314010e060609090a020f03390604030b01030609060b041107060c1e080a0608030a08040c0608070801050405130b07051c1104050d0c12060b03010c0201050121 77
    0x10f43c003a6a001d400c408410080c400348501030400010640030502800340002d0180c00c0c8040018401c01c82803004165004180d001e000e2034a101112058150007003e00724840391030b4001c0400805084042c01442011140510440036452441c1c4030b40300b22000c020810206d05004611415641c00c4900010080281c0c0b401c20001c18001c030802d81c0040c00d01d100552103c003000f0140003058003800c001c0c08103000c500d4044070b1620354900c0d91101c10301c0d000c2e10801d4040c801e10050307611581c08400088c1c0280c072081001e1840d0880711a460000b0b024104020030001c07058044002800b09052000301402d08601c0900103440501031140100d03942c10010704039600e0344482e040a40d4103e481052681003022004085502c600220004a174069049441d00c1440d442030341160184440407a00b001c1c00d1004112282d4030580c0e082c0c0701c2d00307081c807004a404100c000035005000d106550018a01d00b10a06050039076001d48201025a45410010001201b110800c00040e0300032030305010013580d452500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 22086202 1250 22084952 22084961
    0x308150d060c120605030616050903060907031202010608060c0307020a0209010305061b09090a050c04030b070504030c2313020d0603080301030605010b180105030601030b0d150e070501051804 84
    0x5596010502403400020300103241d010311001e590329564080e04207003a40c4808140e0f0081d01c6501d41551111000a4841e040d41c030b0001ca0040c8580380c003074940501200000d01d042c03c240c441c2d07412508400d00030020802c889107142402c01d0b40f40024840ca5192050041c2c80702c000a02011402400000103400c1500c240310b4541e9035540204500825612428060380d1000c048421130600c00c0d03014100400804200191b546c08880103200c808140e5031082c000015240181c4008401c403010301c40400021031814a50f0b10922080e82c5042d181e6282d4240708103010703910b620840240c0720184840540054400e9401440f442c02da500f19141d0903c40e102034020b20509100492143c40c00502004002c040001541200c0c040c1c00284841d0362a103104061038802e2566151146000d41d124010550145003c4d5a100d0014100000c40e0b0880501040b006041c0382402c407540d0342c200031034141c40d85440c46040307017500300c010040100e1400d000c0003030864850040502c8000f84072405030111350b41c03640c01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 22087452 1250 22086202 22086241
    0x50a0609030c0b07081906030215130812071205090108040f140d030b0a06020609060f10170d020f0f0d0315090912030c020d140d0e01110a14070503070308 68
    0x3e4580c110700d400c0e0b1000300341d4441501d0003485104c6a04d03a410010080340985004d49800408075041e0300e81c44141203500e5030009107650419000c040780000c03010424040400c0c0501154081540c80c1581d141030304207a0f050f400c00030300b03010b400e200ca15003a9a110840359030046d80002100501032603400c08989a10205203803c40d5881030a104d074803001d0303064209005c800f2003510300b5205c440e00c0c1c0368240d03111441181c0812565101c0000241640c6100241541045020a4550340c881e1a0009103d15007001a00111583d1088949828003641041034507200c6030840090850554001d001503142d00d84800c00c403003015107a82c2c59a1040e044500301400400c079614041182c0c266504e040e82c10706034050000c0010a107041c6150b9616400865100268811696041a40200f4554a03942c541000800c2d031403041d9240440f4003841824400d404081c070442031015203841243c10020f1602c5c0e0524424101e00c002841f0281c0054000001e8a6809900d420103026903901c10410101e07005440c2c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 22088702 1250 22087452 22087463
    0xb19061d04050a06030b0f1506030a09020409060c120c02030a05090102070905090f1005010609062105070513050f0904120c051507090501020c010c030311040f0e0a0c0c050a0609030c 80
    0x40c00e20481038484e81c0514101d92058003d103a581d5a4034102c5000c2c030b401192501200292500c1a900d10318020f00290341c03020b0200b2001a4041c000d0300818100c4940c03407011070b03505a890f503403811501d0304414a003c0c261948003041c0400020400c000b502c078000c106940042c84008103142207168000e1018601408118108101e90b140401403242e94204400c4141c1e480d015100c8508407824003070290713506852103910f404036402d2034180f04860060b40d035508006070208841d40091940a540078181c02004195202d030f0f2a0064400a801611016800300c1d110f00e4802280540c81d883e0500400e0f442908145080e43c54108000700f6075126142d610001d10390f000e0a00c0400000040403104c600480c0c1c603680f1482401d8944005a90780c100f10444035001c0740c414240c40c00064030a40200009544600d0500c0c18a6658400340240348840c1d0040352010100c03c0801006002a00c0340100c84c0740c15107400300c06801103403125034451040c441c01502103525140b100c0240f5000d81440f00714940c0c040f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 22089952 1250 22088702 22088711
    0x5090318130902030111030a0e03030f01120602070b0a05060114070203060414160602030a0215071e0207150306090e01020310030f0201030212040b04020f01140a1d06040609090b19061d04 82
    0x6c41800140c0c0102c3d040030005117000035142c03031a030000050302c0c460010000601c3e45a400c00070300254401c0262411603400c4e0302005010000381030525035a0041e0301c1010041000d0406000142689051002e102c0311400d00b80720010150340c0c000b403e182c21640203a01c41070340180c64103407141031414124101098040d80b4000242c401e60010051030b00d00d40300d03400c5d110054011403950704001810f8030810000381c1481c2511030024011002030124a101380110307990140e844119012000da0342d4403103030101c0e40d07605080000491501654900c820040c008614602e043c0211002c00422804042c1006201060400c11a406541111401240f0104100042c81c0c00d15049007001d00490b02240510507050440701194040c2d8007116058841050607410040040000c40d50008106c4580d84c03d407412003913900043d00c41d84000c1024100e00e50703c1590702e40c201a0000e040d210f108403040c0c083ca00f0140048094511140600d040d42c60910b010804a49103107800c110030703c3e030034481070b6005242 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 22091202 1250 22089952 22089971
    0x3070305060a0609020a140d09060e070e09010c0c080c0c040504150b24070219060206041e0c05060a181707050d02030d0e03030c01020c0106050103050903181309020301 74
    0x10380718490440c0c64010701c036071074070740551030260300403e6105404184c0d00d03034110211001040107054040d1101d40c0025005d162610f640c0f00f9948a0080b01c03c0580001206200202200440303c0d807000b2010000d024416560300000e04900c0c1d0814040c001c00070218581d0b400c52410b01003da008900100144924107050505a0074540140b0030740895600e0108181c45600f0518980c003410200203640f007852902803407140e841584801812a801906440041150740e0a03003140409042540d0060601e4540b0345070211580130b030070401c601c03da0098559480003445440c05002a00d500f0b0b2400c90300d55090f02e1090760440c445070201d048020752010046850f0320041c464440c11014107044807241540c4005110a003034003110081d400d50406214091080c0c0241d20090301d07000b0280450b07192003901240d80b8226003002010a950340d4642000700299039160080c25004031081014600d400c1d60b140a00c2280c05403080101c2c00342c0458840000e10a16a81c0161344168000d4028030000c200f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 22092452 1250 22091202 22091213
    0x170702150f090a060f0c060209030f030c03031f03080306100306080a0f05071a1801020a02190602060609011511030f0d02030420060406030e03070f060b0909061501030911030703 78
    0x1c50042d01d070141c3d245043c0040d40c14481c000e038103044600c80d161855000c1d0307981c03a014040d60040240b240c051156507501412110100b0040265182d0907005d15103904000b02d40c00b0001c2020780325803c100b0120300c002c2c00451092422241c2204041301c5c03503400301c0700c1210180d000e030040da400388065024000030041405440344451701d20310311a000b0364942c1303078864400118062104a40c2c1d20600c000348007444100c106c0b09001a14803c050048030028030786580021520380d0052010004003d10302c03000c11005404010301138200b00112020140c07507040103c910b46584850345c45900b04101c0a44d60348491906000b19801041d141c0851641d50700f400c0c103010080d40c41900e044030007140349400301070310b28500025035502c0c003070013482e181c541890144206d029200e171a00c5000385001c1042070360f0000d4003229540c01c036548038440100e808a40036040100011000302102c1c4541c000c2002c0200b1004141211240c403482400d0005210615040c110704000006000c9509845444000720900c00b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 22093702 1250 22092452 22092457
    0xa0b09030a0f031a040207050c0405070507060501050a0501080f0402010e060a0f0905040e03120a0204090f09020907080601020d0f090305030403030801051201111c0e100e0d050403170702150f 84
    0x1079280c6941c45600c034160b504408403401c2050010182e04100c04e294014542a001810206c1c090740c1140c491503000c4c0005400c80700309640c0310021500010f04481000000d02a00340184021207000181c0752800c40060800ca00c000c0c00403d000300040000303011a0700501030500d0701040a4031858031040c803034a01403d0078115080c0702c0301203141c2d000002024a040e000f85c55105200030040c60801c00e507a0f120818003400540900c84082d000e01c40803404640340d105100340810301a40109808003a030042c0030350000302419030000c00054030304002c1264cc0014089107c0d80045c035141030b0010410b80e00b00c0c2d90744100d420003451400001070000a040d071128046041eaa42181c0c1d880f4100c114010050072a100f103207000d110940f0522140b01031207902ea400986154004c000418800744003031186003003103000b5811110503a5a0081c0141e844401c0140090004141c14698070703080c1103450302120030303501520110800000059100441d241e007a00c161864040000881e110040b00701c85540701e4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 22094952 1250 22093702 22093717
    0x30a08091801260c0a0501140c01090c0306060501030c0801180603051212090d08010b0a03090f0b040308060105070c0504090206090307060905010f0302031e070320070c0504060503060a05090a0b0903 87
    0x1d8035155003c4030620f0340400e007040d503c032000301503101d01c07440c100c01500c0803081034020415061003440080318880f820302540d80b185100b075104400c1d60b407c1d0f15044003154240d410090406140440d0070003959001003803213055581d8044003a403501d030070b0944d031000341100340c00003440c82c040c40b910360b849415030102800c00308200044023041595040a01da58812244000c0c000065180740104100041c880c01030400005600d80401d003001580c0b00c28070b44424510044951205000400050540c022006a000750003440e01034501a070130388540e48200024056188619902c8043c0800c55a0320801c56601c3c00c001340a0ba4101c03035461201400050b02e0f4440c0d940030415109030803801c64802c2c422030b80300c0e04600c61030410019600d02072068014000345401e041c1981d403503030b024000308000c1c145624041c440240740e90b11007071890042d442c404154802c900450038140140101d903000310701d02d0b9114441440000b003075500c415001d483e01f00e65001c00783c00304070b0360005d2240910003c00107003c0d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 22096202 1250 22094952 22094999
    0x306030b06041e0b01021504050303090106050303030105011d041d03040f050603040308010905090c030304170709020a1407111c02041a01090506130e01060f090602010902030a08091801 81
    0x559440c807082c40160380303035000c1140c0036041020403420462015070040c100010b043c0704840c2c00b0000c842e100441d014055409943d2603002000b0480c2504d803d0255401500c0d06401441c1035524010000c0c00040c98481200d10b801c4004d80c2d0503009813a00e03809910814006440b071400380c0003a05481b03860341d00c1070003001e0041d0000b8030046010b06284040b24000c56055860351b00c1c0ea03180003250401030202074010720003401504404001c51b54104080c0000d030045400b14407100c000794540c2443c2a200f031f40968101030040c0002911903801200e000303050609102155030717480b083e1500c05642d011111915521001c4e000000404d0703041030395198400b602c00d90f0708001d04840d900341500ca40b0303002d1886600046607e1801d10007070403c400179010100e00540d05410342520b6100844007000300740c11603400998510002c4c0e5a42e40c1c040c031a04024403590008001c4550541c0200782c4071041e90781c01401c0c0d181d00042814280d2148000c0c1000740c8507504013040380d544c5440500007807120324025a0403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 22097452 1250 22096202 22096223
    0xf0b09011401090801050105060f0a02011e0c09080703080f16080a0302030a0515030703060c020109141b010908030a0311121009060b0a020601090b01020307021e0103110306130f1b030603 82
    0xd0360344e4148201410b03208010401307070418403842044070056028025030390441d5215a00740349416040203030000821208000841c3d0003001040080c002c26003603100c030086501012040002c10240c0c1e00325505800284129995190040101c00244604410044c01c4000000c1c603d4015039155014501400c111142402641c56071440040002201d440c3c1c0c96168011480802c0064902d0703101c1d5001c01101e000111707a000f0a0b0702c07450b401003541d955102181d00203080d0340071190341101d50079001d48801d091075010b81d0308025130281d8034042c40c8682810316548102440e21b40c980c030b506680c1e03c82c8110014100500d4210040c5402c0c04242c800d081c1000e041440c0810319a041000351885281a90700500c2c3e243c1c81e049a090142500d201902d0550100b0004200541c82d000000d40590012070110321030790109900040440d03860f060a403041000600a01940d40c0d68031009a01070384c50900301140440c00035048200804040c884c0c01c14044c030b0402140c04041e010381040c02182d014105110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 22098702 1250 22097452 22097459
    0x6070602070302070b0c0d030e1006030b04020f09040803012106020a020312060402160809060f0301030309080610030b04020d031e180e0919060605060a0309110312040501030f0b0901140109 83
    0x885006507040e51095400840030740c1d0070544a580401e400903201341c121000ac4e03082c240710200310780700354109548450341181000190705200c006940b50420560307800410385440e44a1091901041c021441c0e444e41d50180e003600441d001c0c00d01d829180d0890070456031141c01d0000a540c0f40e1040858000701c256100001d0410703d41442034604080c160100007400e144142e99260040d882151041c1d40018140701080380410410702850181d03200c4d4403000d1209003041402d038500300006102c0170011001c1c80084c40080c499200f41504568151181135801010b4a070980d007001c6c05405c80074280d48045484203500e41d1240340d81281002d0100e80003246a1038228080c80104200c6112805a0000d002e1190350740e995520800014081d00780024150748400002d84a0fa1103020341c1d10001c0e450306080c2c0203000e400d440001e0b044070200c3c002d02d0000b59920000d00d49006610416061541c0d90700031004030b812039000a0610000100007030351541c0c54010f0b0140c01121104498001540e560010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 22099952 1250 22098702 22098719
    0x315010f0e0102030d021605030d0b01080f010305100c032417070f060f0c08070503041406031009240803030108070614030604020a0c0b0406050a0509010c1d0a050607060207030207 79
    0x700340001a400307107291954071030241c80654402c0c0c2c020b203039000c6100794080114001b030003e0171404812a6002c1a80114000010030100d805003020660764040001000003c1c0001540800000f414402045200040c10140c0041080e1403052607650203045401c603110100e000f1403401d40c2e0766101d20701840001c0103080c50340c8564a0080b60304c1408814802e000d40c90003109081601e400518010400820716a11600c40c1d41103810100c86e6540049010b0001107200007403900031020039106142185031400144004201a115640000d0780d01c1d61103240300c40d0903000e0b103c1000f40d41c601443c1c0ba1551400b880ba0340707900c240300300c9032213000d149804034006214a20680c0078031a103081050030b50302c41c181040006e6008032014004d11400c0808000010b41051286d4420fa01420700020203285c02e130f8050003904c42c0145501c000da4588042c0c1888203410178400c280a0300d00c1114001140d4412000c9110f5040e1500125400f900c003045001c2007221f55001071110520130b030700307544406603642d600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 22101202 1250 22099952 22099967
    0x905040b0702071715040f0f0302070503010623090c0405030312160804020918010204030b07030516050f0a080901020903010203040503032a030103080a12050c040602060c0901080118060b0315010f 86
    0x5a8a0341c2204000300784170308403580c0e1280c002e400307905a940c010100e9510b52030005440034085006d600081d2040040d0700c0e00703104020081010b004580c28800000001502e07803582c4450107440f41d00290041000ea400c42000c0d02e024010240469680315600d4044403034001d01260f02201400807001803451307640c460100f0030b004a40c00340c00e40c401a11040800503001425000c007040c19075003408004040359140706103d00649142d100000d050402000c3d10750038807409902d20f01440030070007003000543c003240c003242c0040d170013442c0002c500d0700d4812003140a4881d41040d158198000f0051009100d4007200070760240030085d80d051036070749012151501401445608610b445800d200420219100c00d0007881e45409910340215007100500071501202c00c02d03144505106c0000c5824840540c041010035009038034100d0345810000d43c540000e02d45001400707130b80102a8006000f2154175010340200003c2e00e006038106480c0c0c03420604045400951020441c0060100d905030b5804501603140c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 22102452 1250 22101202 22101239
    0x8010e0a1704030b01060518131a01090303050a0315090609020a110613110607060908092103041203050408030307030b040f05041a060d020303030c0a02070501022a01090905040b070207 81
    0x21000861b0f1803c1e500740c2d21034106186205560505012460f221384c0d0700458844821582c090001d180016050750f4100d2111b041c200a041c012003000610111f030b0031805441c0d03d0205440d010811589000815100f040c0503405500c0e07803030800c0400f140c0d03550319801616100f64241e032006d4411506501140c0c2d6013205654440f148612140d964004c256514800721075008050b01d0340303140018907071781d031011a00b00740c1040d10300351404500126940303400c0084004d284101d02c1c14008407584518515103a114a12a181044040a1000302014020030640b0020024441230720744914001c00043e0251a00000423072065250000d0020034100a1107100d0050350020b608044440310020000d0300034a0142c2501d80c0f010249075002c0059800704010f500c560280300c030160722016403003030185c03034408240c01c0306055401c0540102c032400030321a03207016003003003290f000c0030700048a00060782c1c104400d4010f80c954038140b40400052005d1000c4160290030b0a07401c441c0030958619201840b12400342 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 22103702 1250 22102452 22102463
    0xa06022d04150c0309080303100503011802031b01140301090209010210020703050a0309080405062106010e010804030309030311040b0a090b03070c02061309180c12080d020a020708010e0a170403 85
    0x300b004856a224003000c8545500c01d0900c10891510760483c42c2c035503041201e140c0c4a00c030300c0403418000c0341000c0c0582c10340800c0f00e8002245054a5500090300e88441159003101c07480c3c1085c12641507031240c03806140c214044a20184c1d00c0d61243c1e030b004003961081020501502c515640b8030040c0149100b00d40705a5010364400d81068010b4074114042c2c2940030080d50000300510002c03a050361200c0003000704114054119005030201e0010326810b1400a2205042c09444050120f450742c000a205a1041d0f0510b80080d000009144c00d6005150300111401318039004a00816041071071001403001032155181c00800765900c1760340d0f890510044420000040304468140d0050034403034048c010b092184071902030455200d1041000300d40d250304000b808004907500031000d003d4802101c2c0082c03e418040c1e44406602a1108a40d52140d00c60340240698000340c1500506d10070312410380a804075034000e100030780391000c24039a1111500c009480f4807a03104042900c092941086400f00ca5101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 22104952 1250 22103702 22103729
    0x906160c030506041a07090b0a0c120207091113060c0606091104091a030c060d0e010f0213060e0105030601110c030d03050a0b0405130b09030d1b08070513090507020a06022d04 77
    0x10040701e034035001070704027005000c0744030020000100d07101d100c48020303025503005118032840c0403602c2050b03926071283c0c0e9030100700401010394170f01000b040150075141c0d10704200c0f183d58454500b200081c5415403000c3e0389180b41035020659441c50f04010011510f80c1d00003071090306448280c1a1010b40c5404d401d0368981d0015110842d141070240141017561204c407000102511058061401d5941007206400d889074000790802d000d200a0009201404440c5041d80c3c80d6014080040c0c1648000350046040c0404501000c504400c01c001d134400002c009015103100d0398404601601504c1c00350781003541c80f0f007400c000c8003031303400c00348102481681d02281341800111b42d52500b03001010f02504c0c4002501080114031a09200743c0070388410070001a50350780418a00c8a0b00600b001c2c00600860200300d020000c002022004000310300036070320f10010015280d01c400006074500504580010003c500100b817006c061004018012055480302c00007c0e80018542d031221800d101c0c0380103056580529 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 22106202 1250 22104952 22104959
    0x702010e060619030c09020405030f071203030b130e01050703050603010c02030f030a060f08070f0906050603040b0606041e050901120f03080604020706090602090a06050f0906160c030506041a0709 86
    0x980c40121042c07a1800c0b840100fa504c039200c2e885020400e400040f000ca400180c200903c0c00e00b084400854214103010307162840c1041e186a42000c00c8140150416484544620300c1c3c0da1590171811a100040c50f041141ca03c01a40e104e02030181101d140e8042843c04001603064201805001000602c44d4065440c1071907802d8120100d0300041c210f803030410364440300820045803030000503001d410b6031001498060f1410440c003148100c1030300000ea100d070034031004124585600c8183e9800c180c0c08800403446568000119a4a016039805117070f695070110304c404603541210400905031a4180e50700d08480e1b807500d0104801004000d00104080402c426003000b0a00c10142c480d00940004c00241c0762a40e01d440780800d48041ea00103071565070f8000f840502074038019040b00001c0c011030412504007030400c1c45c62a224010100f013070703001e4036001070b400b540c68182c03e40603100c06601c8030b001000c003a140c0c10100d40e15001140c00700c0da0800348040d044051550b000140d40716404d81c0c0e80c0d10348024103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 22107452 1250 22106202 22106209
    0xf070e040804080105042411041701140109060e0c19121401030303060603050702060606220902030103080903120c07150c02030a080a12020f030403030203070c060c170702010e0606 79
    0x200244141e4200d1028400820001800c0c020f4a00403400384404400e0214035044e020f03c2c45d403880300401a50762a001d2410b411082020584d0201c40120818949840f26110140d000d4240d800f01c02e01030301032600012903900616800401550902c041c0e10406a0756084410041d03c01c5905482126203004106000b5600c0755801401c4c0c1440503201003400f400c001090b201c132040a030002c4001c2038407110240261503040c85001c2d031020480c4000c0c0030b1810b15001040c0d003889005903200c4200c5284014101100100c05104000e003030456085580790303545e007003489203038010104d054464020200401b00c0c01d6414001da400740010b07100500400c41ca86003180307000c0490900407000744806045c03a0350243e0350512445580c1c50183c502950b45511141008180c0c4081151002070b0b01d00c140b0032041541081b2060f2948250b140c00e0050b03494079542c6050f0b64414007200f00038050ba04200880000e03641c490040850342050011400c42c0b80c407010002d13400d88921480c0c12401d83c3c0124005004c41c036 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 22108702 1250 22107452 22107479
    0xe0303040f0b091509010912180b1b07030503090301060b0f0919030605090d020c01050406140327100609141303110708010509060106111509030f0d09140f07 69
    0x10303c200131180c40510103130382d80c2408542128041080c0e59202c01d0300d02840003001608510304c0b071074940700b1180c1c043c425075215001654011107003441408150000f080b880340954417001a43c01046921691782c0b4079100d1b680354080318205009509107000010112903c4c01607809001b155032000c0c0c10312a1010602075082c2c1d18580d900c450742d0390b42e040000400c556204060145824a02402360703480c1a040c040c1c03410388104031081c1041010007003080f213030b030740b0403c03680103030a14451860f42ca40301c50301203111100c0a04540341100582041000d110700e80045d03416001011082c0c1072100c295140c030414204c41401240d03900d50703010b80000904030128a520162490300c00e0814010003d000c044542c904440e03500101c0382c42c0e56480901401c42c00402500d4010540e0780782c0750072440480c02c011600d0b404410900c0100c1c1442c0e41c04141964410300a9550710030706100c8164988020464480140c0300441d415100c0d0f1080c0540c3c00c0c83e10320301068030810b48600c0c50003000f00034503003008641e040c1d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 22109952 1250 22108702 22108711
    0x403030905010b040603062003010b09010309320607051305010305061809070602060117030702091b070602040608100b090d030c0501020403030305010302100801030c06200f0f010e0303040f0b 84
    0x6569038002e200c0c00766110310656001d14040d0600140c62008c0c0008031006080d0070024004409003880100300d4405020101c4240450078603020408260900e4501101d04541c082612918040540e0800401c1885807034110034081380101c1362180c0750750b0015641d40c03003400288580289201c2007484554040c0d042140c1011002d0044d4690012411020b04440402d8800480942007a4000c003d001c0d0304004850140407190001030325050300b00045962840f0b5000001c4c0614403020001d0342000e4607041050030401e1340c445180e590080d61500000950290040c48046000040424410000740c0c81c0d0750f05031900110910f18042c8480300b040103e00d03940c00101c5c01c020741195180002a000e00142000b184240c80201347d0354154810455400034a008044c100702440004001144101c0301c580e04941203410201e040904d480c541100d8544c40d4045401d46c3c0c4920b8802c1c4008250020b0500c0360300c40300c24020044503510031110307903da220035100039001040d001008000703d0038422029801 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 22111202 1250 22109952 22109963
    0x1005060d110c010c030c0306050f09061005040e0403200d090b03060409020d1101020c0d0b011809120c1b030c090c050c06070512010b04051c080912070504060806070804030309 77
    0x201040040007900351405581d5400005c1e469211071020141c050144902801c4211040518294844007045a41400400c12403040110070003040ca01401142120040c1501c0154600343d13240c641030207803d000e040701c3d2503102c0c102c00c030b000210941808038601145245541c0c03035005151401c9141d03015a08068003460380603541342082ca00603580c004244080502c01c582c1614006620b00c00a4280903030050000e001d00680003403200058200d1a4480c1500d1201c2d402014245440d51110020004841e0040041e10b8055244c400c55410441c1c3e801603601c101c204070001c1e4182d2008419881862100810300420b0000c240a0344000340c2013084c01a006180c07081c1054440e4150f28070f40340054600364041200050380c0b00003002049009030160407420b4078a0b20306480c2502280041d014a070b016003c041291701120f0401c4440070894100c40d0009000903101100a40581d4440e000c52250702e11070f500c2d00340001414040403414a00c299025210440da569954406a0241c070030301e40c0480b803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 22112452 1250 22111202 22111207
    0x90b030601080711070e0a06080d02070b0307090e04060e07050103110403020405040f0804030c06020c040903090b070f0204020406090e060f011707020a0503030a05010510020a05060c0714030c0102030f1005060d11 93
    0x900010410070008064801c81291b6034101035007200d04031005908128000d8000c0701b1051080c82e0002a60000c607540c022480d5601e42c0ea0200c121001c140c00e4000c03407203a81d0703940203000900503a6082180550010001c0d660042c0d40d5600543c100c0e1400e40caa1422a01c0c244020805442c1560101d94018001d0002e0080f01240d0fa5442405c1c0d4040d4000720f41c03000080d103007403040942c10003160728048800da07003c101c01d484680700546003080390700ca41500410300040d03403000c00c41ca210b0f11050490740600159261030322443c001e00404d65501030b41071104c0072000003401c02e00d055040101f41e50303c10784910100741d2103914081c126081c01081135044d07101341c1440380f0000b0f00820065129040c041c10000c9c00b5410b1400f001803024040c941c020842d485507098078040751010032025000843c20840d6503030b07451140b0700b07d901d1481c090300301d64080c040426810004141074009600c903012112070741e422035540c1c100d0541c0300b00690041541052080c0060a595880c581c00248000326900d4961b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 22113702 1250 22112452 22112477
    0x23030c030307020609211206040902030d030501050f04182d0302060613050f0f0901060902030108160b0a020a060c030207060903020a02011115060d080f0406090312090b0306010807 79
    0x5246070300c2503404500580c42501001300844040c020004181e20105180c2e07420380c50482690020300440031100384074095100403990b00d030744951000c11030650281c25103079603843d18000075000300008d00c9214040d200481503400745142504c142c2e881d240c800004480d0070f0140d502d03011516400c50010500da00340c44420310f007800c9100f46803001c106101e540103083c01d11304031040c8a002840c180b500c03003526007410188081446a01c40269204611000200495441e90011030150046a00c800d02240c070020000c26800404185250600850103410101d00c1e84d44c4000d041c04d226118002005800107035a150003c0c005e82c0010944980c82d18000d800d2070210f07100c03c411a5a100811005070307100400071070865800c030b01290307090f0b4a240007501244081d908a2600010010401880350318542040420041c4090983c0c0c20b402c40da800c025191620341a002c0e00e0040e290005403450903259080200a81c860310600054910b040c0741c1609540b2110015210498041e00c2641800817100c08038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 22114952 1250 22113702 22113727
    0x40605150301150c0f02010809030d0e03030f070903080a030506011205011d060420030a0204031a01140306040305040302010302090a23040b030105010602070303080a020f0703200a2303 81
    0x40030820099001035a40394581803001c209109408058000d1003200b0195a000c0b03850b0303020300c1c41915020f082c0151241d035000740d00da0039071142000251501d440c005001e0107021000014610680d4550401462911030380d4082d43c442200d0301c802403164004020180312a0f21a40189411504c181089580218140c0b540000d41f40240c000440069086040c0000f04070200b400a4200006a0b000c000401d00c0d544801c2417401c4082014078050030010100c1c42034070f0b60741e040324000c60304220318000c03400403040d0300e82c010102031190083e0303556009802c80081c5030100b80036000d9941511843c0c0307803c1c41d40d401034001c0e40201000c00d5100c2c0c124800090511203c40c070801c03c40c10111880303815040d4240070001102d500c10b0700e20340660b240c0001800200d40008841050b26014204962156616081d0b0000381c411003801c0d00000c01c021031018101350f0070144c070043c80404002110f058240d0b00c000c05c1d0340c0d014036035005020300196104400408a0032001c0c1550741a948040d00d1070304402c0301c00c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 22116202 1250 22114952 22114969
    0x6070303020304051b0f0f0d0506090c090f0c180418060203060a08010203060a0306021308010903050406030606110607110a02061206090609010e040305090f0d0507090605010c03050711040605 84
    0x1940440e80000400040100902106203110f0360080c01c264104c0a01010528580c0b071140014090401142140b81aa4804030074240384d50303110040358603900d4101034032070701c45504a04140c040c118050108070746d401c82105040c8a801144803540c2440d100e1809040580000540b085e0002c1e0b9a80705c000d0843c0c0c032000c03580300d000e01481000d6524240b0b4001e20442c000b25038400b13005a481402802042e94a01201004883c4c000c41e016071201d01000081c0e401c0083d03540030b41e00962900f070b401010075420801810460350303a9201000310035512a020348a040c030000c10700116401c04000249064000c800c9030300a10000c0e81120700e95031140e0702060590b40514450881d5042150400c60306140010209034060000e0782c1084440d40b410740e4100d0f40c102c01810081c20f200000c54082216110140c542c2c01a0b8001003078040711101508080351104554010b5549850034080040b0319540103000e8490040d07455543c00349400e04a4072440b10390303a242d004c000d03441521481c00040d40d6641500317 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 22117452 1250 22116202 22116217
    0x2090c0708070222050a06060e0f0f041a0d030201090303142203090b0a03050405070605040f0b090f0904030c030e090c04090915020c030c070f03030c0803130611040501090e0903030c130506 83
    0x1b40043c085041000107000d2800c0341c03801c43c0c800c20348003900303281036203800010f071440341c030241c9011405100d81e00c0c58402682426190030340060307502034108249941500501c0240303002c1c0d00c04001d0110405031055a03070750121a620401c22002c0f4201d0710f0384003000d09034a03816009160045246480d00703008002540055070070030000c0c0d01d901c00d100c1400310501200005009078280715107080d00d801500c940300d90443c480d0413040c00010a28420340c2e220b1281d0b001511324001d140004604c3d143c98084c200701030301c07001580052606628561030341001c00485005520504050b4105480c003042035002d031994440441e0008246030000040c0f0446001a2455004a030007a60715256250780c603500d0014103a0011919a0307a24400b0401b00390454a1a400940c102c4d061654903620b54600004040000c840144600d00d4140041201300d03101c0050010b6071401d0f80d40381e502c1660307100c081c6484007040e110001180c0041011800c4d01e02c01e403000f030104100344c0303030300b1a02555101c0000303580360040107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 22118702 1250 22117452 22117471
    0x1501080703020a05061305101107090507080618011202040204210209070203180609030a050601030309080c030105190903021504050a03080a09051c0215011202090c070807022205 78
    0x35000d01c01c5140000d0600301501040d200141445803008803240048001d00c96103005405400c043c500380d074820707803140300480b960908070307500d0640d41c6c043c020080600712500c1340080d5008011514501c2c0075882c0d641000c2c1114a54000369003000c88141c1400e030040401c980c010360800000800740d10140041d819600140682e26404c15503006201d001c4200810490864208000d068580c03150f0740640b02c05100107588858071740400b680401e140000c2410054180d11a1800010801d50700c0400d4805a501c41c90980300d4041d692810303d402e0320410703035001c82d403401d80441501440110380d200286c6c45020348125014890f800f40028000c22068900750b070340e504030719040000c3c960082682c0380c0001c450001004144505d07100c0c0b9480e40c5203c00b5290240300704109042c1014400c0000c000b06503c0041d001d109569108102403d411910004078025480d8000050f80c4001d6403081e5451590040c0000b450408290b0801c00c00c400d02d0070348a0003100b00088000400b00c039504c00e4610403041c50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 22119952 1250 22118702 22118713
    0xd15080601140102150c03070504091a0a0909030801090b180106030c1b0f0b07021606020a06051b07080a030f0e060402031c050a080a02040801021c0c09050f010809150108 75
    0x440701036070341401101c400d040d07610814074441130080300b403a0b5546c0482d50200c420340f43c1c0ca07105012140391040d81e000030000313030a080c4c1003082800c0d005100c0d002d0080440c0d06250f00e13540c800b0060103454070000d000c1c0c04110510010000a411a0480c00103a0700040c600b810b47c40090001c0308200c4020b03041640000d640c1c6aa03e50340607044031a2240942c56041528950895541c3c0c0c81e00146824000801040601c400b24119900810000102c40050084413a02a49507030340203540d0080c2d0710041e03814a0a08001c2402d00902401c0500b0b03003201400c0580c546685034558008990004640da002c06958440300a0803955610850030821540c00c05446c07241028010949405252600c0500644a00841d4001c650300300b001c9030160900b0b402c201402d962044e5001c0003c5c0a950f01c48401e9500018521005a00f80c1c09800d9280176100010003010700c108078100e415251a0141540111001c0d0115071700b0b41c00395603487c0d0300ca0400d104035646130f90180e03546c0c1d031070320303001c2e0b01100d4158040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 22121202 1250 22119952 22119959
    0x903090d052806050903040b18030c0405131703070c03050c030c0114010311090105100c0204090519050f0303070203040308090d1406070f030e06070c020a030f03020705041a13020d15080601 83
    0xfa002d440e40100c4050000c2d03061a040019001c014481c02c46113480b0b07003180f07440c0b01c41c0c1c540702800b080c00e008038000c00800c000d140018503038081116002089a0020722000f004c42d900c44000709032806201903a40340b00300100e56503804e40755648059060b0100e44414800b50000070801d01070641d01100901c41452254510300d000b00b0400d841001441c82103548800503c49600c03902c03071340d0040c1180c618006050034120700126004103241c82c070207020741c00740d0164103a40d507490840ca210014450402c5030f0b110203518206680701e010548003080140c10800c0200003151140d03000c0d0035032071401404562120019031b98400c61815a070741d100c0c025007000c3c0030094084e811403206070103100d090400f4080313200481f134415103c800003000319042c0207002d4211030035902c0c1d6000b103030040c40d8064500c100002c49030a0203540e070342c550b1007054030682c10550740c9240018003000441c0d04401c042c050401300b2650b128500d0181d0811040c40ca90035540c0c02850001d04450b8124400030301010300585201d504 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 22122308 1106 22121202 22121213
    0x90a020d0f0608010b09090a0f0221031603020d02010c0c060903020109080c010204030b070e060316020c0d1401050105060301080a060504050a12081603050903090d0528 74
    0x140c01d1000c1840c03c0150302610703461004681c002e605503618a0040c1e80c1e5014600e00410741c0c401c140300c81005060140c0c0d1030301840f0030004070001d10b41d095035504d0f25607000010340c1e50b100c4c0c5e642c21140060540500580034592541d02c000d220013030640c04007518140742010010300c1d01c0c1d5943da1a0702071601c00e40c03003c85200c0d4000199907072145048169800b0350000e0000350b800200704008600414040d403c0c10410b03000180c1024203640d0b80d20303106003d5400c804d6018055000702c518266003aa07030161681c441a1003100d14100020b0201c0e44142140d07016000b9500600c0c0800042c0301d1a000040d00c0c1c00d03110303407000020600303a94514000c2d00381800c6601c010701c00f0140498082c841900103041601c91031040d20720a201c4042c0150480c15505c0948290f110b50704200580d1215040440c0c80c540388a001c7c00441d4000c0c0c0c8807000250008041600007011a14120000402c202 = true := by decide +kernel

theorem cover : BRFrame.Cov 21942452 22122308 := by
  have h0 := BRFrame.cov_init 21942452
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21942452 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 21942452 ≤ n) (h2 : n < 22122308) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
