-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2987
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:19:58.27569+00:00
-- url     : https://prove2.me/submissions/c8b5a9ca-d31e-4ce2-b4b5-be1de3e0bc5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 537050359 ≤ n < 537230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 537051609 1250 537050359 537050387
    0x1809120519020c06040e1b0d1401120f170c010501030c030b1e0703110403050a03080604051b0f07110913030f0f021c0201020415090302040501170a08070204110c0f150601 75
    0x3d22581e200c03004047c0e0b000291081c0c600d074008001841405c2201c1d1078024250b050294500d00c103030751381c6e00d141c0c03620310b402c40410041c00310400c0180540060000146451600303010307400c0c0b50070032541903032007401c44000b03810a81d0017452140c0f04000300300351000c03c158442291001100d00340c000c0e42030601c4640c005400f500a043c3c9490485043d03e0005090314000c6801104449804403e401d000e0008a82038504074020350a0030006043c0a0f010b5000d09800c549079100140b902c1c03429184c03641a03030132003101240c80a0360095503500707990323a400246004000208003d42e543ea150310b000b50010b01000b52000512401300236900c0402d40100d42030395207643c030b03142a480d881076050040b8020302c9582c00c0780030010104035420030316079803041030307841564401d0304c003005266200d8850824140042070408003680c09505494000360099020b042100c0c8040d2021850b4040444000565002181c110601768041003640208420404c00c2004050b10380f80d440249081c41400200804605909 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 537052859 1250 537051609 537051629
    0x506091c021903061514010203040315150b0307020c03012a170112050709020403050303011e08030301030f05210306060711120d08070203090a1809120519020c0604 72
    0x104419525521031894484030b00e407004116060701c03450b0100081c15408204004021110320100b030552206034141981d00b0160001c608062443e550000e900000d58210004561542041600d0203189981070018120420402d42c07207240800e8003d181c000403a0a8500c030383e0501c0c44400c541c0f0403109418805840720560001030201c8001c003030316900780d072003c0700c2070310701c41200002680200d005d1007404082c8035206944445030f44020440c164000c50002409540042004002c4901c00400101a821701c8030700107450a691210414103580092f03000781c50382042d400791801000f40c2030150080310440120700408040c80c2d0007074502d0ba400014030050281038000f07441d00502c4543e10311401e2000008002c0004500300c400c000d922171500c0c0481d100458449030100700d17140c0c008420380e8541400034203502c00403450054044c1c0c2019003600c0a01c2e00c650340d1000c05000c580c0c41881d00412801a0316000e03511460104a1142d00e120f00260404540214961162070b6130340c0000c450459070710102c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 537054109 1250 537052859 537052909
    0x6100903020d080f1303050105070e0d0804090903020a050f0c150c150601020c0d050d0f080c07080f12041a0106031a06131d220210080a0b1306050406050609 69
    0x105444c0288142102482000c0c0401d000004224054101034419030072580c030282c1080a200a0200d03604401900811101d8240403c2c00487c0441d4040d8140b140030344100c0c0e04004c01500c840e420440032424008142d00007001420040c28041d5290010701072010140c4d160001c0360140a440c1d000d1070380c10500743d28040010500340d170305c20014002c9000c801454006600740502d0b0450380c1d2040098218080f668038115450011701880c2404d1090070034181e585c1c54000950740319091079002c1200000301840c04d01c80600741c2400d144200b031199104807401aa6120801d5121b4190342050384031104150600080042080300700e0a200c200040540d1496101c0981d8258280076003a0b44e00a030945001c100602c1208035501051a40104d5074458480c2c01d040c05130041620034186010080d402c4804801414070f41449040c440d0b80c46140d10000080690368040081c0340088d0346981e03040d203140c6a2205000c1d5141512900e070003020111000c2c2c1c80c4c1000346000c00d9090081c10007600ca0b17507800340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 537055359 1250 537054109 537054127
    0xf08060f061b06040b0603060402011e200a110306010b0901030b0604080d173612040612050610140307020c03010c030905061f09020a020106080f010506100903020d08 73
    0x800741c0315042c1c0d0650206541003072400400356203900031074040e6002000b42c00814900d040202c1d20314004c9806944180d0b2103107501640010881a00d04464200f1580400b221034030f27961000b80031201a12100a080100614109008075811080109211783c00074001001102c0711101100d0740a4001e00f0003040030340982c1c0001e0b4203030107242d221101c14010300804d101c01550000c031211850300348002c800320503100c2c804048141c0b201c08082c60b458040c034501980c9031034104003940c1d00035040ca10450b0b0a48600b400110a540c200d64030a10110f00d101e501a00c484801d8003c0b039501410650b02a04840c141c40b00c018010ba001014003079041e9400070100d070109200703001130a40020b010f0000c4c0048048810020700404003018192154010100400e2042c000440045014680c1001103000a03003000c0b006402175009070004000e640da02c81c400290301c0801ccc00445800850320f40000381918006081c0401c80e0803c0a0b40010030081e41e00034001030b07807003c1030064900d801001c1d5a07142d911038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 537056609 1250 537055359 537055369
    0xf0702031617070602070b130c03110d06090503030106020106060e0d08071e08030f01080a051f090212010c020c0603010627050402030f07020f0c06180a05060304110109060f08060f 79
    0x30b01c0e110b20b200800620300c01804110303001007407103900c160346401840e074170142c100c01c00041c3c580c001014400081c10400108190309004c0c1d8070402c2c000d04015070200207030740710001c69800d504c0450784c9402c04401001403940a1003948002c3c0030600b00340729151100c40c0010b0319840204c1005011500c04144a414803054003985c60b10b1950845c01100a903800d400c040ca641e40007140c0034505c0440f0000085080380000c104403c0440e44080100080301d41101c072507004040c03048090200641e284894800350381c5180001e60070460f60000040c039403d000c03a0080c204060999101c2c0503440800042007026030240303506c04100e110703202202000300b010040017480041c0b0760265500070300100c14007103c0d01e4145080c901401e40c41e000c07140c4034032500710701640b1100c0b440901076002509200d000b21140702c1500362074841000402800c016a128000103070560420394095031440a4a240d0f030115580007800c0c04042d21081c140132041c0c024075000204281001040c150048400034044c403031944507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 537057859 1250 537056609 537056633
    0x7020f060106090320011b110310051e01050105041e12150b03071d06031c20150408090a09020f09030712020a060f02120406080106080f07020316 64
    0x2488040d24015607440e100207101400501003501c009001c4040950003545d6030036860110201a1071b039490030030303520340c01110032812028182da110320504440f400039501800710300743e203407140d078400142c81c101f07641d5111080101c481c414041001110040c01107070b0300075050741d088404c0100c015443d0035001d8006c0e8003080c060341c045c0c411284048000d4080081300b0441400d0311842d0181002409070f0103080555a80c824403036030307813034004021500304800000d1412031ba1040014040310314143c0000c2c1410001c001041100000500400c0074440d10725410a454855445030002002d6045c0d5403100444480c10181c001005280001050407868484003c1c2d440100101d444c110349428240800c4256580141c0c040ba120740242c000c0881c018000506050fa4150042d040c0891141050010788546500a00c500c0c203511441c01c0c11110900c4130401800074219a5590042e1545084000b40c0094000303042084011052010070584a6000050354180385070307a1110000107289040400541c01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 537059109 1250 537057859 537057883
    0x80703050c070b07151505190302063f0f041a25140708071b03060b090106020f1510080a061407050a05030a090c1d040b0601180e0702 59
    0x400500107205032012015104050051443d00b44170204005a40304440e901080400c0c2641a510180585d05083c2c07181c1000042c91210910314989903000148103410004030f0a1214164519040071032581c2d4000301c0e248800f40d2880040905071005484038080010100c4030850081030019080c00202d07010024840160143e00550f030400c40340035410711604000c0d03580200070742c82011075281d2080301d0050000e03000141403410000d0954030740800380c0c00a102a5207a010340035541800c00c0b0b9034070801006620550300060811407400500561f4801648814250340100540650101c4041107144d9900f04564101d0101c1d43c8507003410140d050a41c21900c024400d01d40700804006455200c801e100300990301040c0281d0f90034900326020312907140840300148082c030100d0000c41131a00841c0b4124803880b084400c40d03489500b01654640041da00c0503000000005100034001a01e21041c5c0082080c60804141e4074505907107103014046d44a030001c24806000010341c0d0034401d02420006132 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 537060359 1250 537059109 537059113
    0x70b0a110d0c0f08090a03050304020d08090604090605040b1005030a0903020304170c03070e01030807082d070309060329040213082103040317072706030b040b0d080703050c 76
    0x2220500e002004501e01c040c0c5500400c00c1300001c034841d10400100d11240741c1d030507520329155583e5a4240081c505902400301d80c00c4030700340304000301560b440c80940060034800b4800503034585841300b0401030341c02d5154924043d108100076a030405c0e61200c00c403640203e40320804030b89001186800c070300c1c40c0300d154000d0714101c8211221442c403074030105500b0703170003030b02142200c005648030351420f410340d5028072004040c84810031080001903a0800a00200d2038a41c0c120241b6180001c218210029045600d07440228005400703030406400c007594001414503890200801c0381c0d0303c00910030240d41e0103901d0004000301351003286d265640e9011101c5000348022200d5409035200394407580d42c000c01d254182c45182a2145504d1504c00c282580e00c00c2d074155490389200b140f4551400f54440f000b5003102d080202c4400d06c100c4207070115002d000c1154000080c100b0103881c01000a0454100c081014422402c0a084200c640c0e9205c03070b140e050303d8001550750390305c00c0c0c00d1505403030f00c0c40f6101e1b44207643c1c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 537061609 1250 537060359 537060371
    0x8130b0a090503280b040303150b041d01030c05131503060203010501020708030a0e0909190c050301060602070b03070e06070510020304020414040c1811031501090b070b0a110d 77
    0x4503500c264035400b180c80c180d0031141c00d0b5030003070490494040c403201040c00c01440308030014086000103025540190081c200000c900d5504042090000e040341c10900345020300080c10000708a080320381508050f9101e00102d1030354150354402040c45144d1007445c4c8211013400000103040d59035880008124003d40038101c0c136584c0ca14001001e508244100c43c054050504000b40060380801202c0c460b4240d80e0700d001060688070100580d010000d04240c046120303415440c41041c0701401070b100f406000c1e4840b4490903150404050030f6500300d40040d0110341240c00d041046030140c0b01501d0300940d050a11a550010040206a407800740c2040038000e0310843d00419070f400030603170086002c4d50003550144000349100c0b070400c0302c84400b42c2d4000c008018030402000314403c07850600b140412051804240031844180101044c1c00075902c0e900400100d1808a401d90b0300859044014951414003a050210640b15451030040040407048040e40307818030000d60540301ca0494008203003d45081007a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 537062859 1250 537061609 537061627
    0xc0513020c0f100b0a0317070303060b0c1c05070503040b0912070611120301080a031d060711031e03120604020f04080a11060f1c090506040f1a1308130b 67
    0xf50342904034006a42501c1c0051507480360601c4000c8005890300710390481e03152082c0701425209a84825000c2e401c0690381c8a000c40c07086040c800a0100782000c00080c41c549070104d80030035425280c0d41801007030210402c01c03039000440c044103613000c45810100b400e4079400d1580205480d00d42d1604021424012500045800c54110703040d04120401c4404607810030701480300c00c201d50700c001e000b00005c40d0f01260350038000038441d40c00d41c42d9241005035130005c01060000898803c2e0009601240c0d00d00c040440c2020f103050801c02e402c401c0401b44143c1140c031209805064031303071041950a40c0410150780010740380d070b00d4a4040781c030382003d558811a500c40e84c40f2139850b1105920074040f18007803004800e92280745404002c0d645c05143c0c03444041c0c40c10f040b0003808081081160080e0080c10b44803030f018404140b0501495100d0750090f060141240001d15081210840156402e24050082e27400e1040051180c000162025407080413544e998241501030b44070381c3c002d603000d84554000090002c3c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 537064109 1250 537062859 537062863
    0x190c2a14060a05090723010c0c0801020a1704020117251d2413050904080a1209110111010f0c0e0a0501080f062713020117040c0513020c0f 61
    0x44208039001c010811900c0e941600c1d52101120703c206ca40c81030400d07120401010307a103001c8031408041414444c1c1415165501d0308080056940442216540400c0500c100303900300c21050103d0040392001c0c0c040e07252540c006085c40a4100441d15410b2804c0d002a604003a400c40682c000890840c0f0700d501603d07513650003070645420440d51514511510b0f040542410700b8200320781003100025034007000f08816010341c0c40940042000c201b10303c0180c500001d041d1034a500f41c0307014030b00641625555440702040070300004c20540d140c08080740f5000a5030701240103510030340d20201c0d01b4603180c030690328400c200d240034000380712280506520b8450500f58440d0003042c403400714502611031404860703480006443d02d01c8200d0b48a4480c20700480013600c0e0340380c00e1a60740c110300c0044898400030130304035071130f10f683e1002110008807031009002140190340c0c212884d00300e80c085200d95000280340a6860f03041d4202944581809108004801c4002406503015039050b37403462011121547c4901903025 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 537065359 1250 537064109 537064111
    0xc08070c030c050607020310020a0e0406090605101e0c061e09020907050a02060c070f05060705090a23010c031e121b1409061908190c2a1406 62
    0x100d8410b0405400541c505049081d60318068005000c0c005c4007140095903c0a0340c000f41c0408108503142d000700740e04e07640c0da2152001402c94090000b510500300428004484441314210040c85a8001030040c02c85810460600350300c070b1407030500554145460030368042e01c0c00030035112401c3c8000342695000102540b0006505001725910181515080c03016107031885008000c50058002c100010825103400380213000080c440d01c9200708094140d1075032030500c00700351502d2000541c0040c00c1c9907640f40c109203a1010702400004501e0400252940008403600e001c04141030007002485001810701520305440400c203006140701220013020001080691503900c0190160325003001d140c108281c60030f1009041002e40c1300e0914540f0802a9080903800050740c16030720210411500e5200f50290642045002c919150300c209410700011021505907100b01c40b1610f103241840200c070265200c2c01d41e01d0070103100ca0442c181c0600c000404a400100c0c0c0201a02c4180c0e211804010040001009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 537066609 1250 537065359 537065363
    0x10080a11190b07060c0503100614090d0c080105071b1e1b05190e04140304030c06120b01020d0207060c05010b0d0302060907060e06030601050c0c10090906090b0603010b0a0c08070c03 80
    0x200681c9002a0060703c46c0d0005031981024000012001e00c00c680c0030314008801f000071140624180100d8400203000c0052f0320300c00712924800803104102c040002d0203459042980360a10401104003080c010001d0401c0d6030340904070151070708440d52000414850484003541042100000061100741040d2104c414480c590003038600b0a041c421a910501c2a0380a8804003030b4413000a8903591100140300840e4400311540e40401c12001000501448c89034009240c19111800c1c40d541381c121041c1100c49010503d815504480c00c0303e614180c0c086503c0c810b071511814040e055600c541081c038018480340c4005604100c49210840a040c0c0024400d0b02c100d80c4001281e841c5c23511094101c44501c1071750f030382541040042c404180c481d0f0250300a0310b04102c1010441d014000c82c0710004402d900c01441240221719603c0c410300002003140152400307440c000c2005e12640d1346032400b048040c4414030130742070f01d5907003c24810200381c0710f6000000c88642000d001034070b6598608103024074042c81c0c401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 537067859 1250 537066609 537066611
    0x41a010f0503190905030f03040308070e0402071203020d20090a050a030302030a0e010c06241d041e1203020301090612050604120908071d10080a11190b0706 69
    0x440d030500c900200c038071a410511010101c8203841c016440901444841105c143c0028401a40074010440107548a07a0180e43c80c0c54580c1400c0c00041c0440144429540c09280100628000315103800004400c03c110351400595400803001da59008000c01894120b005031958580e0804040e8038000d002041021100e220312a0b68413400c001d00208540300c000c015030001c0c050800207d008947c4e4404011040c107000c008189550342c1d213070885d0100350b846042a0b80078034540100162a050380e00103414035404c10309560b1107801c0944001300d4001d00003090301d8000b00c59400fa40b96904800d00042d54000310f2040080785081002d0003a400c00d000e6801c0d85460604001800080003801c2c45d2081d4200c006001d00351107549840401c10300481c00103090000c103240014402c4010400540280001100040c0380000e09042814071580640260700070650745a05005100000c6001180300e07078081482d1801915120115804c6681504000f032000300441001400c513080c24020591240710302c070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 537069109 1250 537067859 537067877
    0x7150e031611061b01050610021b0d0803010e0702120a0c14070b04060503091b010e040b0f09010b0702040615140307030f090c05040e0a0c17190f02030f070e1b0702041a01 75
    0xc08d100981d1084a42400181d200d142c5040d030446804841c020b00c800b0241280032120002d469078034060340f0030f070f1180c542e1001d1101004a810f40c14090440c5520307003907004a2a0080c41d00c4001c08280d0260806031520340c420601c5101003004210846c02012110241ca84550369684040c0070f903001104c841e080303405a20141c01040b0007444170a41c1d0703807030140c4620b0f64040342c41c02880300403c107001c0c085801041c0f4860032041c03a907555200310300820468900d04d64030266407060000b6986c0035402a1443e0100184100c2e24a030000d0b106440c010024414644a550703281088010345002801c0e0802c8500e030080d84014001020b18a0085e21020340f0103105180507020690f60741c83c8810405040c42c02e6000e010300021541102038003c0300300c481c2c111441c48240340710030b9100e8000c2c038100b241d18007501c094503811030805100d00349a0300c1d1480003600310540390205031f45041c01c0c01810700000c5110340c1c4074010407500c00000d03101d01070b4020b0403c000d902c44134886003400e00c81c0d140e07419000c111201 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 537070359 1250 537069109 537069121
    0x40905060430141803010603110f04060b09040e1908032d06100311031f0617060402130b0c010603031806120b031203040807150e031611061b0105 64
    0xc0031409803400b041e40da2603031010f0303210341c00f050360f800086604800c00c43d0444031040a030750034090100914000c001519650014104001c0c000000318841d500445c14a1410004070b041031094980d00441078401142c0d81802d0152f25040030441c2601c28440400000e004040c04102d0700030718850307581003480c11aa1031070103140d155140181c200301000e800c2c3d0100010028102401c1580304100035080c0800c03040300071481a041904110749108a00e04180c0001e0f502d5481101f04600410003401c1541401e501c1100700402e441008004d01d004a400041100404410100c00001001824106070b01c1d101804d2001e80078000d148829030020f507054400303c0c3c240034402d68803000c640c52a121191500c000e030310b158024103160741000e82d0500541c0042c2000008902c02184110f1084101c40d40d00d03101490081070b80441001e000c250f05180c509a40942c0b140007084844401c9048503016003c81d85290840e26404401e210311f800c0100840c40300d0750030314818003c135030f030303c00b810f0083c01290740d04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 537071609 1250 537070359 537070433
    0x5030a2006070b0612030d06121a0108030301062a08120a0b030a0605090111031e0106090308040e04170a110105060d0b0412091203050d1d03180409050604 68
    0x301401402ca00d440c4801315035549018042408682c40403020b0300d040100300e424000803101c00398070507a24840341c6036031402040b08920034040e1040102c41e0484c81541400d00e130307a80e0307400140201d400f4040c2d036999001c0761804030012aa52910201d4015001d0003040c5044407142d00940c01d01c0300e11060079404150100348501442d1a041030240042c843d0040640f6400044c1501400d0245295030701c25a5641c64126040210300c18903c0704401d0050390580800090403c0e0141d22035000c03c26981d00c20310000d0020012a002c803682c0c5040c0c40da554907607013800810540c08100d40d40c580c2c1d00c0043c10340101c0d0380000841341007000d031100801160395080d003031104120f08400021f16142e90130002400242c2041c5552038955001d1506030142c0341c03034001800d026021701710190301162003c2882240341040e07029550b0007255102000124960000f14603a4a01a04404640d1004500b01c03c0c0c1164031141d20072240c160300201100c4c0a81014102424421107504109061744031429a850152141e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 537072859 1250 537071609 537071617
    0x712080711010c0e012d0c0f02030f0706110304080d0c05010b03060a05090d0c02030c040914060703020301030b0a09030f080c160c0602060106020d0f0c1a0a0e0c0a030b1f05030a2006 80
    0x51000c01c20914a03c20107e034402001c00303084420300e1113501c1300c0003d6182000000d0341c1224080051041d5418610302030320b882c4036408800c1c41648200300c24070940d48007003a06207544509040502e2403510307500d019409811548156034252140c0010800342e0384281d04031a0054880000303a441c01ca18800c4200c4201d4001000a07406a1016901e04a1801e055100074101c502030003c040340c1c1c001203000c6a0415070182c6003030000075000300050080c0440700c06401c4c0c010140c90030400c400d804075500075000304040744484c4280502e400c00030391441d0046007102c08041503003107a0180801130b407900c5a54000c05008940061050b8030001c43c2060002524400c108250344403035186092081040320711710700b0b07660100c88405030004a0b03480d18110244403170044214031000709070091011b4100d450b01c10413802c0c140c0316640303c940800125845625850300910303174112882002c49810210350310b01e40b85502035030b014812144803000b40800c0070703201c010480c52090070020002c2c0c4c1e0800c0080310b0003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 537074109 1250 537072859 537072917
    0x10020c0109120212060421090513051503030a0203040f06140313060902060c2103070f050d06030515010e010605040e06060703021c02010e0606060712080711010c0e01 73
    0xa01c145090055488840749212014402091844601039013070415040039025075045500d82d2942c0307059403c9500d001d074082401803603850400318452400000903800032017640041040da55610201d810465800320706a0640c1024084903502c0448290003035a03640f0a200e280a902058003011410030f22524000c0c1050401e0360140f4103548a0350040500121002411503115079aa614200140c40751b0024011940b049800340c080300801c1e04445c1c4c4606d92000840750340f50010001c00c44942c4d0000d00d0001405c0301498040d44807084a0880001040307107420203400f6204220b00b0343c80c84071001e410a8180e4070500c1480300c203070341e0320364040e01e45015034001c8150242d05240012502d0400c2c00180c00954001c0c4120b554001e040c00d50016103080c103002c4030700143d44644044e0290b0408002254001d40300341d038118070300402e84c2ca510340c2501c07880e90301d6003c0003240c50106114070700c1204c911054240c400000c01501d04080000340a150300d080529000c14541141442c28504400b90080050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 537075359 1250 537074109 537074117
    0x2010f0c0804022e0507110901060f03020a0e031608120f090f03150907060e010c020607060b06120c0310150c03050f0c01050c03010305011404050703020f0a0315060510020c01 77
    0x929940d0801c04d500001190254250410110110a03403045404001000900380c84490f691481c0f0304003001802c0504040701d0061880d07500401c445940548140c8821080d4900103848112408084640c103411459540e414070417504610b00b54240c0b01c0258045a0700c9008079840e00c0d0f08070001c4405d0b809200c5150001140074003108001d4200480c1d21609030314024142c492140d1400c007025402c0809664064059110705818841d00360480b08400c12a002400e041801d0130f0136038000703601c900c65078900400841c0c072100c0c040380039100d00d41a50400114107150030054504031040c00b01d141c00849004800c00034403040007c0380c02080c0c0086002440c26039603c1ca04150545041c0c5199000350101400c03c041009904140c1d10280f14080c003c041d401d403042da49514504040b42541c0c003a00a20012810180c18400001c0b40010036234120b9038181c0e80030591039800380000701c8a0956a1020f04611000f42c100407621205a02a00c1610707801c4a480c1c4101d552414102ea49851100391a4080303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 537076609 1250 537075359 537075361
    0xc0e150d0c090915090515091b1902010b010f0906020d03050603070b0403061a010e09190b0d0f0210030516120e01110310050603070801181410030302010f0c08 70
    0x18403600a2841592942800e0b14110303510820710040380e241e00740003600b480303011000380078100701c5015442c0c0081c80c1c0c82e00c1d602c03503680c5540081c0c8040030151182d07080383c240541e201400c211440c00d80740190070303611441008181811000c0d0103050f10702100c90020345552a400707881d500441c0c50710152802907009001c25508000b05600a001c040c1219506100c2c100c80081ca02060720002c0010714030520f40441c0d407001084200740e45181c0c004941d0305005501815002d42d40b01c0001c1e290b84089146c51aa02101400c00d030b2070000c14462241b250021a8440c01d8400c1c0814540f000700c0c100d10079078074a0f5403003985040403411110f055800e0003180c080310442501e807030720902000d48803803c440400a918150300075141d0841d14481d28161080d0000b07c1000140340c00501c0c641e00604c8240c0d01540b4600c1e20035030080c4085014020140001030040b0000d902d250b0315403103032455461440c0c1078200b0703082500c0480b0b01802a0320089005600f000d03e024000845401002c0051070207483e07031681 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 537077859 1250 537076609 537076627
    0x906050105160f11061b0708010216020603070903210e2b0c0801020301030b100909020612040f05011d0d1b02010503040525090c0305070f27090c0e15 66
    0x649074411003900d509190491004c07655540100601442c400c00e414004105c0c4424501e40c00d10b200c540c8a4903882c0d1051112103101000c84001c1c107140b80d030403611695656242481501e8904a507040902007006110014456014035a62072107011056140c0003080c10003002002001002c1c0d16044002200005424000c401140c442440480c460391040c40855210ba82460898000764030950b025900c900a002100b101ea4090001802000c0828881c40d00580c0100d4058400c4200304441882032100182c2030081c503402d4000050f52190080c04070403041d00c1c5041503080c004d07400c21668026007207070307131142405242805a842e0007001c43c1903a49115170010b49076500010801c0d9014066030f45a222007282a20b0b01c0c00395100c4c1c8020070711502d82455840b00840700064524003d251501003400749440c1c20150303403a10318601c1d24010303030310700b0b440c1c0d0641180a44440000b20300c03c9042d400842c03200c0040e0003080c0940300560320900d104080d0b038208502d4031203030171040300c0b100000c01091030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 537079109 1250 537077859 537077873
    0x7140f09040513111020060f0105090f01031112010c0e0901050a1805060105070f0b19020705030313080d090309090513380f06030f0c010e060c0c0d0309090605010516 73
    0x1c4035040d5050086d0703000381603403440b280200f210701004440d8000e10104410003455582240c090901079484c001d0920b040074100345c41c1c4d007040c080138240035080515003895603140c88804c00c1280703010740207100d0903020100203004030302240c004900c90028800045482c0c1800100c40040300d0700c6c00d01c0301035848401e041050041c175001c0d020f01c2c104201000014040740081c512009010312403245a105486e00000540170f20300c10050404405004120850224000205070383d000802c0c0d00100a1462003403038031166070b00ca407050780c92145081c5103202c020b05400c00b40500890745481010b2100d540c1b5900c20000d248480c0c00b00508003103208800b413030142501c06c4400e14019484c03280070080c9148240d004030040c0c040f1504001040c4540400c0804d04081c080c00c201c11407904000c150300d404000002e48030450070040107001d0300000c41c3d42400c1000c100803280c450b500281107040e101c281414002c281d0b0f079880c000c1c01525410401d002505502c5401101d8041d01c80307824541114200f036640d50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 537080359 1250 537079109 537079129
    0x3111602191a0a0f030b0f040507090e0a140109110316030b21160e010b0a020304031a010302030f0a02060a11010e10241d07140f0904051311 62
    0x2107000980040816808002c1d500081da9010354840140c44401e441001801103d1398040741c420981490540348442e04e8034001c3c0d6403a00d104440100b60380c0c0d601c00044441c02e007640d0001c4200c3c40d100047c00350200c6668040040000c1b8180d842030b05a032112225010b0316124448500460b50400c00038032540381141100d14407042c5841e01003240010240000c0007890003a01c0388900c2e0f480481d0700d102c091010030561038a01e04d0b48800c03d042034a070075040b806002d014402d81c080c20343e0004219907050700c01e1040300c0255602c150200c03480e84c64114800003010b000d0204034000d02c25400700c03c6040100094407000164001c02e201d14080e4001c1c0100d948403194100751849649404110304051010305c81c521542c080c804d800155031640540b0001d008103003082d54403000007012810b008607403403800c2c4260000d01c00c1c0c0c1884003a440740b03101103c22818880080601c10008101c41145400d118010000b08c2030890b414842d40e1a40c8003d02d00e80c2111900051101050307000d280110b0400308504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 537081609 1250 537080359 537080389
    0x5060d0507110d0201020d0c0e0d020103110c0703120f3e03180a0f0e0103080304021f050a020d050a02060a1104090914060901020901020a03030902150d020a03111602 73
    0x404004282209143c2c0780c14445418080540d4010440d0f1954000d1446030b81060740691400e00380c1c0364150004207884016071035001c0c0c105529204180c91101e030600407240e0b81503031b08088030815603682c1010795280c80c100109800048045406001b01d600c00c1c40008281c2961400c05180030303a03800c41140c0c40c0181c1060005001c3d40c01e80841e04400003c2c0064540e0100c444607140851182c80204a01211103030446040364040314424801c940300161150f040d42d601012290362515a400024100c0100880942c1001c2c1d05441c0fa00010b40d12401420440c0680e80031200313810702121090303031240280900c1c0e1005074003d0b00011442500c80e0880b02074a0b0089242d68501504d035440c1609440f5810b10984401c03080010100031b90008101056008000744000c604107441031000175155000c4000240401d9254402d8500355034903012556041c0505002c0599100325092000001c3c0d04801c4a10780031a1400c030030000d41119003402c440c040c01902c09031030b00342c0344c207542041851240d006003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 537082859 1250 537081609 537081617
    0x20c0f01111602190b18031b040b15030c0408010e071a1308010c0309050c04060b070308150306010306050a0506030f06010911130b04030c0605090109030213140709080705030705060d0507 82
    0x116404800d80326000031300014280680d50b2980c91008181b42684400c680b8080d607c00810f034890341d6200c20511840c5031084802107403a0903103000281070102030b100a8008950004144410b0210600c0104119a807050003840341c0b03801c2c2e560b0746844a6451042100f602c420585118489500000500b081110703200c501c2c19050322840d1030b5003194400000280420341c4e568499003031090401c2041858641114140030007403c181450501d40548a03008086c02601d074042040d400e03205c1c44140803920083c0451f06a980d60303041074000780c6010744210140da4035203008146d50341800f140a400c00c140c40002892540d2828000800610208050210f4810140300064003803010742e68004c0202040d2119944603815800c00401d003500c6031303201200b84203041100d68401d07604041d01c5406c682d0100c07030054286840840a002601644842c0d01c082d240141c01c01420700d401007005001c0c2d404203402c507114143c0354000d040d038400c040d008144e0300070028006e006940609410441c1c0c01181490 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 537084109 1250 537082859 537082879
    0xf09150f0706050720010b0111030c0d050702030f01050a05041502190e0303070b3606040303090602040e07030905070501020304181a06030103050a0b06150a0f030b060409020c0f01111602 82
    0x181003110440005c0754200f076511440c3c0707640d1a60b40800380138080e01040e40918680a0704142155032485c5400c0e0020503c44040f8001c0d095540030f114880c80f02121500910980c600000b1241c001c0c602154201c0310024686100819540f442c401e0b10024040d401040005a80f80d09050310107000b075041d00c07580752008102c900c6c0020744803400c0342c0c019001c0e9884805c011129143c00714440c090168003024540c010603130212080700005050350096003600307001994101d2403d002001e8890b503080100c0000b249428000b4055043c1d2000041c84d0180050f541c840e9101c0c03004a880384100d100e19240c00f41d50030b0481c8a000015804100841307101d071440c5000d43d6000c2c000c10322a0f0000d9200342d9198202c4003007001408004100c481e4000c20446100e60181002440c140c068000d4001d507404012800e00080c50990017075100804c9444002c115079151a030300c110f818044c1d030019100c421640120320b0550003070541400386114080b0031108043c20498400d44a4080d40810320007683d002c80148 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 537085359 1250 537084109 537084137
    0x110d0207030503040b090a05060c090a0f060206060a0902030601170a0e0a0305130e0c030c0307170a020d0b030601050603010522092d05061f03080f09150f07060507 72
    0x21009000d5a4841e031a000d441c0d20300f0f820a210803c07001008400140c010460301c400080300170501a03400142e00e54203585030481c3c0700219407d04003d801c8013480308021a804101c4d160009480362080c0421210008007030345503030032141031340010f940e1729000c078600300214005201c1d03196070a648802d05801c00610904020025450907000840c241c021840000e442c94650385012141030241210340031101060030010341110141c0310007804109a80d01c0840410810351007601d10f05000400c0c001c81400900302000c200380254010341c2002c003894540345824046040c0412400e040352001480325003140e107000103110400c2c01c1140d47c00d0320001004001e0120040511507038140b20f0080462224458901003015131004900101c58501000c0600103800030b4000031b01c85a20000900400440d84400704a102d40840360f50801040e50310081403100502540300060081ea0704129002c5050751054682c07510544a1002d04010500040080f4404202179402454001601f4030305860091214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 537086609 1250 537085359 537085361
    0x40209040906020405120f190201123201050a09020c0a0813051e090402240403050f011401031104050c16050a032303013003080a0501060504140103110d 67
    0x181c0c070119034842d40481d041c0400d05165680c00c000381904401021a03003c59805580d07282c2c1ca6000340b03030990220902800c216440780c1d41e1000e401389200400e01c02c1000c2e40050003c20903035800c55550515104150000c04403852200c40d0480e20080c000642d0035041c072a00303002079400040b006045100e00d0403d240010076540041c510b2074a120300707122481c3e05010802c4404084100110b07030704903041c90015010386d50303400c007a07030050360446058801d500407011500045200d0310500206a201140000900030082000b41001c81c100000700603041c10100c98040015080c00090642d40350a0300b07441031418035030720558018080300708060030541128850b00300c0001000b003c58183d0040303040c2000301a008400c0410f40c1130780b1035401442d007070302c000c96078a00c4c00144500340382860300c00407041000c8500450b9101118182c2c0608503a0205402d024000c003e050343d02c0d84002d4600000059618030410070364040d62010b03003403103543c0c0b94110011800340030b1680c50607189120401c5191584615 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 537087859 1250 537086609 537086621
    0x90c040c0e21032104021801050117040618050604021c080f0d0f0c02030d050606032a0909091b0f0d0605090c030d020730080318030414030f0a051b04020904 69
    0x40350004003a04d140600c1842100b091507821f660042a100005022684e0051070700c1c2d245136507000d100600d5542d81c0c20501c0250014a03520302c1c0000c0a11025001d000b004101580301c0e074002e80c0c8042c2c015000b222a911110003441001d81801004e021140a8500c04c0000b4203580c0d13604040820f010354804e580710221440d10211401513400025102d4049410b402050340c4040100d4200e42189803640c445c02ea118142d4104489040360a00d86072a500c2408082e141c207224003504240b05450880c490380da44813200d05032403020440d9000180c2040c036005100c4009000c024180001c1014140c1c0d03030501400001c2c21141050107003115010681d00d0400c40f0324082c02c6035500400c002c6140c101600071140d203c5040a403e8080850032038055078049400780c0b12a6071100d0302c80d039281d0710890702200d54003c00300400d0490100141c0000c425817401d60501130007000701c042e1040700c1652000e6642da003a00200080490708140904c3d8031003845022603040d0b20790b018002515001c03c2c0340001d800c45003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 537089109 1250 537087859 537087907
    0x12001060f060e0118081c121a130501031e1a390417031c0506040f0207020315060f0603010306020309190c050d060b0306090c040c0e2103 61
    0x200141d4001d9031580c0c4a0705c40d52824000c00c0c0e00382c265a003412a000c1d00c9510507082d078a04004404020707040c040c1300d650242c800e028100410009204c90081828526a0300c0440134441c10800f6030818a1804d184907160480b41d2054501414030840789041c8a0719035081c2080d203641140c10b0b07002c50007156844080e0b100ba40104c03800b41c01901010401440031900598401024184842d004410b40001c01204c0982d0ba00580d0441010400c0d800e103855889910281c1810004460a484404076280c2041d8000d1030100e03001e02038a400c45648008078002c50f04065416071040b100031002e11040f0b500c0540195001e008203a000002d0750104100360310131703401100d450303a0000c1082440c41080c0843c20120903140010f88000d80d0076111041400c5035402040d20444496110303d0400119174003801c41c001025064940e113103088441d41d40c60720301e2108254000c50130030312003100d406e129220803a1116001041640f207600b9070710303a0103e54481c100006415210400121410785011103030480c03054 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 537090359 1250 537089109 537089117
    0x30c0218040302060603010e010b06070212032701030c2f0102040803070b090f030313031209020d03030b0a0e060604170a08130303180f05060c1507170603070302012001060f06 77
    0x420841705150850301d80d041d451400364500589000241d4a48040707070511a01201c2d0f290141d00300d80009821407084960309a000058800324600100030400381302d503a048241c804011507040494140d0700190051109200f0700010b10700e1403124850841a210801d900400042c10140c035041e00d130303103507610400c000d541e00e00c482e104006100344204603000c0003044a40c003031825410001c0c8804071100900034010140524220521136036901d80c1c1c009500319070020030564007003120741009001070954881c0340d8050000c00c0e401050b0720001895480c09070710040c1c805413030f05142501007030b03450070f16800160140c0694840180403c44400240c0301d807011a00701c0d082401d19611300038001c844204010800010311100400a8a002c88510400c54034151502d69a84041806090500703924800742d003608210001400003035903004441984c40c079a00013034498541c490f02c1c02c01d07581d01780e14800240061b5100c0e0140101c0103811030720b0031109021500202d542c40e02c501c040176031102d0541285c4005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 537091609 1250 537090359 537090361
    0x306020315031c140705160b04030b060405041e050109171306110304050114090a06050d0606020304141c060f0504030807030504020907140f030c040f0b0f07030c021804030206 77
    0x40c5002c1c0a0f100b4005140c00000d069211a40c00c040c061890104208400004c04640242401030078408041001220303158141200d40701c0c017a0604c1038206000c20303504500580002482c41c1840c3c481c60380a41d81144441911948807420994444407101c412245552143d94000019a052a110044d07104142455464039404600d20560f400c041c4c5c84042044110700d001c1000e04c20110848003514002c3c44d0540000017006540041c83c41100c070500d801124114001036516408806409a030100359030502900e6510303981282c2c0e0740614011000103007000010040540b0b0070610a0105114030520412018010b45a01d021900c900c041c2d400c40689890400003090340c03080310503901020900b002c00c01401c02d500880d15490300101110300303200c3e068140d000c03c13040074026500e40d0900308103283d07505c1c0b0b0190021003294000b4420170b051640340e40408200c2c096030900340c2c0d41290040300c0180c103007451a1400c96031005c00c0041a40c00810422882c0328000c075908030207200e540079400070901 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 537092859 1250 537091609 537091651
    0x60e0709050a0b1504061d0628020f0a03050315010306150203041805040b0420030106141f12050601200309090a0218010c1b030516150909090c03060203 67
    0x140e512075214150814020403003448115003200e070020300d00e4211f241e0b20280584403c085060b9118140b520042400c030403e82c00000c240442c04054040074584c00e40300c0012012403c55510100781390010080f034003d000240000c41031450142c80d501d01490041401c03503a0380f05043c034091a400c0c180f8016000040c2c10711000c1c5500070402410076100c2410002c031325258440c1c034160240030b000101101d0b91202a01ea18002d0706098542080004008000a90341c1d1a449003900800700900f5024040480d040c000e805805504030084a09030f480e403c240b403181c0400e04004020040c034032418011105010f4a0787e1800a0014204840390001180d460071207004001d445000103020610303903401000840300b200d03565031100300d110f41d00382016125000b440ca004402c0e44269044800701c624802d0001091003130001d200740c0751010421407044c1e03c80d02d0300620200c40381c8490050380400e09481e02000f40c0d80403540107054003402240042d4000d9220358692090340c0c800d903146d5081020004114179 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 537094109 1250 537092859 537092869
    0xf050d0305030919050745091b09050f091509100911040e0d0e040b12030703020c01170709050f06131e090b150714030c01021321060e0709050a0b 64
    0x20101c01600b0820f008804404011841200f241c0087c03032243c20700032641007407442160004009103074011140c03410b01c81110500303140b4403401e2140103001810500440d02e004046004c10780031f4400b41000c0d2004008440b42038003910006800f40c40030344200001d0203c9950a80310300400c8503c900b0100e842c9402200c10001500c4031050f142d0032a4010702c401081164005402c00c0301c901e000d660124905000600040402c011000e2640131804005481c000305903000c11a00200c400903280c1b620300285400b02500084811180708020540c450002e100030f01d041d00c08414041c0004280790719000b42001c800140e8481e943c040e1000f2000d00c10710b13081e14441c100f4501c3c081c00c40c0c0601003100c11030301000112902101100083c10740c000266540c1440442e12024003c240c02c181165a00d86404916078000d503c00148102c400104500100f06810032465903000080000040094030785d40c1c0c0c1fa0b620081c200c1c0342038000b151084e90b9001808100314081c1e41c5c411900c0c01c800040c00701480003480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 537095359 1250 537094109 537094139
    0xb01080705090a03062d020403031403010b0301090908071e020a09020c190611030903030a0506041803031a040e0304080607030510140609060f070c0f050d03050309190507 75
    0x1800428001c07400d1907210003182104132900030102142c0b8a0401d01822040c0200c0020000208640e0140d0070500c00c042d0010401c5034443d03511601c1815501807144c0c52030200b801000c2404508000400c504500d581000d40801d01501c011440d0034400d580d40d5600740481001902e0b0340d10000c00302c409529245600000414082c9800e616051122018649812450000403606808000100180a40ca91100d401c2e5128401c0003640c03411700300c15040d500c3d0021100203020a05060000300f0a017040d01400d2503501c81c08000da00c1300407550783d064000d0a108075810980e405004483c1c8000d51b02e60168001000b45a000b842d6210708120455040c040020460303010726061209100c011881c81081d4401c50300d0100d10300f03082c0d049000005100d48500c03041c25034864030201d03100d60f292175032000500d0f029100c0c0c1e00c5842400d82d01c46921032038803c540308803075000b4a00c2c1e550303002180c0120000c59000341102c065a1003001c080445d00400708006505036215406000b050000700136002e994 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 537096609 1250 537095359 537095371
    0xd0e011406120a03140408070b041a07030c0305030a0b130c1e08010b031e0a05061212180a030b01171005040c23030a050d0f0527030a05030a030b0108 66
    0x100c68030b041e10580840c1d80b5140400001c040045d65614103074014140c00941d80545214801d03184403030f965900c010584d40040c040c0d030305030f0b02d100c62401c03100d4002841115401c0d41d140e10ae0740001c08007038074180c906e5000109011403003501c03003100030883d696000c1c07000841003001c80d00058100750791030014080b149103100c0d03072002464420107a80f0301d41c01040399411922042e075084d64981c0c2d180561100340030100f4405203070200d0782052205580003500064403e08040c1d071600d152865030260907503a140380600e04030a910b03040088001031809071011004003000a880e000c03085540340e030303400602c40b026130060306009842c1c0ca1141d4215003d204c014044200064144074a003416111500c1400091094491003211581c1120050400c240c4020304200d000f03050b01c4442e80342e41803003074481910003081400600e180360782100e828011816110f484a204148100c40e1070f4604c040c4c500500c200100f40da00d4455110302400089040004110b1064540e8021401810f05030000d01090b2001d058 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 537097859 1250 537096609 537096619
    0xf120903031a120303010e04031107091b05030708150f0d0b151206130311011e0e07080a02040b060c032d0304050a03030903030b0d060204030506090a0816080d0e011406 74
    0xb160f20f1401001041d681580c089080800c07813a21140b03410341e04600004400d9070103000d090b10014002400c0d5014009001840c0241a225038542004450a10080f0b40d02c9000c2844000400c46000401182c107409407070280c50070410000410005203410807140045a2103c00caa04101610b4401540f1400d0b1500545099105140d0140110f884001c000d02e045511500000c0034002c0c1803080c0304410451140f10002c01c0b04c0c12804608111102215a19001e01401c03c2d07011582e1a0340003810008136100b4002401410201d5420000a031006028051340700d00103001058080b03c003070004040390020900041981020000381c00e0910404c0580355020b0741040c400c00010404c081132031040e065040c41c00280303d080a1500380c0041400301100c9130042c1e000a1036104010140e4001e000f40d03801401103a28580e01d40321010354811a8a100610402c014882c000d540c50f2120300d00000c10307125a142d82c1c104164143c002d41110860b0480c10704903919007403005042034220f900c041d0064801e8903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 537099109 1250 537097859 537097879
    0x30b03070e101a03070305060109050f0d08040e0f01081504020f04150b0406050c0708061303051b060c040905090706050f0a03060b0307032004150f120903031a 70
    0x40000d85400d040d20510004029101c0081c404109005400025003056001501c200c51407904101c100c1d0001c03a103110120b8603000100d651507025403614000c4403401040059145003007020701c174502821090494808000f8400890310807484810644211039014400c1041d40c9000741c4c4620f003880c1c0281d11010613510b0001e01c005070711800c41d030380014503040d94081900560081d404040e4822503114818000d40481c0204045a0000040c0402d807054070803201c90648030752510351104019070710511001d14075143c40b80001e009a016082c072034030341d080d03030f0300c00003010f04180b420b00b001200c00303041140000034184501d007828450306030400b07140c3c40100030f105c1c01c0c418064000d01c00c081c5184c0000e4004142080080c1c03190b04881d01a2529003402900c80c00d280c800078010b41064500d800020918050300002c4510311015030b812030300000400e03103e1040f082000e85803402c50020010412804511b0620008a40e004402c001c0d8402d5038002a40a516140001c036180c40910301c51003511501307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 537100359 1250 537099109 537099131
    0x3030a0216121203090f050a050321010f0603050603030c0609100c050a09051c020406090203041e11060a2007060905030c010212030c13031b050904020105071103120c1c03 75
    0x1003d0500400900b0006605005804d08080046820034014803510454501004000c40070000e1720344030385812a03601010724010050b83c540b9009004414644038100b6040013000e200382c1090b03801440c0079094a00e0118001c0c0c4103414040100c49440d0244e005002070440301c1c6561041c41c400c41e8082c900a41070010034103004000c1e9180c0d10807503104101c4548204050007480110725581c9600074010440a66a0803890020307401c2154160360345514010154074400084000d040c4041e03002110191005800f010002a5001072641c10100450141103c1102c146040d0030103408094000621565140520042c0480c007076820080c06904901001d955598002070618003c000e600c20164070781c0d5074100300d078542d4003400c524020007101c041000410f2045018820b405158110f0f850007100303884c0c6c2300b4012041001d83d03000740000d00804c44040070902c400304580c462034000b001d461403041c001c400c00342203800815054000d0380011401e001030340945007a242c0b00098a081c01c0c042d010b500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 537101609 1250 537100359 537100373
    0x2100c021b03100c08060a050a0b070305030406060306061410030605010219140a0c08070902090904141011041e0501021c020f0304030f1b0f050d060b03030a021612 72
    0x400c071009000099618415501030100308001240240f0800a112041000805404003550100c0c09500c2480000c54242400c98822050750328070030309145808007564044039950b0000b8000c0d600195a80400700c00900a8050a4024081207401002a400000170403000c00520043d100900d4036040d02000381e82d8001c034641d818010f02e80c0d6064034140035400c000c3c2d66000030801c40600c9014aa88020410002050000554503410102c81459844420240480c414488a954080400e1002a0006150035019107562032101f0540f101811800901819105c0c0c0045188004401003000e104c1400d42d10703095a0305c100c14840c205860f43c500030010f5220121800d580d42211021410418154020000040148010802c60b030391143c1d2400d140001040d071103070894209640454510030600031101d60001c0e282512800306c50903103424100000c61020140403900a5200c034410039041d074013031000c2c5c0409507642c0c010b05243c807007d200303824000c0d07829001810f034102500c1101c00400c4a03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 537102859 1250 537101609 537101623
    0x60a0504021e150a0e090108030a0909050f1602010f050114030f0304031106130308130f080a0201090e0a0f1d0d050c0303041e02040906060618080307151104080105040302100c02 78
    0x4201c500a59401d00b01d4130458520005c00c03110b5402208003000001c1102c070010007400c041d0002d41e2030100701900c4101c954250f030801e6402c50b2180301e6010204810402d00039000284411900002914040000d0b442c01a9a02640300b401d05140c0e90b29940700900b800c0c00b841e00e1511155000d9460b0509584d02c6905100b0244403840c0580b20100c0c080c0722015251007241e0256070869001c13501d07401c0c5010180c4414409000324036020500910025800310002141d55580d94141c40d41603084d4242441450b940d1801011806541c1d2994210710408520303204a92016230024100d1003400c41709200036103010b6402c03001e00c0c1044010068490345540100c2582d4001740e02031503882e04030b010f60141d2240c40e079001070041d60140c0f41a84000801001c0c2c0d209004036402900e4000014a203450740214048552041781d2054104015602c001042c0914030f01071803400500c00034180503240e00d40110781d007054000c555141e640b032007408203054040159000c00202c0c200c0510042015820094803a41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 537104109 1250 537102859 537102889
    0x160504061d03031e07050c0d020112090c210209100b070f030512070e100f0903030302091908070807050604050f0418080a03151a09090a0e060a0504021e 67
    0x10740421030304181d41e0248101d403400c0401c1c1c1c000540404d00001c9a2001d640106011103107441104a1180e5034208110b15450701034050719800e4103003820f802c0440245c49500300c2181c640449401c00300b40841038048841c805484100c400313800d00b8952040c40010040a0300c104440c8206103c10000b40c9403907030031201d00d107a1006a0302e140b40e03418a0b040c1c5290145c0001480340045120802c4071899114103045902c0d0000c64004081e003000c50029a0074200d2100000e00091410800380007090003600100740b84040a40f081040e0709084900c015440e03100d82140a29800c1244100b2080c40704000e044060b000448807285454a040d0010720042000d82c05039000c0d90705e032103444c03080141c6a50949000c68010042c9692111b01c800d00600402400e4020b01b40c504c881a03001c0342c20500304861450405401c00d0540c5800c0b48103042040b0250001e2203c84103c2c2c5800340751000f114140032140c044c0c2c0341081c000c05c03681010300c1002038005006505e80c0081b13200c3d41442c0101c0d80c402a020340910 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 537105359 1250 537104109 537104147
    0x5090c0a0822030f0c17030412030905032a2d07080d0806061e04090c0e090a0b03070f0e070e0415150311120106032403030806040f050f16050406 64
    0x916200400d940c401000705d0054000c1d4044451041e002950070f000718070582c07190108448185426100f03508403144040040c00341d9106010034090f241155a1201a07201c0e0703003885000c3c16140c0707108a840c10704450311081d01c40d600b290822106035200c1da681e05403061624082e240c554141100b5643c0c4002e807146002c1001409000700e062501c9a0040f12805c007051941941d80105019810307500d5442442103860081c40d000e1500c1a0b68815001155250b00003444d040440c2c99080b01c3c1c0340600203a25409070326004091000805590108182c802010080c40040341d9280c5544043c00500e45c4402c0c071806582003180c06a04004c2c1c090703000c02561209807040c0d0b00030142c0207086008080300a03682c40702500009500244e006540c0c4242d048641995061184142c2e503403040446000b400c0c07a00c1221010710a09000007401400890780c0100701070030004006900c100e01e0700c1500e0083e641c0058180c4404180824a14034600e085c00076001c0d41041031034240b401e54003c0c000f088201e2040542 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 537106609 1250 537105359 537105377
    0x316021c170a0e062106041505060a050906030406050a052d18010e011b0306030b0a0b010302070b24010f02030901030207060b04090803070e0a05130902030705090c0a082203 76
    0x105000300c3c00c411400d071018080c50f884e05129124005441000440b00c401c86000c04001162031910380200301c1001c01401c4040d5180349894203022103904801402018001709008030700054a0b007501861149000e4240800e0500340740716081c044030000b40c80c0b82d651a40b011440342102c080000360050750302500c40600420b56950103001e400842000c07144140c0d500700032554421400540005041d200384603822800880406000c2c3c1c1120350034031000700710404038000282c84141507840758614038410304000d46403a00a81d81c52040d031404032032280360a180407020701c80b0f0150885010040e0f520a08110f8151000508069641d001c2d6907d064105900001c0200030030040d500003045481000d40709205442c0d40e0f02c0c11800942040720070b4000125004060039051401c628080101c0d0070107032aa811250070303102224003400440c00183d8062245200010311511803410080c410400045020340301c00d80312400500803100585041c481c000b50f01c1740020111290780d1791394615a4581444094 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 537107859 1250 537106609 537106627
    0x1a1005030a062c01080a0c03020d050a020a030609050f0109020105091c0503070303020a080a0c05070b060d120306170102031b070c0f08211615020c0316021c17 70
    0x1904242d0001074184401c404208024001d415540c525040400c0c503441c0700d1382c1c03107a030340650780c0c051000c0243c80b50f40c190301e0402c0076080c02c1c20500c0e40d03d80a481521580c3c0d4a98000c5002c600e02580221641d513034400b15201449030500c84601d590072041c0c000c1c001506541c000814034010008224480c095080d00c040025542c0740111160340d502100396034a5070380504005d030003904003202e02804100c6090000b1941c0c55584209181e100d180c2e20340b1400c014090f1034a5225050040179103400540604206c0040380801410480450b155580031a115041060045407101c2e43c84801c0300c16801070040c040200c9075000003882510068652a44440480c06c00c4180c0b4100390784108100d40005001160704070000c901e285900e0310104c0b8100c240c42410901001034400d202441004440030460000015480e0f00ca000c40e0800c141005401c04525010850950780080f1864244881810341c940450800c079058081e800000b400d8102080d045440741c2c15854903601030f400200c0000a00480c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 537109109 1250 537107859 537107861
    0xe04020901080c2a100b19030813051305071803020604120302250509061203090f030f10020409060b0c1005040201201e010c0203180409060216061a1005030a 69
    0x880000d20031306601100d5800380c519032a2410800182401e50904040d80d0180c240310400004443c1c155803100800791554031058590b4201480d0291f82401c24075000032169100c4066134241288444000b80070308114030007500c10b0140c000c5c0e10420b4102a2401c20143c4d4501080d80d040b0303002e200c00000600b01c903260403424810043d050844c28100078000403141215840840162101134501c1c100680b125400c01c010480a00030381c51040d80104518141c0d400c11019900698401400305e51815401102850a010b04a001c0010f480c0d40414200105001f50184000610f90659a6460603000c8144552034a1000c540600180d0302ea0b0041011039105203840d0b1508140c100d89030f040300340ea00750400e8565080b00300c25440c6100039003034007032019410300c5410705544141d00158948a041c0e90320390940240c0c0d0b8501e50b8401c2d55061a180419018001444540441e107500c507451144c03481c00b1301c1110614004441e11024600901d400303500d60b101c1061110500b4100903842c1d0740d4000d1144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 537110359 1250 537109109 537109147
    0x1207090513050c010e0d030e030c061804050c132706030311150f06010e010228050f070b07150b04110a09090519110c0a030f0e04020901080c 62
    0x1020191620040102129014040010951007441502e002e03e003d5401100e5035201025220b60240d1180c542c1c80000740200c1191095203006010f68142c01c0c1c00d81c000a0040d0080290f03400e094047d502c00c3c080514040c8141c0703138032640060145041241041e0b00c02d8030842d641c05801b00d5500b08412001040041700c40d0030800e1081a501803100c142c0300e1a0007031007c01d214801d800e9500c00c500445160030101c8030194425000100d19601c5c580e2801d00440d040030b513425000c0e05600610b014040020a40d90a104101800f020350b0f1b0800032041c40c0c118544120011008299008007205108080e074203000c40343d0054003c80380c020301e081e08051440050001ca40701503442490300d00d14502c00383c17000000e0b141101d010785810b41d12541c0e900c0707140d00f503c204903408956079a00000c400c0c0c68100d5a0301c860600002c04854500f00040ca110756850285903003c140c0c00b1441c2d101309c000d5a207500071209006a44151019801e2201480010300780400107800030303d0820001c1240d120103540541c0c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 537111609 1250 537110359 537110369
    0x1207081320010813110103051f0807150c0c05130b040507020a0201030501050409020f060a02030702030a0c08010c03110a031a10030506120d0518030a2a150e1207 71
    0x2580108028400c40c00c0e400e1000c030740301e0214041d100007460f5000038451440ea1070750004060365510a0302401100181401032481c6914800132184241ea80d60a20218020704083c1c80245907040c100401d071444100d0000500042010340342c01c40c0d00186000403a03200700c0d14255182804151031101150180000c8071075030307400a2414041102c0741c1e40c00264902014000c0e00c04000d2641c0312424007090313a0b4079201c0a9001506946210400c0c00d0400042003504c16030f20543e07041c4201031b030019082c0940a0026181c0d0b00042c4410321050700e0a104041081d1218181080394400d49074403854607020b02d00d01c00042c140c0d42c3c1d0194141318981203500700110320041c4143c844040080c070181c010241640e800d80944185182000d86d540005000c0141ca03110762201424003004550310b0100c282c0741e01c072054050191030011070004031000307403000c5007890200000100401d8410303840079604403a806034981c51100c00208202c0e641180740c042c00c0d0350050b11203031140006ca2510520300110b552103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 537112859 1250 537111609 537111623
    0x30c151b0a200304080a081c0908030106031401030c030206070303110a0c0312050903030609040f12030b01030e010b060f0a030209030f0c01080a0c05030c0703021f0510080312070813 80
    0x1003181910b921245210a00c451400c0c00400804032404850ba82d0041d40100034480d0303c00c4030708801060494025040d00000d000300b030741c50400c01c1080981030359a54007007100c0d0030401200600815405000f4411f0800c80280c48115540c950340b201a802e486902c40a4080c030b10005995060501c40e402001c901f481810380195101e0000c8001441300030040f0f0305400199807005c90313960b8600540240c80c040c01c2c40030019401d6031940810080704001c0640304850f0745400c401d4840c0080e00070150084503a070340e0f031400241030f00e4901c00501910701003204160030b40d01d080c1d03a0044641d070320710542d9500c0902480044c3c803405120702c2075000380704151001c2c3d40b6100385195400b0314080050b031101c000300280c0e2040c0e020741310312801c541a2030b0700c0555100032070300c00d00009040810210141210340e02038412611030f40740c002024201c404824003101700e495180d60400c08aa502028000c0007000b80c1e80c002c503e051411010b400c00600040e040c401004041d001180f080790746207420b04001604609 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 537114109 1250 537112859 537112867
    0xd051c0c020c10020102120f090f010608071d070c030509031504050319050f0301031506030b0708010504050709140d030216060503070801050109060e0f042009030708030c151b 77
    0x6020703507078080392203603036203d48290070403082c04a2040c029107000c031208040302d12040e00e5404a030f80012100800d058682d22550f0401c610100c0c0c240501c900901070000501402030070010710f01c11104406c03a100400b00c0c8000103000c0900e921850807403540d034152a1460b120f500d50300000e400c026a0884c01c400010942080c0801e00001000602c0e10b44400d8001103141e1217050015102405250300c01c0302c1c804414070040000c03e02812400090440b040750020b4550780781d07950020b44003c240c1d0010300140c002c200511260529100d502e4124005080c851061803510120310350000c400031010b8010241e5044190400d4000c200f2090000504640405541d80700d060003800c0790002c0f5030b440c00061400c0000102d95025405d5803003502c03c0b554801c0c0001507100140080c81980680b0306d40c01c180c1d0340304040c20207042c2544a42c0c1d40c01c55030031f4003542d4042d8141010320303190342504903c40306c3c1c00400022680003c00215400102442100c0744626034030201004c20b241002c90303001001543c006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 537115359 1250 537114109 537114131
    0x8090d03030b1026041a0f04060605450429060904030f021006331b060b13020c0d0f080c09030307060608070503060708090d051c 57
    0xa040b04085076401d881d240f10100030100708958030021400100d1044100c0b081c10800140140a40caa03c94050340544185401000000c139041404603028951500020140001c10030140180d0000301012181c114501034101a40240050001000d030705892116040071000d103901d0000700f02c81d4800005072904c03441c0c030f418800a15040781c40100340c81411802c00c004002c514101246c0681e8024201c841c49035207664059a003290120610400d501c5070340400c2244440707602850010706084c1c0e14a92003c3c4000303080784500c6c00c214442c82802a01e44180901140e07002c09002d180c8000700c440c40406414a0601c0f800419002004940012042034402d0040440d0f400803d041c0040c24100c0b503003e60110001c45210100064201c0000c510f4804121410100c8014004500c002402d4078a064040d5981100b164020350004050b908080410040c9180a202c565070060315810804110300d82070345401d8070b56402c4084001403140106d02006883c41383c2e001c008041c0c62240e410000101c2131 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 537116609 1250 537115359 537115361
    0x907082211030f01090201091203080a0c1806020705040609020f0901210f02030103021c02150918091c0c032309040e06100801150302040c0e03120a0207050402040b03040f08090d0303 80
    0x8101e00741d001c07400c2c1c01e200141141c544c0c603000e4585500756803036840540700c2801c2c42000d0083c4005003030070800c20500101c213b05160380024010607042e0010914207203080c0600081e5942c42e40310000e081d00c140710442c4c0f003819aa003110555802423030203010781004000c0c8446031a03c00c40040c01d030540350a0700f1001c0206c250740218141da0080b40d840000e503100d05511900e8415500d0000d4000b804c0684404c60301c0b04200c0030b40340014005144030303001c0c0740031000e500c1d81e40400c8a01c0398007030744001103030768612003815030584610903107103080314241d4840d84003e81460307458016142041c21101078006210800c5058405010000303205028220440c145141c0d18602503c0d100300407002d0270000150103030140b01d1015a032042480351481c6601c0c40d000c01005000c0040e4450501450000c0340720980d030306020f030010001c0c01e00783c100d071202d80e8030340c000b49028403030b8211501441c4100000e0041049080030350394010303448502d10305034000c0703072406c0700c1cad140100c1c1001c80c0c00c16109101d480030141c02d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 537117859 1250 537116609 537116621
    0xd050a0e21120a020c1f0804080d11070c24080912030403020a110913020909010f1401140603041a060102010e010f06050337140703060b0907082211030f01 68
    0x40f65003164001400e15040204c0703102181e407070380e0f006004040040e0380c440c0a607085030b50140c0188142070600000c1c80b811400d894503040300c0d21101c400000c20030108044510300038068601851404000e20f840119610203160151281c1c042c0103042000803c004000c0001001c00260040342c9034803400d1618001e0740d20012480c003100c014840802004203820031111940c416418001c4c0d034640d0116a4003132010540010300b10310b4095403a01d0350311484d00200d0140c0417001d80300c04442c0869600d0030001c000003c032031291030b0344285400c00612000c61140f0030150740411003d038a18805446460040c0d005091035074010761203509107d20150380f01c945500840440c0d100b40e00759925082c0e1341e120403007082540c8010100503080e0780c0d034400e04070380c40d52a1100483d20a002030205241c41c28006481c01c4040d078070407948503880b03460700b109a08106d8044c0d0340000440c1004a035a080400c2505030290554030801e05654030b800318042400a401c0d00c42040e0790002c1c05545076a408840e1481c060301d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 537119109 1250 537117859 537117877
    0x7030f030f0e031906020c0610150c0206190e03100c030b0108060d0609031b0c1a0307020a021e090a0e0c03070f0501080c0403150902030d050a0e2112 66
    0xa6401030740300018040e01407010000030080203000701007014640308071410601c4200380c440c19030030300c030605d030503101008018050f503020303072116100130700d00b41030345000000b008041c00030411050788280040e11490203440c4600200d481c1041c212085034030451700e4034440c80b01242c7c98400e0b940845401070301c0350b0050034250282d03503090181c01c55000042d10203a00648070701d9040501c401722200030808541c04118120711a2812054a8080c9881000c0d048030400c01610002c14445040049448000356082d9280300b042039142107203003a17a00039440707000c0320501034001c040401c00c4400d00802410500c21910b802040c1000605064621b5001003451316041320703140c42901425041443e00103070103011a03da040b050b6050324140b03801100c0054014040c0280c666040c0004800600111001c51580c21008000a0855128010145401800000a02889010850b03050269071080d94074941c40c0c0290b0350f62500080c0c20741c051a9425800320111814060b4a0b100c2c00300660401c01032900031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 537120359 1250 537119109 537119117
    0x10b1c091a0108010b01021507090b0406320d0504110d050a0506010b191b06090503030403080a021e0f2107180f06030e0708010510030213020c06190e07030f03 70
    0x107a03c424085088034540900c0b18090b0340311041d91170895203a440c49641c00950b900c2e00c0ea02d181da540802c1c0b40107402c280c0240c0040b680f40303071500c0f4481d000b44c03040e4201480c0c06007146107501c0144005541900c036404414080544070000103041c08004c4603c03404500000d083c1380d03211080ca0411075202c2c0c140d20300856850040d48000110350703100307030143c0d91114403040842801c040d1004041e110003c201481c80d10008180b0801d0000c00c0c036030300c00c401d84140500040d59880c41c0514006007040c0c40109503201440c8113110914030244684002aa01a030303048a031651002c19038400140d5006105100c01c040c0c000c800401c81074040382d00382d240034541c2512001000d02008034800038001050140e0b507680d2050700001c1200f1031094010100c00c1c1800d00c141c50000d40c44101c0c407402c0d01c2c1e08039501c1a10f04140c080c10021030400450395900e8180500e8218280020f5609941d207811028210440180740c00f01c03201c0c1a14090381c407400341440c200007102c224aa0b44e2034a1406d24540b05000d80100d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 537121609 1250 537120359 537120361
    0xd030b0310020c03090631030501050601030e0c060f040e040c0e160509151c0608070f120b0601050c07180b01030e151e09070801061706010b1c091a 65
    0x1509072402968001c0b1105030155091040c0001800029009403481e041894440708205120350b076003038030b0a8618050440c80c02912030541c100ba07420340b40c001c0c014030304140c03401012444100f4003041e0340c0314204003224503a5440500c000d01e000c0030700660700314004401b11141404108190754800404480303050707450204650b80c50000e0301841200c40d84400c04124100400c0e030030b0745010710555200889000d400c0e41040580c85d0402c07070003c14112078444042e40d800b018020b11004206200080250400c007212060800c1022500c100d4154001000540042e020802581c082c00179141440c080108444a0964686401081d0159030302d0070784042e4070340408101e00303520900980702401845001010301034040080e820703440c14014032030180034002d205181c40c2986a080c200b4019120ba40040c00c800c5c0c200030741c40e800c54007203501080302c2252100c5044241203004c100b4078115000006d03107548844400b4506d0050300900591500e000b40780c181d03440100643c4840300e11303081003400b2044140d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 537122859 1250 537121609 537121633
    0x2903180c06040f050f010c06020c07030201020601170a1205160b10050105070816030201020d060f0f0905100605030907050612070828020304110909032805070204020c07080d030b03 79
    0x40b0700c00c6018030050280605010f101c5030414400c0318800d1001071400c03203005021a22814101d800c089190412074000150410956038100451405000d440324012141010008969550461821300500c02c030921681060054020381c00d442c04504141360050250501e440d213003450801c111440c07000401c486030046007651081d425524680e07400b6410700d00d05410310f5442c0d891410100c400300c08641d0200300300c01c6074207518090310b8018440c0008400c08182800f40c50701c034000d5503420030202c05103401708103c05100802e10f039408442c00e80c142640c0e00d4039a0201507040a102d600001c0e01b0403000140440c14410366420f2a10880c0b699540d581942c582100e4013200000340281f40c0c9540141140c00002d03684580d0065400038440c96019280381c140d00c0100d0f60a900072a40307004c04c0d800220b004040744030304c100c1da540b0700590702490052501108030040d1090240f008003a02940e40410b18089030181000003402600b05501110050b289a4400402074095800503038064029002c1c0c10b20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 537124109 1250 537122859 537122869
    0x609160603020a050912010609110d0b062d090a300c0501050d15060f0f090e040803090f100f0b09040f02010c02130f020a0809162903180c 61
    0x501103c5a0f5240307803800100e40c0801000b10b035413120400495507503104c0041d05220b984682d8080040003050356440c3d00c55490f80000320754016450600071401004156a500360103d0304502005104190000b525109111406180612001c1c5504500c0b103003404208119000040c44108003211070064004e501c040040700015024180200100300030380d414001503000f50701a002007021351800080700036a113042d40b60468696030210012810b08842c001503d135005c0042a0b40641c1820300030212460074a0708a500080100302900c0c00d60040081508900140519210494500e04855041030340d821250010000c0e846200030040c038101181016051421b90140b00d15013207211200684402e80043d0345181000f481282e0100602204180280c040c0c13050303a140f40324035040140c0740c000700440500520005440c640301ca501c40d0055000400030010300000740c8100c42e012101c0381084d80e000203000942c042181c5040000032080003801200b20120802142a20049400c0340d80c11b031061203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 537125359 1250 537124109 537124117
    0x30d0501030b150d0b06270105040b011b080306010c02030f0c031c0909022b0203100909260c070e0613050f28090605040b01090c170604060503060916060302 69
    0x54000040800c1318000c01e1010354110760104015140e5108450307801d103030b2004940c100c0e40c2d4407691042c286c010301035400e045c464544869000e003004801260210061080c586038a1401084540d0000014010b0f9214203d00345001394090b00f29169040790743d4641d80c4507040040b80b40d000344900c0011900a0480201091201c3d00740c1c0c5079250160308210391a0040d50040b01d600c00e00314241c19618005e03030000701904080070408500141c403070030031070141d11103804142d001d0070360f4906100000000c90803103c9102030501c545690f01e11003690080c02c004150040303042403607160142440c00240b00642a603485c2c8501380840b103141040869131259802c682d0250703000340c001c480d02c0c0001890f2071a52a0039000b4501803503601d0600f500e6842552081d50104c1004546d410307281c10911003040b205c420b01a0150032488028824028841f078000c2c41400c214412000302a44070780401d2076520b842d171150020384405000d171803041c50802c40b10b03551540ea040c0700e4180505602070000354544030384261 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 537126609 1250 537125359 537125401
    0x1a0417011a01031b0e062a011104140108040f02150403110303030907150201020708030a0605040c0c020f190801050403080405190804030f031701090615170a020a11030d0501030b 78
    0x503100901000003105d80c0300c5a0504950483c10820048000b1390000700107c50000f441403113515010480c1c8a8a400c0d210a13403103120740584203000c2445102d8020090040b085020310381a05103645030308002d010320300440006900108500d00b032404003007801000b003003030b0390244910343e005c500ba00313051543ea488203c50341003013500f2940050005c00400f0310a00c1c0a60324a100140c100362003603c40d1141e540c403c0d03407180046540d5000811050409010350050f20b06541001ca00c001216000b1444034801950741d14414283e41181151541c10f03c030325240607101d8400204800c1c0f03403514019042c410180c40640d070303903c600394a2240408410591003400c5074031164030340c141890340e543c103001e40b25884001c07001d009441b10219541c6001fa4141c5008144081001c254286424004003203c0d030183c03605c5040101024030501107006290071a6000443c1c0b00c0011b03a145500501210b8942d0329040606c00c40c000041c07841c1c05071005800a5040c0e900a000e21001900c542c00018603c403d10114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 537127859 1250 537126609 537126641
    0x90f1d03220b0d020705030c01050109050609070c032001090507090b090c03090304030b0a090203060403020a021e01081b0702030a030c1e031b0309050d08030a05090303101a0417011a0103 82
    0x82e0480d04000f6000f80005c0e03807181c012030f41440c60b411700a0707003518000d81011000e80c0da9941002032900c1c1c48000741750852030b9030803c14000016074500034501130045082e0a003141e2040558022a4000d601854042d81c022003070315800360b01d6103070200161802440e40347c0f050581c41c3c045034540f40d0050440e4000c40c0c4800c0190701d041d00e10360314440300000003008140360ac3d5607114041c001d40c070b0602445200354401d6004d060a0490340c0f04020103240c0040c15000b10500554803401e169030489003450f044000b03180179101e810a40342801000788101e200c002e4050003406040400c240e080041000e019110340718151080840c4054803285502070742c000740c0002c1ca0707a80c61002c0e104d007014807514114000d1034040c0030a40c1b100c0101d100e40d030410038110f84d10384000041040c02c2849200341c030340240c0c03000003442ca981812001c45044250f90f010b607012514410010b401c0c1c00448030101e03801820b2140304840c09900b4541003600a00d16045a0514456034120982c0d041d13100c0d1162130310200034208 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 537129109 1250 537127859 537127867
    0x906031501150e13020c15061005071403040b0307030c14040603020c101a0112090b010b22030606060e0103090215210f01170c0604090f1d03220b 64
    0x1a2403030400b0801c921140c107100030410544182d88520002c08440c2c0d1980002507502d071411383e00a1701c0c050100184070702c05240e44c428020b1603070300ca1400310189022450041d480349064104601c000c1c0350100710a143d032100150005400a0707a0380030310f00c2145951000c020400044005031100343d2461403800410200700401d010142c02603006e80b09000c0a02c048901c5030a1026100e0120740c0400f95030300702c0f00e40c00307400c000303680d17a2002101800d480070388030a0220034210b580c1c031070410300103008145a5000215800083c40740c3d120402c90b4411300c0e0404048070564a0400340d00610041c014080000c2c45903400d040b29502a01032030340003560107811000055050340d607004890b0003141c3c4152202c0305800603c1c0c800484000307060301481e02e414000c0800d5141c46869000401c1d0414800f02c250414a40c0a00070343c0d883c415202202c880c03880200e15601c428084c100204403001c10031001c40308040c020800f880380040030f4000c3c03080c0c0c0181c28440101d0040300a011341c003d84a10707141c52000700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 537130359 1250 537129109 537129119
    0x4030c1805010819080d05010f0f08030c030711120d0e150306090c0c0a05121206010906050d0906060305031204030e04021e0c011e020306030c090c070609020102030d060609050906031501 82
    0xc1e42000040c01004020f04181c0090300c403206071182039100855401c1278520038011151010b112400600e0707404001d500d00510340421903268003800720701030011030440007100c403030b52101c0402100003c14101940c005c6041140702410603600003651500504c0c03000c000403050161401240c2c00740d00010103180301551652803d140325441141800071600440d00d6000008404100c0c00800721002c01050391202840d9640c035100341c1001744444c3c1004003e900801c40700c0e41180407540d11514041c03001c1110106400d142d0054603c03603100034824400015070400b52100080120300036846580d88545007509842000268003c41611014101c0344210040c1090f400000070010010744000104450304950031000c0001071010045060307680000070043c043c9010b202da00da19150803038541e1444e00f0705610100d014058400014aa0780d520006501560b008109070358010b040f4a1052011a48502d0014a05903080c41360340d006450aa01080e150701c5c000c00c060281e150078110b0700c0c219078601 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 537131609 1250 537130359 537130393
    0x51b0108060d110310110405030d0504050919110c030a080a0b031e12031905060102010501120209040311060a020a09290f0919060e01080603030d090602090604030c18050108 76
    0x80c0d00f0b652600c00d0208003ca803040d140071b102c50007903540c2c0006494034500002e05040a4032005024100007003040180f080350f4034101719503005954402d0800c10203000f40700000040c030a00001840c46d07100807030780c3d45170201c002004026000d00d03556088401e45981551030151028540c4e459859000181d401020300901d8045900c200c1c0417504541280c41310f0b890101c0664001d45183d9019a0508a0f00440899500601e80c10a03401e00c0200f107103602d00030f0301041e1888000300c0244695101404101418400c5183d601481e03000c0055400608111210344000d40c8844680b10104100703031000a00090111f184488a181500320b10040b00300006a1401c217a02010740002c510000780105038954031031002184400a0002050074000d0901c031025105e003d440c2110b5040140b09800c020740c0761008020b44580002c141c00100b904483d0b031500c10b0107401004196608030310701050000a0000c0107101c042103071042a5102c0c81c81142148940c161542405244e0490f03000b005600b00781411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 537132859 1250 537131609 537131633
    0x816080f19110f1c021c0c140c0a090e1c0e040605040b060306240a0c062409020a0903020909210a174501060303021c0c0c03051b0108060d 61
    0x44e44140d400740365800b0b010401c100c540200341000102c1b0f42d0940001c1000c1440c00100001c446c10040ca040c841074000203039a60030714080c20803025210405424844020444030340b4101ca50341002580160303e482c018103605080030464412401c02a001030380341094030034041042e20141681e0b00d15a1140107101001a207903818940c0703d0401020f0241c11022600540a5407020341d96211822015080c11010707a130116100103007000c100c1d40b0791101c04000c41507200c204c1c0c01510016880b042324500940e044601c95000be0b400800313600400500302c2010840c00300c0058107058240070050b80126141d5140940140f041c08904c100302c0c02362070309800d96182c40c0c0c442200d4105844c01407040c42c0013405651403208100740c0c044025040130001507040d1015001b90308800080103401c0c5942c038000d607a0083c1d00709500120303602c883c035000301c1441380116041180d00f021140b400d141e0380b89003043c0e07200d04454030301c0c1520b4008900100f880d8450b80f4443d0199030700904082071003042d52195031203010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 537134109 1250 537132859 537132913
    0x80d050c2115090f06010c080903070803071202030a08040b041e060903021b060f032a0a0905010801120303051e09071406070816080f19110f 62
    0x441442031240301554214000401c01145803501ca540c01d091802c08401600d1022040c0300b0f8649004029800014244055100c102460a241e4003132182c145170300e02d0300c200070740c01d80c00d4002e65002142d002c90000040004c0740c4181141143ca02400804903220701407081c000002403103c60200307001c80d00144007241c000740260030741c03008036050280c4141051145ca50490f45192113160102c01d1580520024046d13140c031211440c20380b80250700061242c0f081245150005601101003442420039541c8000c011003001a640b1000d07402440000c0306412003508440096600040886d69521804555048171a40c60907229a0b10203a40c0a8020b810002c2011102e0485500b00780811340200241500401d440005020074600340b00c645021400742252040c00703484d040100d0000140c601c000c584040c02d01e03c40003043c20000b4941103070030f8410083c5080b08110701107490405a82c1280d02c18214450300c0c2c0b215910030301130034050358440952032a4041e00b40c00c105a00e140d044a41c807400d01d6020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 537135359 1250 537134109 537134131
    0x4081c2106080106140f041406040f090c0303020105041e080403031b380f0117100608060a050a09020d0210090902070503030106020f0615011206150e040c0507080d05 73
    0x90b1518105421203203d85d118401d00c0100101181c4282801c1c050344a000c0420b03034060000c0752051a440d01c10400190a03140902c0c1c0c0c5110340400020150700203220030ba403001c0c00c4882d456aa040080c0a01016202030302e812030b1a04031002d0128519407d0800503501c07091403030510386561401d0b2207144802d0904024180040b200c0382c000351840c8850320f081c010801041c503031314100510400e41007580643d00050418100107002e01034088000c094115444c119845000c0c0f88a1b80e8000e08200e100d03140c5400e5603080000100c1c84440c0403404912845050400700290742d00c070b682d1384050702d041e4000a0b412440c407030002405400c0c80c0e0511020013100341088541280d80c0c90310301c3c0880e4040b01041c1d4680e0000f03c0140f08a590600180060001c0c01006151500b0b140310000c9890000046840c180500c415940700b500b01301360800d41c02480ea09030840360301038132413030045c281c580a42d4100c1d20481c80c002021000138050400c0d07e4149030419080b50815001d00104802000c003e05404229 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 537136609 1250 537135359 537135371
    0x6090c0810060305011503020f060c010b030604080d110909190209031006050315040b0a0c030b060c0a0309051e281508130210030203060406091104081c21 68
    0x6410041600c40c50910300d40050420f01d54200305085801101c02d1031007504055100b04050380e1200c2d02c070768580004a070003980d2451088907a60050290381040758040c000d200403c002e20032a18007030042004160b5050142c8580111042c28502c51000303183d074449442d41c0407a6528507039030000b0203140185100107180840300340c00030745025400401049242e85449051225090500c42e40c15110140860780b0010704066403208502c02004000c40c2c4025a11659040300601c40d400c08000f40c0409004184d40d0f00e081c801103a00d600d0111000d4020607a60796001070981440145902c11009040ca00000050180100600311304400c07403003415046043c1400b10b510700120142001010360700c501c1d04d80341c01c03100405044000300800c0c0407100908242034102580b10710103941d179884842d11b0010790766030f90400050028842604440f0303140740b41130000049002031100400a46503080704442c10303020702c0300c2418a80a24080c0703810000784201b6603ca0140301505540c000c5c0e0325001e07404a14 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 537137859 1250 537136609 537136619
    0x10807270807080c0307080c0d050c09040b04021f020606220e0d0224060904080d0c020f010b0301060f1205210a0f080609010314010e0a0b040204060518010306090c 72
    0xd00c01590015412504019410043d88004103c952030032034056014101c401c0c50a4049a114101035500c40e0140c11000101c0041040a102c50340e55454001c0200c449801d040c140002c1e04142140d040b03004031303040d5840b0b07550b0b000410190108580c0e6940188010707070b41c1c0014400040202c180311219228608002d80e0b003507045000701c034107030007444008012040c51030700024a041000c013100710210001107403040d641d01f000128254000300a550140340d5407603c4c82d003022203214008100a40780c0c50641d0441281c3c0d070105442d80e20a944400038012000c24401309400c8600501c82e44440d1036201c0e108000c50f0710318007840745805000f44183c3d030051204074030042031000f02d9a40701e01c144e000080c0c2d080c640c9400c00502c0051044918081800385401c401190f280e0700180030150200829402419030440d00b5006040c429400c40d081d240038046514010380001001e8404134440c03400d08001207540d0410000080901c854030024201d13030b0740b958682c440149040c21064505902804011070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 537139109 1250 537137859 537137927
    0xe0118060b0d0b09160f0f09050c1606060501200303060f01050f120103020a150f0e041b0305010e0906130b070c2306070201020a0210020f07020d03210605010807 71
    0x440366440e0030140c80003402044091580038965001ba008002c4404001c2c04009a141c0300703c010b4074801c81e130014072a1610500035900d0300541d0a038500c01c4400c0e1001c04100903081d0004022140b00fa200e501007450000b5094040020140403003005038002d00c009021440e01d0445421a4401030611900d040c040a00c1c421043c0e0021b050429000f640b800100211f0411003507080c02420242c4885042200c4500001d0882074607800e08006c0101071003000740659510380c46401050010741c1c880b41c00001c000d0014018280074030424411981e1840044c0c502c3d940401e01c0c52295008402908521450741d03200280c202c0094945001c0003090160340001400e00d5886030421050061007500c0d54180300c800300d03d041d60003001c4204690040c41030746072090f000034409015010014001d0380b90030032540c03641d13a24040c1802c041d5000c0f06080d41002450340105103649888000075850901d00c0c12058000203a80c104e22466000400a0002900c0e0701c0c4100d55100301c8215007140690f0444072045288 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 537140359 1250 537139109 537139111
    0x90509120d060f0323030306010f030b011101054002010f03140117160311060d0f050126010902060d020f07020a0608060f0d0f021504080105040507090e0118060b0d0b 73
    0x200d84640885c2c04d0946602521a00030302079100b00021841c40c6460300c00200400490841320080c0368407030606004d2030703001c3c24001d111030002400802c03841c9001c0342c0702c01d207003c0790340c0c3c0c03002c080140c40c03010b40e440031f41d0030040e17840740101c0c3c10360040c030301141e03900444000c0403200410f010942c0e100016000130021010880c0240f0340d09540801d043d1814481c2400d00c41034a2011042c280c0040d0100001042402a031011800c00c4031030a89402c9281c0022001d00110992a82003a1030000081107003c082c010300e0140d1081288201c0c01e000c0c0502c29242200c0b1411000f81d031200d02800a5524000240c0042056000b48204c050030811242e02003002c000a54010b203010401260400041c0c0c2407020f0701e0b001e145d004440c4940044580d840d542074400d29010064041c908101c4018a013044075803c80d8010700c203402c0200401d1170b01e42499501c8801c1030180c10b6181e42030041c500104601405100c114820b22486030400090607030319000200385442c0b1994101000d941d000e0042a40c0751559 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 537141609 1250 537140359 537140363
    0x50a14010c0503070c060909050f07110a02120d090f06020303060405060112230604060302150705030705250b03090606040902010320040e0604020c0d05090f06040303050c07090509120d060f03 84
    0x20082486c20701c1d4001d0803106440e000500c1103403800007000400900c54262030b400001d030303003010502c00c46020020f5080c4840240081e400c0000050034100b140b00008080ca03d5169956400c004942c4824402075401c1c1e05116090050340180045001d504d4550b10940d0004014102000242c03604100c1c1c0060340c0301d8003487c0142404200c109900c0341c04072950968001402c860804c046415607000035041c403031b0a100b1010790034011414000b00719003001110b0100760048200d0f283c43c1020042e21940c4e420f041c51450107440c0200c00040d07800d16110507039009041c00400b506513a55800c0500c0020210400c7c01d86c10561100380001200d1665901d003035200b40d600c0c2c0320035920390800a034071001040140031349000d03510422030010703102c0006c12604074400403441c0050340c4090000015103202c6150340d29941c040d0000400008160700308008124400d804010387d4105561210b40d841103c8084880d103156410040341550702c0302000004019074901d10100040c010784070b407412498200316402c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 537142859 1250 537141609 537141623
    0x605100e09010b040e030906040909020d171902011b080a060e011202030c090f010314150a050a1b021f152705040218150d0302032101050a14010c050307 67
    0x118006013007070300a8908401c2c01d20003d40c42d00075140081032062089200305025966201e40d0402150740d0f107606040d0054004181d41c600b0f101071102c503500c0780e00c03080059844c4254060102c0105006005201d0884000c2c0c1517858a00d502c1c00090701c4400000b0b2040c02002d40e80c0c7e1000c900b90111440c5903000e40000c000c1308800c445940705061600c0c0c40c80240354818020f000801c0307420414640a241941e5210040150408031465400d250141c0e070411541c40422030300401407600d00320707070080d4402c0720801406d12141560000524038294003244003c01038011043c00010b0004180d809500840007803400a104c02111040020350041d68020708404120800c1d034240d041030011303508244400c40c60041125040076400190f02100c130311031201d40c0900d01c03400030b05c444541840a00700001c0281000e0403450541c230f8001d46a52180b0542144900c109404c40c0b54040c40c4000c0c40d0503a40081c003120074090800390a0b40c02052420507060402101c0e0015400080060010b010a18440d040c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 537144109 1250 537142859 537142871
    0xd0303020c07090b33130f120b060f0a0501050f04030203060c0d05011e0513020c0a14060106111209120a06090314091f03180503040504060608130605100e0901 70
    0x1003080402582d5136900c14500c024036445c1c00018801070b10a00c0d080d0158560f2a0f61945641040419050030303600014034030b81a48400241461440141001300307200d40d180940503501c030800c001200340c0c1d008106401c41d0a4420034042940200d000741459184a42c1d603505060356940001c0c0b61400072151401010000300d00949a03a44901500e80035100a00d02e11025060b21181495007010300c0c40707450b126401e038000c813800c0c1c0d05041c0d040b211841c113944161400c803051810a5598610440c10000b5644502d1000203038291160314004082250040604100019049242540e81021180b20307400440c4000480510808000e14000075100ba4030103e400300c41820040c01002203555121a02c80d41005001069502c5581a01c0b600507080d942d00070203258640b048000b015103801c00001e80d2500110a4180080040039004480044800340720403602c42c803080341c00381015281d016214800c5510280000d13070300d420a6602c49060b0100b8666290b82d401e054442034021b44006061717941d180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 537145359 1250 537144109 537144131
    0x50301022d0408120d14150a050303030105060d051005030f06190605090c031023090907030b041e1208071704080d0c030f090b07021e0c0d0303020c0709 67
    0x10007804420381c1c0984101d0030940390841007615808007190308503058100160141c003128540e44103c0424811182510300f51500514804591601d4aa600e00c04e002e0720100207400d182c00001c0768141c1f0800f030401801c052289404001030300d40a00001d011080c500300200e00354a0400a44904400c0c0000514142c10201400c480c01c05071000e0900d680f03410b1550905c102e0b180c01011980240c003121405a490b03440c04030602e000c1c40c1c13a4001c180405028041c050300203541c00f02d0f081c480304045840680380c0c0c030340e00e400594400e01e51200a000d40c100c030700028042614400130000282010400c0f20a050096540741f2088030040d090703c0110700100705000019900410801070030085014041c681c0c00e29850724041406220050210301d070700c60098030300f41ca2003034016201821814501348404602c034030303000d01820700803a009070040c4602d19220694009a140c407005031740318607001c0e101c41d603555410f00c00303400c40c100e500741c082c15000c0040255445080254500621880d00005803600d808 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 537146609 1250 537145359 537145417
    0x2070b0117060412170f011a270d0b101503020a0c060203070c0b090a03020c010801030c0e0705160501090507060c020609090601020a0b0f010504060b040608061905030102 75
    0x41c0c10540c0401015121040c01c0c420004110b40c2041e001507484610700706902003119400c15460102c4640d11184044c00004031500c3d6055050300c1400d5210440c02c0080f6a10001501810248442455443e2112041100c61400d04000010050007840c038843c100e031506001220103460701d03c021000c412080010314880300c3c61102c0090507181c15850005841c4d00201010510306001e04041e41c004041900c0ca0701507034410107180d51003030b012141c1d403174000d42032611600d55100903000742c0222940d200303441d0301c078a0f60103058aa01240d00298142096003111030040001d09001c01e010040203030340c020000c001101c800140c40b0b60004211145070f0720f4a0f80c03d045459001c2c0301070040c070600ea5801a5603c0d8144d1306500c5065400000341e50721000100e00c1c001065401034480f0440c4402d02032a0302a841c642d5058445c156814000140e4581c6900003501c100c0c450180010701030341c0480d009d40303810b14009017401003d820400a080d1a800000d08a9200c1e6070342c8501c01e1080b107030000c400926 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 537147859 1250 537146609 537146611
    0x8030f010f060e0f040e1e160504111903141303110c0117090c0d030c03020d0203031014031e150c040302090f041403070f0308060415061b050d0302070b 67
    0x40ca00e814807104900e030300440c049500708600a44100d0b2140035441d03440c031b42000745074a0307151001e01c50040d00395a50300f2103403030300f120b40d102203401800d0720000305003407d1034011000c2a4564042c84c41c50130141d982c400d41750ba8044d111410030541c03501840884001c10f01105c0e802111600c041c41082e094900e0060080ca640218032401c54100c0101a4141c0c3e800c0b0b0b200040300308030074112140b503544141071282440c2c0c1201860f50f1110103841d201040c540d110003441c2c0140d100c0d40865414401d43c0505030f90741d010450301c5201e400e0100c01c09214545410000c0ca10054018044440e41540e00300300c40300c461806218558039030b002c11200d2002c88140c44000d60405a0b00c008680b8007800c64011648050340203000101030b004c980085010000b94401194203025010b00b0b50343ca60b07005140c002d2070f50303c080e0004d03400241c00d50081120b618052003014446281c088500a90a19200c429500a9420070503520a50f62000c80e02006ca1020b0104403400603455800690742c021074902481c123190 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 537149109 1250 537147859 537147869
    0xa120807020105100e0c092d120102030402090a021803060a1a0a08030d020708041d04020f030c0f1504050a0b1218061b0408031303061a010804020f040908030f010f 72
    0x800200d00301702e54074072400700d60b4008098810b0103586140e0304011411401d040c600400c00101480020703000780280c611040440d0f82d0803120000351105042469081c0d0109681c040c0d071281c06c1e040403526400b00d0b48c1c000e00c0c40034070111056607148d41150000341401c004503070700c4014035240d000001e0203001c0030704261a04001112031541403030603e07180c1640d0b40140e524511450368001403000034024910180c90050203a5812616490905089a451604141c0f42203004813210940746d4030340e10340072071070381d541d20405010141290718460030004942c42482c100c08a408041101048545036910f08230b01406a000c10a60f4a42c5c2da48030115011500a107250001d4105c0032401100003008243c0c260002ea40020003440d482600840c081e8600ca550300c0000d0030322000400d003400c000da40001500b2a40140800c00003d148511028106115110040c1c00a01100c00240c0186081080301e400b00d5000b600010340d9079220f035140aa03d9000350b50aa8445103c080100325102034000080082c1c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 537150359 1250 537149109 537149131
    0x618050d081e0105090408090d0303020705120a1e0509190e06060301030f170405060a0807020c0a0b1213051e0c0312040510030e100f110a0906110a120807020105 71
    0x181c03502c402150080010700980b442a40030f10040b07018851030109650115800610340e0109030514034028000798025101200c0314005c1400c0c21207908100300541d41c1d00450b0380c45102218190500802c00040a5185401840028020484561030f8226002d05616072554920600c906101c22401d02e0440141440e125610400041c40041c059402c0b4880d10356002000c400700381801c01c07503403100d80225003099070443c80128031100361a52004410713016020b184c003507500d000c1501045c00600e0241e07005501402070200f101e0403070380c50600d030381d0b030b80c843c18410780084803030007965a190901e4400003445140040462044400060a01c100070704210110000c0101d80c00c0303d61581d400340190b00c2002e10801c0d0f40b0502d00380c824002c1d00510ba9a109441c11380758140410060b2500402c242d0b0020440103203451140c00d0840c103180115900c2c0c12050b241c101150349482c41c1107a80b42c56031030180d0b02e00e004103154040043e00c51440d06d203440b0781c241c13036103200d41ca0038000007800c41c0e5004081104007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 537151609 1250 537150359 537150391
    0x140d05120109020f070f0f0f060507080f0405030f131a04060f020606010f03090503120f0a0f0e03030f07180e0a11130605030a1d06090106051806010302070618050d08 73
    0x708a004c1255000c0754050701054141e19141030a414a10300d1010280100c041d01404000f040160380c48180301714045c0d203421340240c85a4039141402101181d00408992081000700c11104020b00900b90051340d00e0300c007881c000e884500d0b111041101601e001c0d40d8200101c0c06001c460723044540400302c51610b10017443c10f854000c0000300080103161124080c190344548200c05d0010a000b151540241070807070001505122002141c0000c0c1124166201807a05400f0103040116014103410480035400442c103585542c0721901e02d1802c05000f040a000030000055025564420014001c0817007588420080c82e0a440001c01d4520082d484021020100120310200c104250394506481e02441c02c1c0d07840780d0b240f840705002030560520305030080ac2140728186000c140012503501c00c40964009025440d65801806841851111503400401081c4005045540320350301a1804e0750282c070021400d00b00d6401038800d0240000350580d05030308500305054480e41c000b1481900001d401e1889011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 537152859 1250 537151609 537151627
    0x5010f060b18040504020607200a080c01020703321501050a0302031011130f030c0605030408040612111204140601080d0509030309093306030a09140d0512010902 71
    0x10709542c140524421980d920100c0c0a40d128001030b00c55040e40803c004210000e5400040d034103400122074180308440665000c54151008501440c4c9400c045e0010311b07005086030b444c1032158085a920125180b03210601c0c8280c01d0f0900300b041000716414001e0701c00b6111243c515201200143c1000b1b008010380e07081000103031800191000d0355401510001010503d000c01c0c0211846510440e140d0722000e004081703000721900104400726032080c502c14030343d26620702c42135440d401304407406026a00140800c000d40e80c042c41021a200c035001800142c6e0749111144a420b541184041c0c0440381c0084003000100481c4403000030464070040010b014946c9058807840d50f815520a401007004800314a2104944082050390f044103802000103e00d41381a003000c4115444251943c0d0780034100c1c00e0704070403a411407000030881000140101d0b185a03500f0044001070640e0880440340525400e80c410303104582845030740000c2c82180d541c10350741d00380702921991075070060300507460b2a80304000c0111 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 537154109 1250 537152859 537152887
    0x9030606050a180b010c080d0c031a01090e0711010c090602210d0218030604050c01120506090403111f2f1b07090204120209181f0608070305010f060b 66
    0x60b60075a048001300d868022100101c4809202c204020580f000100e074440903d00242c10900e03a00d042941c04200e00302200190003003d40d91074074503a0205500d10014801002c4012441f0741c401840d040801200c20020929421154849003140009140c10020310402d58144241300003031402d40b45103100c0340d803000c04091a41c482e105808500e01d0740002c06036038954003108841c021040040c1914054a0070f424503a403920a10041d080c00a003441c180c02400d80c0c9144a102c0c060407018000c500c0c00d41d250380e800e844032a41d0018101d854800d081c01040b07040c900a81084182146180100d480c283c00d03004025058000c22004041d000100326001110b0740c46003e80ba100b00000301c0c0f461121442c1c08820342400c10603000b00921600000700032070200200c4411085183c4217a0348015141c0d80c00d094002e00b08080c20010f1765039003080b00c0d8030301842d075003005504120916080005100da964006c443c5001481c0d0b0044419944a501b40c00c1c1c915028841d403c014454007542526005160750b10103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 537155359 1250 537154109 537154139
    0x7121412060f0907121a0a18060e01120b0406020913060302010f05040b0d090602130602150f0105090f060103060f080606030601081c030c030603020a030605040b06030118020904021f09030606050a 86
    0x110405e0303a2081400081065013822292a040140480d01101d480c0c3c079840da003c0c030b000340d050040d817400c0040c0023a6031940c1718080f0307048075a041d8a030202c480556503000e00411001e4400e6600d2074092040f40c8090b500c00c80c608500a00ca42c000088041c46d520024007000861160802401000d0208002c44178449e803c584505810910028049a00f450300c500240240c0104800c4107452507004165030f500095004045d54201c45050425583d11000d58074200003402202e401c09081c0b400705005c0030481503c0b9800140505001c149581c60b56031075100101e4a900004841d80044103201242c101480100d000d001c0c07140107466a010035941c0700d00c00221001c41e17401095a5100050b42580c441d610040256900030300080200b540c03801e00002402c41500c2c00e42d004ca1555010607074038501407040604400003c002612048a03603000c014003290028810383c2c00c202c080b2050f49103032444400e140c0e41c4040689440b0040d90031030800d8030031201150401c0340a4104070109000f41d5075100450303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 537156609 1250 537155359 537155387
    0x10f020f03180c062a060c25080906070c09020a0512130c15090305010c03020702030124050609150d0912090602121b1b1005090607121412060f0907 65
    0x2515808210440c1c5d00b10030305001e0000342d13500946c030a004128100c00c00030001e00e14102491107800d241c8130f8011001c1001d213070f0010503801c2c0070071115a07181881800380003560f02031101004415900d41d030500070b036401207202000050001601903810180e0b4042d540d00300c916070708805001003265076401302501850040c5402c00c100c429520003664802c649030000f540d44000240800c0d0002a0080d010b9007050394203d100754200390f62945100c0c0520381038003000301042021440701d840e2106004040e8030052082e5001164900b0311102e00214000400d09400b4959000800c0d0302503003010300004032522100750400c00c01050800c1210750020390b29082183c80602c19030303500100322080465880d4885e5004541c0202100005034000c10049075040c9101545c8c04641d040601e40f0890f0984203100c0344981c41801404140c0200380c0c402d0802606030854184034480c0700e28851405803641008e100d4409010b001c000304041420400b283c0100b40c2000d480558150a10007409040c100180e812 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 537157859 1250 537156609 537156637
    0x20f0607051006060f08060108160806010507051f1b051c0914060a0c11030706020a0908061302040f05040f021311070b100b07030c14010f020f03180c06 67
    0x10506112042c000e00c1a90440d1410400c0081d0b56400090420442007041c8000714001c0c0001440c0d03035005103038540c81400c100f444004500c58440d0140d80d080b002074506410048103000140c00168200550280c05c44c4005820303034040561128641903c8000000400d5250703600f4050441942081c1904d20300d00d403022146880d1030001c103440008080d004c0d800340c1084071881d4040d0f0040008910720b40109540c0006101ca240700b041c09841c0c020b0000c0201425030320800401e000f141040c0d0190a18050354a0440c00b40c6030f88000c154a88101034450145040b0004180320461425100d01e030000c206c4140c044c0110320349a15000300031504850081e000380a44e1141802d414143d40c410812608284846070b1103130a242050803a07a0412079210351104004040403c0d45c82e0718605840c0c1d4558156206841c0580e2a52840011010000803460307940d04e80c07800d100a411240083d20109a035510340ca030700d0f4070305040c20341848080760244455940005241d05031a86031402184d9249450a131 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 537159109 1250 537157859 537157867
    0xb0d0b0402060906040b0a0809010c210204260114010f120609080a110601050f030c100302040b0f0c3c0721121b031d0d0c0510030207020f06 62
    0x204402d4401d01d15515070000000030082480b410000140c40d1554447d070300d09500740e482c82e142d24200c404480c51480803500000c0405125412400d41e0034405103140005820039a80f100c0c5030040c1004088204032103c0440601c0c00840c50900c42c241c0d00b8981c0501214203549407120103e405a0103000d44000b10484424a1051282d035800c0705600e5948003c0c5c1c25600c41580030001c000c1c0400451b15a464050103000040c10710780616403aa01500040c05010403107080790820201c2003610030f0380c1050580a0000007452a1000050220740269408642e0b507442e6404019050060458854000fa45038888010348031025865005402c8025400e505004070303815040c0346014200d0780071041d20100040b2404c80c036a4045600c800e190312402820700c41c40805142552805440a03024414442c3c40c01e115022900c9402e00c02d100d00320801c82071004903003501c00304103010a800340581d03c0040c009400c11070707424100000002113125117001c40c18011107500003841440902c4206205140c082 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 537160359 1250 537159109 537159113
    0x131b0f0512011b08011d0f012711070b0a050702120d02091e19080619181b080307030c32010e15040209061207080106080f01050106030b0d0b04 63
    0x50f00440f50100b15548540001c00e070500020002c00d8240079100c000840c600c0300040700071941c4d241c80c0c000c010698034030415a0801480301d810304480789441c40e4040032094252400d0303130381303100b1880000c800d2042c0d02d513201c1250408a014910145c005812140703402d04000301c00b83c0c042044103000340300300c81e106d070307640c519030490704c068011010542e60103d01e001113600d01d9042440040d5001c00240da4070540d46c10010003000300c8042038814a00c9070b8119034005907640500c4400740210009a40b000100d0001500e102864220b81d00c60071034600f106494070140c41c01c0c007440350780b000348480d400441c41c2140c0c079540104101d242110040c560401e0b42e8a800785000480c40f00d1801081100009105440301c0ca4510f02811440594440902911240c0454040b03a250258422500a8520840754456a0501134464005909480c81d40030f00940400c1101c002e0003148014400d2a0080504440091029007100d006074484c1003410b00d409c0d001d000946a13108c03150026a00074030146c1c1240e480e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 537161609 1250 537160359 537160361
    0x4061a010c0312110d05010810020307020a0f06140703020c0c190302011412070c0b010506070b01050d1115120105030609060c03071803030507060c030905031e0f03131b0f051201 78
    0x2800540c500c4d040204215400205642c4803070704a5105408940840c2602c250360000c84c4000d0311002c0041c1c0003100d102001c01e1205504085813840f40a00160304419120f40c0704803040c1c103540001c0026000a940329400e0b2041014408820003107035140300450a080c00b04036004c0d01d80c40024140942c02800175160365004043ea400382803050f442000034078180740d00034108101c65808441211030b140000c9860300b041815150750690002c90a08183d080804121405441880032140703002c0c1d060b00c1007030548409210501f43c0e95483e02050b100c0da041c610f5005c0319030050300070034000d2303100c80100170345c0e210000340310750b00080314008041d525214902c044072141c0702e00d10702015081c04101c2c00030030150701a00618040d4041e91007000115140c40d812820707a419007402400c240d04c00d011404c035854107203400a0790024001621860304040303950000d6207400c102c03010707c410246504080d06110705403410f501c4040320201224481400e10020001c2c0340a68014203000e004103801c01c400c0d003142 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 537162859 1250 537161609 537161621
    0x30c0e0306010b1918030c050a080f060a09051f0b10020a0f1412030115092102120709110304050609160303031104260c0102010204060512061f0804061a010c0312 71
    0x804800e03110310a4481c1000c4031f20300d265104050040381d54407000103c203c0b02240c05100780c0080790140c000d5494219595010309800c0006460a010700001d5000d12841b80019800d40d215800000c1043d60700c00007007152940b00103940d0825900214000300020380d00305919540b0f181d0050740d801c401c16035003e0031880c02030344402a00e4800310000c000301c0e1050000f5030060348542c40355601c0820a40398081c10074018044c00d11040311903220661b603001890540c50864481c2001c7c022034400c11f5076104c2e0081600d03103d410300d0356800000401e00042c08024080c2661080d1084006e008940703607209440002d80b01e0344805410036541e80e06024801310110100c600500480208011039140a6200c1180c1c21081143c0d0442d4410071400c000194018025541280c06c291151400c04d51a000c40044524004002541c428800a2081808803001542901d1810a541c60300b01d98030b0545080d10485070004c070901120721040504034010303030f0b120002c54581a81840e04c40384c1401046514006005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 537164109 1250 537162859 537162887
    0x5030a1802060304080c1006120b090f1608101e020f043210120e160602160f051c020d0b070c031403010f1a0705030406030c0e0306010b19 61
    0x3000000740418000550080d02d481352181c0b044d0765210240d005801d04442c0c4500c5000c8000f001121848048ad040488041d0301441c054180d4466415071200c042c14103003001c0103a90340c0c003540d070014049050100030030303801c400d600b0608201802000c40c40103000508240700c50a01600000d03168800c0a40100303035401008000d18090130f0110040d261103401c90b00301200c0e0000d600b00c6c440d55a05190080c6c035045009001e40391500003c152408550203004c0024207a0210300c517461403208000780c4403600e040144195070140c02c001444005001c0c81c1090b9500c40802c030300c1c011609102c56600c502d003c400d4a441c240340759500b58603d00c00303d030000b04880c0020b4411168031042000403600300707189041042c0310b0b91307401d509480781c080e6044641c0000e009010a07441c00e08000e1041c2200901c11402001c0c030714080d035041840d2a80e440d80703994801e400081c0003c1e22101c01e6a1b1054000c0b90b40c441c604c0084020b860b80358104290a10707a03020b0610b0710500d0703030070b1401015165800381d00e500308131007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 537165359 1250 537164109 537164119
    0x7211401060503100f1404080a0c051903170708071202090f0d0c08010c0c0c03020d170d0f050c0a080a05070c0f1406060307060207261009030e0f0105030a1802 70
    0x403103800d044000501061007108010303420101c902d0044c1e030016806c00c0c0300e10b0780301038101d04009290301c08451686103100c048429108115407450401801501c103819584039940e03c01c0ea0f40c2c41c81008101030800a01840103016601c400d01a405030814244140c1500c0700c0700050725103448400003001014201451900400603a090005220100e910001556400701c0284540220f04500700c0d8500d50310780340580211100503040c4010703e085002640c03179a0080c0c000386070240058600c40d049600c181d640b01a041d030749c0c114210040005024896011030b0b211141c0f41045100f5202426900000340f40505450390380c030011b480240120401506246c1040100b0310000e168900030000d035201e801e02d1b1031036201d01c5001446900c1c00040c0c410550351075a01810456280c0f05038820310000800040300d0f802120403001c10102801c01000d8900a11060086508556410b01806d51184940e001c3d0052400702a920300eaa60800c088030380007600e03180f0010300354110301006813000b40b070480025880 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 537166609 1250 537165359 537165373
    0x406050a061d0a09081b0d0306060e010e0607081b030d15081506121006030605060d0507060e18161211090108040507031205070b0105060301031101120e01150807211401060503 77
    0x6d08000030f0383e14074654240c900300b0240791586d00c1690b00342c0124070b043d80007810340c00c1200c01c41d040c2031002e070040c180303d403910f2410820b00242001ca49001d50002c3c103060741c0b0224003d00341e003240c1d000700f40d801c90840100da600c540c104076400da1180c1072084010030780c68059000c90401e4988441030310100e40b000060b680c04d04940000ca0000d8009440251116414040840d1a0f4900b00709950682684000148030040c5840016551000c00440b841c2d404030a500c807452072042d030580d0a500c2070324854404841e043d03010304082c0451440384620544903180c041810030754000042140c200b0301c2c003424032051960759440c09900d00072040d000104a441680c10440c0c005411001600c00240300c1c01c203504031a0780315414070900e80003d100c00740c128203002070800b140354080d4405403210003686401141d58040048650700355041d0344d2101d0211100010104152032040c00060098091500f08030500d819203a8030600e20340d54480058144040308945030800602544031100528010741602d01f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 537167859 1250 537166609 537166657
    0x2030a051903180b1210030b01031101020f0a020f0f06040f09020301080601090e030403150b0907260405060103171c05010f0602150c130503060406050a061d0a0908 72
    0x4070034607a58100c01088085000b0518224004541403da541100502c1e00b0080b6900d104121600c1c082d1160054010012020000c076a04c0b120b190b001c0c5000f4020310058690400c002413910501e04a50304540e0170900350000181d907400580d451900003201c0b1800e0010405001903818403a0764070030440d060300150005041500c580241d0704075060702d0203a40c1640e076680304c900d00750345201d14210400d400403c01840003641405480e65a441510130009000115402003410004c050761301c80f003c01e8041c0c08070041144407c801d09a5180c0c40001d882c11801d255459594825041c0070040860134120403030b032140d2001906443c55120351100384001700b40c10324080b50041000303000f030820240ca00c1401140040c00064506030420f546052103120742d40c0d0f11928900f642259a4038203070744040c254001099074040180c14003030b500031040000c244c00c00011048c215142d607030000c424001e07000d000071070380910020001d81c0000f1002c0c011445000c0e0b454550a14483c02021b0740c0c0440304c00b0003100d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 537169109 1250 537167859 537167893
    0x405070305011103010e010315111c0617060c0a020109050d090503070e0106120510080d0201050f250507020303120f091b060a030902060c1f1404150902030a05 70
    0x300c0703008800030003c2d901100c440310b0551009004c1c1504096020004100090524550103007161074018009a41c2029107a4a00162300c204483c40c0034078039103019410f28003400d108a41c0141052010002e45011006950340c881c1b000620031510300b10041050350b01c082c002e4000484a5a02c0401d07078107007240303460000e01440801d004a50182c80b440f60085111070380c5508140c1038800741d84440300b61300d1204003610090600248003400130103050a00150340101007080510031003040d00003185510f09802e8041050b00020a15511042000801d10000c2951a50607001300900d150980c0e4402041c0086880e5209607004038060342070b06401c1110001c65031018501449042c001c1e600100f50407404011008641d906071544003004102d8240218080c2d03011040b030a1001d010142403858006815081026540684185038003d11080b84000303002e10811701d1086582e10340701c41c14103050700c468030b249408aa80e0140e0f940e0f100441c40035950100b000400043d404802c440c0f4070094401c0f041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 537170359 1250 537169109 537169123
    0x11a0336010c020123070c080a0905041503170307110a0f020405090c011d01090306060902070c0b070c12051606050a030b1c02040903140a05090a0e0f0415020c060405 73
    0x21455181001d212222403060080d440d40c00d07042c1d0405c4445005074200055045d20240c40e240611003042080e0380015000c0d00544160f6105440380342d880c910300800d21051b60703080d0040350326090140d00d090000455002c0085920382d468003c841d01c95994020584214101600d80d411070720620070818200007044075840c200d28400c0d1000c3c40280c44098685a42b4503802d407005000c60b2070648118250040c0b59540500d280d41454200e0320142d8940345c0c0b0007151f0064110181641c2c000849030b041c031103004848401001100316a501d41030385910b40c00348030075036030103007607000341030601320707000f40f02c400c104001c1c612a04c0d60411078000d6942c075000d452075015100000119040c00b256a0303c514003015a0b1090301601c021144552007194200401042c041104505002542602c80000303c400d502900c14240325403509a43e030340c0070004010307211903242e21581c1804e07100c1040005017600118125082648424104000e02811031b03164083e01412140001612400c810801807001c002404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 537171609 1250 537170359 537170461
    0x7021e01020a2a02060a020a290c041805060f04050a091b0f030b06061303030206040c090615030c1110020403120801080a03050a020c060d05090d08011a03 68
    0x801030000f600045900020041e41d080c00c410340d003101420300541007100c011b10a024440c41520300c0002c61380c3e42c10300f15500c005251000e0750703030303d007102c941c0c54081030001038000d02880021030130280307802100f49504404810000a0640303690104074207841d4904860451a0010310602c240e00e0090008d400800c1e900b24142c5291002c40d4841903501110b6844c2801c0e280100f00d0403a1090642e03c480161030f40c00307405140c004c0c1d03082106440400400b5000e201030352081d409025241028103041d01d555103107811000005103030200400c4111520781c1140030640c40c03410086011540294282c8141c5025200c1009500403101c2c000700c002c14a900800540e4418491010f0923420036008469028090054840302d038000b4010a01103400342d0301400c0000003520445a01c106c42c48045000d5400c03d06450318401e482e2410b10000b032400781f042c43c1c0001c2d04d51400700025032429110000020a0b02035100c2d64440000209614011032003201000548542d10144c400030301c105400100c0c1070803250307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 537172859 1250 537171609 537171617
    0x10020a030203071215060e060d02040314010c0806011704210c170c060408131508090d020c060d0c03020d02040305031207171819050105090c060f0a0807021e01020a 72
    0x44c24001065521546002c0d910320f01c91540d029041c12015601e00c40035268040e880b08090146204000a6000820245115002c1d141c151074070701040e103080d20100940741d018001f42c1c1d410451180d03440b40c1202007040c00381d01d00c4001511141403000000d04034012201c0d0440030b02e00700180c100c1c1c00c0304054003a10711898042e10446083c0da9444403501410b0f903e1401500b060020070003003010b01000d40b44030b8030a20103001c1496a42d4101946211490196802017240c40d010020908024004907580d01442c0c0094140103840300e00050651046507107003442c0640d207043c100c01807031196054602c00303086141d003150b4494032402c1050340c0360020032110310307007030036520000d132000d8800d00c011005041078a480316001d458504210000c0005110100f005204c1c1d4149210701011a5445442e007500450000440b8201f002400f41070040b400300207030003401c0800c14401103001d52802c03900c0061031031800c088a500c1c1d03041c0c02c0781429142508140c0d10ae1b15490140c9124406500519800b02c250b15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 537174109 1250 537172859 537172877
    0x60117011e0b07050c091b070506060906041e050a060518090f0d02101e0c090f0510020c06030411090405010501140a0b070201110102041d090705010c1e0510020a03020307 75
    0x2c07903038840c1d014010b08941081448009500303001c4510b0b40c200100002c00011520b600c000112150440403007a07599511031130500c0aa81071210680d6080760080d0303810700001030381d031403449100c0e00d0344c00021103180c0d5580d00280d08020f00d80d200304090300e001031184a411000020b038510b0480300761080900c80c015018031003441d03040043d0320041030443d500a080e050b03400301c071282c0c0281700c00000810840007100c2d0b85c50010855100b103503020040d07512802c2009003480c6200021918580003036020740c02d40055100c0386500064a1110b03c030080302c000d60340f42d0f0707546443d001080f00406030705d811540d00b109000410806400c9681a55508ca1b4022002422041008080c2d034241c41041404a0204558409940708280d24000560f1080015181954900d070b0141d090910182028480f810502405929202844044001d00d02441c15454a07081e5848011700c4036071041c1d41c1b040c0c1d68036483d20300f801c2120034010642ca1761030481c01151134492004015010f50f06c11a003080024074420 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 537175359 1250 537174109 537174119
    0xc061806010608010e100b1c0605040c09030f0f0c030510050a06032a0e01080313081b060a020a05010c3516091a0c0706110c09060117011e 61
    0xd00103048910315681c907030389a441d1008080c881c0402402005d480f038814100400c0340c3c42c040c0000c1c110310010010030074040c9006c0340903104461903030b08914803880c1009118410707c0e60000a40c1c2c1525040700440351031880030700c0c0600484699110003001191404030010500c00046500c41089000d42028085a92a10001d004440b16800004d00c0140c0c1002e42036801402794100d05030364041c1480074001c0d0f544820307181c1c03410a026072107065258000a02051a002070805100082862600400c00000ca41a401d006600b840403200d0040c0008603200c1038103842000110402a0010020003c00c408100001c1050300000a0248e107240c08504c085a8040310181500c0001c2103d50b82c121a516160800c03900c4001c1d040c1c4010800c04c04440119070440c09900c60300aa011221900b59a060041401c9050106e150b0040301800600001e141da204404502c8100d5034800f11a018443d5440400580f49555000c1e004021107106c1c0002003814401e058000c4482030052044181c099582c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 537176609 1250 537175359 537175363
    0x1407030507030303050c070501110301090f11030a020a050d020d0207170a1d0a0e13060e16090c0306030b15040513020a150915020318060a0c0321020c0618 68
    0x15100040103503004801c1000428444d81c013054000500d01910392410850f500d0311425201b0000c8c40079890000080104690805031140411080c0c1e04442401081d00100761042c4901004151104046d00040c20b0740c0c504c0d00c581d04070f07000c40070410390464407005184202030080d00702e03840841e10052031030702c2c41749410303a83c406890466040359034600088074195401c040052602c0c400c2d5800440a0a01141c0034003801245486070586411201d014216810401c0680d01081d071080002d4212000c208940b0001c2c010300b07400c0d1040990040b941c6890410308a001b03103150744c0060161003004013400503e403d081000344a10f081290140865140c1c10700d0141504401e0000039070201007030701c0030040090980504000b425482c200800c403290f5800442c14103084403107982d00103801c0000c050040d05503000034021300f007900b5140a4100702e66410701a00d40c045c156070103014802d40b401140010030704c1800059200c00300032170540d1900f110304401da40d03a040c01e54103840e1701c220b80349024121081c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 537177859 1250 537176609 537176623
    0x30b07020f1e030306040f0605040204081c0c03050708031506160201020d03180609110d0f1707020a0b0d060906080723061b010908070b060f030a030801060e0d021c14 73
    0x82c0c1c0d0280d0b00d0f54841301d08000c001c0402c1d4101c8541581c480c400040d203603076217102402c010030030740001d0121240d0b031400e0343d591115102103010a00929054410100c1e9008050314007940d07110023616030340e48940c042c620901e00362032000c5501c040b00042d0084011170185043c1400d5100380c084aa000b603107040705400381d445480c03e0174405490114040081042600140b001d940580083c618211604d808940d140d03034200b0050341e47c031824014110410800500440c80d2014142c106424090b0642c00248403070780c40d20586c00914408607199400c611a41d00100041c00644002c010040c1c1d0390101c1600c680e42403113988070a854400e0000045604408140800d82c00289890303d0100d19400c80c00c4484050360210409658520546000504110003403400d60301070800d181750b6242503020030907003131000d064081c02904401d1220700040d401ca40481d0648903a803c060b2030f5011800c01080d1602e00341040658010a1000c0c04401082098099040c040c090510042c91340307050704080b542c40300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 537179109 1250 537177859 537177913
    0x6070f08150d081204020a0902030609062806020f150103050a0222060b0403060c0309150b062b1b0905061e07050c1905150d0204030b07020f 62
    0x40c2400041c40c00750000100390103034440100031070310340711140d11110b2450f089120504180350450b01803005503e003030440300004000050040d49945403440125031418405400a40511711020045a0f5032441c0c8104045c103040c1100c03c1d21602e030355401300a55444601303120204600400d541080302c0e0181f41c14050590307401400501d03003c1040d50070b110201608409400708480f082213100001d081a01895005022101340c050b1600e0541c24200211071200b00308509051921000f080000d40c00d441304905208441c0000610940b1309012a889200c0d01c00394011280303d50b0702c200144503104a40b805012000101001500032070720004c2c0521500d00340000100b41c0d181c80030411860084000d20001401880d4084d00c901194618181341c2c21000d0201d4080c0c00411118201d070400611000160380190104101b02e8075141c0890183d0400500111130114000703061400100584c044034010b66004074050f01d20301d001c1d1002074851142c03a8140100d40030316580d88205a884546d0181059 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 537180359 1250 537179109 537179117
    0x5131b0e04081305090a02040608070e011d04231e0f0a0b040204090905010b010f1412090c0a080607021908040e070306050303040f0501080a060803070f081608070506070f 75
    0x140307079611a0b00e81a0003070481100100c03104400424191640c190140c065001c0010250315241001409024240028030034010030444440580701d03680d21100000c60f040700b880440c140700460300d01007000340001c08000c4044844400b80b4034000e10707048601502c24400701c03070400000701d2b1110442a000c102079820ac101c1105d483c0100f0803805c0250b02103482f581006000614055503a0103400c1a50f668140540309650340c0c6807104160758002d040070302c00c20b00f01d10b170504107040300c2c040e01c8800740140001100355102a6000030f0101100704200d0170b920500800d040c1c1800c2e0f036269400d0350f6a2003221590014043c140340184101c502c50440c1d480254486202820141807003080ca9581c940204940105600c900d400512038500307200a10140c440d1001c246007540c02d1030005414103c02070010001685422810040d04101000b41c03003900d540500c042c0e0300c002150520b01c9c15802507820007031007511402c40c00420014088001e200444c4a00c0a50b15950382d421025507900024150481c046 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 537181609 1250 537180359 537180361
    0x1050f0c01140703020304060b0103061a09010c1a01260604030f170903220315111c0515040c090b0307020f060f0a0b030d0c031404050405131b0e 64
    0x15614000a040c0c040c0806000241e00451124020b1012800b9504080800d50010511050103014001e50708048402e007018081645040014100c440000c3d03a9000c0114010070f90b000d40d43c0c0300700c2e002c050141c0c01c00c08042e8081c48450255445942c01e100780d042c0700ca51203040c8681ea140e442c0da0300807a82126030107483c2554640c5c82c2034805e069440c19440420a00341c0b451700101d00c00b0141140520f007e20000c544807042081c40f02003000340c00244141c070b48a901c1d0108002003110140b0401c200501c200403c10b210107290300c665601070004a084c100a041c801d81c14551000d601c1184640300200391303500300d50281030a00c000c07605101c00b89000540d200c1c030180501c080c10001103030414030901c1114079035040814030070304201056859030a104a1482407000b00c003460f01402070400821005419201c10f46080a4015070028100406022400d40a0403110300400d061b2401044060001e1065142c664100032129146160455000842010310301110019a0720754090360a82500ca07606 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 537182859 1250 537181609 537181627
    0x50121020d080903030703030e0d02030c120a031d0d121103060904030219110f0102060705041203020c10022103070c021306030f0f0623041101021203330105 69
    0x44001c0c48005440045040009041c00e0320308000900005020740e03400a00016000461428410341400c150215881030052003600c283c0402c0c4038106440025003983d0780e2000c040150054100f03e007076620314898089482040c02400f081e00e00891000d0359680d4031819000c440031044078000e0200d0582038170103200144440c2403020781c194105000740101c031051b10640040c003149510b084412240c00c80c1e5008074800e1410050002c58050209001400c003605d8041e000520501452261468030000800448180350003400300d4400410081d0102074003004da03043c0655203902c3e49090310764030f4103403078082c8100c440e000007524000c20455480d540240e41640030400c0005200e034041c1e40c21603880d0800800941f40c110350f43e40c558462140b0f01c01d1904582801c008a443e10714440c100c0c11525848010140c1100380180d0744998014803c924442c0b071740c00100c0c80c080341c2c00000400c941001050118011f0300c0749202c0c411004100120009480c04220140c1c3d4881035550503002c10000d0009080b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 537184109 1250 537182859 537182869
    0x30c2e081005090c07020f2e031a010806010f090306110c0d03060e1501110105040b06011b0c03020105072402090a050f090c0c030f0a0e010f0e030604030809012a0305012102 76
    0x100064003c0c1001da9040303010340d80180c10000b0f503048812001012311030b03030081a050b00456482d9400c1c0c00c040000b0102850010302403410040c210781c10000f0603801046c2040c0034010b8400610307004081006a03044100c0315109030f0344008500000c1e48500340280491034428050b400669580740740d040744648902c5911020741c0d0040c007545060101c4403003003103003070042407007050f01c120b021315020079642c2441c8001400c01d1703203460390742031902c00862034100101d00d60003100411650b081c6096541c60f40c040c107044000146e250860900208900c1400720146c80e0394003d01a4050221024040c15980710100100038400740c004540110390880001e04580300200075040d8135584c00c050700e280c1440d1104074400e940c402810f0074045001d001000c03003107580c0100c1c0050611b00c94103115020305600341c0060b40c4c62000400040c104151000050780f079600a4100c013600200340e9000540c0c601582ca1540d15180440740c0c0a030001c2d19010000400c3d10300340d1280c440c1c00700b0301c1410070b40b91714454007800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 537185359 1250 537184109 537184129
    0x8041106190809120f040e0106180b030402120d080405101512061104030606061805220f23160503150105040e0109200405030c2e081005090c0702 64
    0x3d80c0c00c0c02000c42d04080721007000014003200e9a05543c1c16500e03070a0030038186540c14180c20a004105002c26284040188100842c00740c45015041e2916039440d480040c1f58034481c0c07510390920317005540c820f000007500618441d0040348a1002c2c4c84007021003034070450803501c482c0402800035801e16020003608080b000740d901114050007010401403010302c60220140d01c150b10444189680b0101002200d07404021122401d24502600f40010300d010b00080340c040c0b441d906140342c0568500e21130301e0300c1140e0340050407888a1080034000e040e000e034040f80c949119155950a40202c1100080703e41c20000c90055580701640c6426007103481d5007403c004000c0034603890030305200d802c0101080c2426140f81c120700a00291201181c5100458500907002200d0041840c1d50340d81407000384100d50380454180c500c64400e031910034400c80300340058103102d8503505840c000c800c8a1400780300b0250703118372441c1c0300f440320541c4002c8140d6200180001904201c48031305ca4000140110750040c0360581000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 537186609 1250 537185359 537185371
    0x10801181b051906031808070201030209010e0907050d11040e130f1509020f1504211401050f1311040203190606110c0d020a05190e07080411061908 65
    0x46000503864101088203d90b07068110801071401a604200d26130781401017003200109441003a0800c2180d47d01c0d01404d0280301d00003418181c0121b4001456441000c00b446001c10090055500782030911029100d80c0c0400341d480f071007a040035088a410001c44040f20100d40000c403c091070766a800c000e24407401d80a403000c07035100d0780741c034120307808200221101c1032000d441500001d0156101d104003c1128601011240600741000d0380e18548600c0505a408840c040c010f505e0101c02441095008204c091000416032400601020b180700015400309109000022040010b030702e59440884110181c5540208455080c11640c040d9042c141c000e960040f8446550082d00801c0041d104161101a045040010140603850301036a00811000c0311a000548001e1900140c0e0303004241100d1080c0038040c000d44854100319056a06804808000d00c2d81090f22489401d08040c0201400020b98042d901c52203200e4580f540d92801c03500311803078500c07010061003030300e03c010209840801c001011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 537187859 1250 537186609 537186653
    0x9070f12021305010e030a05060705090103180506061801030f0809012a17180d08071b0e0a0212040204051b0f1b0304060c0f17070b0f01080118 63
    0xa0451200e8000303003160541612a6090072410540010150362140003d40e12035407203848850045100420322980045403894855681d00c041001a00035240200082c420800c451185409108000c100d8a0144d130341200d030b200051010000e01d00c0c60752420f00029000441d9000b900c00040c401d0001000141011f0600d034002554490381c035101c03640f16481010114040320700000421451703140098901c2c051640080c2040f1150803505441c502e070300030345402900038441010500903008281c48034540e0102d003e01001c0c20320f40c070070742c0c1000ca20310801d0742c0b00083c032010074086030440c0243c0d641e8501100716800e075903403640c00f00405000041c0038261000c401e04410740c100c80c1c07144014023031030f034a1105461341c400d000c2301d8940c01e407559a103601c0f66507001031005100c001c2d8041b0300c25010765005000203184600904141401c0c11007900044908000050301004116180c08418130811001103032400396a6103043c402d09860045407840306802c41503120740001a1071103849603a00b60302d124 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 537189109 1250 537187859 537187877
    0x41b0c1a07110f0712080d0f2423011d090a14010e0c0f0a020316120210060b03060607060b1203030402030d14030c0d02070f080306011b0209070f 64
    0x6403100c1894058501800081d11aa40d0002e400010814442d0000080d001400300038a010f4100c01030b0702c0c031610000c0c1035040000d1b80719085507041e0031804040c030710040104010245500398500480d0b0041c0d5040e41c8294403100020300c6403812110410701e4480442d40902005940c0c01151000030343e0144c2d116864542407900d04685446402030302c503810341c600c0020b000154014400d20400c05a00000390b00780100d0401c55071401c8001990030300c10f84070b03050f2a21040c42a20507401c48c00f41140c21100d107030600d2098070a110785841414203420442d020b41d519522111101410350345980a45240048200046011410080014051180141e01c0090f03283e1441c00041d5120710300e091185076039400030042c00194a003e114075505408035080c0b0700c07102071303031200c10505c1400700905610030740d2404113203031901c86920b0301100c0d55154480030100c820011450000c0d0b8982050710300358000303510f040640d4109041200c5103400a900104208607655400800721501c500b801040400c1000c000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 537190359 1250 537189109 537189143
    0xc12050903180d0c0e1b0c0309100504090c050417030901210609020706090209060a031e0204110705070e13030c08070201090b040b0903101a0d0507080a05010b040b041b0c 75
    0x4085002d0080504444a54148910070300421ba600310550082008100100b0048a6000081b5010b070041550304a00007072121805640d14011355104002040c103220000420070b030b00c500108151583c19402c0712139005c0d1080800d03070b2805070340d000303d02184136100d400000c0305911505403081d60300100c0106500380c8803049002641c1140c42c04507401911843e0030300851614134001036000e0820340d0011703051407a5840e81c1180d2410941c1e03188002000785681410754469800c2030004070341d484019035481e40303540b4060340e444c0c3d040d228009103900d560300451101c0703122a1110140d60307050740c0d8002e410401525801203d510240d001c82c10f000450000148401700800a4070051509500301d030303122200303102814149510303507451094151031300c0c3c49213980100c070400d950000102541d080403c0343e49840c10a14040e03498200200340d00c121889801002015001f00b01e406805980901807842c0c04020300042d00c420701c8100080e4011000e1420b000c0d446900c240410f0750007600d4450340d1035152 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 537191609 1250 537190359 537190373
    0x203241f21150207030906180b0703020c12010b01020c04021b0633010903200909010f1a01090e0c0403020d1a07110c010c0212010c02010c12050903180d 67
    0x9007008222114841da6001c0900000009941c0d550074401402d5260442513600149649032030300802d001e00c03500d00f08140b50807100e0301100000e0100c1d200490354030713141810081d43d00c80004010034803901035403030300e0b407415101030080b5158400b040e00142410031000080101940058002c0c84400b8800c2001c0c40043d01d0400013180031f0201a00d500c02080049001c1026190301b18010502c004220411400e031a42c3c04440c41044a0b04254001ea034120f28450003200003001c8031b00564800707904824064810410b500c000221040380780c040100300c40d0703903041e01480c3c0b201441c160b000c2200c7e5202000b8502c107480c04190311042c202c3e00c03140b0f010b480764009046070b0300c02c12040c0c0384c16243d006860105d03505401090f4001e480d80c2410040640e4007030400e0740c0c13071000c05a141e0400c02d14902da5000c540311121140e66040c00c0d040280034140b2618402802044201580d4000805104c0740225030b00b00362252500600c42c100180d440c0c011007a207264011250040b910f038002e81001e0941012a0300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 537192859 1250 537191609 537191639
    0x1203090a1511012702130507030f06050a1508070212040308040f090b0307090b2b060c050307080103030c1502120a0f0c0c020f010306030503030c03040203241f 70
    0x20740002005824402400500d40c1c0140410216240c0c0350036030301c00c6030790802d030190034201001030581c1181464920108082d4482800c042210a062005010840d81c060f002101081c031126400c0103841d41e200201b0140e0012442114040d80e00720001d0b81e41907125006903a800301c00390040303900106d0342c507102c25030651090344141c0701240c02060502c034058807107100d0030044c50034800a020920103100025141c0d803851281e0034107103644d12900003080d203c102100710703d504500c1140c540c0f0303600381c0e10700042c45038050760403a041c51a001003050064090300903039005170030540e00d0180c0ca1782540d400740d6240815400640d040d440d00310100c2d225001500007400c00005200401d04181890014070b020346000c0d41c45552428109203c20400e03d80c04440d800c8110380441d88001e03101c40f0500117a0041074250000740042c04004100584004420300450065100740d0849843c82400c2924500b10100704030030040b1100f00f08041211640a004512000788101443c180301c5030350b403d000c030b00c0000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 537194109 1250 537192859 537192869
    0x30203070b07110907051b0115030c180c09090c020a020d2f0d1104110703021b010806090f0a0b06160201090504020f09010c0807120909051f051203090a 67
    0x1400a0018100210240d03c035500e1001980c08003824201108003911b540960b03a02146040010070140000441c00d400041c082c40c00540902d80040d101c0c105500d4203009401864040301402100d100681d0b49446080d0b00c404007556415165418581e00034094101447c0d03c504610581d2000c10140c5d40344c00390b050384180300f442006900c550764503e40c0e81c2072501500501d032142003604456402c1e00e80030000c5078000e41c4000381280702d06007a40001c2c018000290340c00303400b102c0443d24108140d00000d036030074001c00c441d032400a5500000011502e2140031a82c0c590400320300340102b07001c0e0f4651400c46030403660003907002c10405600f6010074440d800c10480e0300d000070050703040b00040d541c0000310080540f209036419440c003030082c101c100b43e07403080000081c100460101d0a400780210041543c10312a8805480051240302443c02422645c07a805211411440c2002281c0c0c0d4000214039071050301d000e190407000b00c0e0328141c20172654651510050070306010400c15102c4a41d200c010b0342d40500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 537195359 1250 537194109 537194129
    0x40312020708031b0d0215151f050714060106020309041a040905100e0a0b06090705040807090b01030b0316140f0301020c0106080c0a060e10090314060106030b010219080d0603020307 80
    0x407060f4140c1442c5c03080002030b00d025034201000c03e0821120400f04564440c240d180681902c03411013005c2210b00c070202e1004002c1d1400080060015070740107008104c42d80c0504589030a500ca02c89820b42c64039000c3c030580c0090307482000058040d08082d0803501d10242c443c41c010308042c4000022406882c107010302200c0a402c0360440c01029007907441001240c55080b4020282c0c3c50141d43c0d1001001e00141500b0721400748200000c010901c0f6100312006080350000703581480b03564174042801380c0320441209000c01c2c00c20503002c2141c280010240104104802180e07156403412401d00140641840b015812100b034002d51a01030b1003d00080c4404400000005041450510003c0c10b040866481604c11103a50100700003481d4010300e40220380344111000708205e00400c1050b5407080c81c6500041107200032030b41402e801100400c149048403180d0302c00780240401c107001240c0320008156000c1c40c060301d0380312950214048001501000014500018100780c40f500064030309901507029408103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 537196609 1250 537195359 537195397
    0x40201120e100c030606050f03041407080a0507031a07020d030f06050d03050301050f06070b0103060b1306031112210d0207050a0503032a091905041e05100b04031202070803 76
    0x3c142e0501c6500c0040203540b50940c140f1001c0510000c0e0b42c800548050001e60070840700101e449811701c101e400900141040343c40b540e40c2c504e0302e581c440d03207548819a03800604489401c0d0b510040c035500c40c4038090980c0035040c10911850f090380244408800311550558540c000f141c1926001e0520034603a000e41c0718103850350324240801c14500c6d003c0c8030042c090b00382800780070000381d22818504d05403a80070001013140c048010128600c0c40d030852082d00900d00b052000418082c0300340030586003010540740c49070340c41044000745079503025001c0540a179804a00030b8504460b00b00014100070360302114098948601e0f621031600d40248200e00341c59903003000041c011407485076101d00515083c05d1001c0f0f04044000c060465060140425050090f072461411000b450303c083c0c5445c0c09810000c000700f010001e454081c00b542d5010316101c0404610301800315500c48184410001150301c10719500c2e2905040d0350305c02d00618049014007003035110300c4c4400300743c52600380f010b44250000c07004031601c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 537197859 1250 537196609 537196631
    0xd0903060509120a050a0c0b0c040e060910212109140f090601170a0204090c0302160206090307090606230c060411060c1f0b090708040201120e10 64
    0xc4400140804680d0f601101000311101540c03010b9030f80032540b50426a4603031034402c0003034521204641000b800c034a034000c100804407040b140600280c6951800c0f40715159100c5017441041e1100350761410b0620740c810300400100c0e111000300380d0b0113071320401c0c25500d90039140d03607030111003404051030041c00007000f0741c60740401c1c0c0c801454402400700b0384a1a00c40c030b55040100340718000e01e40c0094000c4c1050000181d543e409071920421880401808040320b19102140318000e4000f8000c1e032410350706042d6041034040c428000d079081c17010018282c0e00d0401d2654204101c5a200d00c9015805008071b641c00034100c210362040c500200f0103502c50340b003150480d68220300352070040d056910b84068144800c040e112000541c042e40103502203c1912503140f40c1002802ea4020584070106034480c2c1e11a0403085e4200c10500446101110401d2281c908000300b088034805080740d01c10f0000e9800000140598407641c01c1e12000d0401d94400105040355007112401c10300101c00503a503440e16107001d41390b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 537199109 1250 537197859 537197861
    0xf110c07060315030b22140a03030b06070215162f010c080a08070207050301060b1308010c02030f0d02131410020304080705010e060904180510110702120c030d090306 73
    0x120a844103030003100090f0656030340d10201c07400941b6101114900d5140456500381030142482c1c0590400100a0558801d02505a030351030b80701422000242841d14800e201d050190990781400ea004282040c120f41d0b8141c8103015030048a85040402041108000820311904a0a624080c4081440d25900d203100020000f000c0c0303010003034108604030035500c0100d014441030380c100c138103145002103403519681d408a2519809800081c2e05503c0c291000580030000c20082002444003401c010034030355a04030050072140700300c3c4d0030300260304204020f0600c0c11503040240405413401100508054030b0f82c01d885884103858008944500d540390005145140c060400c080e11400c4d84000c5180c9800e001d59540c40e000701d882414148101d100341c0c0c001c00d075a080c041d141d0750f00c00948108083c1070095070301c601e8400652030a8a0a000d0400002841c031168010b5012215040148902e018002e5086c412225001c00c4010407c1c090409180324598007840b11940e2203042d60b8421303d0b060b046080880c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 537200359 1250 537199109 537199121
    0x21030103031403060a12020a0510020115150503040b0705040906140913020a060e0307090212060109060201020906030601201c120629040e010b040e0f13060f110c070603 74
    0x34007200b000e10800c626583c50019243c2504d07904003080f2070300000740c404141c0b070b18215080268040481042c2000d81b070741c1584a8a9102d024880700000183d40b0b204030090310402004440000d042000000e010030310b44220705400c03521760315200c1d2070030303a480011104640c481e03001611042114100b2814514290a00c1c94210211401a044c522201c0c1e000400110440c420802800145040703000d43e030342e0500895000b01244c7e60150b54a44001c44030922907602151540c0c0803030201da03808940f1500c1482900d0818802074100307881c5485100040d14500d044801650580203a82c40d4140900410301c11020702044c0d500c1020359007004100058804c409016040110034541002001111174804801741c9860b60700f18806040076408059504610854000c207481b0070140340001203950005008100300c400c03a130000380c450340b01ca28070108015810740c0e00f00203209124649001007241984948500d44105400085441d01c0311417044441c1c000c03120000f01c1d40c104010806c0255054042d007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 537201609 1250 537200359 537200387
    0x50a20100b12060f0a020912010c14040e01050105070c050301020a030f0b0f01080a0f060f030309091103070c1106041505030906090624012307030215070c060207052103010303 77
    0x10b5014081000c407665100004c1181c001e40d030380310003c10f4030b0840d154110b40c284040a8000d0090100307480181c0d028103204000c0c0d0700012144400b981c1c044100006031016100b1703252840100364640001103c13250400ca00c2503030001c0c070b440d40001d001d030f0b02480100402401d41e103020440050000070002200d180d5540a4090712200741203415503a403000505e603200030350342c1000440b400c8044039040100790070340203c4218403d4090100505030041d40c800112061014113114442c0400c12400c86030200391200c0d000b04010450510004107900b0715100b2280c0060625420700303a0b2101c44010840304414001c0100c1c5d4001709005065030144180d42d0b200c0701038402000141400e0070300100d22003a151144c190f20391180010496688203c41c41e004075844040c03200c0d5005c4108414640950090400314050305c030340810485400c9100802c0c9100312040d884155905000e0b44600b0b003e03502154003120140510851003440c0342c188035000c50042e0104603959102d60540c6409802000d0311814 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 537202859 1250 537201609 537201619
    0x81305030f0423010302191d060a02060a050c09180a090b0106031d1b13061203110f01050f0711031909080d0912120c0204051501030c1707050a20100b 66
    0x4451054410b4071f41e803038130100389180550b500000c034203c19018006402300140d200c000019030324005076001800c0b0b8003607030356004200816103e4a5001019101d0800c2287d00503403100c40c080f8180c440c0c0503c2591000c644113001c21082d54503540c074000004260424408a50350313001c01e0045a028070107049200c0714900052210380e810611203450020311600481c0704200c40c0b090a10221184c5c1c0040009241c1c910101c0c141c0d0044c0d00e00902008044102249644a01f0b0f44d8001552414060240200d00b1030740b04168603214644110b807641c40d140c203840601d03c401c02c0303404440814508616042c1c0e43c03640d5400b10107400e200f016070400e0414080d8204021108405000000d54240c039005c403154024000180e0003403110042d921502134141c0603501070729102c1044860b11101a050307000d40c009076010850742c81481019105945082080800044030328001600ba900420003403800d0b038a00e040401060034080002c0b04040c0c51400250b9441d00a07105d14449001a0b02a8100105040320 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 537204109 1250 537202859 537202867
    0x40b0a081e06190b010c05010c0201020909160e060c0705220518030405010c11030a14010b10080f0603012c06060103020a270f032d0201081305030f0423010302 70
    0x100c03c980c00c3e200c003a50810360340d580c0c0070b55101680645ca0249600e07600800a1101351455000a0300035041b200d00280a01201da00003000d14400e240c051f900c1e001203807030344a40d5117183d001340403103a088100c52054a20801c0c1000c103060381e07503410002200c02c00120303064a02c90040d0302e8000384c0d5006001c0348074540c481580840340311004403d913029940207180071240042c560070309000070025400255010300444900300140001081511540081c00300240300307014035101808081c280840c42400091103000105e00e4900c1170003480e076003018000700040348041c03005803412420234000114050050745d50207080101501800000d9101c90309080840c2400d82000c00903191442094076002d1800810650910302806503010030301038030f001580105000e0300c1e440d2071600e07403003001480e0407a0f60240b4040e0303400407801011102401c1d41070351404501c2e1100752103020200c12211084034640401d00003541548011409032004003468034070a8480580d51030081c42480812500c5810940100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 537205359 1250 537204109 537204121
    0x50d1d040905031c0510060f0c080c030d0b0613170109060c0f020601080718090c0902040803040905060418120e03060f070314040b1b16060203040b0a05160e040b0a081e06 75
    0x101040207c0c1c8003414034004c0028640c034121011642007200405244000c0360f9001c0520000010307088461500508129a03515541003007107900034512048444220318000340311000500051604c1c04114400106108a1940d608400d8461410300c220000b207207216030694080c5e0400c080da0040840d0009850a5410125941e05220700c00c0442800c182c0c60b5400001002041031402008010240d02152101d45500310b403616a40180300c2c0758115420700e00440c003c1e150501c24203c82c00c11134500c0034040c9415a940601c0e9500711140c0c0d1060102411544a60b40c40a0080501c00d0414624441c0070b0300d4a02e8000d000c072001220051b05181c98402040009a8003101c29a040305c04800b04c100b800f100b048070014030744108552003003e1254040c442c030400c10217030055800740703100700c003002c22560b100ca084904880044481d2050703842181112550540980c0041c041e0407000307030000c166a00040d000c1a5003559613800801c443c2e1251301c180801c5800c0807072034610034203960b01520040c00c00d6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 537206609 1250 537205359 537205381
    0x31917100b090d050a020915031e0606190e010f2c04031d031023090a0602090604051f030e010908030f100302030609070f060c050d1d040905031c05 65
    0x7240025003d000100180f10030300c942000700881142c0d005150704410b24100000c5010148190450b600034400c5400303450911030048510b01d0b005131060000e02071176a8000411803803c3e00c2501290480b02c1141003c07401046040e9114041c100e00c00c20303449810b16107a040b43c0000ca14100c0c1c4030300703600031a901c039240f020114400b503007107500b501c0c090384920780e0810b071151000301402c1042d50511072a5070080005540340c0081040035400000b80b078500c0200e00120302c00503000c86100015030409100e9000064035903000c2c000c072080c0a000542040e40b10808610404507001c0007040311120300007001c84460f418000c45230300c206410002c0c44580304c20b40d6106894000035000502c44a07944002852000001c0d01e54401140c00804031009801d160081039180c042c070340100d14402c1200280414428040e01c0400001c5500800034007480c12303c614100c82880c4449603c040e183c0d04c001c0d0800c0305590340c0c0a0350b0304c0c0b030340108082c42d560340c02008880072215412920389078560411081102007859 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 537207859 1250 537206609 537206617
    0x902010509012003042d050919020d060305030711030d0c0803061c08070b070206100b0c0f070609090f110922060e06090702010608060a020c031917100b 67
    0x4282030492880c41680c80d12454100304646a000c148004100081c00403001b21118100e80d01c99918a8140d074120407903034500340307038500559422951a002081825404201e8108110116038005040842c18810403042c1d5940303504c2503034194000700d080c01c1441401c40201220180440c0140380b00030b042d280107000507050980183c0382c0f810100000d50a900c0b003020820540340541e244080182d03603032420b890f180d004848155084074010300010050f900010b0054081c00b5070801101c485403410b182a90158407154240c2140e02941c0c0c20b0b00c030342e420108030100c098540d5848403c441ea08000801c0100c1e01c449802c00c61540c203004e10303010b8a081e6241102c41c03840c42607409a034410f001d100d0761342c108158010350300e0001d403a0000c0081d183c00c0c1c43c59024001c0c2d90842e440e40c400d803a80c10049003a90054010302d0701a401c80c101040e00c6e4011a4020070b00108010166401c011201070800c8610260015010200e56080d07a000928031141049ca5445003d0f8043d01024030f04103010341501e801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 537209109 1250 537207859 537207877
    0x1d190501290c03070803010f0f050d080a0c0203070b0c1501031a0c070b16120506100e010c0b1e0c0f0403030c020612100e0610170a091a100909020105 66
    0x202281e8038103141800c0a0899080030307401c500b1242d03660a141381142055100b440340d04945940070001103070f84401000d111044900041524a00c0d5159460343c3c00c1c1c2d44e1000c0c80060a021081d503c500068071f09200450007803021a41007a194800c0d05070503814401704603112062541640d005100207900080800c2d261200d4900402080d0b40300986203900c3d1081e004d0181072541905c003085922150000442101c07981c5550360062403024030360040030b680c810384610750300c00d12410301e494003e84903143c108400401403500c1783c1011480c0d15000000c100558580f042103d901c0344e4031342100501c1a64680121821030203501d02003810050b18100e0049010082c02c11600051100665a400c01981c0c804440b1180d92001406c00f5254202000354620440da94421078000090051821008460501e44d050316058291011074641140981d001851200480d56072210040441c41d41e01ea45180c8043c1040a0000c50618000d14001100198000d00b1a1410a5141001030764804203a0303207075070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 537210359 1250 537209109 537209159
    0x61006020a06020f160809010f0c110d0618030905041401050a0905061f031410050307030b0402030115030b0708060a06051204030e1c062f0703091d190501 68
    0x8210344181044d24400c0c20f00030b021040d0704040400c18001004c0c01010010426224250204400d038816a0a04002c180c041e000b584001c0503009582060f8954444042c4240c200013100d050060295041c50305201007070340041c605030b5050005003002e2048503004603901d21040f4180d8500300001303501200d00e0180b81d5203151280301003012a00e58001c500d1071541884403680d03401614a40007802040205d440c480c1c40c800004c00714404100103e1520156030000d03000c2c04034a401c41d280c00504c0440038100702c3c1c042d0342c0c2da40710a8400042c02c8244d4040d500c514003420141c244000c00512598026000c030344100000c80341080f150390020b040381c0791841c60255051155071542026600c2c2d4204010f603035001a16004d45104406c0b6241c1c1c2003075414450642000b107100e031449220041c01680c142141d07094a007003000343c04071494802428825100340340c0442c0490b112400058902c1e02d4414000d9415181001d00015617925a1200c400c1060340d0720401280d03142150f078a00074904125604401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 537211609 1250 537210359 537210367
    0xb0303090f0118181b0819020c100501120209010e06031902180c09031207080706090206190519030207031e020a0c0b1908010b0306040b040f0e0d02061006020a0602 72
    0x300483c1c01884000b0305040f8601445800ca080d80a0054a001801412110341c2d850780c03501c1240c0240191401170050381c40c00040043d004954400960021002c003520303200e55404135122040c107006190186c041d011102d11001507030320600101d0318040e0440317808014a20708014840d240001c03050221403250450b1102c42c9458008603120522610311030014804010821003280d110f0390050104500940840b840074200081684060165131801000e4203800c1001c4008030706550010b0311074a00003000d09240003c2c5480d5070340381c0c2502c40040310100b10081101c00c8000e03450ba10744e40c4256183c0c1415881e2011903a402811007440280304a0060ba5a58000152601c02c1140380e480d00d40c845a4210003548451041e0080d230000111100120050b50500011500c6010a103040794034411001c0d00319101d04041001900c07a4510040e000b594503031944090746414041c45a143c05540e010f001d600c41d4a940003820090300074994040412584010001280e00191445443d5080300c401621 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 537212859 1250 537211609 537211637
    0x307031806050d0f09050307030f0f020307150b04230103021009080d030915151701020418201c0f02030603070b13030f12030e16120201020a02130b040b0303090f01 72
    0x142a05d040140c580d12000c0382a10401d50401004444004161516a0f00504681d800c0742d907480380030801004008000801140da82040e004a03580102c000c002288008021840042c088008041a110b180d100b40c010025810483d0303400e00f01600c10b103080140a801d0402d4507580e4001d0501070010580c5c0c030075000080c8007100d0202d814071600d01605228102c3c1b07041c096603103ca040c1c050b00c01c03402009054030408240510890342114680c168031b800c42004403182000402040d1100881005a03240400d91a00d17860002c100c00c58106c4d201c0d42d40f1601c01e2510204581c600321900c0c3e40c4038810400e0003c540c2e800600041281c8141ca51031341e40c1e0000020101e4040260391004250041d00c2c280082001280340c1e80190500c0c2c240c3c0c003002404040080c0540c1c48042e0340f41300903010b84152090102d141c45034969203607a4010700456103200d00c5540800c49a410101c524a0520b5803030001d101240f4260040328200e0034120011401d0514090000340d01c0288880303910b050046103100011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 537214109 1250 537212859 537212861
    0xf1503030f04060c170d091401020928180c080702010603020906040b010e0312030121021503090a0516060306080f070605070f060e0102030a05010e09060f0c13080307031806050d0f 79
    0x208081110215243c1d101c81c0d1081d0007818841f00100c54608140810305046041403085c3d4082d8000206908034400c00f031001c180a4551103100014800e01003240400c44c1e501981044100d0b01c920b0200041040c400034000b0300c02e41000e40b4031005c590510508201503035440101d81e4020404450010380748020b6030050340d004403600c0e08150940103200c0f0301c8400d003010034041c2d4100c0315813159120060004404e415100044410700039806180c0e0608840150803000c05154410601403c03201288540c0c0c0302c49250210000f002020550112000d01c0020783c5030094500401d80d08004001040400b6180780d150b01d454052682005000320300d072020b00c00c1840c102d0300460b4020030104101c40c01140030502070b50080b6510400c4a0402d000054070100c003007101c034403d0b4412009001aa01e41c5c060102960001402d965140141802041545d074044814034009082900055555503c1c40c0343c007600b080e0310450211b200c0c802d030704402c00105402c08202c0c1c0182009890002e0741d0b80d00c000c0064 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 537215359 1250 537214109 537214133
    0x1030204030507300507090906020706020336030405040506031603060f0b0a0e0f090f0712061104150e04021c02090901240e0f090f1503030f04060c 65
    0x40c02c01d11410700005441000c1035040011030542880c145a9040500b000440e040c40d10503006005500a207800c011156603507002010541c0310750009840c092046e122a016a00f05480340b6101c420100c20203441c41c1e20241f0203000b04140c242d80160314403074041e041f40c0c590080703200e280c1c004c42e21400000c03074036502440840340c850f040c8181882003545034180320740207220482400e04503030b10700341100c420351901d40700c81e0044411b1901003811f182e54420486a8039800501b0f8150a8425504110b03007030f4000b40118400303000c1e941e12a0620950a082074025515001c1083c1d00c4400c04120038006510740c0e05142800c1c005070306021681c0c0c45a58082002031050740c0821042000f804210038401c00144c008002c0400102d40e000c403d41d0b02d446180c8a240743c00d900c50030440f418000300f5503e0500502251405040c010054942d00b941c8a01280d82c60740200c814580c2e4100c18010000e4014800107071580c02d450503001541070401800c605901ca11980c05000188680b102440c820880113802c1c607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 537216609 1250 537215359 537215363
    0x2070504180c150306080102040510050a0e0604080c03120a0c02061c02040f05040c03110a1202040308030a051e04030804060e0118080417031305040506010507060e03070303060b090901060e0103020403 88
    0x140d000143d8510120048003407111815002909040c000190408140241d80c00e64100a00d506080242c41c10160781c50f6103d0340e808018040c0e4040140304c1503440001801c0204203c801900c2e0549190003054100020003000f44041241404400941580300d42d030715840c550f0584103e40e42c1d29110340100341c61140300715242c04550000030003203a4400901900300452b04242c1d4140810000008107405444165210081840b0240b0004500d2031281c3c620800744940e0700030051a198403504e81902c4c0e035004503040c400568440d42400b0520040650700c24240e4580d18644001e81400c0d9001400c1c00000750001c1e0800e51070b1041e0b003100400a40c010251781d820284500c0702148145820340341b0f900588608601c0503d0404444c614007008030846032040d003015412401c160500c01000001c1c000580711a040050134002840020180d02c904000309018900640d100d00c044d14005054803459048400d89000a0011201035122030058074103407480b038202440c8680c002001200207006075400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 537217859 1250 537216609 537216623
    0x160305070c0501180b09010203091f14011520061b0d1404031107080307080a020c10030203150a030209161107030b0115051312020102122106030d0207050418 69
    0x1404044206511000c011620412405842d82d4401000500f00d00044501d2907560b00820f4110740c16814994822f00414a014070018000858160f40c3c2c8040100740c018410b004007407035a40b07107003a40281042d1000707094038401000d40124505015107404000d0081d0464140c04903480e4102c0070f141c000d803a2900711484c0100410135105651810400c8c0079107081e804102e84a842d40396040300801e003041030380c400000139890036500d40d075404d009130f1001810340e085006a55000c0c1030741d55007039010f000c850342c0c41e070b0007580320300301649108004001c00c0700c1700e44204240c0d0010030058a856803c0c07640801c0b4000f40285c4211880401d42b80f03010503034071541e1540600407010041141600c16141641d02c0c5540c1201d0440f1070f40c505a03018841e540030809040690042084014610480d42c0c00c80c40c07061050302c0030880c0d80e00c8200c0d01600525003070707030300031030780d80031506800210245035076010004900030810300400c03c9020791a0703401d17409070364080c035100c4054103c981414413032031a6040d40465 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 537219109 1250 537217859 537217871
    0x12031b0f16060b10021c0801050a1221201b040509010b090a270f08030403050d0f23061c03020c0d05030915030403050a0e0d020d0b1e160305070c0501 66
    0x80003512802c4980a0030780121b504c3c605914050701c92110981600d10180c0302442450800d80803001240c032a102c1220780c5868102a1007420350700030b183e00c6038a0103d03120050411756200c200743c50240c00c20707107102040d0300081d03e041080c40002c005441503002600c00164a4032940e0120f4090007a095607243c004c1144001e00400d485981d001070002c00c00a0000e030036001d012504440010440d101c0501040300146228000c628507400840e0441e1181c01d0072403418031089111816101c1d40c0c101564600c0c2d5031204c0c000410000000c1d800d03841c003843c0103d1007a2034910b00245502403422102c440a5100344d100d40b04040c0204904090307010020701088030144c861800c1580c03035000701245400741c02403003600351035222000240c074084d6505444d142d050011007002110025511110594000c007803881c8180585c83d41d281004c00c1c0d030b020710a41039292815004111110030f40000c54081c2045d4403040000354140704620f510480b03903030300d408070391603c45034000c035208460400083c2ca5546011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 537220359 1250 537219109 537219139
    0xa0203010e0c0f0d0b060f1201090503041502060f071206050901030f0203010608190303020306041806062919030b120f1207020d030f02070812031b0f16060b 69
    0x62076500c0304400b1a01294509400014002c008138002e000500044504000c21403528050280b1328000d803007d050f8107010b4815806140c25551900019110b58000060600c641c1e03281070481801900540001c10440c200201c3d40400900010103150411124110030040c840180d00301c94000c0000825000c01941c4a0502c804c0020907408120310a40c81c00500155505022608034038420849035412103011080d1001d0707010394002401c00368400d5595140c03105c0d254880c0084200c4038011711300015680c0c01c10901d6071403a695120943c0d50b410001c05150308071840101100d1303c801040b10030158039040c003107082e00640b01c01d030580c550141100100000d00b05000490070b09400d070f020f040f14641144080d4507071032849007030400780d080080c041810380800d00a18032b6064156a80c03044034032503540d460030281803080695104071030940002c1030240000f402c0e10ba00078800042c0c84c26030b181c0207503020010040d209900307044240322201051041801800c0c1c1c030207480004040d200d0440140d000d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 537221609 1250 537220359 537220363
    0x3130602030c0f06040b041e060c050a0215010f050d0c0e07020a060501060c0804090203070c060516020c030d051b03040503010c08060910081e030904020429070804170a0203010e 78
    0x552600e48603541007903c4800c00041c00c02d0285820070a00d8490751101e44a00301e078566400150711410441e100c441c0000760052042c10319541c030075034655072105144a40282461519001030540b084c00f0401441900c1d05001624200c0b00100c034082c2d80c0020501d410182d8980b1a802850100304150400011035004140454014410f2008024507a2180c01c2a20741ca004c401000e001c0d08010320043c01007480ca40d0040d40c2224040c100500e40380340f29580c410590f08201c5508a00036400d203041618690104a10389503a007003100944001040408000c145005035401310902d0a40c06504541125043c4110307409428040c1c02070100c4011501c001d00075140640c0c0441c01480d9000005450b0744428108505496000004e8901c18208200385420540f1107240103d41d400100f10b01d03041651103100400c0280f484140301040c18004040c40f05410500043c05401c3e201c04100c0c0c0000030310b40038103ca0a5681281e03a420452084025072442d01c0c1c11103600a402d5860115510380c80030b40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 537222859 1250 537221609 537221617
    0x30e040c0f11060f0402040e15010f17280c030507080d080a0e120c010b09150a080d02070614040e07020601050f030304060c170f03010306050f0a090b06120313060203 73
    0x1103032182260789002102d081d80d60041100c81c0d10304041c40c2c1c1c000c900180380603004501c000b011002103801111f1103042400305c1c1e54080e0300912100020030010440440000741094081066402a18110f400c3c042440e51521310403400d01403002210420104004450300920080c50b040011994456200d035000d0380d403103015042843c04540d1142c00524441240e010304d0b107120f240c45010305005e88249008440c1d81c3c1042d54000c2c005e5485064011050f147c0895480c855501d0f5030206240c1c800041c140003c071007842c0c0050a480d0850201c0b40941c1c0d0300010b0800c03c40d0341e40d10b4000c41101090140700c4841c05a90003007406203c180c018898a29400103416068032030443e9500f401c0c0400c401059500d12880c818100410148680400825880710000120a1100324030a1500c403042c807035030403954000d81040310003e586400f88003002d1152400c0d29400f4803159800c010800c09612010300c2c0340d40c010846442075200710f0406070051002d00a60760186c3c00704104090484e103940c000394890304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 537224109 1250 537222859 537222887
    0x302041121100905040809010c2409061107080f070206250c06050c0d031a0312030a150311040905010b060412140106030b070c1109010f030b060301110a0c030e040c 72
    0xc031051003c200f06030244203c80c09035900030794151034042044015130300032480340426a080c4d01000d101c002c00720903090785d000071548082070015020a41c0c0c5032401c202c4440b40080c20701030700c0a111100024046030f0456031510f58038290a81c03650310510000d4034502c6101d9100b5444000490079200b090507c0c80300c0d40d1558030030500c80d034115445a108071014001d41c400035030194400c00416901d180a079000d014400c49200300811140500b8000c01e240100103400f0300c15214000041000c09030480c419503000855441c2800b221520719214440e111340300000240c030840e5181c0f413442c08c0007025881401c525030003400300c43d112075456412003807540c8400170a13a4506d03003552a658804034188161000c1d0f962050001071181c9503d0b20850310800c607007004030307607008420114200d03542d104c01e94517000305440c0c44035002c11400c3d403030107455503003020b0500b5000c1c0e0306110402c03105201d203405882c4509140c1c98144219669824101c0344000d0f41d80c19a80c005280810780340d0792a50011868160207 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 537225359 1250 537224109 537224131
    0x402070807051c050d0b0a08160e1b0708030c13080717060907091517070603060b0901020a24110a0809061b0306060705150a180803010302041121 64
    0x542c045500ba085030700b11030310740f000042e0700f0000030061490781ea014506c50000a41180c025640b00c20505160101c012103800c04600a00c2042140614008242d40c0c440504140e0090005030311f0024a11401003d5009040c520080700213802c012405055034090710402c20344440095480782b00e5519101c0314051031713491058000324181e5200d00000c1982c002c400c1c03000248013162070180d015004021711040c845c0303c03900810740010a066140c65241c44661300e00060500d980c030b041c001400b215120f030300005403410203200c050300d10f80e00410030141ca9600140c0510380a2400d400301900d9000e03c00c848039600b841c00003d0000e441e200c4e4040e111403c1151a2100d0644401c10700700d644110480701c2d02440450450000d590000000280d50001d001400060a020141da00d00e03060010b101c0040000c003804104002840c2e4680c007c03c010011308801c1400c80c3d12241d00c540c10144414007000c2d0181d92101644a10801500111124900b0001d40c45d90303541c02507140d50080c040140c404807103007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 537226609 1250 537225359 537225373
    0x101805010302040302090f04050109050f07060807140a111f02070510200d1b0305042105040e100305010c0909050f070e040914010e070608010f0503060c0d0b040207080705 75
    0x1940680308076004d490b0014601c0c1c0c0d8950b98444481d15000340107008032265522804400d00240041112120410000c0064504c85082c414000d118000040c9618100121400701201039140f030001c1f50303020606490b269081c1d400c0050518981410038600c124103003080c00030550600b13500d031702030030b42e040c0710301e0564103d082811042ca00303544240d0302e04080c0d402031010841c070b2914002c00903c2020a04100403810f901c01c0742030000070b20b02e1009820b0101c2d84031010802080b1100d11040141c42c01d46510000301e050301c1d20000d0003400b85003d1f2000f01c5401501142d07034002e0180081009541c89802030065a000100040c40c88450b44102c0100f113040c41c020600394148100f085104880300d503200031a03c0900c0c1d0412002d86018274050701c2d50210046002c2180c074080c0141c0540e081c40800820080385480c800401d8010160300c842107000007110280225600842d03841d4100e55080300362500e54201c010319400030548a190154400e20004100e4100841c03500903104040c058025038240e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 537227859 1250 537226609 537226619
    0x1312020120130513090b0f040302150406060e04080405010f11030318150a0b1002010c170a09170306190305120f04080f070f0504140621100203040209160c120e1018 72
    0x907c800b9600140560441c0f0440c40501c02c481c80000e40c000d004440c04036030b29558210140c000c03002950103540588000505108030b50b0480d851000c000658a0700b610aa0b28000f8042d4490102074035092170b070480710b15000c0d82090100069111946280301c4289141029a080b0b8000e090458006c1c0c000c1b04806605149907006104030750800381c003a240e1100148200a0922aa030001082118100d43d10150400403070441b1008500504652204582e2410700404115003031a00b0521900500303c040c1c014030000e00b020030340c00e80030700c0a064150b0303c1e501c0d80d054030b042c903009a400021517441007140581c4440800140d1804031040e803207803010b0003501c40c41480b080e10301c4003080090310880314010035030504100341040d054100041d00c03120303c41700c3d0807030542c10300440b00500c150751070700401400150718000c5c17851908aa14192403d10404507400081c027003281209015004600070200009010700452480028010080ca030109980e224007026100c40900c0b010300000224910010035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 537229109 1250 537227859 537227881
    0x150e1006081203040c09051b120114060f0904050a0905030a0305011404020324060409060306021806070203070b03041e0302032d1e0c03031312020120130513090b 71
    0x4080e54008807810b1700705043c130381900040c00c0003030900303c40403654000c0040400d030100c019000c10040c640f0101d21552500c81c400140c403402468091081c4810804040c5104100c800c540c03480e8003e0f0740101d055901c81c1c0041008100441015015020000f900c14450394164080c6041e82c2580300c4000080095109000032800100d882d100c14880414498030b0b420311854055070781a1004120300d19007a12050000c2c00c0e21131603031046504940114142c1d0210802461841c525001a035141e803d041a41c1c00003581c44445202d0406102e00c00000701d02400940540044040c07500041c1e508065500d2400a64980c03040031046480101140c1e10445090106010800c81c14401d00040c2410703008030156a540003c400040900c040410900a428605002941c032501055944038035860050030300c0303d9201c0710200382c8011645010340c0c001446113080160f00c0c5001c241c000c401d4a0b0b0102e103240da159040c49400003907022000c00901c0583c0c0c03002d5040020458442d0705180034a4940e034582074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 537230215 1106 537229109 537229111
    0xf0c0f1205180301181e0605180105090109050c0f0102011b020106031a01080709020304050a0c35030702060a02070b0409020a2a150e1006081203 64
    0x12925a00d0b000d00107044500aa000b800302c4e907201c07600c0e140c03015440c4000810049084080e040340c00c42c406030002c1d03040d034800c00c2000340e4101202204c0c480910041510342c25130911000416000c01805601900350b403083c0205987c030307422001c001914581002c15030440d035852440700074403100024818081055500005596421410925030022008407180c001c01603050041180740b2002480c0303021242d2030900161280c45901d050760400601000240110304000b0010410800b04800351009000105050040c0a0051451007004079621040c86558000380540809070410388000c28900140c1c1c410740301059203c0b42821400d4000707401c0040c03d1a07011907120700c3c4039004510b0310024100d03070041d0302d40c500a1541101d4031002c0803038028040310040420a0300101240c105050100000056500b260b0b13142200b40014501e41c402d030a03452103561520324201d04140304032 = true := by decide +kernel

theorem cover : BRFrame.Cov 537050359 537230215 := by
  have h0 := BRFrame.cov_init 537050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 537050359 ≤ n) (h2 : n < 537230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
