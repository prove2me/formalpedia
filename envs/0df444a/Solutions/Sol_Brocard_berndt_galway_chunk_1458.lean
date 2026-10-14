-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1458
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:05:22.852977+00:00
-- url     : https://prove2.me/submissions/eea4e97a-2d96-48e4-aeb0-7e5e45120c39

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 262050359 ≤ n < 262230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 262051609 1250 262050359 262050361
    0x150103090201051210050307150e03060108064003031508030a0516080c0a0c062d02151501020d0309020a050402070c0b0703050702010e061e030603010e030c071d 71
    0x140c0d8000303044810005082c8080e503030656034405c480c45640942d41c001501403240d42400503011a48180040c1c1422241d074885442030348244c105a80c0b40720a0084880540040020a0305000d02981c190704542034502600e108080d01c5171442e0380c03294003110000c1030100d003440ca00704242d410702c0703490482440d0080100125041083d46542c82c06a01250360134000000f95408070415079506640000768805800d680d12031034210b03e50385038400d0302c0c42242c660081e40070102c1c00b940030303840da00d040c540c0d80d0404640d600103c020901d224031010300340c6000d41c022032640c81c000f82c01491503284a800b1a1a101d540d2807440703400241780c200d000451380205841d00e480200182d541c80e400004441d0110380145c0c955a550400208401032071b44907504a80e03002a4190030550440007402e0041e000b600d50040b446044000c0c00803610400c515103082281d828a00807030804018061904140054000281c020051415a165501a40c0808025400b41004000c295842c440c51000c0301e10f220200c02c21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 262052859 1250 262051609 262051613
    0x50c0601050103050604020909090c04051602030901200a0b010e1608041709030601060c1a09100c0915050d06080706050f0a020a150c0816170402130204080615010309 73
    0x11114180240750402d5110300c08102141e5507501030322503180380242501e40f1400c02c3c9000940e1501d03140f40080c000c609000010f907000010592000c06080d164000e0740c0ba03e03014000450749210054a489103d41102d60507500d400020019145c18502c1200040c1040d41001040c44c42c07900c001f4201c440e188041070720f0164080d0b00890454105034810011a010309502700781c0402030007191a0381d5014412140002a1241e03c090700c680b07410300414a54508034006190341c006d4907021998240c00303074441880c2c9107000341707954420507082445150007440389450b84e401004900802c441c150000d00046900e000c0341d022407041d603005001c00c000401c1500e2034000080c200e402000e6202c0781030304021444445190080c000594420f42c0820038109140091305614002e020314200c900005030381b000000d025030020b00001a42d4000c9481e400594002c0410310300c2a550014400c9803c0352004250071400340540c0050300241074213001601007031a00042c0049001d1103101c40c241014206415840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 262054109 1250 262052859 262052863
    0x2303060c0a170c072112020a0516020406091113090902030705090a2714160b0a0e0418140a020a0608060402190806040b06030f060d1a04110907050c 65
    0x54103502c108146402a603500807401c460b809076100160052550444400d04480241001d01803880039407500a0f40307951844044040f401103680110201d2401c2016241d4000c00340c0409250750710003000810360755156607011b0141d849800500c0e5100c140440c0f250100d0401e40b0071000600110002000f40401540010780e0311422482150700800d10800840c00303151060b0001e596105500f0158483c40c42d9aa10310305503c85c1110341030314040c2d05213188081c1d0020226020521408450b90122642d080c41d8510b02690303c94050340003806099100c08d8915111801441c5028540401511910b031440c11b000d80d80d03906c3d0f61020b155541040025100607540e004124040d0b82d0a403030b01158541d644008070300203104444101c00700b0006a012030b66400c0d8071401c03d40c85a5000d40c2c0600c61740c7c241c601031004500055890348520180e2100080304d030708215540100c0701e4050602d8891204010305100d5146c2c1e825602501e49210b07180310001c25061800441da0800030510b001c51424600303480b019 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 262055359 1250 262054109 262054127
    0x30c030606130f0b0307110c130c09050301060f0f0510170a0b0d0c14040e0a02060c071e0602010612020f04111b0c090105030304030203190305042303060c0a 69
    0x91140d90081120b01c941d000801c4800090600d640300c00100715120300040c600742d00300720384c0d01c4001000c020b1861121480461102c2200d1300162141641511040101010701190032701032003000920900022190313000d002e50f070300506160406078901410441d842045240b1508283e0040044800034140070398080d0716440d950700c600f200c1c403a083c1c0f04c4600d0940603208002c11141e2003009440c83e00d00f407100c0a900d050455100342c00308003601001c0024442034800d988491030140e00280412005400d1003001170035000302003025a0003043d2285444002d10414000000c0c43c440c0c045c00503c40c01350248200409000900d01e41c1c0e0a400003580002c0140a00c000064062070b01c854804401192500c05e0320b00348103800c00c01e40d0503101c103a014996114045003842c0d00c074001400002405003000320448040d04d130054003801103c10040078034108042101407c408120040000103030074410399855603130a800321908a40d48071800390415140ca40040c00058808a04108481200da0020301c22 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 262056609 1250 262055359 262055371
    0x90315040804030f1a0903180901050f0103020f13080a0308010902120a0b1f0f0905120d0813080406030902091e01050f030f100b10020105010f0b09130f051b030c03 72
    0x212000303505072410b2221004407405d03100d04840003005121809901001920000d1600444070f03800b010064100300d0750890a1140d9504185002042c80341035120760010145803001040799441d049018082d400c03034040c40da21940c03035900200d0791038040540c4000d4603801406406401d41c01d001810442081c0b00b0009000ca2118a5031200c1255143c3c071081390f051a69030b00b001c0f0042150b400000e007d1b001e840700d052200000b5001c01400301e22441d100800809041102d801400300b012603001c25294018040d01c0c42200980f140d03801d2000401030300042000d4031540c1d4000c82c10100c98414408880009400d15149800362001002c18521b0703514501e0440302c08440c000d11020407200400d003031401014086101b4050011165210440c0ba00000340b860b030103980d803888058014004a089030000c1c040e10398400041c010030011204080d01402800038028000e500b0003640741c0160080b1440c03c91140309181e21102040001458038401900e0507041c000034510b9032401c098648510300c001024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 262057859 1250 262056609 262056623
    0x10081b0f041715011e0e0c0a03020306150301030c090f020901020a080f1606020a08011a16030e03010504050c0103050c182701091e02040302100e04110f09031504080403 74
    0x28851150810040400c40c456000310f40300703195071110000e003c001a40103210700c142c12900400200d560729465040d2040340d101041c141400c4114404030040d5202030400c0e60b10132841c800b08810070403844004c500a40c0310707040f0011010320f800d0004003550a40702e0042803044c414081340180741d80100f84c020005600602c0e1707591306c1d80c4d46021480c0f103020708841c0b001200d04070b40c003210402100c0e0340280f1855144e074465103810f81c0c1e55402d01c9100c0340c00704507020482d02e09110780e9400c0f00040c030344005018402d0400d6862600392101003400c50f1000c03602515154850100d411107540c01d88034050f00161464156860f140c400c501e808585035a2004542c095104204404000c01c05284440800c1c8501d0840400d5940c0d40d0000802602096060780c0c1ea15284041140403201e40f131086404595016100110031441488240d409820030000c03290460303240c3c1040036094407030b100240300c3c114091070b10940b58040d05007894074081046888822280a60040c080802e0910040e40c08807540008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 262059109 1250 262057859 262057889
    0x4050a020d03030e07090e011b0525060516031b17090a05010c0503010608010e040b040f03210c390302010905070e070314060a090905030910081b0f04 66
    0x303011801040003498213503103030285070400b085200c440e03084501d010024200034000f62034840c514040c007040801c11907011031420024080003039120440c210054a06001581c441c4140340c03611825030f50304590001d03480e095012150030f01501403041580844d04000040c42c4000da2081c040c0061500c41c01e540d1051080d14000b03918140200030810701c050703002c0001c2c030009603454400381054000b1300901011a1484001203400d941001c2203600c5a45c0000e5299803546a50b1903024012039504019020807200400700845420300340d8204032a50a604c1000540d4420910010030404410f14503016011011052840b8100c10785c544208031074803200ca04580d45c3c910f2030180d00403c02e81e0b10041090041e000005844880200d449105000c15102070148441a0030310050644040359000c1e403103d0424428070017510303070780d0103054414411000c46e031511082c00d00103001504800700500000340c80108000002e0075894248205800380c803080d9080141c40000c000290085016074080007003005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 262060359 1250 262059109 262059113
    0x2202220f0b010e1c140a1a040c030303051e180f06060607060b0316030507140414040312020c01050408030618041208061f1d010c0201020601050d050309150a1704050a020d 75
    0x801002650300142006030b4015810300f05480b0301706c040301074800403280400c84440ba410044041d10896200851188041c2156821b4005200203007402c80c11482d403840d01110501400402d5010744285911125150710a40c181c51030441c2c0380c0c584545a8020000744500d64482c182511807a41d400100070850985000c00709151081142e12010345e04440640002400004144501513910640010b024202540c0900c400c0e1003c083c00580f40505031000280401d2080038640188001c03628054580440b401e912802c0d10010b0301c05a41849000050098600e070080c800a02c04c4160f00310014545080d071116400c0c1d81007100150b051210082c0090504d942d600f070901d51442c0b90740303c0010702c44034440000b40300064654070461640c80010b04103040d5170251028850703290b8140d0051105a0a041c24080100b41040045440c3e1009002d81d48990380c0d41c0c240b0080c4e801e4901c0d90581c4424145000801c10100010141c101c490644180008200302294108030070303805645c0000500b03031078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 262061609 1250 262060359 262060399
    0x90103020d020f0603040f03021908070308060301061a040816081209010c0f031805061305010c08040506030708041b030c0e04050c090712060f0e2202220f0b010e 71
    0x4500f809034480400020442004138444000b40c040307000b0340c02c44008141142090740d0f0000414005450a0710a000700310000741b0905885a000e00b01500110b131813079445006605000902101000100001c6402c0c4903201041050344030b02c242545450b281e00f458042e910b40c480c0c100300100c0440c00d50010b5408016400344100c0034042d83e11a82041039841da41c14018960310707501031003c4c0211000e2034009100d00d00407080c4c55114030314001c40340c0040c0c644801500e4500c90440308461031601480300041d5541c61b0000383d40b00e48101e4a0740d02062905c0d02e00030781e1541c284501503a107485031440910104840c1c0d8a1141981ca1500e20b81049031910708066190000d48180940e00c210160100840309a02c41c101a400e01c0a8400c10701425417a14968068a02d20b1301072800708a8400c40000c40d0810600081c0c454111088807600140c030168000c03450103074080101111001f4109848918200c0301c0c49160a001031a0008002080c01c580000340b0242c624101036101e96826003c0005032042 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 262062859 1250 262061609 262061629
    0xf0f1a0a140c120711100804082203080406050a0813051b010c02040c02010f0c090e06010f09031e02100309030206070320040801052a0901121d0703150b090103020d02 73
    0x84040c3c025252409441d10164071403004081c0d500601e0b12041e65a1201d001d01c0b8114040c17684082107d0a19080c241ca2507040b61035845e0705042d0402a440002c08560250000d10140100b079452590390320040d20058014040901342c0070600c0000d4000001180e400308134084105200e04084002c4044180100c84c440007404020394000c0c60148415040e40d01540300607480d0b0344030402444040a182d0b401d4510032914840c2001c001d14440000784698032600081d5003194407400c000260b43d8482e11742011510283c98051103080120f42c4010951801c1142209500303001c0c40c05100072100ca40d0000d48444010b04a0006d241e11a12603a0091385641c01c0c2d0708070500d103685100c1d00d45585100040c0038110030b17a41c98546510091206900c1454410340d8020020104030b090302d824811401103494804510b511140f07903507a403141c1002140ba100d814015284600000c141c0981035007048a140e03105612280111890f100210b84a40c4480b07044c181166012a4515400741036400410b800c100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 262064109 1250 262062859 262062883
    0x60311040e070f031d060a0513021e0d0c060206060108060406060f0806010504080d03020d0e030c030a0e06040905040f0501050901061518030f0804080c0312220f0f1a0a140c 76
    0x400174024100c0c220005081031080403159170510660710740c2c07041801a81e80d166030183d000740f0060503c070340c2840e54500b0078100c9070014289202c0d010301501d50002000e0541c00040051f00420b0602090b580d0100002d41c003d1030031601003061a1400c0c0e40038104420800411042c00000c00020f80d95a02a0301035400609002040e10208440020028001e51060910311501845c03c0c420004186d03002098401c448490001140b502d24614001e9a0200700f0074510b40c1e01200801001c203200f0030a0090034007442c8985c1c164545900c1c5c0e031400c603003541c078014480304d07540c1e1514008100365103503600841c0300c051450402c88111100704100c0c0c0c94460b92504058042010440f0000c100700d00c00c002801122841000e41e1240d02040c42055150864042c0e04246040c0c01d0001082072101d40c0d03c5400041035010700009055038824a003500c508a0781d10542c500c11030703000f04000a04004518414620310324032241c1c03400315082d03009800204400c000e01300d89140400c0350415802c04101250400d6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 262065359 1250 262064109 262064141
    0x1110a0b010f17030903030306150903010c05031608040209011203020114090f1b060403140a140c040b01080c0307031e0501031b080d0917031c0204060311040e070f03 73
    0x9a19441c01d074100380010320030070f14001048060185020400b0040c1c40781c190000740954510b0f140d6100308040d41a80d540c2c0032040d84010880c400c1d481d5400d00c101480810181c072096160301d40045003298000034001d04106010255040000507a610301a060640314004110a064521810304034010043c903401c920007000d4607800d1001c01000040c0c020174054210301255495034442c1d260712b203540f498204468002d40c1c20710003800000c0b544118103402d249140100c0300c020180307469044080581c140f80350440e81203000380c200700341000c0c0a50300702124282484110fa08120016441511000b441c0d1002c140e560718402d1980500000080c080600c018030900072942c40e410074000c0100d1072800038028a04032900003900c20030228118081e1001c2d034542e4407440707203081d110011010520b099a02c5501042214136a03612021403c2c120691110344016112030401c0d401800711054581a0104041c040c00108044040700c0141c641c003140720700d0054096108500142e001e413544200c40401e030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 262066609 1250 262065359 262065361
    0x1050a0201020705160302151c0c030f090c0501090f06021b010908070b0306270406110408010903080109112817190606030b060906160b09060f0106021b01110a0b 71
    0x340c1c807245c0b91203041c0c174000c998843c081c10b000070200000d403007820094550092019102084180c3c503600000c81c99116007400304503080c1c440e000008880012008940c0013512050500065a100742060040c0c020300e151080381508103400650f07602c456016110729800301094034109648201d148500400030702e02110012500e80300708506c01d4004492450003180007100040010303260f43c0c030411603107070762009031400341d102d079140c08005e40a20999499144410000021480024443c80c50110b0107986c0303061041d41080d4400c419980781903200e400c00c51f4180f04042c003404036880407010a0140280c5980034111a51054038201c0d00c1c40600d00ba1031050000b00001c029840d10301e1114001c0340b40b0102b24803525050198112405101c3d1250058400c0c00042c5090400c48003c1140180c2c0064039a08240942d5900002d201e0449151742d19030401d8052000d0500f072840c4007800360603240081c00c400341e440c0c500c04094600010803d81004854043c4c420607200038010042680e412030016806 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 262067859 1250 262066609 262066633
    0x212011203050f0f0a08282c0f060903041508250504080c060301060e011803050d0c02091006140c100c090326120c09131a27060a080313051e030c01050a0201020705 72
    0x9c03000785900d40a0306004010004082c19804011107094501300b1220f07036171560290804568101c0d0003003068010080482614080212070a0b40ca03008500d241d988076a9207003080c101e42d080c020342200c96070043c90103000500c682d41d00110f007080f400e0030a00e0f1050b83c102020048046001c52940b0241940c050201c003100b00da980502143c1105000380c81118a50702d8101d0083c41c0c038a505d02c01c110010301d40300042000700607400010300180701018215801d1203000f55032002203880e03e406000202d40c1c02641041041991f000901100940381e00c048241801102d032160644a203814a036201e54003c00000e407070140d0f103c150703104d6a4014010491138140100c98800600d503d400e6004190108043d0843e42c0c0b80079030104402154034a02d0605c110f00d903030300c80001094058481a0700040110021420308070070009845840d1084520112035441c01d003d0089106103000004645840c40d1100b80b1036482c0000c000d0f0000000786492680c03046131110883c02401100c400903c80d0050f00d0450103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 262069109 1250 262067859 262067863
    0x60e030315180411042007030216061209140607030608060108120d05091507031e0605060a080405010b0d0f05100212011203050f0f0a08282c 62
    0x445403402004240c4815100c1c0104204061044145800c600e00000001c0015042d414012039503c1c0c082d01c0031441e454108000c50440e400d0010f030540a00c4041410414158108100b80d214001040c17600501d6082180c0103042001e5109468a403644803500c071400c2202020803110003020441c2541d46074141140000e0140c51a0312a55446105400c0081380c1601c0201e40c1c0e525200100106518224980c0003802c080c01004203540d009009886238400031254480140703202e600144c6e00004d6862010940c0c81c0c039070b4618000c918050389051800e120f16118501100d225491506041405544501c1c0c054050f00c11141c1860f00500744c010500d00f0048440203d12070309100e030341502d40400210004404078083c00b0a0409040001401000400d411150503a1114024034046103041c0b0320f002e00380c0c4d843e402000401c004103c00184030890070741c00340c031098104415010021820140c0a44540304100b10123040b280c1d15030703c80010f091602070341c102050000348490690302200a034010b540d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 262070359 1250 262069109 262069111
    0x715050d020a1d030118030e0301022109060a051006032a0f03050109090206030117011b0509010318020618040608070905010302191d09030c0f0c030c0301140a0216060e0303 76
    0xf000c4010390301c0206000c1ca0706000d41a150308525075000210200340d1011100c02c49540807071030301035608002c00700c448003500c1d8034000283c1024440c3c00c413505088080030b1400c02c00508801c4054a08001d0000080720391480c0011980b0918002c1749c0100803d441c481001c0070159800c004018624001e02c60f15008002840a83c801e07407000c004580e69514584252490408000e5120700200010301915542071713804104000e1010000820101c199022561003101d091010003003900420341100f19030707040c01030f03a0200c003445000c4c02019009901107200c13070203482d80810300d000344182c1d030085940303482e4001801807000387d0817075044039a83c150060080c0350a0105900036481d40c040408050b55a4031400112000c058a41b4401405a2032030490610060850076a80c0000c00040b029010b042000101800c0544058128100c071541003501d130044003d103181c0207904001000300600d8000702072035440031451030003581e10106000d03901e11030610288020486442c2155620810300000055 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 262071609 1250 262070359 262070387
    0x312031b0e040f0e070b0a050d090f02040e0c0f10031104030803010e0c04030807020f040603020d12032007060515030a0606050108070e06070318121103010506010c050715050d020a 79
    0x1c2120340c284807000340035100c260424418541c08444204042015000108101c207e24500603040603111080542514490b08095981a100d0820001075107000d1040b101d0b910405001040c040b00c0f008040380c3c014001e0402c140c403428440c4c1100f1440360003600034080708070295860640c3d6039107a181c410000e0b0000e0040950901c0380d0000141004c00030300403074080d240c20400b20f9080030002d074204540048a044141d412903200c000000050302c03800344070030000d4130031210509846240c10740182103816040561a84004600c1c8024026903048121814103030082c402152550b21450654611800952203039018402e8951031000c0c4440d0390b00c01c00a0319803d9840000585410104660303183e1000c04065028100304002000240140a036659645c02d241810740715980c2e030300b01c400480c5030400083e2200300c107550090081c6d140038829154003000908100c2181030103515031560303031790042c01000fa014807110520780c0c8440c0203a055500c00b05607040b0640d0384481d081c400400740072005c551 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 262072859 1250 262071609 262071611
    0xa090c090204060c05160b0d05040501180602091005030c0405040902060702120604030f0c0308010603150810020405030c120304061d090a0605090603070b030703020d1d0d0908010c02070312031b0e04 87
    0x46e0419803454607030031004441c0d9048409092803110100700c402010090800c4910b5903a480602c1c0c4078030401017034161660b004400060719200f151041c03084022411281500300103041003000a040c59031019642504c1c029980003c11100c03d2000c14403030300c982500607600c85620b0850300e0044000240942c826446035070740c0a8007010801c816504000c0880d40140865090001444511300c00ea00026440d003454600303404a41c1e548109c642054803020b12440643e400150900282c101040381340d10420050381e4410481e4160011252280614014041000751040480014043c1e1a00e00501c0300700c01810680741c2c2c10110100da000745020300c60f0386e0164480e40006115442c2c04a0030b14100d940c06502d5a00d5580e42c207008034020760203024040045a9155504080725082c04100503c01d0040300061074240000d00b80a003042030f0301e9000440c640e0401d01140314107a4089000000c0300c0e402031040c25141c01c01c030016409801d40440b040500041244440c01240d03104540807440001510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 262074109 1250 262072859 262072873
    0x12010807060302041208090117091e070b0708130b0d0624020a06110d110c01060f03050a0201050310050d060f1802030705060a0504030507091505010f080a090c090204060c05 76
    0x200a900f03a004501c95411000c0b103040ca2500450840070080c0300c100c80c145464500b40008000e0400c0d5000181d55545066000c7d043c10b0302e04020030143d0005040d0b4860080c145185440340405803031042a02c014180d03880840c01240d10401c05030030078050034007080080d0f2101801c3c42140b00030407061056900300100038080c44070346000c0060003541c17440554003808203211141c403014080c104c10746ca02c8640100420a00d46900348070b1040301450440078112603520480d240300f160a4070129001103048444417682000058000503204d0300c40766080c03c080c3d469031755259504031031000640c801500001208004820031045a200c03400c00000e0384400c2129403107210580046480910000b505540422821f01c51450721001808031a00700f03140c036a240c15203ea4540d402c03c0d1899004030080c030340354907200300200c0e003403019400600301c2840c128130001c144407002422080090b04088030150b03121060400d1001460b83c420291151040a66031240e4460006015001a00c1d040d40d503801109 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 262075359 1250 262074109 262074119
    0x20607030203040f021905040903080f1015030f0f0603140d1d0f030109060903020d02060105041407030c030906020f070314040b0912190309050310060e150d020612010807 75
    0x442600d0207550030044c00780150702580e0a000d214044a2801c802158000e9000600350340d0764028020040d209541e00902c600780180e44c4050100041c200400742480400284149041d0f442040c800c12014580418401d8404071544001d0003107107405c4132900d04007100442401400c2c003201c2008040c200c1201c0202449d050304039040455074035070702080500c1c2c030031141e0031340b500f02d032001c040c0c91000b000018580c18950f22002280e00210080f005600030007a20006190180089801040207903020b200410781003c8100250741c0c000c1c561010b04d03544105030240c2078442e80c007048130305500c094115070b22041030304501e06035008900200c0c009402e900040c001a1841e2003503c040b82c070741842c803504115414080200c400d0a21080c602c40348901d041c18000c000c9141c3d1313564482806900c41d002124144000d0605100b01d44500c1000309040600411007159075034400303903021030304010b1030300500c11010014400e00491000030358002008a03212a4800c40041300a040b034502c5002c40d1602c566803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 262076609 1250 262075359 262075361
    0x3120201050405070510050d0e070f08190b04052406041a0a03110d05120403030e0102010903021c0c140c0406050102060405070501180801050a0b030d0207081c02010e060403020c0102060703 83
    0x1202d0007403140d00542c4040003a42400006125400c03003d050450070a110301011008448a02415066680c0328500c10010104990f09080140c0300a8001e44942e814815101c0740e10074800e40005d1009080e1000501481002d200b50425040c1404c030714000e4008400700c9480800080d02c0f9244202d1425841d48641c1031a111210603030745001d40348290451960300c070700341400100d10709950842e02a001400000d401840145c64007803858582980351400e50600800f030880040440b4150fa03d0080c054010a4000400380c109102c26481002c0e12482540222240d141c400c100819820a003601d83c15001c4011840c00d94800d01650f0070000d5550b80d2004981c1c0d4007080d07070040d2164004410a10007175110300c0e0600312049003184c1070490355659001480c01c4500845014800320340d41c0040c0605441c0034410b61090004501c000d000d1142040c004580301c1554407084810b0913a0040884031560003074205000c1000c03040d0907140369140604002e034903101c640102c07500601440c00060a0140a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 262077859 1250 262076609 262076611
    0x303020f0706020604080f04050a030605090c04021228020d1407020105010f0618050d1a0c04080c01030902031504080a081608040807050c06041d0105060703080c13030c03030302040312020105 84
    0x2c5900401081c0c44a07145c2d040c495000c0c2034001c0905404100100311600e0382c403c6100118810000000c080c035041407694100483c00c01c0c903d101d5801007020802c03e240f0020070030303042480300b8554180d038440000c14010343c1c400714a082242d6800481c12000d14045548040e000d0340e2900074440455903850402c03802c840003401070000d110301d403201c240046841503000d41c5401400000d00725a244d01c1e400007030f40c8814404000c8404812541c03413800b510440a00f031503004024a4103003424a41030140703280c0c0718400880ca46040581d02c0c0000004d6540811402e044420501980000790501c2d080a51140c1c0c8001c6130000880c81805c0421010109000c80481451540e070350910301c0d49996561503074641c0085010343d114401c0c00003000e0030341d4460f001400205a00c0d81042202d00c0071034881c5500b2041684118070a40080c0071640120360407203c160f911110030040d01e03907a20000400c9a854690070340029101c005189004002c26400d0750050099a02070b61a8031103600751800100d0907104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 262079109 1250 262077859 262077869
    0xa02071701021e31031a1510020d0318020d2607030f050304020117090d020d0905030a02041806140708010e100915091104060e0105030f150d0210090303020f07 70
    0x104010f00c01e5030064000c20b8035406291120700c00d41c0e961b03841c2c0d0400c894035620074816130307040380c0144401410000d0101c81e004400f9036200056480c1c2c440003030740714401c0c100d803041415250341310f81c000c10743c08000100000e035000b0803081c524503450900800c07400780c55a0998010f01c095608070f20b0802410161b8600c0782c0e043c0c0d1490300d00b1000c42400c440d20340000e803040341404264198035006603000d03903150388135045803401404011011f5170002d2a02d034008000c030f000d01c8800c031030520042d00d0110b070030351080b40c0548010861700b101c90011f01d910b1007080303000b03440d0900e0800380407100803274591014082d88083d5620100d070303601c84c0190705e07404a083d00d10800140030544d04200200d51900050300c41c4ca503250714280f94030390383e088881c1030311035450351491002c500140c140011500015640b034980d500b80303070050861402e121100d041c5940070340bc00001460204910b41d242d5120100c8031001a1f0241c401060a10f10304005455401580021005401003201401600d0000903416040314 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 262080359 1250 262079109 262079137
    0x108090d1d1c050a061d100c1704060e0c0a0b03010b070503040302030f0a020a0905060f220e0309040608011b050c010b0a06180b03090d18080a0f05060c030408070201050a02071701021e 81
    0x75031f41c030700c4150040100c10001c0040c403417089041c00418892401c0c1c5442503001b00c0c0c01050400c501c81d0090b08000c003803002244070780200d50091115007a54400c2d03d0644130800b04441e5104024244140355000b0703035000035494418468052007140020481101d01d034400d40d154070394980c84400f0314090b13030b00c115032158001501e031a44283c680780500406c44a180500c0da050807044442c1c4c40e080030780700849002d0b01c240d440003850b180701d42014419a401041c00000800000b00c030464011112150f5601240070080042070114004034207611a000b200300003402c50407031982c0c1c0c03580038062000b80270103030101d41d5031020001406400041240e1141403c68064850241400404d0350f40b403206d01c00742842c074038102c040401c03046010801c070341d28030380101500b100030b00e072034500305150020050400440302c406105010000d0000d205444100d542424507607164102c510080f40383c040030358001c60f4045a142c03505d0181e00e00641c010300c006001c1400f4040d00600c41170003058107104800ca1402e80c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 262081609 1250 262080359 262080373
    0xa030e09040218010b0c100507021f0609051503010c030605010e1306030507060804150c080103060e190c0f09090b0c280207050108090d1d1c050a061d 66
    0x503180140304658014801446004040b41c41c40d001800ca1070241c11141ca91400000ca484481100b006143c108074420b110506c510725002c00c00a44840c1d0815903001d10002c004031400007105550040c00180000301810481c07403410f00c1e0071100c401541c101d014000c1d440e01d003007248a10f100b40546000d940041c0c582620804407081404003141c000c0b165201400d903107000110004409201010050405a9468195040c1410250a180844071851003010310300007010141700e40055401c1d04403904083e0014042d40c0c58110f550801440100741305940c04017030541e80401400280d480165654400441c000d5900d44450204030342c4100009484107407500b001601c5586802c0c01010519803000040e07500764103850100c190203c1c883c0a50700541c000c0f66060045581c08420141c0c0003807024000c01c503030780040202038088500d020a19a800600540120441e11103c00241c409500e846114620075160300b44140c0324501158102c9032581050b14172450541d03c204120064111680a4560 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 262082859 1250 262081609 262081637
    0x4030c121701060f0c0b0a02040302041104080a0b10080d020f010f0b09040f0201030e0a0303051b0301030f0f060b10090305011b02070909031b050a03080a11041a0d020c1e0a03 77
    0x2151a6103482841004001e082c5c10b0005454200c0142c040c80c844036001d621242548108419107420150000c1a24030600040202e03c0000076042c1000e500a480e426003501c481d60b0300e4100e08030030f801821640c0f0580540c0c0d83c0d0303144c1c00540038151844240003002503400d004070002c00c1e1a07540107070980c0300c40c0c00b8000c0f50204801200c0d25141d940b0506001400030010080603041c5440003000364046039540f81003280b0905010032070000d486440d04a80c3c51907055a84501350700842ea100a020441e11101c60340401001e03a003d070f41c41c400000c11000345201d0340c1e2001011042d10b40000c446950070000b105890b915420585101c041c0190058041c007411b05103040f009008241c01581000342e50720a41103c02c7c02c01d500c801616004030082c0001d4009402c0c06000100c000d440154034503d0301c0202803040a582c0181c6095803d01c1a150744074010401402c003640c0100304158506900c0001d19002410b000100f000c40500c3c800c2e16000900307818000c06840d922441000703800701c0e1000001c046c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 262084109 1250 262082859 262082867
    0x1080705010809010e0f060915040201050d090606180e070503010606140d15141804021f03091e14120d020901022b0311040b09040b03030f0304030c12170106 69
    0x15000b00e43c80000501d40c1000500245011100707040140c064000a050006c020720a000300c400344040c68410003200d0826900007049840382c4003400209035590f5000400b005410b800c00d40007011140320403004e4020102c40807005150305108280588240c1c000010282418026101100c00d5901d400804c200c45200708102a8021400c0c500050345c7e031122541908410340110024049113100440c65601c41030034880c000d04a00002119040b00e40b04010050b0741d20214038208900700624440c901c0403003030040c3d01501d00c41d40001c0096002c00c1c004540f400105815002d2903004440d803140c01c4c000a40c0080d10707a00c4181d00d604441c802080390701001071903500101100345040c8110350009a582480b02c004444c80b042d29072842004070000d000c803d5050042001c8149078400c0907107032a144c13180700495846002ca04030700403510307144002100d0b80c00b802030f41c0c001c416020082d556880d00d07150042190b2800c2401b00d40c0b910410160019141c421490140030512045451200e6400c010040d6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 262085359 1250 262084109 262084111
    0x60a14010509011412010603050a0204112817011409070801140405151207081b0109030b0604091b0e130515060f0301020406020c1513030803071b1401050a05010807050108 75
    0x503030004000303107142d0105c03602442060000c600a1002d810a0071284c41080180c80c840a01c07061001002e001c4604001030090000b4200c000502040d8102c445120081c1c1d059141c00c041c64030155201c4000091006100ea110884540120f4000c460303513482810507038240100703000c1c442c0c0c2d10316194200792050915074000c54000c8840d0314151a0140c4003c000b49a222840000000796000407204000c0c1440c01c0041d0030040d041254071180040404000030031105030340c070001c0c1640c4243d00110708075846903400a8000fa400192004840d00f9104d107021001e0034501c9040102420440000d610410141d0240c824a0b8402c001e811400d41e14a501c6000c100041c240a500991901c071005181e6801d100610007000c864000c0c20300100000b0401100c00030b080172010303106604101144041000d000d202e02504e5021401944079200c0203412100d11600c04030501c00d00000400c0380050020401d591010b12001c2802802141d441c040c032202514400e02c141101030740442c500b44041e43c001c841036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 262086609 1250 262085359 262085399
    0x3010b0714010914031206010e030a0b0a0204081e0c09061c0203010608061006020615060714070b040315240b0703210e06070804201c0302060a1401050901 68
    0xc00d092501d515944c450042e01400249513520000f0040710040300307144001ea0140302400c4c1450f020180f003000c2522404510710040007820700100081c0702740300c954103880107403072a6000c6401d40030403514001c90444c4002c68401b10341c070071542c2d20021813031304400652140e038025100109801c02240001020010400e0480c0d040d500c41401061a840400a4030f106403000300725400542c8c0b900f00301030308011000c3c0110100000500b40c079103254480c20101e940440d444440c0745421550200801e04003055a04100305a2100080c000113010801001500464490f07a080040c1612034000c054807110510390b12030790040c030640c200031019101001d071400c0b5020342002a10040603210030313022030300400c4c1c1100d46543d0720080f500150804104556002c038690800901600745503e803288207180080d843c0380c0940d821425402c070b50321b44409600011002003607c2c00503007500d140103506c4401c05c80d50780003030350f10302240319604003a0425198101c80c00540f8040d031603401d040351381900301040106 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 262087859 1250 262086609 262086611
    0x110f0702030c100810060512060d02010c051f0e011802041a0d0c0303020d0c05100c0908030a111207020d0f02040603080309010f23070e03120a030504060c030203010b071401 76
    0xb0903005500c3e4880c04280d1140c5035a41d180e0b1515000c24003408900890b00490b08200d021b04c0007103a5100c418139080d41006080f50030300092039240c030048540b4608001c004050307018082c01c00140240308035800115680300c1c5800d000310300000088900703c03a040c030000c0c040840c1080c540400b50402e0f03802001060103044050355600c0120020858140761500222060141c0a1040062540c180955110701c0385510305124044215202d0316500e00410710b005100030380da047d404030f416002d000c82c0b5009008001c16245c81c2d940c04940a441152901105803060040e1078100c0c80001c5200100c984240d40141500c2c840c1140d52984001d001c003a440480e001070b43c40d4004004145144081e611681400d400800e40381c0f84450041d0036100c00c8070f509800d9201203084103541c000750b07100c1140d0241031f501e4195034040681c000245010a40d4440080380c0800007010000d02e68540c01881c4a0b6000700c0040c489001505012400c0f81300910460f1001c1303800340308280025854003040303c000c0140e800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 262089109 1250 262087859 262087873
    0xc010c031b05161d010b07030804060203070519110d0f020312181903021203011508060f0a120311030f0a050c0f1501030b0a050105060904090303090c080601030213110f070203 77
    0x401101e500209400091044000c2500d95114603100041130f400342c1442401d15007072100a0b54042c2a004002d00b0081c00c0b5500030001070352191042003590170b01d0751907910001c0041c100d071a02030030f0b12041c02d140d000e040c016006841c040900076980101c6c2e0b00700642c000c5103030000c0c40c81807140000c006051000401032000c1d075280c9c0d0b48401c105940780300e1b643c1d01c60365044500314900a072a160201c2444a403114042c80100140340e180903c0c1d04031900d032401e014500b55110400102d200100d0400f40f54020074802002c0f84003082c410b95840a81d102c2d450b407011078900350820729a24060034418600c0f0081c104120443c0300e01c9030010b4800c03103804500300d443e041c138454152424040d080402c078150103940300040040c0040c0035000c680218503042d007005154144000f00f42103110f21003049010307540340c042d02d80c201880382d80540348454026040030b010f81d8940c452151682003e10050703100d010760558040301907030070b4420301b00700000000c0d005142507030341c6c001d445094000d210103a0381401804 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 262090359 1250 262089109 262089133
    0xa020c07030219060206090609150405030913060602070603020c060121060509010b0405010918080a090506070506040525061404080102120714040506070f320c010c031b05 75
    0x3e0194019440000c0031085180d0038090028508400201000101e52004c02030003080c0c2d8000c50480c1c140c22036621090398540e51824650324501c44d0a90380e070f17000070b03071f000c10644d00605552200043e10301030760a541c840d60307503804202e043c2e008039601124203030406e000410041100501440c0d880c0d2a080f41d0804801d642c0d2039041c2247d00c11642001582d444450a5502d46401d1142c5400f40c151080c0c02c20800d00051080034502c0301207903000380140302c0011111015402841c0b400001d01d0010501c946e078034050f25280782c858801340c0d401c42d5148142e0402812000c00c0c001200c1d010f614140b4200d042d01e180c01401c0300c01c900b804c00039401c8140100030108801c04203000070f0480254983c40c2d44854140703190300406544000310070040c24001400f051041d560344c5e0080b242c03103036046061010011860b04012024480c04407540c603203540d00c66031365003c69642400c0030004050800a59100b001d900c0015190151005001400220a045881c00c540141a030801409006130120b4200207180 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 262091609 1250 262090359 262090369
    0x1d010311030405010218060c0a03180f0f0503160815130209011d0709081005150402031009060503030901120915181b08060415090b011d100605030a020c070302 70
    0x1034070b05840c9a500018003c1410b035849503003400e580320680c3d00c0e501e8003419010254a4041c103c1d0000c04208010010302c0b03078501e450030b0001c050301440d11003e042c030355250141c540c0004ca0340b0505002c4d0041840020f070003c0c00c000007108841004026120a080d02001003201e002c008203c810412000d850340c80140c0c0340c4200d9507010f4903200f85d00d18116a910790f900360104100a04003400c005800c03005010b001c4000c9141201d1a201d0320300810541c445494540e05021000060740d0003901c013000708802403244002850460f0b00780c82040204c00d0300c40c3d0525480344218114180407454803121048545000e0703104982c2d00e8081d10010800000a000d0305e0140d800c0e007100001ca0b42c882600c20300902c80030303482040c5615001d400c65140d103450446502c1d16000e000300b0103050584454080c00b9015000c1e0441c483d4154000c2850b9441c1d0303140e408010310009030703103070000e00140725800040344c09251a8007541600c50236224a8255680c50400e940603501c690345800a81c0580f120000040c1c0752 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 262092859 1250 262091609 262091611
    0xd020706020304020f090402011d12011112010911090108060f030f06150315011a0408070f03060c080f06091f0e040201030c02070e072a0f02010206010906061d01031103 74
    0x4904009a940d00b054010000d42000b454580346c440c54402081c0300060781c018403440c0310380c40780d4008506500c1c88100041e040e5010007140b42049d5003000c1c1d18a117011600b0700200352962400c9080e134102e90701ca10b9648200c27800110740850f5180e040240152a40c0030b240c00d00d42c480401030041e88000c1a00d00464104071220441e0012540f24ad41448a034031307100814064002d85c181d00806103500000700d010841c56044c4146606001d1140f42604840e0481e4100c601500c05e05084520041d913a07400400c013082c1714402586c00b1898403185030460f6124010503800b8000b801d600540c40d171554010030000c040d0241882680030060b03407031120300004007a500b900402d0031404010040c500343c0005000d48544041010841d041a00709101460740c245049405c040d03285480c0382c0724035003090183c0380850070541460144090b07042070410400724080503a030b12071003a425100940d0fa18500700781502c1c0180900c8000c40d56403840c5409011980b00b40b00e607034400500d008200f40020050006490b44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 262094109 1250 262092859 262092863
    0xf0209130504020901050d0203101a09010e15040c0f120e0a0501090c14090a02070204090b04120225031b050a0e01030b0105100503060103020705010b031002220303050703080a020d0207 81
    0x186460400080d4034044461380c0c01020142e4141c01e28045581c00643c07645042e07007000c1a0307156510242103003440004151544560b01410003312541c4884041c8030780482200d0340f01804c0e607843c84100c51b41c1803d01500ca00d00c00c447c0c0b55004400031880f8280c0d14034641a1444500741c0c0d59040c0c5005804041180000c401c0c000c00c000194000c5a060a90707400c456a00f1000050310703c440d60100700e40f200f5511941c041c0080800584654481c400070303000d000c0020000d4240e1200c142403005009002d0107010080c003190b02101c8040f0100080c1841411903009006c4034441080c00401c04101c6500b003100910080f410f0440d0583d480d500014a030201c5a008009000300c000d00500c204840c5500c02d60240c00100e0354011090102d800c010032511004207a40d04050b000b20308a0100902500025040c2c88010240d540b14986401000000c0d0440d0700d080042400f050411082100f9035410041601d42660350b003890b021054130305941d94072002d02070036284c6900f0440d202d0080c91a20140103014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 262095359 1250 262094109 262094111
    0x1050a0b030c1807080a020909010b0c012a050f1903050601120614211506041a09010306020304031404060917010b1311070f1b0e0106020d030f020913 66
    0x8204102810324020307a0070071060041c94059003840c030700407510003c00c1d0f100741c03203150840c41c560b22924113101901500604a411000902c00440e40c0386120024101c0c03100824003c102c1251b0480180011178030300c203002c024041c6884446820b2074070490040011081103480c05180094566040304401829013180300040d6680091112560307200c0c0c21400d03008070441040c00301c242000c0040001ea20031031260b511400760044019034144495080e01c41e20722580342a50458510703e04a0400b50f942154014405c520701b0b01403105011560180b00450907001c2c242459603030030340d960700000390f05c09442501408440d10005894182000080001d0180d5584900d9101d01c2c0000c42442420313240c1c0b0348800d9904208074442c0ca5101c010501c3d40c2c1036003902020890743d6035817103038803c2031055000182c09a8414442d402c02d10405443c60544400703410700c025001ca9550f040c080032410207004110060f000319003555030452103500704a283c9084010014a04960304000901c0c0c007a01d105180d11203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 262096609 1250 262095359 262095371
    0x1d0307120506060d05100b12010504030306050406050303070c09020c0309100f12020910031109130e060603010509031902070f03060504050f061605030c04120507080606010f0507020f0d0501050a 85
    0x800d00b8405103070040e00c180c0d4407a00d1a011503a403291502105048440f5103580c8001e800c03d1692034081000c16070000070000c01241c20710b42801000384c0300d9805000c2c0106d04204000556044c0003080b00c400c0c3d500516045859401d0450340d201942c401e5101040902c8240400c20380382c0d40d00040707201c0705400e03030712a05041e0803190703c054003004851109203046407044c032162929031203030380c08201031401030701e0000303014901d40740400ba81d409200102c0f034110388040c049a052848680c00700d07070200c1c1e4400407a074543e5252420942a510100e40c0d0b0f00c00c5400501170f100043d030700389101d030500d0b440600550b40780f561600300c040000816a0300c1a184151510284400d1003014000c581000786400c001d40340a1406900311800c80c3c080c00c1d8a4800c0050010001e5189040031098030081c041080124641d002d5605003d40d40395458010840c650094002046c1150b00070f00041000d04e480da20751904010943d003c0041500c0c0101e10b4a400680c4001250300080d0288a4688603108500d400500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 262097859 1250 262096609 262096613
    0x5030c101109010e060c010f0509010614060a050405010518090a0f0c020d0203030610030605060c1e030403021806010201020702150a0201060506040f03080f0403050a0501060317090906011d030712 86
    0x3950303401580c41c048204100080e0030141d80c03241056413000010f03030f441e41d9070701e01c4008207034010004004040792491900c1d040c0329010006400240840b03604483c050701c24132003541005007500c01d0070141e00205c2c8081104100e0345d4000c5000d030003850018100d14100940c070f0f101003140400c003259440c1d00b00d88d40704035a8110440e10310032080109001d1000f011540041c89001c0c1d520f00c400762505100b601c4c1d00d50300340c80302d030b101c3e030090307006004003a04413510342d59900e035140d40d00c0044066400b8044002e43c804680c0035400016501102e070010300030180340403100d6101c207040c074014042a0445d5000c111400240e01c0306418504007406440680c1e60350f05040d01c0080c01c403443e64000c1c0d403042c1801c0108110103601c82943c20b0680f908440d2440d6600454072900e4032620603a40000c00c0742c0100d06c2020207100c1c040d44040101c90181c4c0c09040d243c60360441050007032240c0348c1c200358802414400700d0415481a519240000f400341440c01103103520701e000078948419544100c1c2030741041c4c070349042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 262099109 1250 262097859 262097861
    0x20a170a1e020108010308130306090507050a061d04150b131505040b09040b0a031407060206100303170403090f0b0c1903020a060c1407030e03011a0315100305030c10 73
    0x401c1c5403405250010a41d441e40000c1160300d040c44068010100410030106112120800400559000c001044135480340d00c0e0141d2561114070500d44114100f0100060541c09034285000c1001d90410950b02c000c120820880100800514000f03003443e034100118003d5080d6004210100c400782c0d00c07503006443c00c4100485401c4051940381001403d0104020a00d8613000f43d5512160480303000c100c0301d51120114040100543c80030f044400c40c2a1640200c59002c6044020b035000e0fa0300781e42c0c2039615140010440e509a1000130002418006e2100c08104a40d80c803e8201d0300c01d1400d074400580e948065403658406822045480c08005004591504200500e00315500c46004c0c4410141e20b0740c8001c5d4640782081e03030140200703841d01c200c180460b214003005928180c0d4200741686131101030800412000300ca5008500943c83d009401c60f203d42c1030407808007000001401040c00d00c44a41002689100203042c50680031480300010000540c1070000d08012082e230001081c078400d0710322480c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 262100359 1250 262099109 262099133
    0x405031504050a0b01091a010f090501032f070c060305040c06050705012903010b240703030b04091109061f05130314030306090c0301120803070e100807021002190c020a170a 76
    0x5050091030720380b41a0042d00004090100d2f0740902300043d0361102d0b03201c9000c100906030000c54151402d80000324038001034401518845005415041005464507001c0e012a4070949000d40441d2095804115541c410b030b0040c0754840c8a140042907191f004060055030003010fa100c0b000d44c61042428940d1403c09100e02c0749801e001300d900c4a0b0002840500c508a040c4014141003401d40001d031800c149030180d0060b803e07915000d00f0070071900030703241001030031000713240406840303100360601241c220714051030130120a4040b4140700c0306218244000ba10b2640c07108600d9105000070090000214088080300f0103109007000c06503549244c034004022102d940140644900c40052006114004941510b0720807140d01c101002d50b242c580d040b040e40c580c1244211903600c40c08014010b00550f502c1041e142c0108456001c0780d00041340e8800400583c000c6025200c5619501c1480c1c6481030f126940024800340098864200c0d81e494100b850710314941551400481e904c240380d00810080803071070030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 262101609 1250 262100359 262100411
    0x40c0f0f0212030109180f11040606021506041d03120114010908030409231603180b0a05250801151b0215040902070f02030c060405031504050a0b0109 66
    0x1500030a110720b021042180418043c00c040c03d60f0b2500e5a1019208280c00d458006030010281c484c4402e40e8a452200b8060211324240035a0a0a10000f4418000101c0b04080e10345940390400e05e40d40d61007800000d107290341c2181c0051102481c0400e500030244028100c042d0b05138010282d540c1842c20001c404105503000ca41045032148040260100110a50f0255841c02c40f011880c120340d55013007000300300e00441d901403440c0c480e02400850348400e001012154000c3d00d00f44200700312460f407180da451a240003d0f040803140e10004078040216032209501c00f803085048801c048000341119980d018032201c1202141c80c1d10018401c000e003402003561004803030700e040410029411241e00d0200000350000b80200d10304e4103070103801001d6609071030203410801021902c960f02c505240705240395042c4241d0003406541c07500035246c00c024045074140c80c17026000b0421003403041c0c00d0b07442c040d070018010344460140c2c4491000007244440214000c050701200400c40d60803c201658030300c1401404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 262102859 1250 262101609 262101613
    0x4021903080d1a03060f0406060902181e0a09051306050408040e1b18030a12180e04050c01120e0105070801151e0c020102070909030c1704030c05060a0e040c0f0f02 72
    0x880a5550010315164000241d00032070985032141d08d8004058030346904814001400800c18400b00700305503441b8140d010301100e0102914010481d507011140d460b0060756003250542809210290003034104c690080d41d24013503250001c0060307c42c86e0444200b51000c5981e22800101089075000c000465078100d80c289107030320800b444500300e0b01d10314451aa81c2043e0500180c1407415659005e01c405403041d504001d4956084482000080001d1590512009003100301c01d0081100d640c65442544160740c808014030100c84040015545083c1a480a0b51900e840340303048004480c0a01a01c0e000745090b859018407541404405102c4a60103020481008007204801d03c04002c1c911555001d5940b500348090503000d40d00040341001d000c0d4012044190512800c0340400d6400303004001d10724011003001c41218245040320741075108520020309001d4884206120900c0c14000401c2040294103140302c01000001c049802d0392200e0510101080c2a40c0030701e1010742d0440050100070780c1a00c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 262104109 1250 262102859 262102901
    0x9060126060106050715021c0504051606021c081303030509280210020613020f011403010b040e090a050a080a05070b090106030203010f0209090f040203030f04090f0b010c0b060904021903080d 84
    0x142c041c048000d03100c04230440c540b510045028007034180200041010703e24081000340d51076940c007940c0c0303100550b40700e44942e9250807407209413807080165a000700311001d0700032807583c1d049c0c40403805498050030181c1c0c0d9000e49402200465175044124400e0b14100c800c40d20f03640c2803401003002140600144000b907400c520300b003100c800030608258040e10b0303044680c60210150400100c9464155208a8200728000000852480f004401400444d01010340904143d80c40303141031074982c2c464041c0104290b020400c90000280740301c000d030480801502d032150038040c240c0c0703441c3d450100039200925580d54645050007907041c00e001e00030080400c49030a40c03501688e9008595038450050100c101202e5000c0800c045540a00880360f0404070400d0154485481d055600000c02d140a059080c4500c0c1822640c01035008a1100c030300683c01c0032042c6541e54500e41800211903000f04200e034000383c1002641b0001c2c4845100d4805180034411594544d00740310700c81c41c00c46225081b92201600d60315 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 262105359 1250 262104109 262104127
    0xb0105030f0403051e031503030901021018020d03080709061d0d02030102070614011805151201090203010501080d110102070f0201110f0a0b0a050a050906012606010605071502 77
    0x22250000741030107151049a0712400c04881c607014210054501a80900c80a204c18104102550040b030f03805040000400e140390400d40d403032142d80012805a0049031900f40b4082a660081003010360a058210346944540e0001e405021400382c100c0c0400c000b8014410141e03071081c10342e000b0b03203014241b400b84056005140d10390f0800103148280b04e03407440307001c0c2021502c007034054406040d4000c0041c440320290008102501c03609000e1a84003003413440185a402060303000d01801800340c06400c0c0005074111080c001c0002c405407200600e0b640300c0c83e00c6030042e1824400c060003001d030b010241c241d500d9024002091071412410450482e230041c0401008254041c1d80d008a250f424281160f4510007500c02e05e040c07182c40d42001d1018041e601da641c017480025903829215400114040045a841400e207200300c1d0b1041d50740000350b070300c070300d00500600201c01c040c447c1c00a220f00090f03907483c00301c20245181020903046034001070008610001003002d41c0d054201c0e0408064001d506002e40340d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 262106609 1250 262105359 262105367
    0x703090e0f07020705060a260106080901050609060d1b08010b0a051806041808131d16050c0a06020409060329041b080307050c010206011502060f1f170d030b01 70
    0x601176076109000004040e0060750180c2d42d0100011070f48691500d100010f0001c032021140244601c6010910400c00202101e4041c85003510889000701b600e40151140414001b910402d5201200d8601c000c001075074440d0040880303240202805000890850084400d010407211242d0049000380354070130340d040c0c0201c190109a60310070425107000403109900e0700c0f0540c070181c0c0160060059540000c02307150075090080c080c41900c944107843e4115100b120b0903a0a100da00304d68480340d03c0e450b90081619544244000c10304d0b01c400d20304681d014420b80c0c5952080b070f4031991103000c0c0f1550340c44081040000c4070541030384022500c1011a500c90105540c2c120103500180002c0c611001002940e0710040c4403c5030070301800c0410b085075103600c02483d000d41d441e10100c6240d0b026120352000003c0385483d4030408110310700b071540030741150744410b0340304444040b01030b00d00003116000c03510310703c481590354503104000e01d001d039070711850b030103211050a0a0601410726507003018101901d4429503600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 262107859 1250 262106609 262106623
    0x10e0d0903080f0c0304050d060902090f13110402090307060c0507080f0d0522030b0a14060a1a090405040c031703060901031104090605010f17013b030703090e0f0702 73
    0x310f0070f90764420034000400d0442c400c98110a40c80000340c41c40078280451a88402c0d01d05200340d80c450201e460300003440304c00c0b82d412100000c5204951a480340018400000111081000360000d8200441d40c0006810300c20070350495000a01c0454290050100c200240802458404082c6c8105220110703c552283c900c10703592820312400066841001c11303034920440f00c0a854800b01c5146585030314106031010410f4a8048030207040101c40521410f50440d82801030030b005103020307c518901842d0420812400700780da00008030500154007541c4a60140a1045d40b142031215003141c03c51410007080c172900f810b104031800e024810000d05448940074241034a402020f80c04a40352030030001009040c40b408018181401d143c00010001d080d4503c000c2501c202c0e0714801a880f90710700c032180c202e034206c0309140c64880c983e01407a019045000901c0303010f49800701c400203960b41d10030105855076000544c01c400080790510104603101e110585143c200714280290360740b40c00d111300c000b035607801e13 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 262109109 1250 262107859 262107877
    0xc10090c0e070c020d060c0201050604111c02190c1403070512030405010e07080c0102010e0118030c021305040506250806190e090106140a0f0e04080912010e0d090308 73
    0x1d02010600700b40c000c0d40b02100840d8000d015102030300c00743c54010094881020000c001d0b40c2440e010854514180c01550503051150728410301700b0b4402c0b858405400710303020140482c1c0d60700300f2091034030b141d520141c00000742454890309100c1ca0145400310135941c0312400000d00d43c00c140072450016501194011400e120f0185a036141d072900c0c20f140b801408161562107452081c0100001c0c1c03800003207540c03d400ca001760000c100d240e4000b0350035401d07074a070f14428034001d140c000d554100203401010003130b030081e0020704103400f00001d200c44003041762010f039000d0b42c550348410104034180c60f28180078407507044e0318205511980b16085010740300802c003a004a201d07100c02e0141902141c0d045031110011319005450482500f0035581c0c1d02e0003403425008100c0a5400c1c40c0441c05181490410310742100e1180f00c9400c0c0c400c2c0380030004c680c0418042c00440b00380e20200403071883d83e03882c07a80c40701c103e806050000a04c1c043c003580541c07800d0101c0601c03109005c4119420130115400000b80d4070000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 262110359 1250 262109109 262109129
    0x21612090b130504200703020c100f020c04020a020a1722050105272101111303030e06040b03040605090606031903030b0d02150d05010b1606021e030c0c10090c 70
    0x569403401610045d006000ca1814100002c0b4071041816800101140c0c404000d0fa19010300304281501224030110140005002d41d002c1400140c0c1400c1647c000c000401c01481034440c840c490380c0d0b4100c0310748d48441e03580c0c040d00c0010481c801210000c5809441d851415446014120720380320000e0541d0160075495854409000200e1f0040142c900180013554070042c07250045030003042c0c904682400c0c200b030300e80e40b5610345031000c16501d246504032070420480c0208010707141e1956174200e564003204408150410000c0c00b00003641008130000e1402980324060224242c0b500d003ca10b490507a001307128912039800301c850200110005031080d41887e402d85000300d00306d030844002c80c10001b60380c88025004022003061004c034488400103010040038082003400280da035800e104180340203004203100520315140400000403500d9004207145400010382075203b1108880081c10b0b90030854002c0d009000006e00c8610300c40050100d04a2030006034401c1084504640784c03203201c07400c0e80c0074401c502 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 262111609 1250 262110359 262110371
    0x9030f0204090203030a11060606040f15090918031805130f0e0d020a05060106020a031e030b04050a0b120105150d0c1a0a09050108071e03021612090b130504 69
    0xd521160400108140c026085940e074140c4c00400412540070482034040500400f40810f90500e8140200c030708440c1c0464640300300c5810440415102e038590644003003800450900010316404c140520700b4001080b840c0c41c00e200d4100e090103031090803c24200c1c80c5d81e5000c004244559039400c1c140501c0090050000203015401e41090310040c101551300d100b0b41c1c810310751105070700c507800629208100e11501c06d0f141266a02c100680c0d9944c40031b013000340894007100e0440810803c0c01c0d13220640358031900d80820408a01c0c408141103450a4803415a0151120f10404040c00c100d5403040d00654100000c00803880c0420680749103d200c050703054481c070f8001e80100c050200400c0803101510001ca020040c2090244240c08550700900501c0c01144559000140304d44c001e85445218115940310b0b0345040621100d14184001c10034035040901d9401d20403c209e0305502d2400105641c480c01c0e000c214190403560240c4516403e0740303e0850300004104102e40c1c5018042c0110403641d003901c0200c1e01c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 262112859 1250 262111609 262111613
    0x30c091703040503030c010b1801030f0201050304110d030e190b040311150f030406150b0909180a0309080f01050c12060f09150a090506100e031203010e090705010302070309030f 78
    0x3140b1565014a034135200105010418060640c00254a41401c0b1a8004094540c04281c1550a001d101c0680840131710041c1d200994013581c015544184150164284180d005000840b10001c4c92029070000310b003507029041ca800e1078481d07114515034000da0082480e2420840e40c03150322176070100808080903843c000b01c00b51a070119a0400c00d1001e209030351224105036072500d00e900110380031b4a203107013000703419158103c28092070350551304400c0c5200c0c075010f014420300c4840d5502a1180c003800048110b43c00a442050210307c000c684640d481c085641d180c44441850140114031340000ca07490718043c801e1042000d4121020310f183d150020416a0703e1030001409050480b0002d43c000c3c2000041000790070026041080141e8121005540140c0307401100e01113800c02c44407607070800c040d521890256030148100d00c4032100c005040300d02d4000c0380102d40c02036400c2a404075900c060540140501c560040c03050301c01604080c40c1c114105903446d1030050aa82e410b00c005020400c00b45e1103002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 262114109 1250 262112859 262112863
    0x11a09031507050c1b1005070c0315020a030b0301050c04050d051006060507051b0a0b0d020f0a02060609070203070203070608131a0114010908061b1903050f0106030c0917 75
    0x78035a440c040d8038801490840c201412607800f80d40b8044550284a01451603d05400402c03c0c40540c050100c3d0710542986405890b103234072190060702c14446400b400070001d104101c0e088600c541c20180940c941147c1d0f01c0280590b00040e003024420b074141400c01c80122121402e071011107404940186030b2002d03e08bc01070034140042c0060103150708045001c1010b40d0402c0081003102d22690440b0100c00482c1c1e45520503101c0704051036844000741c0d504004e90210000544a9440040e000614108080698002130341c44006c0c0d00c009608030030100038161510380f048681c0310201c0d0003c0d40c90001207500180c3c40e00e40c540a01000e01c164040880d080742100c4d001c00d0390540d07200c84106148840300403450940d0500344940806070207040380300c43c00d5521820fa00001c03980c3d644000c01494440c40c40c50007052440d20344035400000140540548074484401111614081f900e0014180c141040361500b0a03505070400350500d800c2420300d000c49503104c40762200b242c070300d1110512020b132100c07c840c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 262115359 1250 262114109 262114123
    0x1c02040312053403140901020a030e06042105010605031b010309031e02011a0406120809040b0618010f03140a050405030408010c0801050a0504060605040306020304021306060807030c08011a0903 85
    0x216000404155803c03d5107110400140714074000c3d00ca10003512003201c00402c552150101650050308201e42d1500020b01a51400c0b420040c020b207403d041c0f43d180c0400040c1509440454089469510145414000300703118410151500750060040c10841e40024400f410300000c5550400d9980c600da001458800c481800b680285403079086a8017141400080c081c120700408074240c0c00081e4402c0d107851401c0d211340002c88240c0704141100756060b0301d0740d4082d41c00070000540c02546600c0552403560f80c04c0f000b0211080c807008002d146a82520004242c0840444c4010a051802c1c1e10700302034440c40e040c8258480389003180400d90381e0b101e180140c198012580b0070030807036003052160459a0380000c0707030034142c034410359684200d04d07034520800c025101607221b2500452003c01c000c1c40482c4841d001154028000f0309081400110050050200c07102030740140000348002040c007007440c4d454058410304071241d01d0a0000c55040030000011082c403c590500c08010000d8102c0c4d86403414040c0c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 262116609 1250 262115359 262115407
    0x3030513050402041d15030c01030f112802030306010503061201090203030d090303112107090503030415180b0f0711180103050f0d0509010818060c1c0204031205 71
    0x7551070340c2c1d40717003010fa500e01400303000062000e001c00000740111141034540080c00100400402100409800540081c01801c0c625003c064035090800a40038446008282c0390701005800708020412540b9049100720065070001190020030500500f60707801016030350044811504207100c074440c0e07a01c540c0107100c1c00000940502010079581140303d016407042c88850b0103a1014011158425041c51152003003404c0f55034210040300c01030304a01c0c20050785682c46100360030140780d0143c035032002a00d19041a170021070f00c0000d40c52a00361565210380c0c81201c000410025a41685c2420740c03084dc03d0040c0b0f1210404034101282d03920a000503a0303001070030880060002180d0301c0050101c6180300409000a641a100703040300600c140300001040c0d030300c1000d17540d0b5190401640b00c0c0112501240500480c0f4000d02452041c0f0581e0014071502d4002c800000d029950b52000e640c0b050020341596445000c1280305120404c0498101d156001d454045442c28681c1d43c400d81c0d0b0503000e54014190302c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 262117859 1250 262116609 262116611
    0x702030c0304091112070305060f09131101022107032c040507030908040f08060c0f04030605060d020315060f030c03060a0b0d0f05011e060518072604120c0c030305130504 75
    0x60118051f010350005001c0c00e0240c030b111110462810502c020200d090b980132500d410705110031008100000001c1d03c1c0018148142c441800329001c050b40009114120303c409250300007100d0b010140c06c410348210014010070300284180d101d410b0040b4000d210300380c0c140110b48580000b00d08610a500c0910700039880780b6115155500e0301d80380741000c03402d402203030703880e106003008215296180c0041e141008040f69500b4540350840d900c840182401524164125400c4088080180c7d001e024000300004000c0345c24500b481c01c40308000d101403490103114001c0c0c1011840e2041500e0201e00030750301c0312060701c021408540103c00700c2c0e40071407800405400c0070300340c031024001c210040d04000e20204140800082d03c46001c450f09084a60520071203602c04000061044a44075205910360b1000d45802c20091380d190300300342e41808490789a002c100702c1c036040f010031003004000d5006441182e802e00e03101008402c2c6558990049a0030f01015061200106948021510782d02118024140281c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 262119109 1250 262117859 262117861
    0x92103040902071712010b070201090308121b0301050a061d1215060108060d0609060e060907050901080d233f070f03090312060b0306090702030c0304091112 69
    0x2680000303402603070003103a20030b03c821120321180304c1d4101900e03241022921405040d0b4070f0b00d1580c10a80d8410b0f94202e040c041615000408103071000083c04514050301c8410001d443e1241100408a0f01a02c5d8415859401d100610058030f5501d8a001540c019003010202d40428a0401c18100312461402c1da01c44103034034150b00c2440000c04c51030001032040144407055260b240040d141c542080388d003180c02002c0c0201e448003082e02e94102240060251900041ca0403160b941542090000c50303490559030b204e04401c10281c2000c0800d10700420b41c14010b030a0842c08144001c003a0b4070b00301c02104a031407000b41071021070580c88007198610076030f05442500c80c1ca0105541d6204242c904800012555030b0b0f50344c013001100c40203a080c410300242d5201c0c501000040300c141d0003014120001d07002c0000241c4e10b600742d103015119042c041e0689500d080e03160b11313000c010480340b1076004210b4801c6400034000e0b400012030000c10344055038121307000815040c0c05510708030000e016201c4d850000c540520 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 262120359 1250 262119109 262119119
    0x111c05070609031a0723090a031b090b0303031602030d020309010b010f030c0c02011d0a091b021501050f01140a09050a050102010213090e0c06070b070e041109210304 73
    0x181d40d08007200d2095003110804041c0b04d41008248800b01e03100c2c2c011070101c850315a80e800c6002d80d0240c1d0001d240300660708100c0038101152400815820403155107040704010462141001c0019001342841c0d60103000062030700303020075100e02002e0300c03c8103070009031a00b80c024240240155007010f001200210f440389064800305018119000e0301d10301042420214140d001c1c402d000d92015041e0544a0301d0480c507240d4011a45640c4640c2e1414100420300c10000c3e031a0b48941d0700314002d0603410404103a2101603103103019000d0041500b01c01b1b43d0b00c20324048040100403000380e4110352048517151000d08802c00140c40046006e04038079040703400014444015604100d03e00240e4400b91a1030004031344441c0160308074401c4079092203400c441c4580c10002c02d181c1f034101000c800d02c0b20041d00c1c040400000410031136004000211500c102e854100001146c2c00400340501c90300031a000d04c01c844400103e0141c6204881c1c3c03e40c058040c148000b40710951411440b00000103150890b9500c81e698 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 262121609 1250 262120359 262120367
    0x50d0f0b090c07060507080402060711120703050a06060e0105090f0712180b0610051227060711060106080f06010903050d0207061e051b010b06070804090b030109111c050706 76
    0x80041260213503e0900032444191040035650310582e801350216181a9250710b41504070a91005001d80c446034002880141010611014000314401c0005040d445c10900e0054287c801c1c580221540360216001040540d8540310101e03009056000340030465140c078141122107c1b40901c180d541a41061001c04504001410703007410240120b02d0000c0c0c0752903060401990100003216100000c00520401d00805080c280090b00884c5400c020320083c4059440a0082062a0702e890300320f070060410085583c1d00541c4218a04101c00302a098642c100b46000d0102c05020b40074008a200c80c90010307000c0e90103001000c0280d03811508440401c24000c900135910901c40c012540003418100c804e507107841d034202640036512a11307107400d0306000e2001d02e00c0d421005a1a0b44481540d01c0e202451565256070340241441801560500e541e242040301c508180c41e144281507000b60f141000c00f5010490f100c142800e1424200c1c0c1482220802c011036a13291480791102504500442c0c000244c9035403c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 262122859 1250 262121609 262121617
    0x18030912111e0f040515040b030718050115030c02120a050c0f031c020c06040f03020a080a020309040b0303120c0d09230f0f0a03050f1c0b031c050d0f0b090c 69
    0x4201c6100c42603441c440e044c04150394042c0c40c140790140030581001010b10b02504600c3d000c1001400702c8403129500c02018400c0b4415580100d04207030f95000500c1400c90b801c00300c90403030566080910010340c3c00344000750f0f03400490320303440500c88022500b0303a4882d10940c2290380c030b106035a04507010140442ca40e0740e129404800019440840c98000c107403031515a00a45080d614104064000b50b951501c41100c82c01241008408600645208600003040840030f0400d000b501d41c011510784200c0d9003030100f00c0f410840d0ba00d1113548140007a9914100381d01c4c00b103520606030070000b9115a9495540f4001d40b402c510000c1c11800310343c0c031030180034a01c1c80f40c0500d219480c2c0c0481c2d20314500101c0c1e042e1188014001000580c02074040780d40407902401c002c0400070340409881d450078141c0303414101c4020210a07050900e540b16038440c006845d00300184418105045010403485000302e078050460b01c614011100b91503218204200c80c0455540400100c49000d4003820042c135102e003079030b185584 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 262124109 1250 262122859 262122919
    0xc02061503030f0c0114010e04150501140d060b0406030f02041d031209100e10050c0f0724230a0203040b0402060304060b06040602030c011803091211 66
    0x4608400548819540804452203050160140d482e0901a20f40c42c3d03400c1e40300e05000700301c640d00d880304500942004415207000300340d03282c4000440d007810f281039008a98500410101a400d0100500a41c40809501145101c003154140294841407400c003020b40034440245502c503141a100206001884103e012454030889040150922500d03075a8640b41101803048104c4d0700c140b0000544241100c0390a400041d101c080750542007402090700b0942d010143c01c02c845403c40214400c8402440c0140c070380186401c6c204501b01030384404191070b033b80a00c42014000205581d150401501c49041c04010030640210070b00200300d00b5442c130000d11028400440c106040d50700010b01042891090f280140d038000e08011041d2129000c00001e50400b401c03d0b90b03003d6a4154100069680344010001842250003540d102c1c450507030005d086620a12155000e402041c0e01200000da0000740c407030944d410744030f20344110710450a00390101007084034100c0e013010030181ca00902e803c5220100000c1070f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 262125359 1250 262124109 262124113
    0x3240d05160f080a03140703050f030109020403060506030c0102120a030609051302031207030f0e03010212010816050d110103021e04030507030c050612010317120a09060b090106050d1814010c02 85
    0x50b50f1000c9280e079441c10064003800003120f900200900e00d010600800352107009291150810a0850100d8604d03442a48840892540001d0400c01c0000c01e000e41607000100310098040c111403100040d40b10428941040146400082c0b03a540f014029130121000d07101c40380c403c201620307040c5080c03030380307110302c000305074400c1c42103044080d1918584e00c202c502980d81030f035400198665032038003134801c50075080344181e055400388008120740d80d015603010300030700c4003000510040f4102c845103402440d1980045025010f60400b5030045410950030204120081c030340140e40310516078105090300714050b0781c41112480040c0000500400040782c2d01524051403071034611542e580304100301d920800c1d1141c4248c4122100400c041040f00d9900d21061440e00010b038a407940a0302851048101140d100030150b0341c07200042c00344641489042946031050303448040e0741d414a1009022400790f180c112400a444045282c0e0034180303507038170003003140d0702406403103100c070000315100d01074404580d800b0014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 262126609 1250 262125359 262125389
    0x60402010e0901030c06080a0f020a08150609150901181401090e06090604110f0a081602010507020307060b010e060a030504060b03072105010204120807120503240d0516 74
    0x1854042841c50490b0340c00400b903182c0506e004800e440c03284000b8103100c2140d60b10044120108201d0006000c003a40c0ca41d01e100c220703d0620b81c43d0381c8013035105043c06d0280c0390902440d03100742c0302c0c880e0500705d8000641c1919210040040122204031641d003414000302881040080c1200c0d606000025010b0244c940044c2e09494900c20001c5500c00ca54442e4405182c4005c070740d0908050b802091000e11900120b89880311000d000d1450f0750001441400242d1039038108003440c1144410002402040c2c8000c0c07280781000c0c00300a581e401041c2000d840c01e59203503500301b10f5030300603680c04428010280489031103504c1c0443c090000c18040310184c420ba414440da1108501c0c000c500101a1a05107030603041d04044102c0c980c80440030924101c603299400c0001094071600300e0349540040e4032a000c00d40c1d03510120314041c007840b81c1070301d25813052001c240280000d049000038071080c109400310000d4480460180000d03020700483c0b2010f4007078017458041d42540800b06030900705031810302e2125085 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 262127859 1250 262126609 262126637
    0x9020d060c020604060c1704020111101109031c08040b130501110702100e01121a04150312080f0c0d09020d0b0a0e0f120a0c061e060902120f070c0501090506040201 72
    0x707130072a0100c41810711f001030400100103600441c814121003610030220b44001d14881071120460381c40c11005400500302084000042c501046400ca1050020515201c0a140c2c00000b0700040c2c0041c20003001c81c6485400150a2480818110540d58004c00207000d110a00301e1a0015a031000340705900038400c140b200c18105000f0401c0540034101a520410850641040000145038001d070380300b12032810f80781048656640d0f00900520405d00700707a00e076501f403552030102410741f62144550706100d044004c10954251010101d0790011800300711950792801ea9000c54014821a10025403000714a031680052080300021540b04401010b8100312400d0526440b035500c0c1c2d20704048640c264001b9407440801c5110390081d00b1514441d0030b01e041c1e580e40590300c00e0162400706072490314420040c0c841284c040410b008507402804280c50443c60510040c04000c8071040041000c1c0c1600b6194011034040781c8220300064501d60002c008100d10b400a1400d9922540d043c2e405034005040d050132660 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 262129109 1250 262127859 262127867
    0x12010b010f030506060702210708120301090207020a0308030a050609010f051c0c08030408010e0d0801050d031110020d021b0d0c030c030905180601020f120d09020d060c020604060c 79
    0x2040640503120745200319921003085014010003444030350001400c1c4054070041c3c0f20505143c0c00d0700300f0070b042003c03004148040141342031466030001c0400d82c8800300002c14070071448116419600020000f51751410b0a002083c44c4a20541c40100446000801c01c582d80e48580d007c0303801003104a4008009903030320301d12425050058003a841e807180340b9180020f80210300d0b2840c41c1e0a1881131001d280381c0380c0d5800109041d600254042c4c0b0381651580c881e28100c01c1c090010081d004840c0c103084c40c117541850045280a08008401014044c1d110300790f40000740204165400903158030030555495100035030190180d00000d524a6030000c44403c2d1400369030006c60390951b0040980c0e2500c0045000b0746049400840b070f05400da003401460b4074003003059154103803036404a8512400350a010f0804400080ca8070b90000c411a0943e04841840d1107100315203003c0315240c00401c240821552003500014040c0140703034000030042c1d0b2504107500c2c0d000380c010580920403401070500f00320001030340e0001e803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 262130359 1250 262129109 262129121
    0x9060a0e1204140409020303120a14250306050406060e120304030201081303090911180a06050406030c090503070f06080f090705100c0204050421030e0c0f0303071502091201 76
    0x40010802d1009010807001031a448811440003040030a00c081c0a03004a405c642c00140e11809a00340c0104001d003815481c011405142c0143c0784d005100d1030258070298002e401c810264a8102d40a04c2d08402c40c1c0c80380c2c00050103010010010400c0d99075965024001d81515101180a640364440c1d00c01303103c40100581d821250181c444649a0f5a0405070001004070244101c040c001c2c1c01a01041604581c480c4c240102e02c02e072000c9641d00b21905007020070101c104401c0c3d1090404050038481075511100b50741c1120840e05000c500b2082d10700d025646025290800341d0184203c800000d0701c1030b103810460007201c485840c0d00005032101401c250303c0300d10031545100264804e040c1000581071070803001802d01c4d01450100030a0301c5c03036030000d4162a41507400380c1d603440842110b251186803245500c01211032900301000418016100030381c848a02404803481003104002c2c0804035107003801100c0101d41d209560642445101981000035042a480b0600450081003d0b81ea0408144501 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 262131609 1250 262130359 262130383
    0x40c05131a092806090513020a140d06031401090b06100207051903140d021b011b02150d0e0709060503030d0903031b120c090608010e130b09060a0e 65
    0x1645400c407081c1c1484800d483c051000741c010444150822004801d4005000c082c0c0890f5032070052480c5804100000c10601401b02c0c09840e20402048115540260050009440000100d42c41c5d1840e2a40c0800400180d03001420088024403a542040010741c490390060344134491002607034a4220074898a45040c0602c100545d110301d0b82403150b840c2800d0444611450811480116501c99071800e141444207030501110345c2c0800c0c180c40b9a540c05125480c0c00b0031450703040110b0104e450340000c1c0032a007080c0c83d4003404c5110000300e00a5440300440142c041611440055940c0c040e6078900004098140003000c40d405038960200304041c0034019641110300c020700546c206546a00031000406903030b2303c1201070503519111039490001c9404120402c2400307482d0718080f0b070315666010094400c104456400c000707000c8020300440f900210fa490640d0055003180a041d580c1003074000f0000400107015207460518030420904000004026128101810081c41280240e50710700da44c421200540d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 262132859 1250 262131609 262131659
    0x309070e040209071d060703050a02100c1413080a0c0303020106061404140103270b01050603090d1d09240a14060c0a061107020109080c1c030e040c0513 67
    0x841c0305503101d1241002c100c10808680a10310305c1e640f0026900e82e110680031008620081600d1811a40501c02c0c0244540c2010082c00107049107440280003202e40003290380d21178000301d0810984401c600000b40640365800271601000824202108222000d1008500542c200030002c9102840346110081c05501d00070064101424000c084c0c2140311440c2d41781d410196100e0b00005842c0390f1800c041080c0d02140c03414001840c0c54100383c0c0440105030062402541f0410a0000104c07000a0344651019107207844481c1014240c01114111441d21690f680180d101017400142c880200b0030700c5403103420054501d42806a08180a500f440501c04c4e44041c5c038604440a00fa23003401c0d001040000c140505031091864a5596442100c80b015080088a50086031010031540c100f014003000d066090010305201c504040018200c240c0c801c0b40103c0300d2540480481014092101d02c50510001402030028101c1c0f084018542d401c90390381002444042100050009070008003a400d20f151010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 262134109 1250 262132859 262132861
    0x901020604030806010c020d0305030a0b0303210c0d05090105060109080105090c270103080c0c03120a0f031d060f070504080a02060918010f0315060501020d0305040203010f090501020309070e040209 87
    0x4054070f24078001801141800001b1041d02e006a56003881c1110440c400d031a010344070300b01000408220784034040136034040d5008200c00005040e0f54901c280c1e0014100180c08603903a00d540b12407525000f01046450341d82e0501c000d0055803103040d00310620a070380a07603070149420b0303441e0080c03400c1c1e48003660b4140e0303150409560180c190400d0b11600e8840003e000c2a44c0c0041d502881d19103590b03600340e00540c0c01c94004900044401024490345608810483c01440401c440c041003040d03034480c0c4c0002d00107004400302c040002e540030b5005081e0740d00d401d1410341c0b0002c05407400c4a03191103040702c0285a82c0c4007000081c80c450b00800a0f0707410b0b0358000c401041030741c402d80d09100d000c0c1e101000f002d40c4078809541590310481c048a801d8003a1040408883c4160301e9481e100f8516900700d030a40c8500c40c10404180f0090341d002034200d9141d10344d0301c1c001c20740d41c9460000c40e0040c0958150340c011107050034080800c2c000c0540055000b004500210f8203d0380c2d40340c1c41c1084031031003510004d40c0009550 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 262135359 1250 262134109 262134113
    0xb040605011d120f010506030606030607020d030b1306030302061b03010b090915040501170d0203040b12071101230f01050a0e07090914191a100207091a030f030901020604 75
    0x1240081c0c20202414103114a51501c00444c542101501002c040d60345560030809103060a00031190000b0064000b00301c242442c9901030f4035503028030302020400d907507000c03040030503524081d51582e03212100000b002000c1e2a81802910784030308035542114542c1070714038000148003200c202d07412502d100404504201d0614104411104003030640c15505040d1240c80f5056603d5205850082c40b1403180345080c070100715812410001a2042241035401c14041000312400180c21500c8075001c020300787e40d05a41d124016510103d5054118480390300c0c0c448071035001c52003c2c60171550f00324440301c0050030b0742d102c0001076421402400340039003244400c0c0b400c000850701030b0700d070a0704408942010828291101d480004a031609955282c12424010078000c0c401460b581a054075030b04140144042d10120342c0c2c03407250054000313441e030040300c04200d5440d01a2081c00038501400191209001c02003141810381c40000c89454001c2c86401469142210b1040000031103880d0078040e00a07045d281d07074507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 262136609 1250 262135359 262135397
    0xc0a0813080a0c02043e13150507050a080a030f02130603090807080309070501030e010905060606030a02281b03020a0209060a0b120f0106020d090302060309031306090305010b04060501 81
    0x2075002244c100ba2510382c405881d070088980c2030701003e1101c45090030440a501c24900040800f462a500c1280400110340d80814940202c41612400d08600488c002d024400315854030402c44040c142d801890000010020100010308951040f41c0c2c040c4203458a1014840403441106a588480c0426150400009029070031600e466401016420704050130342d00c031041b82e64012075a145a50700104010b020341d681500c5404502c0502000130003291150740c0e02d0945c6c4038000b81c5482d00c103200110008004440780c0d01121503410491124840d0014250b1061a214200c0d207603081c0418200490340380c02148401550640d59090780c000e0854071000d80070300180032009400d25400c84070f00394010841200420042404100406800c1c416144c00c2c1d81030000c0600607084a021034200031000c10f2800e03800410141641e0f012174a459507034a0b40500c56203544128903e00c2e00300c0c00c07515000a02d16420551440407240120000e0018081d000c081000320744050141c2c60100e0303120181240c0460b8a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 262137859 1250 262136609 262136627
    0x10501050a060206010e1312020309150c0604030c110307060815010807120504080d06080303040309140f1228030f0e01140c07050307180608060106050304080d0605090c0a0813080a 79
    0x800c07c0452071050035200d00002d0758610b4450809179100140b01d4040341411015542c4100d04212110f00700604c01303a0141d102c0350b0291014040000c442809014414000d0b406115000c000b0b048840b40c59903284054600340040707585041361010f081c2d042e056940103044007032040f2142c0e13407190100004200d001000300000f03001501d4094080c4407500540c80e2920500c0d0142004400454413407074580b0f0300a03c1e1000d83d401074640c515400d5015041503c5045e0f403441c603550b0855184400a03580c91609280903400005220075000060b503030151440b000301390144071070081d6118529082032000c03e440c2020106201030000e13510303002c002501c40804000d0503202c4003050580c1c035000d5403080040c1c60181c00307800c01c400c0c0040c1400242610b9803a4410f6000504081000d1711340e44d0b15102010703000c1c2c000100040c113180e600044c803142d03a0200d50b1100c1e015020060182e207060801c00d080c81000e400050325880880c20940200b01c004240980c00c8040c0c0781c0c4607001c90716051015600300e0f00d00f80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 262139109 1250 262137859 262137871
    0x2060123040203040804082a01140f0f0304051c0801261b010e01090506040e060d081c05060d0203100e0f120c07270b06090405040f0203010501050a060206010e 70
    0x25038200c54030500da581d400110702460060790415200c034140014542003807248001603590b201c03400e0b550640044480080511803509080c142c4090040300d0019919208800a41c08429030004004400304000405180108e00920482e0700803030072014090b142e500000329130008904004010004145400c420f1464030fa4030440c0c40340c044a921305000e00d0b008561040a000c8008007003601d0a075644003e44440141003442c0c95865280f03004003140d8644154002c102040101d9400a100c80d00c841c1584420f0b00c2d03000444c50780e150303440e0b9150300c14150b02c880305030900c40c10200420050318002c01e1501c1ca540c0c006014141d07610b00d50203408000e1840a14102d0740d4003415007141e540040a008a036161142031400958503140c0c016007900307281182e0816003004c0000c150ba0210500a0000502400100e202c0080d4900f140c2d00060003500403002c8039984681000708000420203410300303145e2024800d50007030040b40d81f2502008918203071401404016407205004000082c500010160841 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 262140359 1250 262139109 262139159
    0x4091b0513030f1403031303300e01060e07050d110301080d0804140d0203040305060106230a0512010915082806090f030c1203090809060901120f0e01110901020601 72
    0x14440c140a13500719007007202d078081e0356690340da112401e06401030904030019007440088044208810440d40700c1035584a480710031140c1e200701d502c4408400350702400c06040203002000741440d14810080060f84200c81d111404c1d410110324a407403003103130000d89050300d5481e4003070144285000b00403641040c004100f41d07000c072807460f03c02240402c180f01e01c442c052790a41c05995240d00b9402c2244c507013801a4000e030100701041040b40d03045040303524240003c0400303a0503140d8943c08100100d9403800f5248004da601074981c0300000340c042c042d40c0000e0304000c4840012200c01d645507501622400c11342c1c000825003804154200d4500306000380c04003000c2c85060001001d41c41038036680803038000e1000c00c80116440500070024003402e1042c44000c4001842d0904c8820555555001d640c020382c01c085d4002e210100f00d011260780a10032803c181d40300340d401048070030340b44040302001d4485205290025464131a47c06d204442e00000ca400000040e00200801e901c3d1070344070611b03042c181900440310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 262141609 1250 262140359 262140383
    0x1081f0512010f050c0712050a09080706052205030303220605040602070b09010c050f07080d0f1b0c17030c1e030105010e090403080f15030304091b0513030f 69
    0x203607211442990519040000000d421480ca0304410840320090300b90449250309104100000d409a4440080300c4618035015456140700c82041c1d44901e0284c02c030700064024440041035899000c00604050400400071144c990380d1030001040205190203400d405410820014007000301e42e10003070404c100b01030070410035004103071600c5080f40c6043e01c045030002c1e0002081c0d81842515140303541c003c0d14a500030008a4240080900180f003100c5601490890100e00c210500813546c080d501d10105290040c05500c001000309402822840031194a042140203400030f400e00c20044a03d885a2145107803001051803000740000b80c20081c0065007031801080307040307031003200c20308184ea52624210449440e541070000241a81d14540c0000d400b076900c07032081001003584601e00d540c2024802d01403030401d40752040c40021542e148100c036500f51000003000030b10301c0c226074070074204140750032810480076207210030450b07182c0700e0180756030151040c00c401800070403580d480d4100207a100718214262 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 262142859 1250 262141609 262141619
    0x602041e06111c02030906270907080f1909030221040620010216080d110703020318010216260d0f110c0414040308070e13110d0e030301080c030c01081f 67
    0x45601a848c1903003a0202825603541140c4109145101190100c500701e03c40e14003e20b000300090300c0202608909480b410110b103040a500104006000c203114092000ba6094203020303603642482541c1c0307903040102802c248120302546003030b541036079115641c020446410340c4084035005950030500155540c208000c00c07014030b01644200d041445200385a89481e074020380c0e04100d170304d13401c07406194480c10060440000d0b030101c12038403010300320302c0f504554201d1400100d14203a00c900800482440382c02c0040380e00258803400e042c013100290b508004512607008266103c46030220541c011a9440c0d0039110101d000b43c454400c810500e2048074688500300340001c0940e40010350a5451608060510060642c0001d000d40e00c241242028480202100085000100032010402400c1d40d80c1c880c015210400d00b080320742030180003a042c0698984407050f00d840c3d074820704c514841c51051003841a80390a01240342c00030444140c4840f6103d58440d515a0070b14524420120818201620003240b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 262144109 1250 262142859 262142869
    0x4060e03040e19090210030e010b04020406030f0e0f03070f03051207110c01031104140105040305060a020c0708061e060105071b05010f03110405040b030a0602041e06111c020309 78
    0x4000c02e0020035000450070902c42e03041d440040c2c0c501c4048024100301c580005601c82d00d22890302d00074145030009011290070301d014010107800c202598031a000040000c5e000344e06400030f1121407540c1004100041c4d80f109103e039580b10300c00c91000a500f040c01080c001c82c0b07041c81000c08290090410a1411080301841600444c080725200c000c07406001140720501d004001d0100f00304400e0070100032454200302030740414020303032041a590f0a0600c001c071080b82d2188066a00842d07000c0202c2c1c3c03c6013000c021440181d08080d040441314840d5a00006065000150240c0100c40d00a265180c5030107504c0816003c000040015043c46410046400096a2088026041810740131000a010b081c2000100816540b41b10b5104050400b0409034100301010115004c07030308109e0380024150044030200b410240c1c1c1c800301030100d0740301180018843c10105681e005400c0c0e9541c0c40510151607a03815681d110003160504483c0e40410088040b440000d141090b0540c120f004803414404503000040d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 262145359 1250 262144109 262144117
    0xa05041d010504030215010806240a0803030a02030f13030f0c0f1401050727150c080c0a0b0a0212040f151a040c0306030b0a0519020301082505010e060304060e03 71
    0x1340103a02c4101c002408203a800c628502403d001c00181000d410000d031885209110f03110005410b0020201c0c3c2c611590f541d800b4030000300300b00c6080d40c1d182e29040034910001e4004681c501070400607000091081a000d0301e80341c01341303641525100e115440255048440c640790316806c40700c00c0303c1c908550000c920011b50705005184494008510b9240c07109000300042e81ca1106c050044811411244100061a0401d4166003c0c982e545c0fa61b0000400c0881e8070340f03070450003d041281c0004511103a02c0c07002c18420b000d2401004010300c00d484288060040b8458694410340d0160320701d020500103211800400e8805000d02943c8100a608c982c8103000c0300c0740d1661806240340d1180c90140c241c1001c1c05168481c4d42e03541000c000c49491519103840b0032400901444003207035203400240d5200540400c503145c4400055045490f5a128081d4eda40c3d030b80441450800118000344542480020900c50001d461043c1c1d2194460725900051101540000d08100c92306030710b58442d0f01c2d01c0001000030b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 262146609 1250 262145359 262145363
    0xc0b090a021c05010b09070c060207060617030d0608030901080105040b0d02030f011d0a031403071413031e12030207050c0d060903110312070507110409080405011103090a05041d010504 81
    0x4141c0034500207084420140156003c0c01c0d45108010003e90484194a02c08d03401c40e42c0540c1d600c0c07451610b00b000f40410380200c011185103c101022000300007028007208108070f00b0402c402a1100852035490003904915030010f00310714018406c80c101900440b0800740090b100d89140d680c03690009080c20b19841c0907083d143e40d03404022100d1685000c0345900c60704014040e14503044a520020b04020001c603405011031000400b0170411823081040ea114a2654100251613958480000440090a00c81666151400418600039080b0303001111031490380680c2c0c0204d030360000001a0b002c0c2d044040295020700441900c0e40f01c40c1c42d12002c4141e402d00ca100300103024545440c1c0079020b40200b8500403010707407040c407c0140001082c0d550680000090508076225061442c240c0f1207103210714005a045400c1002441c1040008405132058400988620802000070031445a13640903000007280c0c064041c8a007000641031036409240c140402111030400b45080d0802c2d182074401c10380302 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 262147859 1250 262146609 262146649
    0xc010f0617010b090103110f03071208040311030d020d0e03071d0406050714120c0c10060503280f11190303080705210621060411100c0b090a02 63
    0x6911003141c0c01c3c0320701506801c00b00c0e00c40381154195140c05d43e2101c107010b011405070448900723401c2c042d0b030204028001810800d4040c4104d90061030180e9594005100c21a1127407001c2250b40711515012441075035802d00780d030092001e2103210701c0440d40c2d015540042609030061800c0440e059400c45034a420790307034211200e8040d03401c1510f411401ca6100074942010031801072105c0240701280e030300311824010402d0240b4010345450302074050511644492110510a0140c003c1000009400c01c40c11650f00711b040e9840821f03007a0740300e00c042c152049110032502a11046d6000204c42165501540c0e0150602048040a6001096500c086044c0c420002200a0010020184d2151415034024400d107044d508041c00000e03126030743c003050380307040740c9910442000132107a4641c100d10741420b418400f513048400450000c81c5449000944090b981c94904040c0701455080640050303420400075901d82e90308a40a485640741c007500074025116501074401000d0144c0e4518104031207040710012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 262149109 1250 262147859 262147889
    0x5011407051c0609020c0f0f01140a020d1d010b09100f09020c011503030203070b0c04031a04060f020d0605090130050a0503030109141311270705040807060305010e0a020c010f06 78
    0xf030b0307450103140c8c1040c110180e041c8000340d01c1070414041d180ea0030905a460242c3c03a5908006440c001c3c12425840c0e0080504420700c07480b40c80e0054200d4180301c1c0b0180ca840d207090b1114a4591303070018040c0100c1d00c180740341000030000803001d81d00412080401c45e000080602d0140b0b502c0308004107584c402d60040c2e102250a0082c420001440c9401c9400c4401080ca09851942c4142074004044040304d080d100110000b0180441b940041d44c83c0c58544200315034400f48024403000529050103400d00640311540045a540e2441c800300d94002c4548000070400b070000020640d800c44220710480d40d60003034005220009100300083d40c047c0400b080085507505040000160905005142942d1722a50140e2140440e44d840307185100780c10192414110140c403140c10802e50180412904010000001001040d41c0c1c000058002d45100d0002d0303d040c15640c0c8003c5003620340130301880d10780036905004500c045071154014500d0b40d0303c103400070804040319100642103401c240d10070200700341d0010b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 262150359 1250 262149109 262149133
    0x6150b480d05090a0b0315040f050a060605130905090f070f05010f021504060c050f181203040e0105130e030c0d0e1008040611071e05011407051c0609020c 68
    0x11050307600724402850801e0070a84000c0004204843e10301c603940c210900000400c990310301083c12100c000c0406042888040f03502041400241021645940800c2c40d0240c04603110344110100ca0480715203071881303680c0314208050913000b881c0181c250b609a01c6a41c6103060594003c2c00020028203d0300e000c07126180c07900e4000361000f804040da0500b1500310103840801582148081d40d0407070340184000410341000c0070260349a00c2450784c42c112500000c00d5104649420342400c954494068440b10040c0b1680d40c6030540e240240c0c001ca004000d8510f0044c80107007080d00074661086148440424030362032060743c82d429540407007510802a080010713140f41c1641c0126a2440b802d10a0342c10f140020800d5900412494028000503c01902d079008607401010940603a90300a40011702c8009199a004c243c001d46004003008441c82d50030911050040701140104501c00c20403619114a01109903109586580084810402059980401203450a403e201a10a081e810801020003581701 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 262151609 1250 262150359 262150363
    0x6040b1002011506300204080a050304050a051203071205090d050d17090c0d0503040806070203070c05090c12092802031605060f1315090306150b48 65
    0x75000304003840541c4500500040c4610b08121004100c000d5140000742c841c011707030002e07124503030050016101d031002c804244240440180100e500c11603040301a5556407090060041612005d07001c070b508140802c0d1301040d0034009040c030039205841c121b0710305941d04c00003a5140701003920650302c0340d00c0002c50400460300114861800000d40c070300ba8805160050f0000d990380000340c8170600034201d014800c02000410001e0354054250b400036100300d803030072000081d90b03030b01700c00340c256080302945100140c0c40c100a40258019281c044006152428050044640e003801601c0d184103413140b0b00966248035541848042c00038050544c0e1342c04200d0f0303801014580842c180f10342c4030400701c100c0208983e55414040314000c101040250b41c070349280203c43c02040e40c06901c5520001034610041c02440da1000514007074a100f44010041d90130b00326030300414111280941d41c04180b04000e1b006a0000303c650341000550403c01007040c1901c1010510003409010307403200116004620b0140e010703041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 262152859 1250 262151609 262151651
    0x260d020105060f0d0516090c1209020a0504020325020f16080a020919060602031903021306031503200102070806090613060b040516080702010c0804060506040b100201 73
    0x45840240a2030811000094a00280d0f00b10780c0e00c182025466401045020300403100c0d4003c120380d2042c006a42c4d01d0100e4007400740c12400b03200003a94003224000006452203159a143d0300501001c03101c60411052000030350010b82100f80f4a50300c4e201454803040319120703201c07410540d5409000c009800700d01540c9401030b038102c81000c0042c0c580c01071000100009811805170380455694400d070b111010030504082031240d0b02c925550500101046003500000240b5000f4520010040100307080e41c8100c08170f01076800201c02041004200b000394a2107070b045009140c00303032450030311000c3d40c90342d403041d102800a41540e12800360ba40d03445560f68041c0036400062100c2d40c041d22040c41c0130300405440b010020031a4840401c01c1d80440144003866025410544001d04100140c3c00e010340f0f20244070803503a081c0030000e83e407079001800d12407041c080e55151b22140d849683c1c0c20f0f01c40c4c1c3c1d141400780c90b00501954000e560781002000603520f807000c0c03820f590038507000060300c45456400005040c01d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 262154109 1250 262152859 262152883
    0x40b04150f0518041707020604030f11091e060303040b0d06170c150a0516050c0405160e1c0605130c090b060a080601031d0106061209050d050f0426 65
    0x150700e000e10041c0c43c6120b0b09440c0d00662004a240d20704080c5203008407030340078240c006500071001150100070860380f2030b1540300140c0510344280c5060203a0040044826080710140c02410307070a50b0190050094900d075541280307009080c1d90410380c0b0343e003030f101003500603400044980391584e0080000c000c0031b5240700c50b42500000030b004c9005081d000b00e0350015024594010481c00010001d914921450a90307000e10b251b000a260301c07168034100155034070038088074036105130701d4100410107454030b02d030951094030312540300c51141c8038000042100a40c66008074217580714201d40082c0020300309118291280725820744802104c20035090101342201e10b90844a241c038a402850b505d1942c07590181e40c411411460104402c0e503507600100d003c0e205c21245488011180701c5000c4210106401400603540c85030f440d0801c1006601d00700c07040e01c080c1c0801602c0d03500031101d0101940e10850052000300c0c6028181031800f5620513440e21310300d01600b0400ca008202c071403011021a070074844040f040d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 262155359 1250 262154109 262154119
    0x4050c181002070e0a020c0601030f02011814150403050d050301030c0b0c03030a0902120f0d030e01060b04121a070210050106050304230a061409010b01020f1506040b04150f05 77
    0x459401e80c080d5442203d40034000c0032a001d4000104240000c0d0110352000b106407050781e590303580d649004996580060340803030115076030f501c000f03403240e20003d880b10403100307101580c00c8803c1244081c0a01001c82d0940b0403c0820100004408507500304140400303000f6a0752804d0b81c070742c950f003081d0280074495042032034141810040c4003064580081580c2d008400030000141d6030b0000c0c400603890345110031884c0c0541c020512030482104004c1240d02d81085551024014202c0000701d90382250010300170405019820704c01440804042c01410550300e2048617003e16a280100d0501e8203820300300c403403100580c003490ac88600f010103401918014000b078104903086044c1a6281017440201c44118220b5142c8002c1901001c80b0801051a2440e0001420003900e040b03012111044001100c02158075030812502c800c05510000e4078596581810f809015080450012a810140d01a00295229845920800e03855560b4400e40c01180541d42d001e00070640342190140540c040e9502041c411 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 262156609 1250 262155359 262155379
    0xe21030c030703110d0f0603060518060109050a290406060e0d021003020f16021816050702010905060d0e0d090b0706020f04030b0103080d1407050703110c04050c18 72
    0x1628408007030341d4110000f0704000c102c0c0b58005020184601401c080189001c2c2448486030841b18070341d00c82030541c0d003d0700061000343c0c1e9400c004482d1600e07500b41e901d8030360b100e080100803110180c0c2c4190f130002140d00d8040f821640da45007007003010360007505200c910002810001d03543c0c9000d2050500400706410035000042040d400101c0640d0070358000387c0911205000d120320316100342d0441d0f03900c11200c2200d980380da01600050b4078154190008a001d10060720150204425825840e8031031120301c10600303034029202c40300311481e0300b00b080124140700101e440814170343c0d41d1001503d501941180000b0345105c00c440c1c414a0701c0c4042d1b603a0800d000c1140024407000c2440b00445208503040000540d68404841c0105043c7c4601e500191000342a0000402088200d10003800c03d00d400e0b02c418002c040804400180310340040e03603540003040c010065a4002802010354940140d010001c0e560f043e419080840e0988030202e0b092009901c2c0068070b1000d0040c0502e0303141801505888104031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 262157859 1250 262156609 262156621
    0x31c0f0207030c03140703170901090803030903031f05030706030504050606090c2a07060e030601060207120f03030f0e100c05040302090f0603100c02010506040b040218010807120e2103 81
    0x36428184c00064040c01c010305250500e4802000040020341e03202c2542910000092605036003038100400c05d40c0050b04100001660000000c2902e01a10008001d1441d40c1c075040075140c0440843c08642901c0f42854400003201d0f5130a011410080c699924081094502898064281100200106d1042d0200e00a0008009400080c7d840d041040e0440011220b12224407081000b1190300c201c03a540314845001c12100da00c00c0b000401c060041d0308454007640c0b580c0082c1e03211100e034001c2c0001c00b20b11003400e4002c80c510140e81c4a486000341030000e03612400340d841c001600c40e40249500070750701910216886060724890140c5e21040d44ca052400d090655000070b04c2c640002e49551600310720900452059035040c4003110141c00481c40403c07128500400280c00f0700000c40714140302da8505110403101c0d0405000701c03a4400d4030030b242e22901450001c0195000300c006014039003000f0b03101004014454051080d205440d4500c0e0041c0b076071442c0410011440c80c0d0384a140c0881f0b410034018052 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 262159109 1250 262157859 262157873
    0x2a08010e071803140f0f06150103060306020d0501032006030a0e070e0907030314041532030105090702030f070f080f041d01090606210902031c0f020703 67
    0x410344981244219aa440c0e44404a5610312030344500c07140b94048010000c20406a0b412044184413100d041d980300c0c81c201c02e07034580c82e28460f451400e0f01da005800010301c80482c0180c41c8041003014100001c00741d8680d01c500040340c1010060301841950b030700c010320900403002c000035902180d08002c64411781d895004120300c0e000180070700d10039944032840e000301c000c0117005080180c070491082d6180f9182c00b00d842aa1540240702c01d0307002c00c13000342030220007085540803117050380c0e80c800d0b03420130046a9180848505400c00c0303180345540785500c0c08168000c490075070b1440c0c04070b1402c005c91324ad50410040000850700a81088250750042200c900d403e001103050b030750346542000c1500b40001940c200b20980340b094030700030021404006004505013101c10117040c107020b00011003200310b030b80305c0a01c071040300d5007801554085601b03011040c040658108102506030202d510214882603281c1c0802c1c076000184548076682c52150204004055100d0704840c0e00d04628401043e02ca071860316100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 262160359 1250 262159109 262159111
    0xc02031612061109060a020a030e0a21030e03120705010f05010515030c09060307270501021c0c0807060506030d0c080316030914240c0d200705012a08 66
    0x62240c2c1d00c402e455180300c40c1d480140d42c9100c130043c14240d07644602100003502e48148690481c046060307259141c9040c103050142c4015510120a240e900aa5807102d10004107207040d0304900b04a41a0590701c5180c405000001608080c42c50090312004146442403c0d18040d200b0754000302d00d80001082540d841035840c12041c00c130284c14a5803910741c1c1e103034503019100310559690062000030500680343c1d4420901d5150754445000c90911031840800d100d00c1401c107105403401a4080081400030120403d00c0002100032801c0411006410340e0700c4c0c14050304500000e50b5056520801c0050b9800c090208001715409071800703551803c0c055a03880018000070700446110140440c0f104c422034040c0c2e10070400300c0e8001c00102c0c101c4001c00c2c80761340c6d10301c100c03200c50190441e00700e102c1c00c6000118160f1401203a40b950401c1c100a03188125000604880c82e0001c0c014a0340e032220400007100780020010720b030003040040781903050030b102030810007000c2040380e441050554005100702e03400343c285 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 262161609 1250 262160359 262160363
    0x8060906070309031403040b0610030e0a080a030608070f080105180d0c031b060507030c020111160f0b011503061211040504110a0b07050c01020303060a030f020409080a0c02031612 79
    0x60075003007501307007199207600e0320b0743c045403d260020500c0705009501c03552607c100c1c4125200850320425210890595214400110f91640416031a10014040b6006088200319610740003d90755074901c0500c4c608072260340400003000710500d0620241c20300380112540920310700780201c9407401c4201495036400c4401038800c108003031780c0b000404041c03056043e040f07811220a5180082451800c2040007400144c03502c5020901d00791680c40345c4e80c018002d000710329641c840071a0418100000c05007120059003411210311180c180540b002501c0d10101034017030f009829000d00004400313100503007228217a070420820103840b00c006100245000d0b0101c814444261030110b01a00c50745000c42d40d80d001d5455183d40912420004a03540c1c40c1a0045d210a0340900d044900e076411403801662644420b0781c502d070b0004c48040c000e101181158504940e040d10260000580072100d480e001c4050300070255601c00104d01e04034a206526040203000420590301200030003851500d10b446008909990700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 262162859 1250 262161609 262161611
    0x1b08010609030b0c09090a02130e060d0813031202151b030103080d06080304080d0219080f0318011401061106072c0901030c050901090b010518030a141006080609060703 74
    0x144d03c6100c0302003a2450601c02400301c50302c60a2045000b00a504041000080340304454000104400d071030b945580070742001f402d02c0207041041e485107074840d4412010b2000180540c040000050010000308584e1103455000e06541c0043d2360340c04101c904050101d0103150003192400c00807986843c11241100c1c2d001e0041e682d1002c1d081c08003c050000340c2e000406900000c1030010303400c503003c951f4601c081d401350300b80d40f4142d455148a050300c812500000c0c0440206002d400031105060004540110454070203142c4d10369400e51035800c1d50554000201c002002d5001084400e030002c96503130004143d48003a248524006800400d1540070040fa0b00d8040030809554004201d100f10716210b0120150212081d580c41c3e040c0061515482d100d068058404030f0300000c0d8240c0355100f031a0000034141e580c0761801d5644202e41c1f06401c0541c0604d685401004450340c00995801071602045190710060002d003c4202c01000441d46142e021010b5504018204180c50b0300c00304030550300c8a11414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 262164109 1250 262162859 262162861
    0x70b070c06140901060f0e010b0703030b0303070c12020f03012f04031403120c0f04061805040203070305010801050a0204081e0a12030603151109090c0c010c031b08010609030b 77
    0xa100000c1c2118042c944a109440001e101406106402c5041921000c0560140061340caa400c0154120240b107450f0340c602c1c09201c180d0010b4820b4010703a070101c1d0010112810001507031a130403410070185e03200340c00304041c484109046080a1410201c00341007100200702c0c004004410f0048440f0b034035051401c1c0101a8085807a0a10203010344e0050754005801c103200160900030386941ea440303420159500744110300054442e80c0c0c0c0104844812402000660602c0c4c940710b000c4d070f000c5042c1e03840c801e1149060100410a6121480a03621884881d940491103500d04100780f409c40d4400350295403114010003003402070200010b460710b058030020b5810390525048807101424416500b1000b800ca1424101c2c100e0765991541000081d280100800e5111259802045085030644402421609402d024141c002c1c0340c42880c550744141101d800d94689010302c1c84240c00c60703c20504a60200742c0c0e03a4841184100f440c880d041240482d400c1c06802c5504181c030140500e02c16210080c00030000c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 262165359 1250 262164109 262164113
    0x50f0607061d01020c030403050111030402060d11160b040308010f0f0b0d0e010603050a0512040e0109051b0a17010e090705130204031e060e011b0e04020c0607170903070b070c 77
    0x102d4040c0d91040508003c54464601c1082e8540700c0e03101d880301350356942c2030070070000047c5100b03001c8a002d1540140100d24103500c43c1d04810140c000e2410360004440c0901c4106040785c00f020303000412600c9a0740106a40c0703000e103800f601072039040e000b8403505242c0b1481400203801052002003070380d8003240e465071900fa004503240003030103a42141d0b00d4030b542405c200008101c00083c411110307604c108260307000c00c03440c00c180203228040c40c410261b140c06e5103401044400b41d140c0c44641c01c60741e5032006c203d80d018043c102c0c102c01c0d841051614002040000d0b00355507100e0b45203144e4090600a0440c0f0b02c1c5050502d41165512100d0040e144181c011099601060341168100c0780116840210150000c0304903da40e8203603540c1307000541d410350a107000300c140102d041c407501d0300d0101d64000c041c28040d184482111210003107880d50f500540d0800c43c180060000f001940c1c81040b141e0346010200c0a400b0003041c555074050408240d581c000d11075000020301c00c240b003550040301132400d0001c0b0402d40c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 262166609 1250 262165359 262165391
    0x1021009050a020d05010225021e0316030804061803020303220305010903080a0b040b011d01030e0111040303030e1c210516020106120206031b09090a09030801050f060706 75
    0x4100b0095104901c4031070101041419005440903101816a40d00c0040340c00388054440b6542840084d40300e15022501005004c41da51642c86d2800c01408030303054005d09100d007980300031294000740c452072000310b82009007e60054440420410504c42649120314550104c0c5d564020041c03110b22040c107004e8082d17002482000e10310021034001000788075054083c1009040f1a909403501190f06040c58400c40303481c101401074030030341b0070103a54800400c9020304400504400103e0446d0405450301030408801c04240030b1601c9200000d02c8050303490f4a585806012a1140b9489e15100d0b00085009200074200018480c41c41c2941c2c20310440410315402d03501c40c1d14080c00c4110410b82e1625061180b148501d1402c0181c000c2c081e0001c120040c1c0b42e900100708040e685400951203082040000d4038a0300c0c1d81c802e044014600b10800341413500200028002c0d03581101c2c92812950b41d116000f040c1540700074103074010641501c0901492407450080340051082100160001d5114908101c4000c82 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 262167859 1250 262166609 262166623
    0x1503060102030f0a090503010605011d0112020904020d06170723190306050406060503060c0403060e030702030f0d08070f12090f02040216050c03030a050306130608030a030c0f0e0102100905 83
    0xf00751119a50844498003500300c0b441ea0107101d001c0e61802d8004612940114050070304005804810200500901c0c011642c40e140b0059844a45409100411950302d0b140040c100107940705001203410b905111035080c0d0301c016040380703803800da02001080104000095810901c80000001950000d01000104030483c2901c1d16142e4100703490072001040c00091762005000740e1041c5000d00182d075407030f01016a1081c0a442485590300704010030000101c11f0340c8420642c46400c010703a802d01d5220340000c0c6c20a100d011114001d5040b0108895034560b11040041d4000c0d00c5040800512403585401410303201c1801c105419140d54074841c030103000c074240222220a6000f0402d65484220056040d00701c0c044540864251045c60b4180655260200507203b013962265125410b50703072001d0821080d1039040c810032408543e140d0f400304460b01e09000500401600b618049202084880700500c04c4c0c2c0040090020841c0c1d9618100550380d001c00c0000103481c120784003141e40085403e00c1818294 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 262169109 1250 262167859 262167877
    0x11010f051215120d020309010f03090c0635060904050a1b0f0501031e020f04030b130b01170706081b030901061521020310120c050405010506040302150306010203 71
    0x1819000c0040c1200c40c0100103510303260a0b90445403c8075441e01d11036490610710040805608103020103060395108076048035074100c581c600865050a151101000b002c915000032002a45000980050b48914900c00092544c031043c441c070640941010b07100c1c0c5281c0500114442c42c2c80d01e0101c1e040c010104014038069422881c024081340003042d00c0351100c0007500c1206c03503d0040c1400050550f000340310300fa030500c80707190039030740031080044100c0020340c44044070306640c8200340700c00f001003038a0302d140601c41c0355070300e2042c00c180d5200d08100c0d41c0c964050740002c24000950480444e56240440d00500710b40c0b2034207103039034581c0780c031680640a40350301c00f015000c103d80132082184481c1c054026004a0b140c075840030060000204080321086030001d5807a01d4002070610001c40c4419950085a01c90303000441c84a0700fa440b010fa0185980200e078042e2244403440360207210307078502032040900500080300e001c0d00e490300c0c41d404240850420f441d1100044070100c00100d15900034402c82d60692 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 262170359 1250 262169109 262169137
    0x909060204140d080405210d08060906180f0615071a0a0207110108091903121b020a080a140307110f0316060b0406080a0305040602010c032a0309170406030f0911010f05 74
    0x861009001080c004044402078820448440070606c5420b00c03240ca202c8071000c0a503682407a540305002ced03580e66240501004c1d003025140d50022056686000501a4a03203c1d401a40c0a034103c034028480b00350380944180c0307a4606c1080502c0008400920207280c610027801c1c148070540e6003c061a0a040c1002031070554040144c00b60020140d0000380503c0742040c41070108626140c20015242050071007020b5805680092100c030081000308001c0c241043c9240b6015003280114101c0c00b202c2d0f001610f5440204207565541c2a2b0240140400008810444001c0d42040190b26810002d00c0542c100030745403556948482549440310303005000a003402c0012500c880d8072034600108035901c10b2003140015407030840848812882402104182003281c5a41a2a40d010f4005005880c42c2c1c1c8141b031303051596500b03442000415021243d42c8013003d08032110b442d14034040c4081c0680b0110700b11a40d20340d02e000b90f00000200d0303030712010041d90428603140c0301003030840340156800d02c1200201c141c64 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 262171609 1250 262170359 262170373
    0x10c08031302031203041a0a060b1303060e0a1203020d02090406030b040b130b1612060810060b070822080f07060e01080906010e100909060204140d08040521 69
    0x10800c00c01214155510036000c5a134441100c07040390382c0c54081560010244001d03a4810745803030000364000e42e00301d4142200020080c0e9110f00082d00c2c1c1c1c0c003110703404060181712441001848007078440c1c0c40034400c2c540060140a19550749400200403101034240070705901182400243d0a1a4140c1d40780790b401030700401042d5101d00342201240e0b4101e070115413002031100055401034441b0000388a642c1c1c0140c4048245d15003881c000d400c1c82c2808180002c10440c00c0405118912a00805000340041006000c441810000d4642511240d4204002d0188108480300014400e00e0032904207800e02c80c1c0410005080130417034103890107d648440721500c540c0750217441e14030020424000b2100a80c0b80e408618175000c1c0151444081104c03850020f81001004100181040050541c84004115003000050f11140040101c418903101660703055030205092208000d4007449149016084600b085400c606e6524542d144c8218021903000300d07041d00607020206121102001a1203000041d40c02c3d0f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 262172859 1250 262171609 262171621
    0xc030105040b180d08040611120f0414030913090204020702190e0f0705090405180d02010203040606050312040306111c0e070e06060d150803040f081c0c020d02010c0803 74
    0x20422060350b50001141010350842c4010a000a2a41307110381c09440c0c0c0d460540c0e0726207804008202011a00300b21000401005001d0360b501c04202d403140c8400248c41070b0500300381c10315100034032140e8a203111a03802009401403940e41e0501414041d19590404141e129451010a0190054460080d0041800120946504800900c0302c06503902804038101d243e54501031007040300400e4070f426000c590100308030001030403c0e400003540800b4140c17004515101d1034024a04e041d01000030500141d40c08010310080180c0d60007100d0052030210003c2c2051b0612202a4ad907521a034440240050340d40d4540700c81502820042c0d4000303010240c0070164190a15400c2c4000d030410199031b070401d00031702101281480b4110300c198022400074010347d00382002000703113100400c54011100201240301c00b00040525040006202600c690341115000910705000b00b45042c625030107580d1600c1c0d200300840c00266101c1d8101c00c006404607052108616030b40016941e50703081c0391020700144000410080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 262174109 1250 262172859 262172873
    0x171b06271c05180d1502091503010902070201020606030d0503010b03150409060603060b0405190e010e0d022802010c030807201c0504050612041b0e040c05100806010503090c03010504 80
    0x207002030292181c03001c000400070042e51803240c03031006017500c09901643c0101c0e1035a0b80541414030000d8080300b5003042940194a0360b4001342c0c0200c8200da000246803003156810300910703400541c20ba00520b290540e0901c0640305010501840c0016003010000a1402ca8a01806034001c0f1014204020501090034000040c100c00c0c00b058400d142400c888000d0750030644190b91241440c2c0010040c0081060a550040c0a2003502c0030311075901c0e00281001404240840c401803281c640041200740b0110103585840b03600c082d1244440c1c0d080c0b80482026076002031600161a44c1407800e203925544400d410741e100c00204000c01400b0001c43d85012060a0008030f804011414600e90390500ca91020f00f07c0d1b091040d0300541c0c1d0040c10900c15880c000d80640720054000d80b1071088a00152015004441d00e0012070340511001108401444140002400080040e20050718418400080848041d00760780001c0c00c45810018004001524003405001e410751584000b0000c2c0600d00b02030601030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 262175359 1250 262174109 262174117
    0x4061505030c22091103070e1c05060f091e0c0907031103100e010503190f030c0f12030f0b010c14120f0d060b12070e0d171b06271c05 59
    0x1150712454031440ca1410703012002a45d2241200b43d48c2c50340041c0340c2d4000c2c88041c42e1a04070902007520403508002c0020130078464144501d03d00c108181c8189040080c45103000003400c0120380781d00002d8a444154080850174081170401a40c498156480341035045001b0000d121480e1294080802480507210104c20807804a50701c0c811503504170703620781e0b0401d5180c03210201c0080c480342d002c0109200182c102119200030724000c0c01c3c4020740345400c0d03d031500c4c0300c1c0d0390810444012803c1c101e8040c4054141c0306000b5441c0000368108544e44c48040003900349048001d01a1088030445083c12011360204800310b0002c83c001c401c82d446040b51485d510180c3c20100303600040600742100410380c10600b6003aa81201024911407100d6101e100c42030300c2d40c60301d4400c0c03d604884851180004144441015080140c2c0b10f0381640d41e80d09a030215074011404943d52400340c0e00864140104402d2903843d620304480e040c10302c0e002400480140170f15000450240c03120344403c06103280c610030b402c20064 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 262176609 1250 262175359 262175369
    0x504020a08160207060905010309110306100f08010c1715060f1305061612050403020a1205102a03020702040e0a0b0a050f15041514010e04061505030c22 67
    0x5030070b0300300424800340e0711142940140c0d00000e6100400b00103542c4607400c4810054040c62081c50701142440229040020844e2884a54000380c3d00c100001ca40304a0307040020a080c8008006600740001c0c0180440302d9940701400c0e81d10030700042002c1644594601c4000c1c1802450181c1d0703070900840003c00307a08004c41154140b501001c00142900b820000c68090004011178085503400c0b641e15031405103074021541003040002c1c0404001a1100444207000d818105074035451020540f61003490021607001d584070150a00c000b00030341c00420f64040c0400319160131364a08840e40014200c00230300940304043d62150414107010646400440d034802c1060050700404441e55a0101e5541590703810788512612202d041c00113a10036084007a164040d84005002040e8440400350705003420800380c11402c201c1105c0c01009107150781013030001c91100743c00d460501242d890080580c150892030074240003804400400a03001244010480d03100e40c000c6560000c03001194266240201103130b00074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 262177859 1250 262176609 262176631
    0x60311040b01020109050a0b040f15020301030c05060703140a0212030a0501060906020d050a03050601111b1c020603010504090602070813090507090509070c03110f030d060e06011205100504020a08 86
    0x4038600e54411702912402581040061130740041c1c650301e03009030034002401629800001c1078144001500040720043c0c1c0044000003588035411800c000640c1c40312a07000c1c0384a41e404100d0100000d4100003903030700380400300420700d8480017407080c26800c1c4408480c8c58100c030079000041004880c52680594140c0d8069600d2034541902c4600583e5280b00300c00700000070a509016411503035100c0d03080581d0149040c036007000d504c8a03032038a040ca0890340b000351040701d601d0700b54030308035600344030091042c810301da0f16202c60450800d40101d011440180a0349000395287d400c800103214a980459100301e40c8142501c0d40c1d468841d40701503200364607000303481e40d8506000105121504c505068403d4500c0206a40300c81d0f12212030944003445104022000d1040300a45e140342d40b0030511031035516444d410055070380c5090983c8900111802074028600c0c0d00b100c1020300450307981c041d0130803004810800740040c281e241c08a607440c0e4240245d100325441400065010440390b070002c0003601400c0c807541 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 262179109 1250 262177859 262177871
    0x11409040e100b030c18040602071406160f050406050903030f042904180b15130609051002150702010f02270d020f0616120e0907020106080c01031e06031104 69
    0x3003016124901d0414003544105004030300002c0d1b100041190b0382151044000600d0881507503290003101000d2142000c80c1e4102c1c00411504480d00c03d51034628901a00d0030070f03550070380e030900601240140d00514040107008101892141c808104032800c10782e8040c1201c0e02d9542e6041d8050b105c1c6050b981c10300103414448003404098050304d05440c19106045200d428203082540e07200000c16004003400e80c4428030501495600a4400c02003001a00c450074050ba0345080c6900500420300680c08980200114600c441e4100c0e400b2a1309544244a05901c90185d1503141d0102c2c05072a12442d100c07100c07480050440d0134070b0340d81076488002e0144c070f4044c40728603c115404c0224010600b40007942054252900ca011403421400521200c0f08900241c4c0d4003081c95201c44400c111050b4010000c50641c0161a44500d8407402959008400784000d000d00c90402100d5511402c3e50b141281c14541ca500500b0341c80840f80080c0d125601140f01c040068990724202501c001c2e1900c8091070007146044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 262180359 1250 262179109 262179131
    0xa05130f12120f0203040e070c02131512050606040e0304080d020c040c1d01050d020d050c120f040f1106040b1204060e0d27030215090a0501030911011409040e10 71
    0x3c10a03403c280d8000d1403c0500c3e00302184080d5100504220401010151910059071001c40c140d140c501450703030000d680421400020316031443c40e0005c0c10070302c00ca0403c2a000038030000761240d01c40010760380800d102000001092843c0115080441140610340e841850180d0000d5001e0203504202c806002e01122950190794040b2416a030548106503401d2500032540104020003002c0c04922005203002440515401102c1d01514001114a000642c4924819504a015411031410f40621440307040c00d641c1c1d407100c07844c0500e00401001c02da540328407440d42d41e00241d900401d866034080da5100c1440444402e0220704450486190345014135054488200080b103074151000c03030711200d1000010102003108030f0400508003808070074144c4007200503250032444000640c041840766840c1c40d64081000103441094110504040c0340c040c000d008244203e101740d944034401e0904010340180e4510314110391065401460b0024100049070520b4a0001428100d0520602041201012132 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 262181609 1250 262180359 262180367
    0x4050d03021510030b04060c110f10143904090b10050a0927020403080a12090206120703060302040e0f10060b0a1b0204050705190201110a05130f1212 66
    0x54040170b0056080c1000040c00902c10754040e5100e01a03900344003402c02103011000b864003100140c00320694001c0c61003051700c0b100034040c03504801001d40f84103c079854001d8084944c1003020071001c00c116101c0b0340d08440c54511003600c0112074155606180e4558a031204c8030090040b119015004c2d90301070f00e001c40c100384a0010b40341c0002407030750766444d07582c5019010070181d44940e0641402c686180142501d4028a20081c03004500c00e603096626003403101c0b00900004012407a5091a0b4200089400140d0b00c8408582c910f0088484040c0152a0002c08074018941900f00940181c60180364290215000482c81d1520115130211500da0000c4403108043c0c80f181d00c0750002413941803040c120050301030082c2d401c10034a25170311000c1c481c54940010b8140e400907200d44000c10800200400c80c840310110100c1c000c00b031400288880082c98140c891a44224a02e1004210b000f05080c510060a681c00100400343c9400c6049400d1b00d40140c04000884004102e51103070000c10320032a05801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 262182859 1250 262181609 262181641
    0x108040503040501030c021204030c1503020a050a03050a0902120105013206030402120d0e1302030411090c0d0e0c09070908060106081503190501050903070803160504050d030215 78
    0x100c034001e107090514010055000e0a040c4524406500480c0782071a409a650000b820095001e103080050035480d10900222507a00302d108070f000c02d401042240440340c0c02c441100c2600310903103030010325581c404501c0b00003000c020300000c0d4440f11003044000f0700c0405410042c1a100b40d1260850048000c0d54103e40030030000000024080e040c010403049840c108010795407007800a071240702201c15000b203060421300d90500e15404250401c800c1000e50500c80400b5050400c210011403840c201500c9070310a840c01a0001885800c411b030005103180c0e20403058542d0103085003010301c420450005840c0c3ca1307400f01544640103070042c1c00003aa0310b0340b00d01e58410864130712038003906003039003088011a1065001000740d16000c005080d0b0010a480401000081e4100c00300350340c2c2220f51a00e406400d580c40586460300e298000c1c46840041102801100e8100042c0d1701e03034000340380901c80240da0038095580070700d034040f0050640c0c074181a00850288042d6000380f0a000b000d40d9001c0001d580251 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 262184109 1250 262182859 262182863
    0xd2a030e0a060e150721020a050d05030c0306090403030b040e0307110301050705270a0305030c12031501110f160e0108010908071e02031914010203160c0606051504030b06010804 78
    0x280b0102d11004420b001300040513410b0040c0001405074403040a903003850030401840c4c200680c0200c10709401d218041c45072805031007030340c6081d5183d0700304102c0c0c9004900000c0c1007184203013884004101051300a43c49002001400342c020b0002c44611841e59440c0d401010055a0403820107103100d0180c681881202d20070006601c0e51410a12080140348091002d560705034613800381158080d8030303590f460096200840c410401580d5520005c141d06040200d50382d42c8404220090003440641e03074421460400c400381c00c2ca0003507507841d00ac1640500e001c10440c5481d0560140f0f0411064404034880f124007904c4040e140d0620304d0766581078241c00c0301e091890190001409004081c0000c0035140b002c8804d920a00c180844040d4980010f8200320044e50000a0720216201c00b20420006500401808005100860451034a004c0100780000f20b408a4400c000b110050741c0c00700240d5034495009041c010300480544490400c0120150b8841e000c00d44002c0c1d506800a040e56100c2c1038100e100b5a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 262185359 1250 262184109 262184119
    0x40e0105040b09040f08040f0b031e040c1401051b060123060409230a0203150a12060c09080111090f09060d0818090a02120f01080d2a030e0a060e 64
    0x4e540c40d1101030f266114078000701e498607800c00001540c44209401000540709101d1044e030340f401e18284244010300785100220680350f403401000040b44000310401e00f02d44034211010703a452207580c01210130f442030070795071610101d4451f811140707602c0c002060360595954000190040000c40c040500c1000840001c039841902000309010890f00c1e80c0003032082d0000243c00040c55106a0115000c000044a840c0c8406601108024507450b20403040360038000159080700036142070100c40b071001d00403c0b0020300015210098100e8151160074000c00078444400204203050381c031480c500c8103501003181c0c1480351210b882165658035010800d80d00902009066602c4980d460b038905283d5001005c0700e0354091003001022a658446c80803092081030100f000682d07070f0540034405040d0b140050650507040503004014010842d00041d00842c2c0000c50074201000d06035604030101c2c3c03808401c111580e20546449503400c0540080403030885400c01c0fa00822601d41719032080740c1c1c401d441c1d006a0307401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 262186609 1250 262185359 262185361
    0x6040e190908030a0b0a0f0803030f0702160b0a081501021c020708030d051021030309020307030c03030c050f0118030c08090405010b0301143f1002040e0105040b09 72
    0x14004000e49408001400400851504240e403a11400e07a0002c4904003000d035260200300d110b51070300f246103901610320100c28828880c2031081d690703901e00004080c40890002d07500441c400c54000c10641d00851026121022850340302c144118081d04012600303000b10f081d00c00490050808078140c09111441a070040c0204044500c079202441000613641095004840000ca078200f801c1c0010400c00b0015540490541000c40756101e907120b403580056050302c0d40b00305c4220310000c0001031507075503a01460f000c2242070090000074200b25684c1c0c40107040d01219040001090780201c0310342c01040c000c030300360799218080c0e801c402d090303d028600d11004200d921682c2000030b03018204c0b130500c1c54042c8607214102640540420700b1150284c100f01d44004002c030041110003907070103803115034500948244909482c03020f00c24a500350b08140d901602400942d940c05074024004205003110b0f4610100c1d06842805c165100083d03210380103441080301e071980007051a0400f805100041c1070054280102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 262187859 1250 262186609 262186621
    0x10030b0705030a1d070f090b01080403110705090a0b040b040603080f0f09060a02071a040506040b0c010b0d14010e0c03060714040801060b0a08012103030b03030c0106090c0e06040e 79
    0xd0b40700402c01082960b4904441c90b03840c0d0f130380342040000910b900c01440203078103014040e00d815016900c811401400d040d0b9149459030300843c001c3d0055414141203101c13007810022135040c5001034201542100342c0c1d008011110449800072040e0203000d035000c000100002c8180020713180b0500020b001d550702080007941c4c07010450001d100308800401840c0c00c00b145140082d500f82c2c000c800142c0140c0c841c40042c410206c8070750110a0b000b00c0985524034082c600400300d400c42c0124810080441c07004100c1c00209078081d00301b81c1801c2c8001300f417110303800c1e0386107040d0b401081802c240161541c600300385070860400008201c030300313210000c0c010440f607558190b084440030050503204443c040c081c4000035501609001d400013078007078810415103e0102c001c0060041304140c1c01060440810340c481d0241010521903071200c182c05143c0070980824500c0403e285201c0c41040702190340c0f07040b038000740c48540c039400118030050a654010510110034104044c44c056070040c0d0040e51062000300740 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 262189109 1250 262187859 262187867
    0x9030a02010e040b04050c030906010b040f09020a0c0501180b340c020306090f0c0103060b070f02042c010b060c0d0e010c0b0108060601080105030d05040308033c10030b07 75
    0x4402c260003800030600e44440e501180070b584082d01c0300e4460030404014003807400028440c40d80900b507109001410546000200742243d50799115500c08290700003281c41c00c851103201c0000e0101e401c5002800303025400000c0c0040c0540c6010203541c1e4204810200310302c100702c0a03810020303240301045800d13042501e84101c1d0714085241002ca0900003249450001602c00740300c0c0610980d01d6101a00740070200b2104142803039901c03020309040610300202400708400460542d00b0003a08420340410950070351000c24005c6c400c04030b050781c0c0d050301c100d09200c0202105c00d0345992240545c0c020b00c00c120019080c80300c1030003074501e82c03c130303a4100e01a91180c0b14810a41c10390303902014982a40541c805880e0483d0f000820707002000c05401210410507c1c0d6000300c1100e00400040e0b000b03000c0740d02c00c00002070160007a4000208584000404502000c0a4000000307404100c420480c2000800b161842180e006152200307031200ca010303001925465101d00701c102140c1e0008203400d82e0f40d5900908503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 262190359 1250 262189109 262189127
    0x90203060f010e061e0c070501020a0807140c031c120501050906100903171b060606041406040f0f0317030c0304020d030203130608060117040c0501080601120c0201050f090309030a0201 81
    0x5404c85010f200080b515910f200c1d02403104981c0003211a0740306a0102c03603500304202034200c1e605550044801c40300091042040741d42c016003108454503422583d042140c100103c503255194144074549607000c03048407011448100751019101c1c0580c80050700e100d02c06907082482415031048000002400e60709125806500001d41407801c2d12040303480307036a10410503031703070701340c0881480408107010306114404ea402e020b210a404c00140124a0448001a800c3c411303401041800da1403170405201070307103680e01a9805000050641801c03203844400701500c1000903c81903030303401801030321030400303440400c1160b00070200350041c10b00c1d603510342d024440351141090044085100030420020b0040060000101601180c0d5400707030507051030340c0014011901100744c00c68841d104000d100024107416180000c80320300f800d1445c81680ca40005840c0303844d011820007422410541311010056065000301e206e010a089400e0071511084c041079035a006556041d034269102c0341d0024055800f0302808 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 262191609 1250 262190359 262190387
    0x21e06070f020321010302100c05060415111209071a1801090902030a050f09010b060415050405030a1202011d0d080414161508160e041d060709090203060f01 69
    0x100c3c81d10f44942190000e040d10701016000e44074410005004500e8040d038584052340c21454032031110110b68407615203e41c40500001c00d41c5008400d44079065000303400182c0081c0c48450f2550300d80008901240302c0e42d00444030310313000340107020010074240e0180200e8201e0030b100c010a82e00f0401700c0854480540141c06016041c44125440080c001c4402d0004600c500c1c1c000d1004505814100c0440f4443c2c0800303890944142d04003056802036488460030f81e0201d8442c174001e504080d125a0055901e48110b80002d034150040044100901c038984a030f812220f440c0d507008000100e141842c80030a0982a00305485035001110001c404610a0542d1038120b8064180180b903211102c6900d864120400d0f45c070040202c0004081041000c081a4240020110300b0004031034501003880040801c00300100d4400d00c0181c86100400351510b91107014000c1e281c139110601c5100d20f0801c0c03035882c00120354203800500700c1d0a01140c040030a000b640e005000c054000040740345410015640c803404980c003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 262192859 1250 262191609 262191613
    0x1707030209090108010b01090501050a120504060b04020a020601030507050d0b0406020c0f07140f040e060115172502121b01110a0e0909010b06120c0d05090706021e06070f02 76
    0x5107401c2c2d40c451075400e00030404a40000b4040f25410005801d941c1c96502c4181408000d100401880d0381040014600c040d022130009815034407842d00718020400c3c0418a0382041c80403d11681d0309800260540c142c074050001c03070703162561b100100845151401c01c01015200302038081000182c00c0d8002d05002c0e003100080e600d000000280032841c00190b0340c08041062045000b90500b0300b807686c5841c64a8138240c5003841400d040c03401c02642d07000c040c0301e50030359000005c1d1484134070b07881620110300ca0911b11080501c103041402c04203041c1c400422610081c2a41a141c507014940000b40319544950303030880c80c40c03c011491148140e034202c10500da07805075496034a1460040b68400003400031800d140c0794549824054014004c03010301c0204111b900fa03242802c85032559a80d04140c80c1d4048c1041c1c0d03240c000d0768034424200500c4c01403040d048a450701b40300511140840100d40201940e280b03500f2a404050450601507801c2c40303080ca010000d822510100300550b2090202481d18001401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 262194109 1250 262192859 262192867
    0x602100903111c1d0d0807050703080d0203010f0e090601090c0c0209040b01060207080f0c130b030105070c02010e030d08040f1a0114041107050d0c05010e01090803060a050a030317070302 82
    0x8025041014a07070600d840242034a456a00413030308148900a41da582a904107024120300703021030810448002d0103031424102141c900d0401104200c440702866005410700d0701c4141030312514001e500280503505a856580402050390a501d0412074405e0340058000c1c0381503440c10814800034040c144070302c01081141c0301d410300940c6401084c903014510800d0344254a44c94403074001e007040f101381c0062580b80c02400180c100c1001c00503007002d002c5010ad41d04180c0d04245614a8002c0506164481c2c041d4244420860303084d4100070056001c6000781c864080c40e40c2000101516801141c0f191004600e0040c00f0801150444004400452003450f021085201541200608032400d0340003051064103030207485c0140c18140a00d0700800e01c0c2c0302f01e031410040c2541e80d294440c900108484100281119240284002500320354100c1032070714002c001804050401e01d4496000300c0e0420300600300d0150010721803c000303410300103d907010384d00d000e40448020200c0407a41400791140b420150280 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 262195359 1250 262194109 262194137
    0x30507140304081204031407060903030302031005101d121e0c19150807050f13150e0f0a1d0403230408240a11070506040c05030f03040602100903 64
    0xa289504c40c3d04d01c030a07903140c52852911401401001c50209810703003100400b0041aa00a9a26010359606040168803644c0705404c50111810310b900c01c90740008000300c0c2c3e1810a070403640070600e504d40644240f09100c400c00a00200e429560b081134860392001050142240c070880529011403c0d00099860181008000801c1c000794130b0388140309192020000c0012000b00c1c010300c01589020304010165180409001c0c041d03002c7d00e900c43e4600b020000c0c080e8464006888100042c250300c40c003140901a0b0020010101e81c3c035400d086018035421692010289400b81040b030448200100f01014480c401542180c9210081d1089041c0944085040c0100440d14040c07401980c0802585444900d412182450a0442480130b50310b0300100c242101e21024210710742e0703800740c600b000108650040f2450401188519a0060824007840c0305101c100b00015100b8821180d0480031124400e4030340028a8032440346110340c40150f40040100294100345402c44081c80c0d000e8100720394540800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 262196609 1250 262195359 262195363
    0x70b010915060f0f0e0310060b090f0a15030c050706020c03030708060409210507080409020307090509160e1201140402120f0a0602030901021909030201140703050714030408 76
    0x80c0c11405045480c1e4500d0a080300c032480854000380ba840c900707080500704416000d0100b003501c0940000b001749004020006407010440c1d001200d941180c100308541e40c84001c2400c5410140143d480f8001c00c816491031440d210791a48140c48101500b2500c0c80c8100300185c004003545040c0805020301804190042183c620107082031060a4018650328503000d84020040d0100400c0c10303104510b800900d00c0410b21071201e1702c0c507059029502460440d03541c2d40c259030900070400010004007000402040099140e0051070090075541c07184030300684c42d5130800c07000b04021640202e00c0380b007c0d0203100c5101d120b8000f14071140360250010f803c000d124004203080d9407a8007014941200c051040c802141480c140342210070500001400000707000000700b80d10f41041050203440c803900480851100182903048a104030100f81d0421003880d00e40102400c0c42885100c10b03400f2560000500c0d54102c8100115401b15600d550b5540c500401503a4041e40c11030701103080203851105020105460b001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 262197859 1250 262196609 262196611
    0x212091813051501091404080304030c080f070f021804080307050f0d050108010507090b0c0705010e0604080607090801060b1303080d0e0102040f14121c020f07060c060f05060109120206070b 83
    0x36003e00401150f0501281800fa904041c0c0b01c84519150001000302180d060b005407030300103a1620700441040514100340c25a8001d980f00c5070700c107140008160040007141186500198825a410205100340b0030810840d1130781102d014080c0b290400000301020300c03d000400440200310362542c1040c1000c1c0004049403000d0300261120303075440043c0850b403900104001c0040c40c64407909440c19211f140115180e40981c17040038180b01d00030341d9460183d134489040c4d0700900000c104407139440c40c0501000380140074510030f1100b25460141c01060701c007810411911822039000d801125185141d98005150b484188280c7c0c0d00759442034040304079403013070000f040141046800504e80c1400e00b180c0030920884503082e24858656503170031189030311001c0703040340040c28010080000d0804440c2c0517400c0010192141c00c103130040030004509a07801c9000b200840e070244004100c103030300b0046040c04803002135500d02c0c0440c0101d4010400000d410750000c5240d840500298208a07895136080f80e6140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 262199109 1250 262197859 262197883
    0x9030a0b130f03030c080907060f05090d050102030a0c1107120201050705100c0816032306030a0501020d1514010806100908030304080a030e0601061409060403020d12021209181305 79
    0x24441c52003285c815804508540c008494001411a4514240020380302600030113280042c05800f00300c6210301e03542e18a0542c2002c3d001802555285840f4015600074140c0c18024408100e101c81c8071b031510384d00012000b05450200c15a61207403059a001581d644d0400c0204807000d119060385007010072081e004031000d4503003584848500e400d01c3c101c0b01d494007005107100d00401d842c1810200c003000c500040503218041c11510b4030181e03240c01002c07034108140100c0140c029800040d28102003145070344510b49202c1601d5041e142d580d190729100c5405c110f204503141c0096505804951030b450401186002028135042c0412025542c09081c0c0c103640040f1400d446903d0301007082540c00f5050f00418010100b203002034030035503040c028040c0c68488403465001034040301058000f400c1d100c02003154041e40c1c00a02450fa280042d01c0c00b2084201000310381001805000f0301200000642801c0d980c460304c004000e000420108502d482c1d08000003030814464268034802c2001086041c0100c3c0380c0b5030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 262200359 1250 262199109 262199111
    0x207021f0f080a090816020d0f080307080c030402060d0c09081506030105070e0a06030b0102011e0e0f07050609010503040507050a150207050102030301140d02030c04150305011109030a0b130f0303 86
    0x3a40800203008000c008103080f00c03c90510502d140016004421102003809a000c8405080e40c14004159140c000a07402040c0d031250b120400c0c1807182c144040c5110781e55036516805640d5450700340000c0c07800169030080d00201f00b440943d1640d1b03030715000302e05484924504151515a10500180342c2143c002d2203803c3c00c1a000d05105880c00d0078010150302851604158248c10340c1100829141505403183c82c042581e5641c01c0d0145038401c0d088040e01c5010070000300c0a0688800c0490014060501c600ba49840380c040f2080807004d0200d1a0760455200801250825200703100640703c5a2004001329950f01840c08042583d955010218002d000398018004440310b822001a181440ca908485d055600a000411031007a02d8501031a9400e801d0750452103d140902c0030a103000507803400c00d42d000342011044161000e0b11040c050849024030024406070003120b49900c094403a59046a401d40c01a440440c00b0030080703000c8a8219010f1170419001d20301c90b86500b401c03011051000c400003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 262201609 1250 262200359 262200377
    0x1503081b011d150603060106050c030c03040e072c010c06060e090105070f020601120201050c010e0618160f09050601051c09020405060105091003110702061b071e0303030207021f 78
    0xb09020003910b90440d44016520072a030030b0a4001a903244414401e07a404c0000c0040d40c448007000500955841c00301ca041202d85607501d5401410901c0340132540c40c0c0000354812074081c0c400601c0a0400e40c80c0e00c001090703010b2a2002c40044030074078100642a1200c1d80c58143c0001c188644201c42403064560740d00006180c20180400bd291100b900d0b6803001b10f602030801840b0031001012421407881c0c1c2400c14907a030300c006524560240c994a20322038458011501040040005984203004241c5501c5c00d84051110780e11104012a02c1c0d800340032440d070804401400b9010142c0d001d03a410040506000d130a24510a90208611030400a04403525849040c0c5401314203003070107015000902400d01600b4802c4e0307800417031245403201c40082d0070952203800644445c0d0703500084501440c2c004e09207030399845000711060540b46a0340c03021899442041d2000070910078107880c141c10041d0701813124540341d03c1c6407000c5019410504c01079a10400302c00d0103284105103800d070800d0303401d42521400e6613 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 262202859 1250 262201609 262201661
    0x2160b03040b061005030a05040f060903090315020c0303191107080403020f04050c0a03090201180e010e06060901020304090506010216090b131a0d050a0f08120108011503081b01 78
    0x18018003e41841d01030203a410326402c0007074000080e680d02150b070401c001003a0751981418176900c2503c0350050002480d1900030800c2c9035100d1001e20550340204000080c0c400c00d060160200e02c206c070b0701d03484950001d01c00304502482d4500000c06124500b0008a0001109500c6c51982e07400560101c40304000014100110f05052001c00c420354000c4030308004501d0590441d405500c1190440c0c0c04142d0b076801d0b11421680035030607412001d80760f032101d00c04042e159a4906480340080c0181d40e6a0100e03a00090074603e001000c41d03c0c003500603400343d400c2520b03010b920b10140501030002415805041c1d0019844541c00010000900f08220301081580c9040c040c0005400100303002240789007040c0d003a80800e1001801501d140005035074640d40f40c0c086081913410b06089000090124070260700704400c0c44a004c01820f490800c00246000c140d03642c401e4242210024004808044845c0004201245025002e0852030540d21582d80f0b00d030840d4400c0d41c0c00c6034040d0a84170344000c500540c0200d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 262204109 1250 262202859 262202873
    0x191202030a080307051b030412030c06060e07020d030e0105090703020112020405060f070210032906210105150c07150507050f03040906050f06040522060602060f0703150605030702160b0304 83
    0x9401b43c0400994035050904480f09901c44858070081e09020306903980c0001c001040d40880001d06840402c08860704210100a440d04040703610880002c0c14100d44030f991000602c1600e00440d4040014403d607450b5030b005407282e03140702e00101303212642440b0001d00c035102d040040c0610340503151004d940e448a4070402c804500c592180a04041ca08144d0703082a01c041d00000b445180b1041c00e6910409500001503241c0c4915480c00215181c07400c0c008208a60084040c0d050f0380c8200d03542800f0014400e8441e11a000c0c0e01d82e4440f8030b503c0010b0800c16080303030300e004202102072490300d1480e0205540b10035107031050f20701a01846500c002010810f0ba4220300c0f901c0040c0c8002c88800704d0041c8503100040e0b240c000d60088911920700c5c83e60400341c01480720b042050b8508181c40501c12540d5501c4003075101c00c0100e4240b0300c405840310000d01c41520920500034100802c071000c400e031904012046906400007083c40301903100d0214030585a60695454400401d00343d151140c1d64030f07103454201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 262205359 1250 262204109 262204147
    0x30216080114061309060603110a06050307140304170304051e1b0f0616050a030305060409021c0305041e1404290414040302030a020c191202030a08030705 68
    0x50300c5915000c00d50210700600c0307100700d030091002c80f070030001d845511642c43c008200214000f4002403408000104020808200d403080ca90708441c40100c0c2517641400f6038451000702c407008000f42c010f02a00f62552010b401070f540050080a03103003c3c014511044041980c81520142e425600c00d4076207012076180480c51190000c0840040c01c55503000181d000421070155800303910404054000700c0d034a80f0f42d54140d40442c3e07852044031000d60030381c0c101551280c0303c1c018243c1c0040c1c103000002d8414205406003010090b806000419640703050b02c0d0078894001c2c60403088041050400000075035403007041080420841020b80c2072402c0b450712081a00c209040d461881c05a420a00000c50400f0310003489046224100c0c40010364003001030004004040d0340108491145100080c8028994001301400a01d8125000c58074122105410030641081e0001e183e03006512020060007006a0341c4c030107401880c8080c00301c40c0411842c0e82e55203a56081207841100081000c18100c0c1c01c0c00c4201510 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 262206609 1250 262205359 262205369
    0x1302040903030207050124050603090c0d0c0801050f070c020405060414070210060f080618010227010e010903170906091804120302040308031506072a0806130212070f03030216 77
    0x1f8a09030500752510311700c40e100d0700c5000e00c92200440003807a91a000e001010000d00e00030f121484000c1c003440d04001c01c1c004c0303010b2481b031586030100140c4003482503d0545d0185100e610b0b18034044580f5820000540401031a450300f03d5102e851501c2d18401c03d6030264050f03c529005400f0940080030000c0440b61141e000c514240c00c2c01c10100403444020030050340000124840f03688482950603030030b000e48655403601c2883c080c06201e01e0f4910b8110301210015000036a00c2d2900e2030703903480046a401069000181c411443c0600600582030f4000040c184940082c08150038100354100044100142d250010354000c012230406c400c02955000ca108540310320700342103040c14110f86030000d080c0001840d42026071500e0111390502c0d681c0109603190150301c030140d0b00004a05095201049213056a4241640c0380c02c030b004500c1350780c089201031040b000c100041a941c21250200000c602000d84503500a0141101c040368581d520400200030314000c0c0c00a102081b0203024800c10030b80c0d69400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 262207859 1250 262206609 262206641
    0xa240902060706021b0d0201020a0305090619020a031508010b01080906160f09050910080f070303021b010509120c03120a0c0b0a0f0c02010501090e210313020409030302070501 77
    0x104010307500c078801d0303602041d080800140c0301c58a81c00d68140e00740911910340501c3c4151842052001e6054004200d1020299000d1099880d100d01042c0c5d41d0b00183e41d510380b001659220000c5d4450264050035440005140214800800421200d40880e041e0403000031a5112000c0301860358009080e281c02c0f202d03000080c5054941803000140f02c411101e01442004210700000010358440d8610b140034040044c9404c616003030200e642d0340d4414203481200c0c014003d803024001c0c2d01c071001c5a01001c89030150054003104400e02c60b28003500c00d84843d854103008080c80801d078507484c0c0381108980204004001c0000e20f04840c1014a0600110700c2e10026400400000c1007446e8044001d024550344075804421039100e840c001c1d0054849201003c441515014000d00031540c1500098100c036a000e00411140382000000e540f6000000140243c14210320022803503c00940300030740d403010b014503a01921881507400070b0140e40441c08198000781c0c0114080c403d000c070a1140395109408522 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 262209109 1250 262207859 262207871
    0x3030e090c040509040f15050f060306011505040b0d0f110a03060506040f05011214100e01090527010605060d1a03010c230919031205040522020c0a24 66
    0x40001d4404c90020802007240c0c114401c3d400400c0709000d03100c181c4140030031090100d4a4000e458030407a81007162814070034891080009416090000308500032043e59441c64581410800007080319841050401c40c1c03141e40e003120005940c1544160f18070b0041e010b1801d0365a0b601c1d010300a05940243e080307544950401c05c0300300b2420680007521000c407075013800e0402c45481d02e9060300f40100540c000801400035a10200487c0c00c028801c4c031400d4071580002ca100c140d072204a1601120001c6401030030120f8000000b0001c5421016002d40100b00320001160541c2c98001040540e0000c500301c0c00840c1d11069840007001c0c000d0b00401481e06e099000b0030050719454001068591301504440d031035401742489046210ba41c2e012110b5070b4001030b007001c1009501003140d01c0034406512082d15906840c00501c10054030400c00c0b101241d50040507140414044c1541401c4450507481118505500f0480c04030030100601c071401c560750260703451401038106900801c045070034424008145030328100b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 262210359 1250 262209109 262209119
    0x1c260703090b0313150207061104060f03023108070305070e090c010207031106070b0c09011e020d050906120f0402010e03010e1e191104060501031e0f0605060403030e090c04 76
    0x3002481010f90480414001226810f040e00000e2240b0752014041c00d081c05120700c05035027010024400c881450b83c5e000015241074804500b24020454881802056480b007804000080407140380b01007194568410301540e1500c2c603e1030039031142d100715050340010320308100c540d580400d000c1e4403030241c5014018a00007100000d4441041d03000040404500c08054041c41d222a401d80f10450f0b8082c0342154a401c080d514008a0b800000020b4009002c441e010320440c100044901c81100b8160000c01203081002d00c16034146d0441d2070015003000f020700c0049440c20807441140c0c0201e20030f20b8151802d080c9030000401d45012a01e5850080c1c1c10055000a524030014106100c2001002c4c64000c0c50302c40203c442c200940d01c51140800c6060003581003c6c801d4000c4c49612080003110200900c5686400550940c1c00e241c12030409124401c2d41030050002c1c5400000312000119000921b8a44900008545400540041d000a0350100c0c08100b507040040b29140c2003400d044106040510700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 262211609 1250 262210359 262210381
    0xe0d0b060d0204063c03020d0b1b070f02040c110a120309080a1d030102030702100f1104270903050702010c0302070503070609030506090705030a0f050c130b19051c260703090b03 78
    0x10f40001046580c404000901c0c1c072b200422055207900a44402036a110804d00f0456007000b005201039115504d0800c200c80054007039806001024030020107450145e1141d101e420200c2126a003d405040c2c030f13010184000381c01c08005104456040d22904400d8401c0107688903d089038100d00d600a0303104105120300180c00103504071503d00c0c01e01001c18480a51a6200050034440e8000690801e000c40d000c01ca0000501040070084142004021415070325108801521007000f000350109104100c9413001d07511840100f01c250f030090044034103890380e03280070030300c0c01a813a440785001604a041c2070040140032b00049410103168801491160300b1722700003945900718000010301e0048151000d0080000600218403400c100800654105030f8150030074010f41208030410744159103061809d0908140559207205854000c0c2c81200440c11030090f0130700100c00301109482c204011983c4500040300c0d42c0030740030060300e41003515032166190f240140042e1040d402541444400307104101e119185 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 262212859 1250 262211609 262211629
    0x10080c0d050613050c090406020a12090b04080d09140105060f04020301051c1403030a0204090605100f1101090203030c030d0e06041e0c180902010e0d0b060d0204063c0302 75
    0x40e1100c88002d03503c551416602d046030000c00c2c584c11800f02420002441019405070a9203a110348400d4004403001d13000a04407146990002d1680400314042008180f8990140c96a81c0e185080019040080d4560100c201124181c0c101c00ea912281000741c03500300540c0d200000b0100352010342c06d650520000030303d0706103810000400c0391002e03901002813181c42500700d070b9050001015207a5030b041089600002e5409401840700d0301d802d1110009503420050284406c00416a450000e065a040302c121307440212000e2541d181d648403408900940e40c01d0000380103000c0450300039a61001044820420344a655801030080d4100f0710400010401c090100d540550040d400f0211509403484d00d40c040d69000e0f00b08204500300049070a070303890061381c003100c0d14138000d88800340d60300240c1c410001e0442c03a03400001d01c104441030106208d42420003c03c48041d1000780b022640c5e6454a000a10400202c3d03407803007075400c0d21072046860b0044ca0040303e082d80104504208050b0440e004160399401e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 262214109 1250 262212859 262212871
    0x4080a0b15010e18070507020d05070503151614040b1c05010b04060206040303020a050415050703031a0303071103070b130f061706060a1e18090504050d11100510080c0d0506 76
    0x2a07030004900ca1300c00c50485071f0140e4024140000c080c0c11f4240313260b442c249405000e00038071400b03d6440f840301034112540d10404a410609029600034002120701c5141c0016841c2003110038000401c201120718040c103030403c2c4400c04c92540810404620b41a04c6042c0e0201d0f80c040402c02003402290343c08608143e025415040141c0e880994440c12101d03031290342c0c04001c021460442001c01b103a4480000c04800d80030399001d200640192a040708920150660a0352540c4204600c0c000101c1a203e1710101c500c008007034400707169446c0710824007030b07000b014116400b12914000744200704003003100c08064001845d01c843c00c0032100a510350080f2001e400288106004203407200c84078440d00041c0310340043e03020181c001c0d182d00e040280081d011000759072005441da0001094454040c42883d1140da0801c0061498040e010300c183c8075814a00005071190113504200c0300603c440b40150390041070000000035001c1d2805000c90304064409035018820310b92900490b020a8001824580200e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 262215359 1250 262214109 262214149
    0x507050d14030d0e010b010e030705120709020c0706020d0503100902090f0d03020d030c080c030417042301090503030901120e010f0f0207061407091401030204080a0b15010e 76
    0xc515040001050101c00080e0603540b100140703a00c402e036581d0304180c955014000081c8000e940c1e040044d80c5080c400201550554409101003060749070081e040001c20f01c9002c26201c2c82038036100310000340d90000300d807403440d40e001b4030701084210307030400078660038001c503103000340c29418881c8048902c0e5584c0d01c0792404075a008201c1100b81d90b0350551100a81031300500110038480103150107910b903100074202c040840d00d03100005610601545e003c07445900d101c03172440e1560b510380e030712a40054802007060f042c0c06010700005c00c0600240580540c580c1000700850072031268400010304034045500602c0c000e0700144000c0c003d69803c41041155990207040126400484d01001401460100d2000d0b04050034152404035440c2164014510540650307024009042040ca0405101034207842840000380b40c10800c02110001250351402c1100c1450054941651681074524043c0c4012054a4a42c1c905040c800300d0001c0d004030b840100001e09100b1468062000000e40103908003150500f0310b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 262216609 1250 262215359 262215379
    0xf010e0c0409020a180506040503071205010608070308040e221101020c0307060302191407121e031d0c06040504150f08030c060a14070f14180108060607050705 70
    0x155940c50558001d0500741c002151107900148004041c842c103010b041504243e010740c00709590600d602140c0a542000e001000542d02d0406c02480400328203a00b61144d540c0c813800448e42030820300410000314000c02c5010386071070611031130807040301c40a002e91134100402481112042c802d584c1d5001c089410004000c0b0340c580190040c1c1c20080c107000300581c140248040030a155405d035010b0580b940103200402c0050200210913502030104618002e1107803000d0003104005802420007059000c040c1c0751203540c4202c99062143c142d0550b4500a0119403112815880c0e4502d89103001c0c11010150000c000c0d4111140103e2014815406224040e503241c001c074000356401800c88000401000a42c4e0030303402d81c0c03080c6640d22074210f042d03e0050340c066200403400c20a00c0f4003c00281091141c207003005a00c8259040d1403401e1104581824807032041d91015050080c100602912800001030642d0b2003901740006000c1400201302078800c0390309102e07100100b0780c00111790b02552b40c16074880c210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 262217859 1250 262216609 262216621
    0x102040f05060a1e0c0c050f090408070809150304030806150306040e190c030c09021e0a0e090901020d111201270e030a030b06180418060609050f0f0f010e 68
    0x707112032a000c0244078882c0f444031500c00c245d20003070041c01207001c0c2601d0070f103080d00d4a04005c00c4042c0c0c50f1a041d8001e0b91400841c012400c41d40040c0380759840f40384403516110050f00443c80c031819844142c0c040010210401061640102180d50310280031a0001c00f030036407a4035500103900018002d61300403035545c038a20304000b070204030b0000502058001c045c80740c031052410101143c00d03404121411004204002442d012a000b030b01e2494038800d822040454440111420702d4102c54041e20820240c0104103d098440c0716103070780101540400540e6079411075542000340c0f1883c10032814440c0c000c002d10510f083d010064035040d1030310074102d4610a0300c0304400245a640c28021f40c2d0300c45107061801d40c401c000000052243c9070240d01c3c24002e249001e8200050383c0103215901c0d240c1c21b20051100d00034074281d0b00400d0719544e40707038030b1051504813910388408440e480d400480d000c555850a2181400c41d041c1d44aa20540d08400c4071078516003805484100d07801841384280219840c07003c242c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 262219109 1250 262217859 262217867
    0x20c12030a090506010e0412050a020303040204020d0207080a170601170f04050a050f012f0a03200d0e06061005072d150c260a0f020a110c01020102040f05060a 70
    0x1481c00c3d04201100c50a5031140341213203a07802e0581d0b0448807071125664032145070303004500f620303240304c400c0c0c0203181142d8958090002030b42c4610407503803113141c1c00c22903280020380311b501800009215564440301507a070715255030b16008001d44120706004e0059041e5241800e0194019441503166442485c103850364a81a031a050f900c0d00c00401a000e8242c0f440c2c0d80c46015848601c80801c001c0c002180d1399080c150081c0c801c008002081000e01042140080e8503000fa001483c002d4124480070040c2ca0b40105036042c182c00c04c0d00d4601a6a17152405e41104d10810803d10b60000011203000c02c4040705854041c10901c9061002440a05581c9440c0911140c80c0c1c01c01613070805c0b44a80c166000f1903860709515060348180f1502d5140e00d824810803030148608155a0541e40410030f9030303c00b1202d42416843e19200078954a50582c403010203184041403400600480d141c1611503840003c0c5004000341407000c2c0a90450440e0b10600081059200008540e41101c00c02e0b1041540d80c5e5880320215 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 262220359 1250 262219109 262219121
    0x40f050f040207050a031106010501030504020f2206080a06110f19020309030604140607090b041e0b0a0206100905040503070b04020f040c231809100e04050303041401020c12030a 78
    0x141850081c5003610086c56000b101030b510b103c1c01401501e085a803103500640c115a0146c50180d08003101c00340c19007060400074a5886560342f50f41d416904070b0740e8000c2d00070a580d40c0d600240c900390440303002c200801102e0b0180c00100ad070140758440c18a0b600c1500c02005000c0c0e0841064550b00344260001218024011540245030142c00d8501e1071409040003062036440c0903068881d441040001348105115190800a541c83c085006251502d002507141140400e500c58032402030341c407880080c4180151006105a40d841e0f0042d1003d0724128540d1400410300368001c9a825040508100003d000401203031402644000290034540307941c004640f014500d0403805801c00d140000001009400c0f880681008000d9816100041100550303949540200004000c401c10440603000080c42c000c2d8080303500c640402c5100c81859a5100d800b48541400e94007998180c100100340424001483e4820500700881402945020020b040140c2e0314103101150380000c00c0c0200c04a40c000800d50400f0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 262221609 1250 262220359 262220363
    0x181e11040b070b06091321020106080609101419180f050a0b0109020f030406090f0507090c08060a0605031605160602190f0804080f07080301080f0d05040f050f040207 73
    0x941e498450525103c080d0b10002c0e903d843c441c0c03102d400064801000403005410300b40d4092143c40c1c0c0910410403001400c1d401d07030f16030001e65480d103101085110007000403600c101c1c0f4060080c0440c004185c2c0c01805c03100040600000c0100f82030402811002c11081180104201c544c00505071703131030312007259829000d040d0062500100342d14640a00500060050546025080d481e01503641d40302410120311a10f803010204490900014000c00c030240c0c00b92001b20f00640480e082c890242e076959051200c150000d800c20f42d9a607070003109041e480b040295203c0410354402d80007a00303021014005010040200c00240f10303052000716a02e00c114141c80a010605210408500b48c0345080d0000c0e401c004000d800c20180076400d00700350f502c98030110303403028510307140c80c0019199030710345444030f1384512446080c004080249a00003a0420019802051414060000081c2c1a2046400d004a0701c000f2020410144014449201c01d080ea01c07003100ea0880b008036080802c03502242c040c1c082e000c80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 262222859 1250 262221609 262221629
    0x130f0c0804170c10050c0a0906020c1309020301090618140606151b100e061003020a030f0305070519030807020106030c090b040e030c2b0c06020d091b181e1104 70
    0x1c1c0710040716800058280140141ca070801109c1e01c4d044103d90301d131003041c841035005484213440c0142c2809540032030075480c0054004200c090141e1a080181c0317405a0980150000751242182400302038814004000340c0381c4090010341c05c080c00040c440803545d00b08c8402d12800056440110b500c00200d00141480b0442601c24090680034407400a2081000140c0d840c026200001e024007400140ca006403035004081000e10380c1075486400001c554058100d0a100e810856403012900401522416603c200400c15186681d0b00c0c0c02080c0c8078026040f0015603050a00610004412581d030a080c1d030849080000d003845840002009403c032411441c440340000143c0c98861000459804a0013035501d80c400c00a0482c868102006d80c0100c0900e4006a86400d41000190a5400400240390002ca003c41e80c0040e54a881c0d203981c030044e410303085040c080c2200f003200400e0455049080903080c0310400455041000c0643d50030315a400c4029030fa66100000c0701d6050840007a1405003220b012 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 262224109 1250 262222859 262222861
    0x6060906030133050402130e101d042d030e0609060d0e0c2b03050f0d1e060f050904170a020c0406050609011d040605130f0c0804170c1005 61
    0x45031111204290192245014541c0807504e82864000c9036031845003039565400e4286405044242d915001d0308102c8140c028900004101600708511107044a45c401b00da18141028504118401001d850708607280340c11103004498021030300c0b82c01400c0c80e090700300250058a03420026940d446000091903010768045241c682c0c100407940038610480400080300d10140c2c00401708080c0c2244848110001060741c4865601c40d14901d8420f080d140c46070410364106201020441e005401c00100c07600c8099450100032001491b202e615400c12101d403000b0408242080041a450289801030600030070500d4082410845401c07141c03c04002c0c1ca031111078607165155402034441000b4080c043c803036030812201040340e14040303003101c150b084140c41d14110407000c040e0049a41d6001d500450f030043e41c9103000600c1e41c0b2001c801240d590310841000484c0300c0e50307004070b1040340c0003e0401c4c010800c2c2481000002201e803018011021081d401007502d43c240c20101ca454490601070112050342884 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 262225359 1250 262224109 262224161
    0x40327270b100801050a0b1314040204090204060509040f11070201050304050312040c0602070f060909050a0902130b040e01180b04060b0a0b0403021f050406030e0f0105070e030f0609060609060301 86
    0x2d0140c181c542c1160549201c507659480c0c20058001d080917020708d0b0483c80b030f00308460b5180409481c1c104002800c0582441c1d62055108205d0b0000e0380b010001c14000154410280340a00c21495074180c01c2c00d040198030040c82c00ca4003a801050802410701c07400002040038450200140c9060500c1c4483c003000600d00361420380b1001456100d0200580305038103010845500e035070f20040070780f400755a808000700d02d06010300002d072202500d9880d01030780d6090500c016840b5a285130000780303000840403440310b60185c00e00048070380da203007142196490141e20042c0b07020700300c004d190300903041000540e039501c030303810128024080464401d5029000c103900090303190401c0058003c8900031205041e00101c2c064441c0c880e20010740802c40001e208000910483c4c4c081d074010b0241e0f00c1200101c4460b2007080b8401d03030859100390303100000300d07088540030b02440c50700300000e66605c0c91000242c805420304c1c0105503980c040140c0300900c1072070601c0020351107450075807010740c0940d40b54801c01c221544034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 262226609 1250 262225359 262225367
    0x27151e020403050d120b01020c0108041a07090614040302060f031b0301030b040314070b04021201020c15012408040b04080d1b020f010b09010329040327270b10 70
    0xd1844c180401d0b4007040010034244944101c150026040e00542a4000c5100044590980003007048a40c56101040e002c1c03144003040ea620700c03408203511000b81d064240840074004056062040d03245c90340400c4184016190481030b142d400025a5140362240c490b9010b084140340d5100729041c030504040000000e00c41041c0380c9500482c040e4450480c0b20850001120140c401c09030082c14885a14001c10010304004203907650b044052400141005004841c59003401140011a115100c0c1080103004828140300c0503400340e555900d542c000384216100142980c080200302600340c0b00c07040006024070990204580b0725055866080181c000d950701c2c1241c040402d0002d034401031140383e0540d040c002051090015100303006103c402a0b070f103155030710544036044c080071110018100a25489030704042105501951280c3c4a0303800500484e0400c24440102c10603a000043c41400b040104140c0648c0c5110301f80c412509441080070a0302510307010304000e405040d04002d07140481c0d024140d00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 262227859 1250 262226609 262226623
    0x2030402010e0103110a08041104020423040c0807210c020a1b06091202040608010507050408100c050d020d110301090e160608061201060302031027151e02040305 71
    0x100b62100042d000c10200114201c40c1018104074030030100700f15070030301c5070301170110740364828800c481c000790021150011405980013903102c501c00708014a40450140340f1041d1503076040d44250381c10403030340202010007402130307030301401e07640c10300068440d4081ca201005019201e0040904000c0c420b0b169403200c025074805030b501080c0e5041d5440402d03403a014050200c0103080b81c1003583c9000900341000803400c030300740d481c43c41240d2280e070b42c82d0001100e0b842030295500c10a0681c883e15101c0d0b2810001034141820810540a51858003e09204154021081e0340c96143c0d0120010303190036107460b1580041101800210b16450084000541c1440304d4016441c505802c00940d1124a18034604403840101402281e0115002e00c002400500700715040c032500f04d500c040042040d03a0f8030307000f207400d0603440003c030002191035002c0c0b0300107024192a002414140c00110710301703504107034407000c003104070121004c0f46c081d40b070f44040600101d0716070245030302c0f441607902103588a07034074580241e807010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 262229109 1250 262227859 262227863
    0x305010501170f01060803032d01090902120109020306010e04030302070c1e1e0501030e030d02030108030304111c02010809100203090703020103180b01031e0807050c0a080a03231606020304 83
    0x301e9103c101d400150107010340c40c00c50300740100460941e02c0707034608103a44c01208403409410803911901c021150241d001824000d0805180002c0c0d22619030041c0107814a1201076860340e80e0404c1950001610006000c0341140c940e05050b0740c0c680c0301c030b2a0890107441903002c050b02d685018200840c40405200d4102203480702140103c130081d64814981061010109801800d244002820402c41d40203070031541070742e641c0c0c000360f03403819001142030790881e0020703000380300d09500200410040001c43c002c0056201411166a0351980380303041ea0483e9030899440003410800c1c0000482e406041c208001954400001800d544a1400000352543e4480b107120030f900280c00c15500300702c000c20702001c0310005504484440700300c2c1c0c00d540760810704110039002c405101e060101141d0220300424060800b85218802510139000e951040065601c0d20742c00c600320580084520304c0c0080c0d00900b1900b800421001505540568151240550300070210515100c000762481c60082210310343c01144118 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 262230215 1106 262229109 262229113
    0x902041b050315040204080309040c09171c030212180304030f1b0905270a02030d05070308150604140312180103050612060601080c04030501050117 65
    0x200314082600041020081c41090040c02418100004003120158249414400080c2c5c6034810404174074860743c6c6d5400c42d880c0e903a0141d052440100a4454580c10506103c0b42c203580303030401520040c2d03518218003219204d05010b0b209070f0341c1710403074000202c906aa0341659140000c03035002c101d0f46184030074440000020101c030141104548200071141010441d45410f03210110140c00c00340089050400b00002a80702181080c40c00d8003400525500607140d5403510706000b802c0002941500841c041d0420071034018004088892190b50b0740a0b040c0d03a60f10090781030038185c0d008954050410001008401091208800742044c000e055410140c180d40e4480500c0c0c0c40401c802142c9081c07008100c20a60301441000da0101c2c050703c40100d2144460071040e121400200300605014480b0003040030310103210b0903034008d1940030001b00703c1ca584801c41c50110310309028a102e03140c = true := by decide +kernel

theorem cover : BRFrame.Cov 262050359 262230215 := by
  have h0 := BRFrame.cov_init 262050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 262050359 ≤ n) (h2 : n < 262230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
