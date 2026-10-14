-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0340
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:18:08.612903+00:00
-- url     : https://prove2.me/submissions/36f1d158-dd37-4a3e-9e4d-345d23171806

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 60971226 ≤ n < 61151082 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 60972476 1250 60971226 60971243
    0x9030806011e020303070809011e0b10030b060405040207030513080a290609060a0b030c030f1008070e060d05010e060a0f0c020c10110a030309150504030206181207 72
    0x601400041c01c401104202002442e400b0420400c0103900100300c0c2c1c1c0c004024603280c2815100c501d03426015001601c0410003080000e8500c0d241c0b414207500c0703102000d41c101ea40c00f440c980111001d806940043d030800350b010605000070002070500b07070000d001d501e1192070301c107251220341e420f520005506a000141c1907485a0003000c2046141c654000b00e2511030b512114480300036240003012640b000300424010040d04010a8041c2c644540080182641c250450340302d1503c984070940c0c81d0801c44440d91041800f0001c00d0302c0750f00061441d030a481005010b003031803600b40403038400704400141060b9049181040b030280890001c0c4a00009031030000090080381c18840108020f8807515031a070b5000318a0114000c4881d43c001031400d4107200183c514110645e01010103807201c5101c1c000d100061700941401004065042d448590000e108042500050541c00180c400701c5e03900320340060140c0d20800204560f59502c49041020451000844251080100d611107450b04407000444180c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 60973726 1250 60972476 60972481
    0x608031605120c0a0210110a021005160303050f0703020c0a030c0c0504051306150f1202040e0f0303101202090c07050109080c0c0f040504050607050f040e010b07060b0301112506090308 81
    0x346c03110451780b1041152512030301c082e81192900d911004100e4000740701c1d00e080d0701e0542a05002c0d0301078400e004644244007600400368100500038100488403010020804800620b005002c6c0c800d80340c1034003203075000304030719000e03942c0c00e0f90000514807058540e8030400000243e00c0d82d441c0501031141c110a2068074030011a4600320302900d0300101c849074140c1c0094001e01c0190a01d510400888150110304d59070389106002080041c006200c520806009808007000f03a19800002540206801c5910103405a134803600d4110002484100a5014404001003104440c000000e46030160041000003a0380e149a0307105059035105100c000c00c40c0e0804480040d880c50910020710b04c402e41540e082c880d510b0315549041d1910320040c20b2009110f0049070541410fa096002e0740c02a0801800100c00c550312a0900004c0d070b004441c0456600b801d0035074004260806002d000c2c01d142c05200f1150030004580c0341a107605107280304d16964121181540804130340b150040100d02070007921060040e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 60974976 1250 60973726 60973729
    0x20403120f0e04050c030c16080304050f0601090903050d090812090601060908030304020f060f040305010e2a0306011401030905100608120c0a0f1703040c180608031605120c0a02 78
    0x70b0060810107102d589000200510440700c00103c950020030704008942c2c85441c4031001c00c15244000d000380c0048c001104100400400107071201840131600d0031125070742c0c2c1c0e0714592002e40704c00c03103001000900240300c111120070b0039420011409100e44000c504082e070031040c601044404071a000c031b480c1d00000041005641203200c00016202071000345180d07141036004901ba40345400040d6004440c0003614070505003500382a02d000d154008000e1080407c440103090342c804014181146070282c000480c0c484442450040322040e4029000c0c00740c0e1b030310b082c1c45038124581c480c03829070501d521400b1410000390280522101e2501401d40061220708016102d07107080940400d4030600401080100d007103220010310702c0f038090390104403050060100d01e01440c030f000960103403c44d50b0802105100821003400c50350b07400d507504110b401d05501423034128a0143c601134814058150410001d407505c3d0070340ca2a1003075044c0d000340304a9038010074403034400407217600902d5503c100703030441190042107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 60976226 1250 60974976 60974987
    0x120b071103090a051302040e091f060e040b0604060b040b04150c080301030809030304030210020a060b0108070c0303020d06050603042f090105060307020f010c110f1618020403120f 79
    0x1401040c8005500309a07052021810121a0340150351140318000150300b00b041a9070110350182100140703000003424000c02d1540d989042c00c100e07020350214105644c110180c0c910541c07084a051103901e400300c0d1a075858100640343c2c007a045a80280d100c05c1d01280301c00f100001080102254189580d03994501100e030340440e104500d400e41001080000e01000c1190274007520b040d00e8000103455500c1201d80006481e520959200a4120708984080110503801080200603540110340502c4040c0416004451201c0226501b03004641444c001034040791203a8090140d0b45450900010b07400d455200050305070300100d908545454100060085190550f040340400c4940b00c18103011301a00799001940c0320307605008650280034084006070205100304059400011088000c200850041c03800908559a030000e0b014180b2560703c00c0d9400d848001030318801140000d213440c960f54100342038111003000306070203558010b40a00000c40440c0c4031b022140c00300721661b12403041300b441c00c4030003510 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 60977476 1250 60976226 60976247
    0x907030212060f180c030a0c051c02010210020d090c1401090905010605040605390c01020a0b0609090a05060901020a0905040203071205270c12031602040c09120b07 72
    0x50b0022014028a2820b045005400c03800712101e203585020920701092400c10810922603161003800c04c04024450451509401d4810aa40791503d007814044821a0003411410007401030b0f0000e80d030355820680650103050b000341c880c400480e0700600c0da1902c501100403500f064142030700681ca0308205603081040ca000a08105c0b0007449590b1401c43c01608900852045009010002552007407500400d00c0c5501000d8030886299154680342c0720407080b1045807025070705140300302c0c01945550b41c000903a51000d00e47c4a071403820213a40302020301100000183c02082c0078400d1b0705105000030010710250307128818000006840e440e891000070703c249040d42c8074500481c4100280030900d40e1103880740c3c1c1e400c0800100825140c4440840c040c4100e10010106940680c6c0a201c010352100440e0703202c0d860901300c40c0310850300d002c610116100c0c464022128802a80400000c005041a0704080329071011810506c0c1c0c6190796000b018a0320341000812640c20030f92104100c41503030807090040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 60978726 1250 60977476 60977509
    0xb0405060108070806090a02040b0c060105010f1416060b06041827020d0305160c09060807050a090c0203070209090a03030e060702101119050a0f05070b070503190509070302 76
    0x900a040c03c0401502801d409411a8002c5034424002400c4044030780490b4010444503d00c1a0369005071a0040d4845c9400e00509000401c45071451222600c5400200241188a00c0044c605881c01da0440074100d901301c0d044840d2615492800450364075800500000c00b4100c4100540349050104442110040c09050b00c0c41e0940300c40c18440da090021100110b01c0d819103691402c803401c0e0070191454010318400100003258040c08a041010103610182110b074501c0003071249903200c0c25040c0c2c640c203890107906d4100c84640f10170403d00d641ca0f0401c444d403c800f40141d0b4545aa9900424030014040300c900e1003540c03003840400300705980343c0b00e680071618241d0050040f500740004000e46607500b000c0b1003002192120680e040b03026841c0221604244070032a1080c07088030309000a005900b008510300040f0f031010581800c06400340088410300359011900207140ea0b00e91000f40c1d07454201900042c00c1600305e840b5480800030717a1113058090340b01c071401020030031710b1031040104032002c000070314 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 60979976 1250 60978726 60978737
    0x30a2703080304030806010210150e0901020a02061f030602041403101b0f03061d01170703030203040e04030e0a03150c0c051e16090c0908030c0601050105130801050a0b04050601 78
    0x300003080804050740c0c0c120303a0602e0b004405031582d90040346819620200d2010b1180741c40d12580c031020070800c1607000c42c0d814a00d101d0003903031404000da00300c2c02000c1d08200541c2140b000140c48203503106684148902020203585019182d40f42c1c481260000c2c9c102032400080c001d035926040c5410040b0f04d400c3d28035170a0034485283e590070b004071081c0010520000b0f00c0800c2d810360011a000c2e800c4000a4180d89070003d12590305120b000054003000c5c45a400080c144408200303410700c010a0010652b03405d40c0045140601d004407000c902c090042082c1d01300030031803212201d507940c0c80c89400700560086034003100c141c02c1c54081008030303101312101e0340034002c040354520001030002c03a01004101a1103d24648503001c401e003141407014400c0c60020410031441e0100e4090385550001c11185280c0d904c6600a0341c983d80941d41c0ca10850070510756079840000104129881003000b480401130f0540c180c0e030a25650104182910010781c2e861900a849101a0055051503c12158040000d2030300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 60981226 1250 60979976 60979979
    0x90304180e1b030c13090201091a03071d1c02010e030102090906040b030304081c08060a0305100b01030f090c0e0f0f0c0703020a0b18060603011b03020702030f030a27 73
    0x2941d60781e00b4001e540100c07220b180c518841d46a0740c20b00000101440180803030321076001c1c040e812070061200d0b01007240072a40307560000c201da921090380c4c0b40e43d81043e2440d5a1450b260305c541600c02c5c800c041150800703513034280501c0044c5e40740e41d11090328004039842c0c8000107002500c005444a40b1080703a80c0c0c080e82c814442c1d143c0903134910756419004401034600040106a1030b01081c254491030304000c24074801c121800c8208040207160000c4903e0680c1d88a0300c40d00c0b000c0801600c140c040c840035100780e104c0c0003020030301c0da9264404101c14105060001e42c0c1e10040720004141d85240c0000e841c2c400e40a50200440800c95200c0e07035110700111241c45092500c094400c4803404007414045007500041503030380415001300024442d254001c140c4c244c4030300d410101d21808401889008038a40150004103016003014080c0b85403c62000c01c009011001c91802100250000b5806a91601c90a4050050319205000800c150305040c0d6440c01c0c1080b0003640c1881508402c4078034414000750b10740 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 60982476 1250 60981226 60981251
    0x10509010509031605120403030503090601060203091807091a0c0709020301060215092404061b051b070b0f03180d091404090c0603060617010e040f050f01020309030418 74
    0x311340c400707824160000040055420100d10300001c24510949030b51000401109254104001d14070404c4a282110000ea03215007049880b030042e60081a0051002d05001280d801b1403440c00703900c03403598a04008070a5840e070410a0605d400c11011213070410018404603002c00a001c61000351440d00740941c0b85500d441002584e40c1c0c2c1c481d40281c40d41a1042c00318484103c01d114544c08044241e03598012800c12405030240c0b403e06070b034221841b9241c1a403016101041070401103c460300c03501d82c142841c4110619201c005070035240d440c1180512500407400c0103030100034041010341004a0b03600d84ca481e58110070600c0c1c2c400120b0701c41e5485103141c4a2400d600414800560f00308800d24005000300102250250001ea900104240d42024010036429031681c01001168060f5640820800b031f01c20ba030101cac166003030207074001d0075000034009804100095140c0100c1e078460340c12107041440d41203000382203070400d481f00c1ca842c4ccc10006041005801000c80e42441002c00b10007040107141010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 60983726 1250 60982476 60982483
    0xb030105010c080c0a05010b120607270512010608150f04060b060f0a0206090c01090e01050402030c070f0311210904050601030f090503040e010902090312030901090f05030309010509010509 83
    0x800d00e81006003903010102008107100039a25051500c10031508601c1017450100c2c0038121140482c2e010304401c2c1e2018401c03502c0040d800303000740801c0e2680401445440d210800c12f41d10a120360300010100c40c0002a103855030082c2da180444000000510b15082c424802d080501c820422140f9a08480600c81401080390183da081a402100010000503520102c1c01c035000d00742c501b024a0234081241b01c01e1913004900a4852151710040e5400304032070500540d540300d40c0740101c4003426a041c0c010300c410b041542c001c58018654a0145003804400e0344d6900008000e0481200000c15180034500e14020802c00c4e1090401000c41e890720500280ca28004203010700d015161045440314007003415a4001d40c4120075684050205000070100f0f41071103940ca80c4184900490a2080c0c000020480007074400d8a170200e0300140074003840311a09158901c19000600740e0411556120b600d2800501080090a0010710a801031612898045074503400c4600c01001101140d0411003006100310022 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 60984976 1250 60983726 60983729
    0x10c02011e140a03020c0c011412040203012004030302010b0103050c0a030b120d030b01080a090201020a02130e071805070c050c0d030908070905160207140d1b06081f0b0301 76
    0x1c0202030488000c070002100e4144004421800c01c0d0000140808820f03403540040601c0c1c0c40301012612911015801150321312170155a0013003c000500a070710014404240c2d40c0d030010b00050000c550010764520a140740f0180d148074940f500b0f00003030700300102350b028040c1040c502400d003810420752030130401080d01e80c0304070b800260030156512002d00345640c40c0508031048015000885070f41c280d00c048054002c060041c08540800c0c010400511110000c3c0684d902499041e806480501d1550342400640c01c00d420245500948460022200c00420080760004042c0c0018945600d0b01750051207048410250540c001c10607401049004281c0000c0c1c01c018000c0300740c1d13401840d00881e040c2100e820303014bd00702072002d0080000c0040ca00f42c0a0b0403075406210905050822410704c0f900a980d40d0241d8455908040a00c040d02c01040c035000c04000704103400303058120f015050606041701c0d40c408580010011a0040702800407841441c0000b1640c01481d0206c000c07040d0400e032a105090205 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 60986226 1250 60984976 60985007
    0x100906080f060301240812090a0308031012050d08010e0f0103170d0e0f1e07090f110c06010f08030405030a0813080f030d05070f08060f0118180b010c0201 68
    0x112010440303e440075400145d00d807500540801e010070f8000e4035039244000340c0c40741c0701480c80340c06540d86201c411002281d00c6508024991800c2c28603507a1030403140d4000a007101901d891201d030000c1c00c8228070070043c01d01031141d8050f000102c07019402030200c2d081a040000488003010810854440e03121125040d0707a0070050175684018030844100320b521401540c00d55590900c04001111000001d0741d10758000f8100680b940c111000e00d01030b400b5001d9442c800082d0317212034410000ca0310390350711040040c0815a07000c03800101c00711344045154000d5519028035400000100b1820402d00d5a11001d09101c0c0043c44c503080c50180000e030351320302031500509604000501d9195000192031020000d003140390640b50240300710720145440360405001602c20a007800c0014030710398400e0103014000c03400c41d01c1d5802a0f40300e94040c01500214881060b05002001e640c039424684480c4900b001404140c480c0c2000e011006441402c1d581c000c0030f1141031017045600440181e070000d00c02200c1524 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 60987476 1250 60986226 60986251
    0x120a0c0b060f040204030b0406050c0a0903140a170a0207051e060f07060501030f030f020705090117100516030b040c0509061c0903080601020f0703030203030109020c031309060510090608 82
    0x1c40c03600280581c4440300d00541d10a1000600000f00720740001070510030360081408204a9a51080492940c45a009900c0001c3c0d0490414000548980d00b600c000b0301d1404d04a40e8942c0c0340390764080315100c1d0030121040701c0d4802701e00038000b01e0381003200d540900020b807036141032806c4d100903440c0000522401684222404942da40ca03025940e8165044183c03c0f40091040d03580d2414001c3e04114108802d43c006440340318441c0001d400003078441c1c01c64901401c0d60f10b0580c601118105150b0300706c00c0a4a07140690456000111100d000300d0f405040d10f04841d0003500d1910070040e044400e4890024000c5007055803500e1410303004010749811007001d0b203c2a1390390740240680340d49816040943c2d2806864404c0000a06074003e221510450080e0205c901c0e64032031103606070fa180b001c2c0c40020010790042006000741c42413600a07105080502c0201c0c0d0501a0440c1020070100050f045110348664508040050740b506000041e485005424001411030900328020101c100041c8143c1c0c5200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 60988726 1250 60987476 60987481
    0xa021e0301090c12050709020301080c0f0102011b0206060a0603051501050c0703050316030305010b03060d12052502030706080f060409170a210e030912010b03070801020408120a0c0b 80
    0x89080d0006402d00c0c0d805030624203066107544038a0341644043c1c00c10ba805104540c40410f402d800e51085a0503201a540100703072040342c8100304201d600720380aa490455403030340b0025190451080f20564a210290094449841c00206001c0044280d511010401d030510050041c6440f208150f00d0724441e080ca000e9950b5401d100e0310310300d4101513500042c0680702c002218445103201d4100b46041d58072a80c1c0034819039a0b60f4030220941d006c02c0d103140d940a003007003201c58005240504003000f075a2250401c2402e10911121001c400d01c00d04001c2044949461280c00862800703000c504c3c09031070141010300340750509648003188030710000c0c081401581e4401b180c40c1400910811580c41500741c07903141c0d80d01c0e120143d00a2008500428004070040364508907010f00186010341c0b030405c2d0301d80c0700a40c208128030080165203010442195403d540c1c407e611319003928284120000f40401d003002694591400f62000c0c989080002e0001d40c0000c1841501070b0664001c3c05040c2160f009170940170140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 60989976 1250 60988726 60988729
    0x20603011205190602030a0506040207081c0e0d02030903010f021213030309060617010e0c0d0209060f0901150e041103010603150918030207080601050d02060a090503030d02031501020a021e 83
    0x1400d0225414034030f4070598080c010006190001e40c1301e0440050b0520554490506000580c080c42000500701581488007000c0126040d00500184000f118041040c203030086d09982014100031800c03006810000700c10b01c00d400e00b400340c508a00b80c01c1004620f854000c80c00c80213620005421302060000700c00d440804d140c440d4008000140e004403041080fa030f0707501d245000c141d5485020342220350810301071821500300402d01d680342c0c14024204500b81e00c0303140d0802c201c1900040200f03074404583c400301090781c1c45400145004c5c040c0c0e81504501c0d41c03503402024059450f034242d801c0c401c0e0f003048292900720800d034080ea41161290b0070049909a44807040313550941c05504030805941c941103040d00304c81c0416650040841c000e07000e41e80d50980300d503c0542c66038803d0043d90740000c000c1000400504103600100004d100b6842c098140c1610352002a0039680111403001c0040d802100303100e0720700031440300d1030740745c0030240000d050101c06503021540700c0c800200c0c0300031041c888142482c1317603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 60991226 1250 60989976 60989983
    0x3110c0309060f090a12050c030d02070b09010c08030f0601140307050906070201020f010c08070f030e060103030525030c0b0f0910020d060b0c01051501021902040c03110d0b0f010c020603011205 85
    0xf0410042ca020203858407000b21b61000344080405403079510076140001c5250070007040b2041c0721511640901030733680c1400b031406c0305940420300c01410801110301000200b85070b4000f46004900400901c0501e051900c00103000866040b01035124000c10130a111040ba04001107a43d210310603522503494840c0c500040c0c1c103080c034a103610507280d42030512042c005a8041130007807186c03c058440c5885110020340440840718140c0f210704095004100610109001380c0c0034054440e010540e400f5241c9502401000c1039070507100032000700e40b260750103100300303e40c40d446203074012012062082185401032079296111100210650701c2940015003680c00201a0406c102030081d0780000c0b5650540622081d009007c11219410b03105048040d1314034943c4040791660151072680070110915204c3d4007004010100e0569403030038076665912411040520801400143d030b0070007000a0346040c480c0c10b020604540e1a0450304000b42010400c0c01a82c0d42019039055945141c00c00c289441035280c164034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 60992476 1250 60991226 60991237
    0x303150d05011406120c0d0213110a030c1704050a0b0406060b0a1206080c0306042d0503070506090303011208031005030f1c02030712120f1b03110c0309060f 69
    0x15079403c264020140703540b112a00c2d806040e00b0360390310351546540801340303464080302d441c4264440c0070034541c800985000b01c140030313031003000c0340000400b10000b001c001e80550019a0381ca0109484500410740c0381c1e04052126000341d14503284418a140a0307036281e4480b00d240d41d005200540600c0490103010f602e512080250081d440000d5440000003000703001200916000c0720714134280080494007980214840d806400050300614241e120f9079121010b00740004096407101182d80f007510750040c414140d041d040360207100511b68416681c108a41401001420030b015a4402c00c01081b8020f11340c002c0c407868540100d54991261240c051120450000d507100139454492040030302540540801d080c0c4140c045092000c001c5200385100f0b980b640560380e400360030304d00300f8a14015450300ac1c070211400815442000548821050318941c01c0f10051a003201050f840c480c01c050030a41c15200d162403100c680076080d82028684032003140d40740714902100d80141d101040342c05a12442e0000d440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 60993726 1250 60992476 60992483
    0x806070e03120409240f0e130b0103020d030c0b071e030501080309010e010e031506090702070b0a1b150e0f03040f0504020a050d0603060b0f040c0f08130212030901021c020303150d 79
    0x121025a5110525190b403158040d84100150900c04102e1b103030608ca0084042d20743c000c0000b64168030f50340810a03051034059007a4184080e1074010800507c45e1070030144986019118407201c2c00c00b1125a47d40d4000500c1d014061601d41001840203890000c1134030b80b44402468100c9003521502d004941c0040c1d09403d01c0e40520401402144010642501c54815076080c1c030502425911242c0c01ca1740d0749400d109030700c81190704000f48a07a140c484d0320703040c0c100e4203c0403c0c14420780d0305980301a800c442003601c1c8002261342d084062070f0031405201c0003110314080d400450800f418100c03070b1104e17400e0380d2007094400da900188030000c0d90f00074400d403105103a00a800b00000c0b503690401c40003a00d0320b0408603101e42d41c15481d840e001d1616200d6200c030440603039110b00c10710740200015544c3c40c070701502c025401d40306c4682e00d0005030340303008040b22501c10440282d03403172340075101c00a031800364240306c2130400d0311100d4480d41070950300100b40c030742c003402d90310010340c26405040204088041080019 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 60994976 1250 60993726 60993791
    0x60111070b0c0313091a03030a0f181706070306050f09010e1b04080a020906040203010b0304060509120c010b03010c110d0302090604050a030602180402030c0714160806070e03120409 80
    0xc0040866001b00102a07202c0d920608004103c0c003010307101c1c859140304c42c011501201c11610480c0c41003100104900110b030785002005c1e20340318060300310183d000741035810364414801c0182d21a03060051400500043c1c43c45124075200100140f41d200050182c090700e040d10900240680c1204005070a80c0108101d0040d600d50300c9800b0240c441c0202e28040c1c1c001c6600c0b2000ca00c05003864401c90b4101c1e0310310b40403a4115221a1344100141202420415951007164180c41c10f411a510041080044c00400094040b41500506003581d01801c412010722040c0400c0300320601001c0f880010b105098038005030307103401407000a8661702458001c50b030404e010b620040204030842d4001c0c140200200050020f1041410403c07040e44411183c0750212601402880c0020300c1d0a8007038602001d22000b0f0324034202c4440c0c09130221900075401760b5800d601c07400030720510170740092210790811401c1c0c000c1c0004d422000c940130a2032142d40314000350709980381804004041c04808103020305042c2800b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 60996226 1250 60994976 60994979
    0x9060309010b090c2215030b0d0503030a060f050a0b09010c0507031704080118051c020114090102040f06020109020a0311010512150f0604050306010605030606041d010e060111070b0c0313 82
    0x41c2c412070304051300003c13201d0040600990091242d24010080302c6c18040002d145403500d4100714094281000360300c1c3c01003560703044103001500520203188501e140e200006009854000031040c440000d0f441903021750b20990080c00030807004401c94044007801e007407400f8184102e140141c0b910a140d8405080001c030021600042040c0c5001003040b22003200c000e00031007441011641584030414402040b9078441301c20249002440710702003c00c0b90560000003203118034410404100c25086954010030795000070305002ca4294805051f0207814203100030001482030350701040901c1d00502000e002c000100d280100980e21620032074120000410081805040900c05d4104603280c40040034401d0501105024040c20400e064070308070b030001002050707a40d00e0320b0415205584090401500200304200114a02c21410500e90401e080303403803094140d600d0408000400d01000d422941003089040307819548400010304401a00d040201b03155a403072a4580700380c82d600c242c182420f01494402070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 60997476 1250 60996226 60996241
    0xa0e0705090405011e090509160306060303090807030b0c0313050d0c0b07050703090b0d0912050a08070305010e04110f03010603061e06030c12080702130203071806020309060309010b09 81
    0x540301c1c0038410b440501042c5d8035018003084907050f52526512410480b6403c01252005410154101d00d004058880d51841c1c134070b14a81c6001c198001340c54107503c65008004065202a41c0e1000780a890041d1000701d080d50b030f132140045809081c0d898800804404204015400f02848000590140c203c40080c0d03c02080030340403e840c2c80c01643c0c1c200012000640b0305002c0c0c000c0342d42c0d8682c0369644120b2141414000f4059403c5106051a001d6466a0107000500c400d00c106003070f41d80a847d142c1d00d90703c1c3c003030000f04840b0000780070340101818135004100a04148650300c1d0440d91045104150440c0c0034042441c0314106611a64590300703200000060040ea07a02003806e61100d1150101d00b00300c134039100b42c10fa41c0c103403000400c018031440d81000012462250f8403070092055510925107040d03500050f001d001d084403890f50380e5500209100c02e03940c01c5070403102201401145502080d29203000a5240d01922080500524000000500700002903012213441ea2000704681c049041502 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 60998726 1250 60997476 60997487
    0x20d0b09070c05070b1603050706060305060103030801080606011404030204020a02120d020405030f03030919080d140702010b0307050127030602070302010501030201080f090c060a050c01050a020a0e040b0d0206090a0e07 96
    0x203400b9281070003190008201d110840701100c03903c0c0c07840f0640031404602560116080c1c1d09c81d100c1642c200e07030f99200c088009031f0140680b500030f6000c0d40d00d080d260f506000855003404005800d241c14840d07110000c010a1083c4400c0d141101d070119030060702c0c5c80c035062090b400c1c941d85014201c20004001204208040f06601800aa900c00d4080301c100c800d0815030070740e4910054841c0007495200c200f8003410070450030202690f6500c124001800c2c08224201c400950b5842a400351540c1705000030440a164240b041c80351840081700200341e1035140400203400c5680c13004810130b030f1240c1c00c111060300c0361300c03031301c0f60002140d104004556808031403d0080c000d000030b00040b800100610f011440c1d66040300e008070b0003030352404040c00303080403548100401c641c45164507000b030100034040901c990b01c083c4a55842145000700140c1c0c4c84115183c018080320b0070804bc0c9100f603140046404a075140c3d00e002d01c414680c1687c03400c1d030300c090150018016201a0f400303001c00c0100b41c2c04000105a105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 60999976 1250 60998726 60998747
    0xa1a1201150602060606120709030b040308060f101e0903020607080d05010e01031520032509030320030c0303040501020a08060a0b030601141b0a02030f0102040806040303020d0b0907 80
    0x1c80c4000c00c45440e0ba00c100d803588016070300c3c50b0b0300140a1001352148219500c90580100d032905040404550f42d5840146003141142c2c25400720b00100c04100103810240d006140c203070400c499508000c03510740303c0600307480b90000000e4024544004000c090a019601c18400713184c004080715241c001c686400070701c0d82e00580408505a0402000048820a0000c2941602c1e4080b200e80c0941102924240c02046001c032000210070050700030780721101358600118000c0b0303682c0714130043e030402440301c4118038040310f00c2140030400705203820000b00b41d001b010f000f17245007c840ea002c0c1060301e400a5501d1030140034035004140c08000240410001c055005140017180da4543c0d1009a803011300f04400e00890b4480c3e02d5548030b08000080e280d44c4a074182d090418040b01d8203e041110010404254030188211a41258401c3c40c100003945000c102600411820b000203628050600a19948414000d0300040c00c0c1900445d00040b00c0c102074101c0048504040c0000200f0724110704000d0885205 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 61001226 1250 60999976 61000001
    0x6040f0c08070b07050f0a080a0509060702120109120f0c1713080f0d0905060a4e090f030c0602120a022205011b060b09010b0304021801030b0a1a1201 66
    0x102042c5603004400400c240c0e11031f0750072588007414000e0700c41d0150f030a5881203000d1071f480f01003081200e0041c1c3c1c900595403000604c610000034010b440f4038000865412011007502885202a01c4105040c3d1001111030059800402502040e07810f464045403405040030300540880d0001c03004c02d16030800180356030f010740510704a0b0403040b541981039900c0c170124081c00c2d4001c41c0400643c2c156501a01034020702104642560980c0b1044412303110705c1c00001d0b14850601010829443c2030300c0800040a400701046c1d0780200f01c03551080d1340d0b1002c2490107100040034401c440c0040c40621213a030341900c10584880b02c00d91194949220220020340c0101c01014003d50800040c245220400244900381e92040c0c45414070750301000750b03229170800209001c40d482c54440015034a00c3e141c00308250700070107001030030f00c1e1241400c0c410021482c45008072441e0341c120f9080104085800c00340c2c015000214202c00140b000640c4030000c1012240c1f0243d2904450141c0035118900700550140036903441 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 61002476 1250 61001226 61001233
    0x40305090306070906020a0816050a03020c041103060306010504050603030705010615120917030916030b0601030e030c12070311012c0102090d15020403051207050d03020c06040f0c08070b0705 84
    0x6070f00d8000d581540c164058103005a1000314000001144c03280101260701412041e106100495511280f03455041d480440c0143c000722680025801c250003802113158001c00b41a09525110000c42e42c0c440741407040a110390744801c045002d9840c140205c54041da08000240956900c804086a01441ca503d807900080c81605228080043c00d111302c058465100c071078408000641c0e1141840c54102401d2826940152081c0302500c2071004030040085100700040440c03403810400140032110082040c58140e0003c000e0045521008a040060003101101168031110340d818100c03081303410000580c050b0f40c43e20005801d816040340c1c0540ca44c51112400321a02022145480d00784d0241c4403140c0d4120b11403881c1580024003040501345040851040181002e13503e413501458200e4001c01d440001000003030385030a225045c85441e0b400d00c9a8181545032041d41041147d450200a00140807070144c50304080802c1101190f80c0003d00c0c80c0800c6580c807580312020441d06500041041f00d8070310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 61003726 1250 61002476 61002481
    0xb0108010b0c0a0b0423010b0a050604050112020d06090905060a150501170603030c06010f060f0906050304081e0d0f1b0c020108040c12030504030201030506040504022103070506040305090306 84
    0x720001c4a81d9048000d000d4a003e0560380d4800c10014005002202c940c68a241c40e500c0f030f5022841c44410b03464610380041010140ca0050000407403043d00141d01a240400007441240d8200c030031594003c980000041c0e0b10601202ea002c02844646c2101c008607040000d03080a00c038000940c140180e0a5030070812190184444505100c15a03200e1140401c902d140c3d00605000d055140c103a02c5039000e07003502d207043c00984030141044401d13040480c0c010300003102071000c00d03030205040d0000c510717908007080d005081420180040c0030003030004108460010310095406950303040c540b41114503d410a48480c119040000507140c45408148aa89010040d50b0358103d1482030380500c205548540c2c8500c042ca40044981e248014015502c80100000000322800d2981828042c80d000356107441d00d45041d8400141500c5025103514811802c00d014040584d8070310760300a5400425414040c1c000303000c081090300b14041c6600c0504240610800c01041c10b40020041594000031016a003956 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 61004976 1250 61003726 61003739
    0x150301060b030f1311010c021207060c17070510050604090f080414061606050705310e07090501031a030a0b01030209060913150617010c0201050702070506070807030c02060309010b010801 82
    0x1014013807809010101c03407030300741e50195000d8038000103800e001810040300619504c200d580342901c2a0300910010b102d5011f50400d00c410038282e0030000400c4034035903180031603a403070b01907880c08460b1101c40020760b100c011a0807541e0748c0d40043c0c40290311491900004606042c811100d0f00036204040080404daa6607001510341201115070201105501d86e6a00d0303096180c80d002400010110800c2c000d08000d0403207422203c82c44061900f01003440c4e581901081c09081d060021a98001d0403418582c0c42805605074000c045101550070a10340003805080e140c0c04030001041042609415000342c043e00340522000115a9040e41d00941b4441d8403921024240407088404407081101481d00c0c0d4040400034044c10003a507044a115200810183d84400c81c21204050752000ca480b43e0f0b66400c075040000e90280541a4421030310300180454500d008040381d00d51107520700041281e00c0028505e0308040c011440e40c01d2080e0081c1c061520703480c0089215000746142240303d400b2884200c00080c12 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 61006226 1250 61004976 61005001
    0x10801180507090b04020405030a1101021605280b220b0309030403060b03010b150c0105012301081b03010b13080307030c0f02040b03100212250503150301060b030f 72
    0x56000000b01080d92501ca8400000c01c81440741d940d019800b0800010f46580401ca4510001d0144900d008003009500019203401d50740080e51094840c0240100301503501d9411040c1d0795105a01110152a4188070320011501030b41c01c0303080080303400314040d07a04105059030f00402601100030004801d499191000003070000300e40d20001a4005c200074800100700c1e81040045440180011503040c0c0075000041c0c00310035403059541200004101c9016100090260740c4c01080b9050704174000c00d004c44056044040440c5c2c8250522000321301243d175200c0c40d00800d05d070000345100032507100d507103c0d5079100007540054680c0c100310040100c0460000c4c4040100d07034210342c0c035448121045020f40d07209140d50100540590340141c0d502d1141140b41c502f4410280e15410700e520041e601d99400040748078402c4042c0c00d5000c40050703a4600740b50040060212000001e540c200716440b0360b41c40c421701540d04082d01e41103815500709400094100f14080140d80548840b2a040d5890b541d5001c80a14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 61007476 1250 61006226 61006271
    0x16080c0306011e05060a0c0c090c0e040501030305190e100c0516080606012703081b01180308041412030403080a0513080904060f150801060507031215120b010801 71
    0x410400c8102c3c02c01040c07404a00502c480246420710400ca07030303002e44039106032401d0b035804924080e45801040e141d66603c08605880c05500302c9041003154103603180203145005041520188000054400c0c031024002e1068900184000700001d00f544c0048600802003038842c1021115440307019583e00300c00003105103040a46810400810181e50744100440e5404641c055441601c0c1401480c0550003ca5031607600c0070750302842c1e50300d40d941650010344210201da002c41c446240d06d4240e0301c4d03074140e00b0511982190340d058075204e2059140c1341007040b40c401c00c9100c0c441a61242d8039078480e1260003007000e94800da0090300d6401896943d05112401d46030b0480d540d020709400d20070314900003480341c00504110b10003d04002001c0d5102d50031806100342d1900b049a00c5040207941d400e00e01e83c40f0075030030b014001514201d42410300c01d68000e006501c6104910000c9620303034000310001a266070028005012901801c00c002045007803403001d820f42800b50204c01d500780242c00751a60494000c200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 61008726 1250 61007476 61007519
    0x818030a110108040f050f010603050f1207140c092d060303090d060b0d03020703020301050105060906030c03060102150c070515060105070303150b0a05030f0609040f08030916080c030601 82
    0x7500d45003101e0044a2085000f00112000d154080c43c1c840412410081c0c40d043c582c8000001945605504119180110501024060340e1002641e070200d500f403002510101544159440d1210780e401c02e449080803180741c0030b69044080728040003408141800708228105103d43d400c40c5003c9410702101280300d04075a45c41d016401000600d402e03050440010110700c0c0150320004251410030000317011001801c1c0c007580180d000c4c11040c01586030030320038280181401c0305c20514005000022400c1404000c012202800010001400302e07402480700320035503024003004400a02d040d01500a043c1c010100680303092040da510308a101c00500a01401000140c4520303081c00b4076541c013100600400000e00c10000300b40140087c28058802c003505105035140c40b1240c0364900390710300740c200c0174000b0030080c480c007413090601000c120000100d07000c42d5009503841c1c5d902d680e0224010b00c3c2c0000104d920f1521082c11800146030b0101251420540f0811021303591103990760200110b03007403080e07000c04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 61009976 1250 61008726 61008743
    0x405101403011515090302150403020102011409060c0a110a03211e0906110310150203030606040b09061204060510060203090f04090c0e01093303030f030902040501030818030a 77
    0x602010060700d0310f03a00130042c00e02c1c040c0200780e06d95000c100484401c14000a0540021500307204541c0c082c0240c0a1a60005c480101180f03001d0b01a2544c62501404442d40d04100051080d5002d01c61700300050354a2000d0116018110705140040c0b0f003664405075645501107044880480010b20302514101e4a401c1d0b101810b00241c900b141c44c000d01e40b0401c126103055a45190441c44401c0a010354860011248050811440d11403545041c801806002045410400c1040900d42c2d8803025102540c02c1c4c02c04003500d078071400d0b000c9141d034452028041d100000703002c208410450503810a600c100440030082031040e50364403051740d0303c0c058000300561003040001060802d0506a000f8004a0302034686501d22690710110f2001140c0f003030304881c0c010f82c0c86007190300151142c40c1d80301996103810b907500306600300d0400306000107000da800002c0070071100c00c113007484880c420b42202c1c0c4200e80060007005a0b580d645040c1c80e06500ca0784002808029807603c00c1040c0c079002c94000700071a040400b6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 61011226 1250 61009976 61009979
    0x81c08090d031e0504080c060106080432010509011a0303040b0412030e090403020c040b0a05030d1809020c0a150603050a08090d06020d0b120102030106020c0f04060504051014030115 80
    0x5a0241044442d60000304048000345070b0320740d0f428003401d03009900901c5d40075541e0703140d04401703420080141c0046050102041c24080040c1c803034900da0244084144d0f01aa03003069100c58414071a2040e218244a9800c110500c802e020301035000d05a410700d0312070b0380780e845040c44091680342c1c0110300c0f403804a0740080c0130400403500c3d0b00c03420b030340310358824034102c9011607401d800980d402e102aa0f0a41c0184c0c44101e110030642024801c2c41040341044460000d035500c2c11000981e2076003100d82c0307201040180104294000500810030f005084101801d40d07e5480c03401200382c0d00c00c0d070320b441607640e0080b071452213403803034154855403060741d07084406031404a405488040140d13000752001500945010070403404603182c2d00c080c0c40303a05140d400110b280071700001041041c1401041303260990340304000403ca040c0d00081d000c4801481135440032030240d00c91000600421a5902c121f8000b420705041011028500c0c20b40800d403650000001d00d010401e600f0325088440d41e500c41c6401d910381140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 61012476 1250 61011226 61011253
    0x20d020705040b060d0216060b0a2d050307061d12030909040302160e0406050f070503060f030a080a11120c0706050913060806090d08061008190501081c0809 69
    0x20500060364043c2c02245080c07410170508040340d00101458094400382014101041403900880c02d0101007100c0c0f40040340d06240300e90003031505070b40c94460000402c480d804002d0106010750001044001c00f500c002a940b9800a072040d4981540d48500c41481c000d0803a01d0f240820a11901860407002035003002c11500a100080b0005041070b0203500c5010181501c440c4485604000b600c41307081500c0b440d041618210058031800351080c41200d00900c01c10441680c0081505e0703100c0400c41c0d2903000d05500001090402900e150090320107440080c018071600e8005062503502c0c41d9041c00c54000c0c0d000b8500f285040d02681d072014403a500980400c000462180b0040e08007814010035020590400c4041181142d600e9071007841c1913080304040040701503051044044c20655424a0b049611b05200040c2032113400490781410b1200440201d076245060180c0d90401c114021806c101d01d58607004200c0d03442d286990140340250340c050780680e100d441141841d00602d078101c014690403080300c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 61013726 1250 61012476 61012481
    0xb0306160c080d0c090f0902030f0406050a061a0a0206010605040b030114010e0409050f070902040803030f150901031a010b1207080711030a050310050307320405090f060106020d02070504 82
    0x1c5081d200e0a8050064a1003070320710784680340d1484d803291181d01c0c4851802c80300b5000140950300001180b44148100101d0f800c0b4051900d600c0f5602200018440c1d0310070b00510010030080e0805a0b0794441031701d420603081c00c4103004203268045034080366201e0381c2e5204100ca440c45640207880001c64180010007004c3c4144640c1910503805040c103101c3c4050305800f28080716441d0700151200d5000307081c40c40c0306240030f024440181081c84020361070a4209070034070359a40301c064881c0c10b0f0460143c000481c1056466000740e841d0000030f08400855035242070804914060745c503020010401c40e00005418000f900803603240400404040ea001e42e28140c069445400040202e02444501c2165032039890082c0010310405550343c45603a02c0c1c2c10300c0c00e042e60000700e01c5d810141c000d034070203070703040c82612981e00010340380d20762a80d000d1011110400040c1c04003a1010f54180c1c100d4200414004264070101d0f42c4250009410121511aa07941e10220b0355400d1000035180560130889040c8420308154 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 61014976 1250 61013726 61013747
    0x1120303020c12120a0b0901121e2103051f030b06030f060702030d050c090108010308070c08070902030108160e1317040e0402180c0a0e030a0203070b0901030b030616 73
    0x91090f115044910101d0b0031a0f42d2001d90380607004c1000c5810071610310102d1244d0880c100013070f5910f0311150b04002811865025010300070301a603807601110100030421203560414035905c42404a003860916503aa01404030612078400442c0c01c0030b0000d05d070002031805c4000c0b644008828600018a141c44016252070f0290000e905406402d00e00c5020540410500740518416070056694480b01a0785d20300329130700070700394032000c410802c10310701c29a0b400302d40c00303040d039400400403955181c8628100d40030015907072000405015507400014490340e40c2d4040c4d81252a100141e60014110000e17460f06100c56000e54102d080030080851603c40b003100310320000341c0c4520021034501d508191840010f41080d4801e00a81384901d08000850900224280b194000541c1201c4c03581046a400390441c0550750b15142000440c20f8500300550f020840103d20b190003509035500f003902c3e2351004101e6070000000502080c10298a10b00b9402c0029170f50b48545c20418001c0d4201c040d88200701d5052061 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 61016226 1250 61014976 61014997
    0x9150705031209060a0b010c050a030807050705100b0414280b06041502070b070b070c08071a061906020c0906030a0210090501020607030b010e10110a03031d060112030302 75
    0xa0080c02c1c602c14001c1161802140b40d44010700d543e1030884518010742d840410400d04000741d01c0e0485000a10019100d507070030742e0501b04600e1fa0b6036509001c68040c062400c0103031080c492817610401c0b18003150302c103506240f42542c05208110130301444001d404002d03105403075400150010078440a442e82d1190001d00000400898502103071000120242c1207170b0001c008190016441c1e4001e90340400c07030480282480000103040030300035241d01c6802040100302e00180880d4107258410000b4050440d12240c1c2d0000389140c42c0554403458040e1141d084803114059650384003540b0a48085140220445801c1e500078145146420240f2030064000f92a85030035109084014006036070394403079407841e002d096560024003480c00300028540300d00a05241d040c9880e155807018036076404054101d01074001d8407490141c000d1914215503803444408400814081c0c19481001c0580c16044000c05001c140040c80807030303a0915a20b600d4007800e200340c40c00c08242548000009000390050b00e179541a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 61017476 1250 61016226 61016233
    0x105071a0c1608040e0a05060607030c020f0a0806090d0302040b1e0d05161403040b010e0403020a1202010b010e030c03031e04030807030c03021902011b11040204090615030209150705 80
    0x6001120554000340d82822a06200045400e0015403603800113246d001020780002d01560600c2c0c0003046942c170802d030001c0e041082c0d40ca4510b0964484007848011500b01612040e08107075580789194581000b0b40c2d120996008142861034071030b20034000d035400e50300d078490828584030300185102110311750001c18407116032040c04150303001e081900c1114807038401803550400d40c101014005012031840680c900300c00900348140710115060003051410350740b035a015a841c40e161806d05a00d0314400c401d00400203900301c03500c92031540c0d0640082c00c0c2d000d001e88aa0600040050030940c4a03180c0c0d804140d0158001c0c0310311801086c00d01803503c240040103034040d01d8517469883c1c4d02d016600401064020a440c1000002003542c100100b03070031030010311001410140542c1c0000d101c89900e884144140584118020602035018580c42c02c0c0e0f80c00134805c560312656800358201800b194420f80c0070541c03104654521441c041c2c000c80d40c030b80340c0c000c00d401881e808880031413503140c20004d82a5820710 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 61018726 1250 61017476 61017487
    0x50417010f0906060302031905030a0c1a01030c05030c0607050606060702010c05030d0b0a120b010302060c0106080a12080702030c03030c130803030a0902030106080f0309240406120b0105071a0c 85
    0x1407541c0304a0344101d01039400801c000b82140149032034820000307200440b0310382120541d80170a0004c4240ca600140600c2c1420301e03a8001d0800ca001c00544003107880c0320850361000082000702d0f942c00e070780072110264140c6441284c1801002103a00600101500c0e81d04180001811450b120000300811881411300003141c180b940c44041c51900040784a40c003084c1c0c0c54407034071018504503580302d009019109030349018480e1903540c40b400394018440240100804101c1c100701d4442900304101512100003207900300040c070f0600c822001034101541011941c0036010170705640c404011190300d0b0003114000d61660b1900c0d440034003a80d009a140720b001030000d050201d142e0505000a5000e03203090311021134220194010582151490340c0180d50305d6000549090526a021042c1c03042100c0481e1024510545040003410700c104041803101d4102c0c0015002c10021303000b4a480565880d03190041050042d5500192040c1c8100c16000d09603503440c0c0343c0f03540c00c010010300e0181e011490040150404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 61019976 1250 61018726 61018751
    0x1501140d05060102010506040b010c020409020a1208030604051608150103020d050c0c0c030616030e070801020c0f1006030b0c130801150603051f2310050a021c05041701 74
    0x940150311040341094451041c050150b03424003945400c42ca084808000441c0c6010003e004c50001490090190391500c80c480203664416003200014a942510754550066501e8648910350003140c81921552411010844009a110072400107142c6a1689040c0391141810394440d9000e0740d5641c1d04040d0200300030300704040107004550127106082c0c40c0e03035110460100d023581072048040c03c05000c0d50048080201000304020744141080305810700103442c4085410781418410240c0000101d5800005c071b412004000080a000e0b08041800f0764842c01c1c44150714000b80c40d444c1c40040c00401004021030b601b051040002c049035502140c1c9030b180b040d580c408450a440284014160601000c6020491941c25000d13059100d0507103400040d9166842c4620000c0b00c1c1103005400d103641080707104400354090060349424a00740144020f82503101d18800131b01c00d90200e03860764010302036006151522520448440e000408588481e401c2504021060400c11100709005845649031004000d60 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 61021226 1250 61019976 61020017
    0x32070516030b010302030d030c0806190302041b080a0203010605070201050904020903010c080118110a1107031502090a05010c02210a0b0103060c0e0a0602120706061706041e05061501 80
    0x307600c41c041d0400c8a600d580105418210840c0002052500703120810071015030002c445179020004032540030346070040c44071501000386140c000079041803910a03000c2070f030200d2000602c0c0c5d4044954801445942e80800c2100b680003c3c490800842c000344080c82c019070043c4043d10150f1000b4000500b0f01a944001a081d03400d07804005012811f004d00520004000001d07800c10106640da0030310820703545a407183d11178825440d24808020710903080781e088400c2402a40c0046410045e440c1c144c12582507074a000394401e0f000c00e072242010400009240d400350341c1c0200e203aa002405400c0701c27403541c007a4074003048410040240302d000e00d018043c002102c1c00b00d03140c080c600412000500f00903404014203454030302c8861a20842222804119040d800035120392803241c2209070940360f048502c0e0180c05050340c1d41040c400041d140c941c65904460004290380300750b00420301046000044082001690906100074007107400400000b200305010300381c420399130364043c542080101018106541d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 61022476 1250 61021226 61021229
    0x6081306240e0601020f06040b0901150602010c0e040b030a060504050705040606050705070609080601060311041206020d0501140105040b0702121207030f0503100905071101150632070516 82
    0x80c0e010005400d00642c9481070750b0b03640c005000e000603d014815500c82e1030342c503178008000070001c480303000000710200d100b904a00d84942c1508400c0344119120b5002078080d04030556201e0024034074a142c01040e10700b078001c070200b03400041e0103003c86a070103894100141100038401d89882c800e0100002e050380312407064100400e425943e09494240c5894030350b0800d40e403640005c0401c80801001c1c8255000485c2881c1100d04e00d003400120501b040c40c10502c00e00440d4040d0000a16110700c3d0014015560010b08284106034000c000aa0b02d580406d20984a0107102d01c0c001601444280001c0c1c03041c40003080d82c640010411400d01d0050b6220324500548802501020200801c1803401c05401020142c0011014180f4a055203403e081440508050344103c0a29588034008114100d002c2c0703580406200240009001c0f40f2a084504441c05550307100748000110b0800603180e00c50400180e90f000c07070300040500c101591551201641070380100c50b05a41d103000e0045242d5860106895403030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 61023726 1250 61022476 61022531
    0x20c060d0b01030f0509150a0902030111120a1a150909070e0907020705010c02010302030a0b03060403020607090503030403020d110105210a0c02011503060c020a0f050f010c0906081306 81
    0x341c084401000182a42c0402000c00007240c140b00600403078000101d94202d0081000d950010150380d9081010090720f412207003e50994602003c50480f043d00f00010521501d0680404016484451107241110a83c54080104a005132030502e900d244c2802156001c650340c0003014104004080010f085920603100100850664141580207040c09890103a1104942c005820f44d01d02c2d2000290500c1c07064013009041544c000001a142d0099501075045e5100c05801c58071309203040e24000c1d50360748055a017003011400f4800d000905103800030071030302580d9000d4940805844a0781d110851003590b1208039040c00b50900000601d0803000d0015001030700941c440c0742c035600300307400140100c9006284400459043c6083c2e864250043d00c1c0800c1281c0d40100001001c4071021000c80c10881030840c002c0010b1130011080090060001d00700704245041c000810001d11049001d80d510240780c4508070206105600144140119586840a0902610011a0721140c400926185200445681 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 61024976 1250 61023726 61023731
    0x6050a05091614060d06030503071109090c0d06051503030309070302090106030614130f020a0804140f10151d07080c03010b070f0f020a0f080d0206070f05070201020c060d 75
    0x1007000b030b04498400949050110300e0a01c0011200115884003850040c1d0b80061401d03440c80c603903807100e0011600017003569180c801503d03114441c1c07445104500d115800e120b0100f914048049107070405403000402d0040c080d40550795401c05008020004400c840c484882001d454500f40000c40c411784020000d0245141988100100400c0603000001010f00d040b8050048030306031080c808015408075040d02265062601ca04050321002004060310350011880000c9140c001e405280118422010342d2054503090003416038840c3d2060364110940c3c0040000f1070b2140d8280e2041ca44640186903175040580c40b440c6804001450324010012040b0990810803503540c0034500c950130948908950f032175945002c42c2042240104d0002401e044485000442000f65040340c00d407130142d015008070055640d86442c40c1110344144a1120980210709144c50315034408901544504d40d81e0b142d5015150982e1412a2580c0083c2c030304a05622840c240c000302942c451014103100c540c0e04001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 61026226 1250 61024976 61024981
    0x120506180312010603020c010603080d0b030f03120f07020f030f0307171501030b0a120b100603050c180609040e0c04060605040819020d08030c0720010e0f060706050a05 74
    0x1034402580c800014402280c10038404905408280460141140d805180260b1130f01c024000c2180181403a0380700401e4001c0000340b90040c0b0080d90041c0610001c220291500c0035540c40140362248607000040001d80c180c1c5000503400a0034407122a080041c80c030407100c411701c0d11642140307164007103009060b04442c08401c11401135405000c040a80040d8903103400281003e0349100440c0d404161200e041c151101e400784000e8444c586c01200400d000082080d60000c9400c0c401e5240c002924001c41000200300d020840f01d00a0007080d0103030202030812490801110300c902105103900d1004c41d0300190401840600d5907441c0100089400120050880003015004001c21078031789a00c01e8040c00018402000a46000306401d240070302a000030250b100104d20000d8140f01810600a1042c80080140708100c00c013180a000c1c1a4407070004e210f101085001e10380e0703484100da118903002580711520000d050404103500c110980002d010507013003040540e1160241c40d01129451012a901d904 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 61027476 1250 61026226 61026241
    0x8041403030403180501030b0112110c1603020f10090b07020a030501020d0c0e0d0c091d160504060f050904230307061a0402040e0c070206041d07120203010f05120304120506 76
    0x807007401405d09007020009404242c002034500704101c40a0b035101070740d502141c405103035a4400c45444c54080070076569030b0112030510610300542804280c1c0074515444486810b0306000c0300e80100c0304415250000c5c0a4a485505642c940c40032504a030092002c101c00000038030240090003142089960220707903001304110003032601c0c1402e1000d0f07209e106509903020100b00704034804016206451004903134407003007201482e03010b08080a200740510440031422010b41d01e0b84010030a03203204480078009156034102000c1e2805250003042d5010008001040c001008610130488040001d41038206c020015610f05040d50450b113019511142c0320202e90b141c851708849000302c2c41c60121011401c19042640b41d1044410040480c00e1003c400241070040d03650700d4044d20010500361031001e045082050b40400b0243d800d60304140403840c0d05907102190f250b68000d0b68140c0b2503015146001e0352400c010003000802040b0607aa0501080001080c0003001200800086000710004d008a050008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 61028726 1250 61027476 61027517
    0x30509030c01030c0c02090a090c030c150507121b02120703020112090b06120a0203030403150e12090d0305070602120403020f07050102060412021c0906020705030303040c030308041403030403 84
    0x760400d450b10292034965904000d583c0300040c3c05903513a4000381e079a030750f00300c3c02400043c0c40900b16101c100b00000420a11680010039562010100c600e04200508199003038010410010b105190100089108500c11000c07071080410b02c0d42100407680d01900800e03d0310a28481e811501c4e0030080c02030040d540c105591a450500d0408200903a1342151605600080060100703446a9540c1e014007a100500300241c1c03011a8000741669070b6076a5070310f810b140940a051540100c1c3d81496401c1e41c008101084041c54010441074107840c00140d4410445000c444074021418480240146008515240b014000d11800465594141e04250030080e140501d13600440c00c181e48140307800e0003140d81c00b24160390019407046a12601a5080d10180d090002c804604070200310071805104c10349601640410841d41203809032010580c0710300a06849100494002c3c0c13031610701e40c2041000078856501c0c99401401031520711344078805220024199441601c0036070001e80d0f04400d082c02e000910 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 61029976 1250 61028726 61028743
    0x904060b0d060e0c160203031b0706170402031e1204030609020301050619030201030507030e010e070611070b030609060609030a061a0402040305060a0c1101060b03090601090606080c210403050903 86
    0x4083d5421494402600c43d031a2044005094400700d100d45240115241081542c04000d240c00b0410700c0510070440b2641d17034010a2140328009120171503218002c01c4c041085a000719006009025002c0303071803140404026071f904040ca07072031044003032440885d203d4102a0018520840c000700d1450241e004260a40b103006d07020303500c108021486d01c0c8011040d00348250441e682802c0105266540c504140d004060419426619500740013099155080204030141500c240742c58104401641008955403142d45024031940c2c0c95042012519a1418000043e071004006021a1404440c800424108581004201c840e96151881e40251394500541c007840e010043d9411410185992070751981c44001078880c18040343e4400c00b140d0850310640c33144031100c503446e0091102d507586035100b6480d0390040385d07625420b0103014004a841c4941e80101d01c125401552a51125211904105c8043c3c0c04140b811984400440084c1035815004064521035401313500d860351205240f40c01e2500300041c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 61031226 1250 61029976 61029989
    0x703020c07030f020604050918121611030a0f14010f0b010e010507020a050411070201080a020408070e09160605030402190513020921010c020712030c03030f020904060b0d06 76
    0x1481844203040c4000342407021a41c021030f1107104080e490000c00c4191040f600b0950300002c6480400c10a00303050840100f0486c20101183c140080190801002c2e004003401d600c00b0620039807904001c00d18a400da0041240002c02740c8000c0789490b034440c0d295118000c1c089805800103e0751900c41c540c00c0c821000030f0790600e0010300102000000007020f00308018801c1381840400306100342991103c0840b4809010042c00c108032208442e940e010482d00840c0049002651307010000350070404500079070307048508050081a1050811482601c642001001503070035102d40d0810043c02503e83d01c408005290640b030f02e507940c3c14280180071a805400400c840c005442c03900030801501e0f4842e085c3d0020642010043c1c03078181c01000510708030f200b8003044141004122008500040652050060769056000c84c2d103210b55465a03845038650004002c0c0c04581c5415003200071a009401903050b40c512914014940341c0c0f407100140c126a010f0b0400d000b80c86011900c44c10a0485100c0d80c4040c022 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 61032476 1250 61031226 61031231
    0x30f07030e1206060303120a0b0d150c140904110c0a06150509040b1f080102030108030409050f0103080a03020f071b0f091104030206090a0f17011107020607060b031f0e01050703 78
    0x501382e0100b503680c41362000075451400f00c07400048082141b036000e000103090082002c07003180300c1401e10011703903201485000ba03100d10340071401401d01d00401d1401307201003458901d0760519138240f0801c4024409050810b010340d03820000031009002c2440442d000c0c0c1e21404e400200510009a5400c4004054000720f020381c0d010000e11020807900300105d60b008240359200042d07820f030001c00780d0460046500c107030010f43c004400400c9119020001c0c10603102101e03001c01003a030301c8460419107003000380f1018150300ac0401040c140184039400900c0010340b500180c910b01056940d031250383c5443c500312002000c00200d02405071810301d4500c040101050704061004904480c4404024416444000e10503c80010404100e40710720b902c000080c90f00d04640d00804e5501c3daa0f080246020350b444001551038403204a07400c00e18001034032141a00941241d0400c4815650700c1d006110000203036506114002501c240c680a030264001c80e810301030300100c0d0a010313800d501030941e0f1004c4c04880c02d050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 61033726 1250 61032476 61032481
    0x913140105041812020c060a0305060301050c070803040b060d0c06120e0105010f060e04111215010c030e27090327060712030b060d061806030201050318030f07030e1206 74
    0x550107461003460740201d80c0d040071494041c01030b0310f006584880c6d00e801a00c0070510040d000d4243d48071522a2105600a100598442c0100e4203544940880281101d0080c80420003150b400007607039600950160006031416856154003800001a41c48100002c94601820118034658000c2c0440220820020704c55541444002d1040503000d00030700c03080203a0f66101000b1581c0b15008213070110954400b0383d42d00e861166066000d034104071180c0c0a21081d0f880f6140340c0e54455410000307807a07010360f15040aa66070608105031003100d043c91810403000e42c01d14668036800c8007021401240610001e595450b0700c0700600450540d0310300360f1b1382c5864001d8080d005c9501c88000f124080746d440700a44c40d4180c00b41d03005900505846100c281c0207800443c5d03941480111b5801078080e92488040e18282108442d1001e013510310a001c0240010028004190080f034984000242655084d040d2420150f5145040506400c240f0b810f42c0024002011294030b400e00c0c091405c2007a21801c054034051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 61034976 1250 61033726 61033751
    0x1a0306070309030c0803130c0e0c0d05091507030c0e0405010506031617150103060b1606020a02030405190f0509130803040c12030305040506150109090b0105091314010504 75
    0x2160020000c0c4245501d5016060405120b401000101036000c0f905c140c0b82d0809036202c1c550503c070400c04440031100e891000c40e0948851040070302c904c0020b41521300d03000109541b4405010b000d000070b240c0e4804d1803c90002e100141c00d0261143c85591380006e01204107000c010f242c4002200d280b80a42c2c50702005000c1030f102e2320110707a403082d111030342411031142000d0103c0d100508954070301d441142000600c090b51070140c545818081e03090742c00b0300c0442c0e21015051928030580c1d060141681d15600300c4c40005020303402034100705003c0c0c01504d0401d50f88001082c00c20600c10880a01144403007000d04c24466501403400c00b0300b0050740c40d00700740d1411080b00340160042c0000580b000750088005000c01c114a03400c4400f400d1206418002c603451481c010340500402c1e44c1c01c0791a4002c1c00e000618a111400101c0717101007059640101c0b061408103044014200c900c000c1e810000704010b14881c0e40c54514980c41c1400401c000012110410000c41c401180e047e082a881981403804040c3ea2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 61036226 1250 61034976 61034983
    0xf0d030203070f0c0f080c030105071b0308060310020a0e03010c020105040503070807060b1203130504051501080c040f080a05070b0304021509041d0705040b12060103080a021f06091a03 81
    0x140d5000c03100360000600f500300404001c1c2680d1202c0f450010341000480d01050104a248074082c054009000740c0d00c40c10380540300300300241c0720280001c500c04510400300780305004240e00a0b00150503140301a802000020503a80003820400105000c2c0399001c029080910400d4101450f1344001c101c1b50509544494803440b59a101800c41400031688009100b01ba03800304d40035002c01001441040d0f170000f1819282d401091400780403904a0b90001281c0c2014040c5503c504101c404c0d003120280307a82d005444400e000350202d40b400009000208120401d002a20701411751400200b41c00051440d159141404607005036804500034414040140c0b24821b001510006650707242d80c481c0c03201d102040062085643c40640d24074065203208848802040050a550041da0240a4480820180224a1343c9119000302d2640403038010030114040402404101d0307243e00c1590200030071540440d1281e04805a08207585940d100c0030000107055104400c20b550805054811030560300300003070f44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 61037476 1250 61036226 61036237
    0xe04030f080a0f0c09170105160f1b1b0801060b0d0b060705060c030a0e060411042a030213060e13180804080703050f162606040506060f0d030203 64
    0x9120501c4080740c03641c402e642120a144034060300400401c0e005100c0103040f507507544078600b0f100340280c1c04407243c1d040c1070060703034840c441c030b00068000c0020640301124145100200d240030843e100c4444107450503001d000b240d200303000d40b000d826600c20403900356180c003a01313621842c0c850703140101c1044804811800e8555440c0907141c00100d080c03c20b0086040c511540c41c0091043c000e640801000c03000031005507000c0c8003203a50800030740b1390000415603660b40c2542c020b0013130064079900c203442e0f10f00358020284c0c10710f462400342d94050f124a004490302c41890484030102f5004075100310010b020450800040c02c851032700f04060000c80003c640f0720690041c9400c1340301d0f05c44d203007540040b54001c805207822350b1101d146942c9940d91000251500740d2400100d9190240800c0390054003c00a800c50075400000c1002d0511b501d0001008428010390381c03c8a0399911000c10020040713824404184151f02136000f5110740d141ca00f040080f50714060305440d100c3c0d42c0c109089030109a0010a0b44c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 61038726 1250 61037476 61037507
    0x40602070302011b06240501030e0c0d020a15050702040c080f190b030d02100b01050307091401020106121b0b0c07061103090d080c0c1c020609040b04020c0d08010e0403 74
    0x102c40c11300c0d400061643c0c40c500308014000e941000841000001110304c41140050344002c100b510b00e071544011070590780140751583d080d6008002d104c815207000d90041e289140300070080c0950503500e140354179040c2040f10100004c203502190b00c02c00d41c00c081c003441507050810318141d0024a03089082c1189200060b0111803080405030420f48400d500d80d104101158004040b01c80c144c2c10488002e41c0c1c0d1109a0b14490503030b04288100e0040c0d4041c02c242c0b8000c280c9034071131021103401c1101c04c045040740c02241c00e0456488120014820b201014402c075841d029150704c6105038082d1f0b0340050240c002c1d41c020f40000500b00a195035040020842900350b4072a8a000d01d012015503500310b2079405041511a8042c0740e41010604008400c1d0040c181014000259400d501c5a134041080e0852509443c07100032800b00c00b20030040c40c058000740902d00000f000050711001c02d40100e0204e0b04000d1050256a001a1415042c1600800010300410324045048482c1c6041e6500400c00d600082500c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 61039976 1250 61038726 61038737
    0x105040603080301090c0909320106081f0b0a0302190215060616080408030316020c060d022a0706030b031f0905100c0215091504020f040e0709020702010e0604060207030201 76
    0xa0709507e00c02e19240009150810091100718030407405c8841c41c50f1407a1882051038200050440c0c0880402181750480d4000e41700c5046070380d6000340c0c03034100340c950b94003890190754400004105012040c0c00b506009059540050b162240d10311908001c480411100301594000701141e0204286617400681c0b08501b900d0094960090841c961305403500c2a030000d044090100c4c011481503800800355104030403500700d14496040021081e616100e200c24815000a41000680c001c5100780c0c0080c60000780c0340e034041e20910034000380c0f40304002c0e000340707502410303048054100110b0381e15002e0703011242821000341103400340f40300050000040719804170701f0a5841c1c44003034003848418012042e0070b40c00901c0600a56019240c0203460302c0707102403001c0d202084280400e14910001a810340101840342000100ba00d4540800c011021400d40c8150b2160321081d5295460106014850003403811010150701e0328024400500070704107240c2010f00a26091008100b890b5002038020f0403241c081c20325 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 61041226 1250 61039976 61039991
    0x30d0509060d02120916140907051204030e010908030f0706090503070f0f021906020d141603020c0f01050f1c11182110020c0102160302060f010504060308030109 71
    0x100344035004001d80c502035240f01191900e851449900c1e10382c07064818100b40d420f402e00c81004504040c00c40c2c001c0342184455109807080f81c1c00c2050321907800c01c8003401c0003401d0a90301c01e800004080122400c40c0005d504851406155800240c0300d000f9189a0020313604104a04004c59443c3c01504000b40030151904041428031009000300c600c01c5801040d180d00941c400d00b001c51045400400c05c030b014200311880c02d004850320369400c4054400301e2303000d800007402c40c42049903640109001141840380c20032078034119903081410850614800e4000d090300030646010040103108118800381800030810180625440c15012546910b04c800720100c00c00c0d40104c10103008100d0200c6042c00340100040302c43d0459125010f00c1541c4100700ca005401040c900d900e41403040301d490403045140d010101c0340c191802c0300d0700030740301030301050703000500340301c00041402ca00c64040030003a0301613084481888400b03011020710901404094409014007855540e40788400d100511400d0111542c803100d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 61042476 1250 61041226 61041229
    0xc0102011505010c0f1b0e01140303040501140703030626011407020a030f05120f06130e07060c020d1506170c03060103060902011b1101030e1614060c0106060c03090801020306030d0509 81
    0x150b0031111040e69004000d9980715000003002007c28040d0348202d020740c0a0f501c0301c03407800000326130a446040c3c2d1071624801041031490a19003001e00308806250303c031074001c42c400c51041c2e40c0c40c21042c00340341140312251000f121907084075881181624110045420059000e400141a010a81d4946024070401031a8032041780d0034043c140890241d04c01080600001d20740a8400601401040300c803c1492100221820304591302010364100c9030f04003410800c00307103019200f80342d00380c1d0026100000e00c0a1642e5102001c000c0c0d120448046603952205001c02c0011b00c2c070240f5240405801441d2038001240002c1d41c955051100901240e1180121421079100340030400f80240490070ba8440c442c007a180400e660f900d50001036002915001c11429010f00019070f031184c0b1040106a6181e660900750300d8000005400c07080381e00500d003003010040d4504d0034400c5000030081c07076848144266072454002c081a91560140205238018410700080755008102400c55000c0303400d02a988054030270 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 61043726 1250 61042476 61042493
    0x103180228060207150201090b15060403080c0105040501050601050307092601020a0f020d0504031112121b0d080106080f04060e0102120a0e010203091009050118050c0102011505010c0f 81
    0x40a04509401c03001600c9900081d01c0e5080d1070050b00841d0052808800c100d003244c0c003a04c405049a495100481c4507040c955140c0390a07450060b21561620b620b94441440c15800f155906000769561800c1009201d0280b0413690008400d282161841c10010350040401e1002d00503261404d28425580c044c4407041c801c40044484244c0083d51a807101c040064140c5044904a4015016510203088410300c5103045a040c2c80d481910100e1841e40d00b0300344011a15280c0031103219100f4001c8090054640714060481451320700300b502c6559544144040c141010000b1480078801c5005c0180302e429044a00c03036503c1501c0303846901d115592801c0c100068811103444c803005520001e07444800045a20743c99106260703401040c8041840a0000b41c201e00c4211501801d54001c0c3c014884151003035000306050f54014400410b841c1c81c88921518080032480b070440f201e902401d20300300956020700405020804601a0a510703070b184c6030029244684030786004121070a55202042005440d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 61044976 1250 61043726 61043779
    0x703020c07050916030606021218060d050103082137020c070608130803011203030b04020d0207060e0a0507061404030c0e01050315060a0b0706090611031501031802 72
    0x1000200c0c0d0b130400c842c100003804240c01e82400028106407010410038000150001400100742d02d4501d8510400481c4141d580954071395035000800300708078241c1088900403140031794010003407079658400480c20040108040b0540001054103401004031940c100720001c06580c58180010b8249403d5655440102c1c5848030340b601300038800719445140080c00182c85081d20401e07120004203407542c8140c0ba031043c440945c01418441c0c100014002c0c080c400a480c00000e200341000315401d001603000070103a07004980c1d0312010b44e0f03000c60800244490340c0184540c0a00b840e02807c0d14010b6a03e540344c442141e40601001d01242c1682c0e20a107403014000c45000f1a08580350b685015100c200c401d09101c020702c80c151007813191940c0a11890300d407a643ea4041c500c02041c00f20403914190380203ca13a00300040070303500d80d950b44ca4101c006c66914010100c1550318800c91958a00d8a0780c0c520040c43e40d400c0c2d04504051405c10240c5040d1843c100e02c0214580441d2604402034030030548928140c0c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 61046226 1250 61044976 61044979
    0xa0203070309060c0206090c010c0b15130204030f0c09051014010c08030a141b09040c030f090302010b090903090303040e150a0b0706110306030307030e06160c0504050603010e060703020c0705 84
    0x1840091358240c1e50210f401805005158140d170300301240d100044549514071800030303201d0003d40b404520317244032580380b071841c200c07001c1c01c030844818803201104101e820640c002e80da41d100c090b4502d0b08200302408881d01402031440108918140340b071685804034014002c0c407000748012008190b2a80c00b40300f140e0782d03055103c441d1a030f80745002e0071a03030b001d0125400f0042007a803484000c928140043d0589000101c4004411410010319604210180412801140c1450358a1920207105c0c9164002e40752001c0c065000841d0a401040902a0710341000f0810322140d0020b2001150341e07540441207504481400421035040d4880080e01c4510422803400d00340d1005c0301c0c4000040c0c40b9080005000e80c503000380300801003140b04c0507010725540300454a8030f61680003042a032001900401701d0f4101148043c001c1400c05884a0005078020840c42040d614a41840d00411192402d40500c65011409400034440e040060b0341c02c40e650740010b807070070040c1a00031500150011003042048000e210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 61047476 1250 61046226 61046231
    0x20108041e08070209011a0d05070c060603120f02010b010e040f0b0913170702010804030c03020709021305150c0d08042402090f01090f05060a11011b0f0201050705030a020307030906 80
    0x3842d1818050580c41000d040307004040c101d000042412600c040c2203800d640301030384140b80c00c00c038420380002403100901503c24000c3c0c074034410022640314031613040518410705001c031840d1071080001d000a10403440c1003046a041401101441e64401c2000c5134840c0c007614045080702d20000c0c100c002c3e003645240140c00021500402c012043c0d020b8505a180f801060340743e00d00c8011904240c020300c42c6142c081d021030000004180040c0c1314030303c00081c15010b4419900758070746616600040c0c0e070010450f8510420380d1242400f42d071400d454943c022003034180f0424644004001140d803510001c030001402c1c400ea1800290a00c01d241d000c203031104901e00c0c200c403213140602c10940006d4105402d0304d8040c1004a5044115500641e602001e50740440d80501a083c27070001000a5035001041c40410040031001811071484240500c1048a0b800087c40c140c41d00040002070004c041e522168046a0416040c05241500302045035040403190f2009640e0340e56505068002c0c103002d81004040341e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 61048726 1250 61047476 61047533
    0xa0201110706060609060c0209060d1a0a060f08031801080615040b03010f0e07020604140102130e06040e03130302060f0c160305010506040c0206060907090e0f090c060403080702010804 81
    0x5520f03841201903400c10785405414907200e00044501c108451030094002c07601c0e90200d4031514001161a20052154000d01070703013a11541d10703030841d0710165100321095485440a0050781200c01c2454050305c02540118200700304441c0c603503040604450810b040c801018007180325900d4000b00d0040c41f414044507144d8032036841c0b04030401544240b00d02c1410310003224000c240340c814100400d0003802030b41c1c01003400d501c40762113804040301d40042c100e56540d42003140d102c000000285e04001020a036020020624041d418041910900c0685404e242c03c10800d207841403032943c40c528140c0780c042d11299220107a440f250091b5110307058019545204803804100d03800c0d00307000b62a06a031310410003030006480d00d40510003500c4401a00740d0140c0c016500240c12800c20842c42984059580b41440034150b071100446818103054034102000b4645104001c4804400c01007920b4498095409504c0c151440d281c1501303c0c000c1040c002c0c100b20b01200814103100c0000340b81c0310450300c210081c0c540c81 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 61049976 1250 61048726 61048733
    0xa091103030301230609010534030504050306250e01050d0513120201020307020a02040908040312020a0b130c060c060605030303090c0102010e01060515070311011805010e0c060f0a02011107 83
    0x48410194402d0150700103e13000c1c4a0341091015950114010784682c0e08001c00d5120762a81a400344890120b4221038445130000c800c8415a181c440f507000351101c1e40d6413814a0b00b03060828400800c9001505020140445903c1d104002203840c0445498481824825800102ea86100d840180070640b4201020721000840c01c410010100b807080f0103000c000500e00b50f059003030340411940c01015070400c0c4044000341c205500185100c501c284449860700751242e0f2100c01c510107a07052400180d004031041010005122200f41c3c1203844040c1c46074500c0200c1d55401c1000d80d490160300c00b0407240c541d6250070042140c0008000c2c0200905490700d91610318021544c40114003a154019800c181c0003401c1442c06100314004d41c1c00187c01e101d400e01c980380714080e040d480008200d00b0002d40345a1900b0440c0d0038816080c07502d0300b13050140c1c001422805c00c2d2782551100e04038402150050150000166100d80032030300c912071440303401600c406e61808164011300d070f2142c10075090880010740c2401c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 61051226 1250 61049976 61049999
    0x90c12032205090601091505071109070314010f05030a03031d07080c010207090b0603060d030c06020a03090b0c1206040f140f09010c020d0e1e120f01061d0a091103030301 75
    0x2070320b50a840f100459940c040044071010641c2c0b15800300c4103040845801d165114a0040070000d00900800001c00825408034003554011201030000075550491401c0d01044441058010618121022101400e03c1e0000391601075151f070007030078140d0303400035010a10700800369451442540c1e003e41e03050310394400490f612209500c0c001c5005018000f004102c1035414400c010381c5000240c142c0c0c0c00d40c1d884030140030001c0711465043d000e202400c940c203000241d2a0006019117001c1c5e603400b0995a602d8030380002e00b9100a000c0c2a00348030244103980c0c0c1c0c08040383d0910791003102210085891740846241100400038503203601c000d80e00c0343c0700300601000356038111805031242d000200009841040126103c80012001c4c1d000108481000b042e54504004031115031a000b103030069860003050300007851105c080300c6c0d1102ca600a0301a599844001b07204d1003005020323095002c410030100d07003c907000034680104480600d0750348000120901650402c600b5451038080c0403039a49503102d6801482 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 61052476 1250 61051226 61051229
    0x30109030908120a170402010201020712020a0c17060604050a021c090203060604091208090c040612060b0108011206110d050c03010f150c11041506030605040506040203090c120322 79
    0x184200344105042180359070031503505444c1d65035500c0000c1752101c0031520034040030300145d04646d024018040812000d8a100072110710710740040440c500c0f1858002c40c2c5009551140c500d144150010131546500403d640303a100c00100c400059a580c0c1d48156030003806035808440b0501504140d0340201302d141d0780100040390080f01120080d030f03294010041039074103400d0300070564603181000c003c8880c02036411541112500d8150f1b0f80109580d8040b804403012507005000e0940442025014049940f00d0342840400130b19001700d8540c1465103002a075007005000a140c941d58405422048000801780c0b01d00c2c85010b0014840360a05c5c103c90250f640081c0a4002070704540980015035070509411039402035041d840d000d0240c0700a8582052049004610f15041034594a420300e0750041010702c0c00140505440024145052a042c0706c01c90788010320700b0707009a10400c14491049000500e055190000b15610040300a240300c0d05030950040043e0b0b0a120203200c0907201035400405004c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 61053726 1250 61052476 61052489
    0x6030207020f03011515110a0305070317090d0c14060c0c060705070b0a0e0a020d080307030b03030913020a020a0c0909030e090609240d05010b120a050c010513050301090309 76
    0x542c0640781d102098200c0c1c0c00315034407100e000e0b03ca550810140c02850102c03102e403803060810404103030000d14410b00f00181424218002800000c00c2c42c1015003000c1050070344180b04e10b261020b0310341850751540c0c524043c903642703080c031020b045071004102180e40c10324901c0030007405039000341c141300c0d49100c103d4100c502001d505004000000c0c848034031400580b0070150b00180568441d860308403044008185000e01003d060040d1014040540c5400d2002c500151207103c483d03a0720f00c0c0204000301100c04e02401c180c46a08204611203507680c40342e40381c10468101e50380043e0740e01d080c1a8140e140080c1958005c001c00c0c0d40120010b404c1510f603001c070341c0352402034450180c111340c444100301409204550039603011440708040340b0012441c070080c40407580c0300c3c030060800d208800d0010f07100408800040b24669156801c2038004e01b03042102c84c5103410050010483c040003035071165110100004658100034021440da045c0300707e807400b030384001c21020303008001d0b11820341801801c2d05098003489 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 61054976 1250 61053726 61053739
    0x6130f1103041403070c050405060a03021f020f0f070e090715020a020108010605040b0706050a020c0f03031006140d050a020d0e060a0606081605180a150807080c031f030b010603020702 81
    0x45460040129104c5c294401ca8015610381040b04120082801500c0301d608040203800200c01625170810021012542d0500c080c000c84641034020b00d00903010389024001c1c2c0280014290441000600405948898180c141142d484410716450b000060f445051b04103411603c400c00c0c9034001c00c1a0803494000ea030340e116281c1c0c82c4d500550f4a07104034800d40b0303080d01042202c50007150255104680110399000c000d45841804a61903140001e446120160360b04000188004230f840c48050720014841410005404544c0d80b8407581580180190300380c0e4075403914001143d111150341144c1c804810301000f0007025821031641e1781e03540801c90300409524035100011030755074041c01c1202c0c0300b0140801c6810320717210100f07400c94240d08411507806ca0f410a104240c512f580d601c00c805c00103400800a081c04107403e1a400516941029260f4406d0046900501c40b03810f546904980e880031240c1840c0b2408000c45502c3c0c5602c2d84035174400741c00f0403054000401d0041d410b80052200a0088441 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 61056226 1250 61054976 61055003
    0x3010c0507150b0f04020a020a0507090e0115051807020c0306131202011a0d0305040e0a0c09060f0e1002030c070303092d05040c1202040f090e030304020906130f110304 74
    0x94070200c40c0c00e0000f45a2103400d89103880c0b020b02d00b0350000c1c90100610310684810f860113942e00d030f2508240d6000981c03500e80b25070002d40003600034030550684036648164160290b2414001c503080e424a0650702d10f504c100700740040c5941c2e008210002c15400b020b001c030f4000b854005401c51010f450300c030085800400d50304078503000e18814003d0400e01c58800c443c0c091551044001c02101110b45001182403000510001a0000085018501c21030030703130101240031400311000820004040d0092420f0088280c420014564440100007a055003503d10000311510741400342d1035401140ba80c4040c51013280004810140d2003500b640c200c980042600c0c0d40c500f00c0c1440411003030548001c0c0510011141410042490719401a000c910002d06116101518030510381099174080c0c0c00000800c2c40f507902c1044110b50f07070310843c084e400444000d035085003042e40c00120f100c1ca025142c18030030703000c100c04079801c030304550300541c459815050f04000381400c030f800b051401d800840d015226401004070307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 61057476 1250 61056226 61056263
    0x31812011506081b0705030901170709090906060b0d091106070215030a060f0308070c060903080316050f12040c082e0603020a090207060501050303160b041103010c0507 74
    0x80d509100c900c950324440c1e11410103900b1980140c0c0105901111160301e04c2e14449a21a60000c080090056000d580da03440118009420405c4000c0300d80500c0d466203041003c0d142c0d2080c103440581d040808003040f0000039081241c0a4845500080c075204c100041108940b50f040e803004810520858400010300784000400819009060380650810400000824070396241401168440044880000c2050b1540c10441205ea5030f40c204507031280c0d000642c8828400c07644004401400245006030400342150b4030707030303410b400040c1205514a80b0720f420000e1081c05a410f41e001000c0000810f03844c1c618851107d401280182d40035101160031910100300e41002050840f421f00c01040308000603601500c1c070380c403260000448402c085603aa00080300503a10b5551000c01014072034805a1140e04500b405400c40340c0682c007162013503000300040e8034010f490907280c400107900600c04510301e40c1c860400c0340e00c4010155100394194a802a401c6c9155080005400500e0003011403070840d07040d200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 61058726 1250 61057476 61057481
    0xc040501050d080c3d05040c05090603070905130b06120309150d140a05060103141b0c01050403050c10050907030f02030a0c080105060f0f100c02060c03181201 70
    0x460b900009601075040110b1421801464607103000004c451039102c01102d00d01004030164004440101d284244ca9079003040c201440043c0d0098407400c0103541001e135034407185020f1602c5a540103911580004a9666087c07141c4001040503440c14400361030044039046040c0d80011040700d80300e0400700801c6003420b000207900c41841903040250b00e04142d9030208003e8840b020072201203010204030202c15044680914250300c480c200701c41d841414150307518419110003c021030704040c42c1118184485014145607604410906594030302080300f80d0407090309116056584070304e50b0074a800e210415502030300a0401480d01800c1d2055800c1c202506419168140c414540941c4840010300104090490700b524142c4010102c40380c141403599000680d018652114441c0e0b5541c10810203035040c40010b18040c4001180c0c01c503d01081000081c0f008450b04035000104111100d802c01107449020444012480040c01c494030b0740e00b20380044880c03056649055009524420301c0d80f02070003050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 61059976 1250 61058726 61058729
    0xa0602010e0d0c0206030f06030307060c0e01030b03151f0504060f0603050f101a070b090c030d0f020714030a020916030b0913032703030804050f0705010804081e0406050304050c040501 81
    0x14041c51460b15402c0c108408070390003030441c60b40b40c02b04210180000700d2922a101a0300c4207610340c8070307801c8200f03400901210301650005000f80c001505111000304002030b2a80e2020780c405a1100f03281c03c003801210b0a9115412058020380b42c004040342004400401c40212480390740d05205076a101540180090070a403500c506a0200c0c0e6010703c0560f09070141d40c03541b00d0060752211f041505944404440070f806662843c602e801044080116040c14002ca44821003942420b003000700c120840255100301504c955030006a1301c002001c0c16136000c0c0100103510350000c1c07802032103007845641c60700704020040622010038030306040100d81d402c20310107040c440c407518601017005030010348045d9450203110383d140e105040c20202c0d04018900f0080800c000c2d5020742d94007121440c0c503207019468000700c8000d18407a0750000800b00466a44030814583c401d03800740d540d03500c540f07a03030761181007a52019081c04506c1401040c0030034207690040217544101c1c015021903400e044064180001c8950a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 61061226 1250 61059976 61059979
    0x10906060c060e0c0a0306020306030607030b030706200a080a030c090e0f070e0a060c140622080d020a0507050c0a0311010c0f02090901020703080114030c12010b0a0602010e0d0c02 79
    0x1a140007030049080c65100041d4043c0c62820f0b210848a1079002072010780403904101d4040d6804414840203060410815610600e44d050421012200302e00181d0340f0720362440740401b04460029190029440c2c955040b611400c850204c07901601700d45414092a00074180b03a200091400c09440e64640c452000e8508580301580d0000154441d0541c000041728020000024040d00e01d00a036a80d03107039818040010000390f0390390002d0360403524050101c5008040940c0203a400403043c060745a8145c0016840d4608490f0381880a00c503d10b44854140100141620414800710303c1070502600500100346c8070b0f21070300540d0101c91144c01000014809400060440415035082c596554001c1c000c4180c9030b0700441c034201d44407040e640080c00169003182c90f5500c076500440c1c481d003095080301c1c00744d0240c100c1a0300041c0100740031010950382d240c6034407190301c142503251031900207550a40c0701214102000e412181c00540380e50010f4040c003980d001103419072107031200d01541107114051074040341350b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 61062476 1250 61061226 61061237
    0x301090507051509150f1e0a090f05090a0b030a1a0f0108012a02071a0a080906070c030804020d020405041209080c0105030604150e130507060c121215080304030b01090606 75
    0x5c0c051050074a60410180d014600f03204112601110184484150306691a00449581c0c1d5a81e900c008228510700d0788140940303210300d0000d1016680b01c0b200d2507484041c450000071190300b0310001030300e02060014090038140078640d00012251b05c0e42c8040d403203080d83c041644600c0e40d0300e4040500301c03000c56030b40c42d284034000186400b104111507070100604505104568a264583c00e01699400b000811810315650004a5085013074020044a5020180304094039003840c0c5620043c0000b081c5c0a00103041001c224000b030110350381c40501c00e903d260064001c020502d820700d010f01c030b520f145400140105403c5c2d02d000070010350008100380c00c031006a603650704540b92103003440054103c03082410504c49420f2400300348403400c0038259100c0e12060010060703806150034a14240103141c1c01540410604210080208040e17103081c4640100516003416104060030304031008050901000c40d4447d440007002924500010241040e607005a003101308a980e550742610407504103100e4440400e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 61063726 1250 61062476 61062499
    0x6080702100b0303040b0d0f050901020a09120312050408120f1006120905030316030e03031620030309010e06060904020f09040503130603061d070905040e0106050301090507051509 79
    0x41d054229082d5501e0140c212410300b03032100b04c1c0c00b10a400c50800c800c0e0959584400020364002070050581040c45403008502d02958010b00901246040c02050410b4510319448810103200700381c030168884500d5000c00c40c0d42403a1078090302650000d200f2010400305100072843c12454a1012809500641da11400071031401c0710543c0e032001c5a01034550856134030650100070a03824001144030b26405166081d401a540030f0140464185010000596005101300008411854684d00c40c0c01c0d1142820400c0c40e840909002e2240b81401c0d400d40c8a00000c818000090b2054100310b0303505044405a031202d0707a401041c048100c00c2210003940c04500d82d030300d9460340d0400301d406581143c09902507900c0d12815140c90a00e4101c030f0741c44000060760350003082000500900e0410410004803650340c044e420700700c1c0010040301c142c2c001c0901c115039500191807242e00c02d40c1320000611016000340075900c82c0e410942c0e181c00d007512a00d8080d480c0719404001c0c00d69018122910480010325001210 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 61064976 1250 61063726 61063753
    0x9050708060f0306070c0f02040e06060a0b070b0106050d0f0912140c0606010513080a1208070f02070515090414040606060f02030a0c0f0516090608010603050a0602030702012a030606080702 83
    0x4440c8a02a40d0700f4400e21f000001585490081580068120009100d0360a044041c001030358050340c001114100103020a5002801b005040350440382d07186002a00c0f10b13010003001000b014407117206599a0316003000e860030445600d84c40b003020b50305a240d020304114142c800b1b8415104010920040707400035000903c4130b6000b040580035110200801c40251034944040918050a00303006460720b03109044103c540301d901c114003903800215880c0c00041d07a1181e03107029540d8030046c017405100d9110003410010526842040d14901c06008000f4030050800c403908035400071050720291040380c10044040750550207441e200c504101035500840c90f00041e030b02c08a58010040c0c1e42100c0902446085602280301001050b0501946403500c0b52800d01d0b1243c000f045030b240c0e0340f003414240d0401d40c080003c5200868000c210a0b0010300140e0b032580c600300128010000d6002ca01c4ca0103150356614000e80204c02c590003200440c0340c408110280c2c0710350050303070b81410440c1c41d00b0050340040203010740c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 61066226 1250 61064976 61064987
    0x90f030703120207060b0d050106050906060405010e010c03050d11030414060106050f070f080d020d0b0907200c03010c051b12160f080a0309030912050616090306020409050708060f030607 82
    0x1d003801170368001201c02901c4c0028004a010040030340b0706030345403802400075141c01600d143d0040000c54800b031415150000103464040c250000310705020400300f0708014140035101b16146030101840412511104a45180c03e640007a138043d110246160040140c0d4100020f20905030b468503100e1b03904100103084000c40036400742000311243d0311042140c0340014002e0002d4101502c181802680b40c03410701c01040210b0390f034039403071500c00c82200050011250700690701040c5111542c11070b112803501041c03c0c0e49010030401c1c0035500b542ca000035007241203074000040c01d0840c0560341a0361803101c40c056940d030368114410a100d0030000400110809809003602c40580c10f108002040d007000c401d8030340071880c0c0c04c640c24202c0481d40790f90700b04003050741c84417a140107040300b042c4004000c21a6150b0994030b460040551900c10380007000040e01c54002c00750074008542c82281950303035a0300e4210004c09080150f0b03c99002c64651000b2460030301d031a203045440a03034054000c0002e540d071074004644 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 61067476 1250 61066226 61066237
    0x607030201020403060212010302180c04050103110c06070f0212090307051309060f051f030803040602030402011808010204060e060a0f03020a0905090a050f0f0c070611040e0708090f0307031202 85
    0x1559420800003002171010300140a601c0310180f2514282d40c554014131424800c0040008041c0b4040c0081002000301542a1403c1c0e807420719000480000915203c1c010703114000c100311091041c0c0e410008007946c01a880007205035107500399a114104002131504900602c0c901070b61541250b40d017440310381001426079102001655000c00c0d66252a12403608403071000a15000240d292420012492035510707040b1424010490707410507280c0303581c550301d40e140005080107100580020109080d603116082c802040407200e100c2d8152103a40d0f0600c64000e51151007000301151034100e0040c118501242602d46030402e036240c205c9031000140e821002507000358445400c1c048920800300da1520352007511032240110060018050901d1003103046204001890907907440034280c00c02030305080443c01e9980d4940d0100020aa40d00d1140640001e401950000f9040f09104c0d000c1048003580b042c1c52070f00514a40d81038a0480c050076204540740c0c822454082d000c10290790103801c080000794001c1c107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 61068726 1250 61067476 61067483
    0x1d1e0d0e010f090306020c1606020c01020606060304080c0304061d010c020102030703030903020f01060303230906040314010b090405100b0108011a031f06050309010b011e0c030309081605060109090b060607 90
    0xe0309501c031740e2160101d802481071200c055100580c0c8581e695030205440c4c0c05820300d40001c00d0070f8004400007d507142c030020f0141f4010800800070804104000302070b10140405001569191912a00c0003000d2203155900d5046440300800710341c0a0b9402580349244054042e80034610304046518282c001c0c2600d05401c034114801c10007101185a000e01c691400307035200b0759501c84441c0d0081c02c040d80b030200401c18018414010000300c0c0c60790b5248030032036044035030010a030301c001c1001078441401444c03611800b927045642041084100540414601071140159100300031450841c801160f00074824010307616407000c0d402c00b0312040034040c0055035100d4481c03120610560030880e42c9264541d10b40d400100856008070034041084400e004030076260200b80785c100d030100d41da080384104401441c140c58051240301d04200c2e003418800e0b04013401c0d40d5085030407a03546070700d03c1540350309002240c84152040d001d482e00226004046020380928150066205022500c83c10304003c2258402c01c401c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 61069976 1250 61068726 61068737
    0xf030d260f060d2a0503060f01080d180506040f08011404390305030a080a0504021507022d04060602060c04090509070f1d0a090c090b041d1e0d0e010f 66
    0x1040a00080d55071107641300c411000082c1180b81509151a141b4003600d15010481c0400050003d424006000001c141c100d04e0b000310b55489200c84000c0005040d009160000800140805d0340300000e60064116143c01d0002c1110b62142100c0d62001c18059400802d8480303c14888080080141c50303100000188006070075a101c480c10341c0b4166070745c803a40201c5480d00041017003107905400949030b50b07102d017000e102403125113444d41c001941a441060200781540c4c2c045642015500c07000311002c01902620f1a44451440c2c002d06543d161162a9a551080781401004a442d900c04900395014403000352582d82003d050400c0700b000780800800d07041080c41079000c00100500d0308030440c0c00a0548480c0c100d51318100d10844050b0f0f0900501000c24182450503100c0000c20800c40201181d0b41e680c07001501302841000213000d401c0d022103076006540001e001e1900702a001c07034140c0d60b0846070a020f90683e101072034565113510501a105000ca01180300c149000d50003541110f0f841202c51809 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 61071226 1250 61069976 61070003
    0x102040504020c0c18010e06150f2814030408070809090c0a0906170f1503030c011a0406080703030807140318060106031e0207020f030d260f060d 64
    0x20070304a81020450004940c000107003242c40b414940c0c0303800120051090340e42115810518a24100000640500d000d90b6440c40c0949080c1ca400055400f0b0080c00418255a61040c031055040d068004032800703400a448601c00c41c40a000311800ca92403c9460b404605603601c90311814074640000006031840d100420840d80c060391004506449410108540368481801141c010300912071a0080c01c1404000309074030072401c188940655000140c80140080307a0745503075842c0080c83c024842c0c680c040c41701003601c01884206401201030504e500e07101c014026240410801500c402c2d10606459800c07240090010034440c00b60964080002d00303017810b000c6c030305800d0301103107a00c101c941a0343c1d1102d035840d00d12000024030101e0300400c002d103424040d46541c0e44034922810100c500c0c0404450740018a0011901d950302c152907021300c005d080d82d004490007400641141310720580c40080304000821880c0d03800728040b2250282982900c01c401540e989403e200000494000594011000d001c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 61072476 1250 61071226 61071229
    0x30302090a0f12060b0307060e0909010e1606121b050a050412110f12071e090e070f0801060e040b0604180501020c1005010e0c070311060a090c09020310090e01020405 73
    0x14000b0060102c00070240c185441c50814404079440c2d01e0b01c86100e0f42100b40104001f552050004000003c00c41e03030a4190746070303082c2c00350045c911900141c2050059545c0c06002c0d090b030382c455034211003880e29440c00306962544e0450440d1111020001c3c48055581c2d900c9000d0710404c0604413144084c1400341c68142c0340d12003459410740e2002d0803170b80c04e804007034401d00c0f07418210810b204040d02035503210740380150381030a00d4907030882d40114182c600030348010319090b01d0315203071880041c0b01e400c1042000e040061015911102103000d047c805441242c0c1c00546075105210300d004880180458000c01e855a0366501d007040c50150125611685400541e000041c0c000448815144620001079894000c070307428500b04940c1203029201c0c140782c1801041240c440750701c802d50012403c1e003241c1d52a0800d01c0c065412105006440c40180328400030403e0f03000342c42c0e10441d505405003080b08a00d941c0d91101c070046e03100403030303240c803130403254a4041008880c030742c2200f040480050005030400e0303200c80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 61073726 1250 61072476 61072499
    0xd0c0215010f030311011505041e020d0615020a08070803060a090c02010e060c040e0606030403210902012c01030b01020c10030203041b0308040b03040f060606020a020922030302090a 80
    0x20001c2c10640c100d1401001055045041602088600b900a100d9058840c0d01011802100e00c90389000d20f4407048030a40c20003240c81c00c40c00300440d5060031034031058a00d543c03070001c6c45503002d030441c0781109101e40443c0e2400007034403013149548049528034092160f50f54460903040a4160717600485e0320076021450b908a0300034101416200c1e400050303001c010340c0015140090241490802d11030800c001d01007c0c04c0b0340303201a03201c1400d8403000d07540d80315032600711411400c3c2e0b880b0303a030000b141d5111640008465006510418003d9a9030304c1c0c9010001018113140700001d014095900348011f04903115402504407104640050060b1aa00003044003c140c0c2c0f4248007600c0340000741d002040108000c8650140e800741d10ba8003010902440c10b66071444030501c600c0c004c1c041182da0120010f41041440721812012551007030f01400490f640303503000307550f030700350460220300c100711007000031b01e551500704001e04a0b803603440340c0d07011165030945094000390b201410b01d94101c0c0c0c82c5c40000c50003e032042d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 61074976 1250 61073726 61073729
    0x60d020a090302150307030b0f03070611030405040203010b13080105071713061b0305010b0702010804022112030403080603010b0108060f060c151b07050a02040513060504060c02010e060108030d0c021501 89
    0x70b5a034585d0b240750005d0700a044031000d00071075105600c01000f6080c0c0d5100007038054103841c654206414840807001d140d9146d8011580a1756005000000200e69080c07180050920380c0c4030b021141c921140c40300141420f0700c0c02266031f840041c654684c00b6640203040c1790075582104a01111104107000e40c0c45150644108081c0c04d449113070300c2100900b41030741c1071140500404000c1403e5080070035680c0024440300d40500064802c02200110400e507001c0801220005030129049488442b00980401d5803034000f107806801041e001d400044042c02c0600528a040c00140d46031010355540f80e0400a1000d040c0d89013035000003003800001c81c2ca89040100040a82040c8504405481d03c4007140c018900b40b101040c09600f4103104003c00190005510340d100e03541101c0110b003540d10b2003520000441c0e41d0b100602141e040070107100a101e21580035903200600b070b900a00c800d01c19118400e0350b482c1c0a00c2003000550081103043c0c8403e10a47c0405c00c0848c080c816680603c1c80c5501001d4944400e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 61076226 1250 61074976 61075009
    0x1030f0f1a070806010e0f0a1e1716170a06020a030e0105010e0906090d0e100509091306150b04140d0b040b0105040f050601020a0311010b0409030c0501050609010302060d020a090302 80
    0x42c2d005004c155038010b21480d60405048540140b220180804105646818820402d03400c060a198110740340c0c519480101401c03076560340e81c4240d064400b5040d901e408010300790b00d480d44c2c00000880d1040b000040000a000341d60b000b4000c02c0015642d00c8001d43c03007070000e00d040580d10404040180420b0044d035000f4070303200b4030500702d078100401002e042100103030003a80b060b8000031000c880150052600324510404403050030030fa81d10010103451612881c43d0300d55100c9810350410101c894803204010a9601449080000000c610712a2944031a00d02400b00204c0042c4000c205034420614500300c10310028003a1007001e4030a03921000804000e40701110700141e943e005000a0605120306460300960500c10b2240303080c24070002c0d465500140303000c0d04001301c46d4122200c03282c09401800d500c03e0040c1c010404000c00342001400c040d80c50078220780075400c18022480354608042000d050b42c3e0000c000600d400100c0380e82500a50003c800c00c801c0c07200700b21340000035954034018500040c01c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 61077476 1250 61076226 61076237
    0xd09050f010b010201180303050c070212010f0c1107030b04020f0603010308071103010207122f01020705010e03070b0105061c06030609110d03080a02070819230301030f0f1a07 77
    0x300301952825110980b852074110780c50300008603850310a0140d100e00036500340c10005041d4541304148415841200406504031940e251500340c260380543c0040f084100c8440e0803c107401f00082e00b2900281a0103000320148d00100782807020803000500309400c2071005100104d03e05581000c84d003250400d03841911110700c0842e028003809131183c94209501c030100c008500c0c04181c0d0340c44d1441c00b5661400308040002500d070b101c041411592215140300b40c5420781110b400000741c4014040d40c8103c1044a20f075090400c1041618000000d13078032b00b0742c1d201d506144c1607820501408216080740040804e2103812050480c0341410621440000d180034a901146084407410710244401c8101c203030300e014090b00030428003c03076801010580c0107480c4060140e41c960b4903081050003401a1000e1503444807221012a04282c0c21150841c0702c4018060000c00410004000005900003488090710700c0170460388110001c6c2540c2312103801ca505c00c4661070081c000e81c9900c040321120031076154000c101c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 61078726 1250 61077476 61077493
    0x303020a170f2502120106050310060f050603130c030809040509030705100c020321010e07020d0c060209010c050d030e0f1219110303070504090b0d0206090f0103020d0905 75
    0x41c181d9200580c2000c030a14258800a0154682c400d4034203201120000681c1d85001c03042203000549025001001d440c500764400c1c44480c004e14951080398031034410b1440c240c1c0c0c01c46c00360103040111413074130804010851170042480115807001b00541581060080c0c1c1c3c0e0001004005428050342c003403004140c85001c1c1e002440704403030015003842a2039109000001c0050400946108d0b82c0c0700c0400003103540e40410505902e1401400c1d901c0040c0c00040c802030414081c241c10680c102c40c02010620100d80b26030806a0301e4690076418140090700d842d2060000c107095400620311031074103141c905620a80c036103605090450100c1206e00013a140c041d00741741f030f140c1008071201e408025009020100c9502d00228603d00c0740c042640142160154460b0030ba0340526001c40c400449a01500d0307407460446030041080c5d215004000c801803070407001d60100d00303091400b9060701742e010302041e140601020403c000f90103002c80756410150200400c265680e0316004183c0500c0c4070f0002004840f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 61079976 1250 61078726 61078733
    0x909030c0a0b01050a0f0b03070f1206062106030b0c03042609133e040e1006020105070917010b030106060306092301120515040b070813020a0b0d0b03070303020a 71
    0xe507486d903c22181b084030948184400325400084a41004190820f03015124000c4025503103015030040e140d19440c60900300040c2c0a0300195905240c41301c806d4140100440c2c41141003c40b40d007400040d1143c0c202c24005400d1011a100840c1c01c1405000d86560607007c030400714031089200700f01c0221680001c21a1052803c159000d1542c450f000c0700113001c0d080003026510301c1d0850b0450b003a1481c2200075111141c104948030511b016107042040746503117075244c0c0f000040d12001074400e418100d01501380024000c1c41881544d0080307640c0e030340c0e40c0f003040e10345084c01c2e0010340b000113200303c15561900c1c09140d5070340074440c8100800003500c0c04141d241c0307800c10301821036084c12134a10110307000400303605004e01c192448038151804d01e0f01340e8030384038903a0070003e00c1c0003200d49920303a484901400f448280039107280b8081c030540c0d00303943e840c00956480340941042e42c1c0800009400690a40c824401a80081701424102151403c00101003c480c0002032a01e0f083e03900a5002d030b0081007039802031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 61081226 1250 61079976 61079989
    0x10203180f01050f0703020a030b0901090606110c030712020118030b060a060201020313030c08300705090d060e16090213080d230708030906010e010918020909030c0a0b0105 76
    0x212000350002c02040c509079100c413458010080c0103504242d40001e450000d02c2c0280c1c44002034040140c1214095078546d0380740d000601c640d020f0303400030a150f505000c50030a0000740d10645050060090304406190541000e04140d490b2400c80c103100b070b0044520503003c400e01e410030003180035103940d40840c101202405807820340340c0c00c0340b0116401002082080161040c2900c2095418500940d40f1031860406881500030807265100d40110800d0404191034100140750790007203d520b070410346403902e2809032500e1246502d910b41040403000300c40007052156001140e0b510b80c1c501600c1001c160b680c0240a512965000010400e0340420107501030303822581600c01500b4008000c240554008001134106030f0700c840901018a800000d003c40c1c400ca200540d03002c59400801c01d0303100d040c1008980e0302d841c024010300c11014005800090050a07602034183c1c0d180603009001590855a002d0101c0504024654503851100700700f004105003042081005890080845010a505081c1004a0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 61082476 1250 61081226 61081243
    0x40c05090a06080a0807020d051504030905060403050c090a0e010903020115080c0a0e09150106050702010f0503010506270306040b04030809060103080406052a030d0506091006080c0c01020318 84
    0x16042c0c64503a080c402c0100001c0c034910101c1e0040f0714070b5250300c510f1000070300055191000511a00a042c440d00d0390401c2d194080e8041e6210b85c0b03890014545417400c0c03211500452101614030b6200d443d0500d042c0c00d00010440e01300c0303441c00c40400d010711210002429180001d60480051703545030040d06101164800b45e10207040c280c005484455401e4001a45100b0780303020b9400f0f00c0c20309902080420030308102010074460318401480c0c20790b07580c120103031407900305940aa0110300c0407a0b080c0019480b40c02102e0503518014429418180c90b000d0142e05000700e1103c101c0c50350080040c0e0f8a0740d0f98100002d6200b1446a017880b8000c2c43c091070b00800020014000400302d503c04801400019080800d8605640f080c0c41c001e17855800030320354201362a1103071948000c0801c005580f4160608040000c000d9100003807800e000580362081071000c03c24040350f030010725030300070762061008a11402600f40c0180d0101845070510143d44452400c903401620b102d0304440c180450581c045a0501c400003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 61083726 1250 61082476 61082491
    0xf031206090c0f030a060312120c0f021e0703050703140f0a0503090108281b050f07020919051e070f020703020907050412080309010b0a0b09040906090803040c0509 72
    0x2080707400c02d195118014010401d42094502010000451401c81d940c401401103800c070b42424002005403c01401c04114081e417040c0140c10060280010340c0034038400007202c1d885a0050460032003800a096190b030602d03582d10400c1c050b013800080412820842c0c0001b42d4005c41c4895016641c0170000b42c506240d050503000941c00100514000c2103000c000daa031482028280f45156036945070080310780ea44603500a26481c41c260700c01c1d04211030503a000012108070031003602c0f80c0d0401014140c80f203000b0000065000c1204200b050018100200f031542c110070050350303202c1c84020000030601550400c44040b08030500600182c1c0c1c6804c0c040d004140c2024041c10030764010491114000e48901c59400040d02442d20040815112440303601281c00074582011a40681409450200426442035400c04c80b29070904a8a40052800445175011902d030204c485103446c20352014000a0071141006440880d5a103c2c00c80100d541c00380110f00c10b5201d200140017403814102003004121014000c0c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 61084976 1250 61083726 61083739
    0x1407080408131805160f080a150503060403110f070b0316090b03010803070b01060305061305180a03090503010c08060918011b08040318050a0e15030a0309030b0105031c050304050f0f031206 83
    0x100b851f0044001a00000300320004640244980d04a4450a2207584400c0c0c01d48904070410041c0342e440181a10010f18034405c1d50302400032031070044e5564000d4090000c0254003040410f101c0d0f004035411040392036070340c10322480013a524170150070184c10981c40608150400140b01d0108200706040d50302601b00b9050401050420f0408206c6044e41241d608030361030354440100c1e285e510004c0450540c01e05140844281d5400d518004040103980c0c0f203941d01039030070701ca03031035600d2802041d801e84641005000540340c4c0e51072192a403001c0c0c01c022480403041d50b80d4014a84040481041e00c4402655a2a014094282803034014400b0100c002903003041d00d03040c00240456602c2e00c101504555150244199680f1043c81500010002030503c9030f051199418940c00c154200d44c1910482e801803055180aa076034909154407008068260f4500703021410805042c3e5000300041d41d00a4007480444038a01d03c0640c0b03079880c0540e181c2c9055000d500c08180340c0c07250411049183d91012080c1c626 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 61086226 1250 61084976 61084997
    0x501050a060e040f0203010f06140a0b18010c1716051504020105040b071704080c01090803030c0406030c050c1e0c041802040504020607060204030b0a140708040813180516 75
    0x40b0000c21010303000802c004a1840d01c84107540c0d09420605140542d0407080007020381c0e85a0b80d80750103a0310658103004032a00c801c0060140c109905131b44840d100802102c4c0c2150030000111441c100c500c1044130310400c60038034a11400d00c0700020380741001c2180079406e40034400b82070081c9041260b000011217480440108030040c1d07801010b90f012200510459910ae6030346281400c051926906120402c1001107130000e000700740098001c0b2414401c0e20303080001c58032015281d03120301c001c40741e101e84504100010003201d0700c01e80c400800f100042c40c01e581446409500c2504040c1205032120505102d4860001034002c107000000c0120800c0b102008003003014001c04617180031480c8081e01c9140d03110001015512a00202c9070b00d550321030300c11540c864030381c54140c5d0100c1c41607030483e502c0340c94007016042d2068506400c90040d003280e2100d000c04c1e074503581c40016aa20284514540071441840080c04a29600c00135080020b840c0c4007045914011041a0300034002601100030011107110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 61087476 1250 61086226 61086239
    0x906070905120703020111120715050606071106130902070302060a0b0d0510020f0712050a021207020315060f0604030308042a0905130803070f080f010506040506160515040501050a06 80
    0x80e070700f044903420308100f004071010440c21030a2144a014034508054005440020403000904810584210701010000d68640d64207102841c000d00800501c401c901480045940c40c0c850090301c20701c0b4000441078580ca4440070a401681c03c0300000f200507921075807d11445c0350441c00b8500e003088060710741a95020381500d13810713590484a540403962660000b14680210181c60441d01615040782140310140d0350108010129400815250018012a801007005d0544401124841c82d00140101500c9d922806005d5100f040039081c00c1c2c5c464258000c0c00615140c080c0034000460007515540301626050802c4840d4500c0010b48441c414001d041041c60800021400c40554400600019483e91344103061807581c0d02001e0094085070000c0200088168000a95103240c212983c402d602501c0d181000320010500303026042d03102e07405201c1803203541807000240c0b800b10101e03619111403c1c010744a081c28415050303040012500488108014841d090013001c1d0000c88480301040094980721 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 61088726 1250 61087476 61087483
    0x3110f0d200d06091a06131a0403031d0607060e07031509060e0102030903070b040807060f06050130020f0403020d030c050d1b02010f0203070b10050a0806090c010305041a090607090512 81
    0x796140300e0313a00464034111000c7c0c619042d402400003001e80201c1b020f401c904813082c5400c5403000700e000500c00d00000c401c10ba5480c40d810712000e070142c022800d054440c0e49502c050300300c0c42148965840b907071f0400004100d203018034624460510308002402c500310300f440d10a4641000c042002c981c0100103000d2980000001c075800385404c10080072068071a442e000344130f449000000350480d41030611005640c6034690021080710000d0700c444180c0246605244203045011079400305560790f0280c60704100403581c00078503000410b2081c0764601a01c07940056103c82503100d05600240046d5000420003000700030440c404c030483d0800b03650304490400b0404c00019400c600904200d000522003515a000300150303000c15900c4000302c1440d01c0c01c1c03049251040d00a1150920402951400003542900456883c1c00b030761b501d00107000f0800b982e0700154003074000a8070444440116480c0c14450004c40310b4124040d101c243c0142c6901d041440c0001d0030020355400070b610032102c14490815140000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 61089976 1250 61088726 61088771
    0x50a05090c030c040801020304030306050f0d030903080a0e030a0b01061701080a030e0414091b010302070507050f06070b040c030c09020c0d0c03090801110304060c03110f0d200d0609 80
    0x22210964a50f40c50007a000d460141da800441c040d8000700c00e000030160541c0104098440070f440909148510004004500381b07101405000b040c4400c5e0244045403011000303003141c0c5110f0070700481d00400e183c0800e10740f1020840030b0f90224210350050041552110079400016454024590329506001416848480741d00000f420301402201c49011500d440c5c105e0403000300240f1580f516885c02419554440b44030078454014001d454112200301c1d802482900d1449401038010085142040b003404001c180111041c0d44c0110b09100b1180022040f0034100c0c803c80c850301340ca180c0b4500e94902200c0c0c03850fa0341c20440c16280180444d180305940020940c00e00040391804190b00022814152440000c60b00403003030035400d0459407142c440e55480118000d910442d07003080340d40d025480481c2101c40d100412118900200111540888004003401048114200006e800540400b00301d050075880c034542031030030380301051041d034801091040a0040c171a851040c041d80c1c44408c0f4080c21018023 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 61091226 1250 61089976 61089991
    0x7050303030907180f0e06040b07182108040f170316030e04060305010c020703050c090912030414010507030f1d031b0307120c050d0f0801050907030f0f020a09050a0509 74
    0x301e03ca141800417500840c0403042c556208006002e04449025128101102c00703840c1c03100c4010107c0c820034801d1842d400c030a001286210f8a230360508a945125049142013010080485a90b40012801007130040008203440c6c3d486508040c640f080b0354540320203003901e41409420600201c0348801802c042880d140b40c1c10714100140d03540c4500020020700454002030b00d19032a1a0b001d80c0410380015a00050f84d01507002c90705004000420000144005c80d201e468642044c1c1e640000ca00154002e0358005100d10304120401e088800c1c41c1e030845004417146d000294441078a101d06103818031905550020000c160f80c80c580c0c0143e80706030303a0301c500000c00f02d09110411140111042c14005d84038030a074044055a2480c00100c40280100c050800550725800740381e800d5005c0e5400340980110300036580d03c80b482c60307070300e01010482d1041c80104100d0a2640350410030071042c041e4030811142c8034800800580760b60404030010b1001c030541d0450350141103581824071055552a80c00c5501004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 61092476 1250 61091226 61091249
    0x80604030509060d1104060e0922020102030d0c030617010213060f051e090108131a040201030b091602010c02010c120b0402120117010b04111801020f190507050303030907 75
    0x10b00303030100300284122000301d03d1040c07916040040007600380c0c000700100c0c1c0181d951000300032904d008000c10780505440c40c0542003690100107034081030b051503082609005006490030075030700307481c18803e44180181c000000782e5591800d02450100404207075081100e540210b040c91310121300e0355502e0006004420a01c44010381c01301d03840e40b00740704440d04070100c00b003907a000142080d40d01f0226003140603000c1c0469000381c005050f2089031151740032a10341101d001388884401884444514a014100b44d04150f00c07012aa4000d84070f050b15580107070045001c41c9a080480a0000d0840e403000c96902c0859050411103001c00760300000142d0b00410003200000d1629900d00018028840c000c3c0716901078041400000e42e441d0001d41c940f20030f0b9030060092001c800c4000411048a61940003416050014044046024025000d090314800c06004465041d1010300e4900c1c81c080300d81d240101014080c0380c89800300102441b0034001844290021825820b1070540281c451800d4001c481c034005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 61093726 1250 61092476 61092487
    0xf05010f0c15111309140603011506050d20070203010b0603070207051903060c0206070f0503040210050c120313030905030a0201020c09070302041a0703020c0d110d080903010c0503100e010806040305 87
    0x1240714040764540c00340e505040c10101d680300f00f05c1024200c4038075840540700c052000a1040d00b018018042035011844400c021a81440390540d501d80060f80c551044541d01e14001c40c0007003c25840700014204031064640b00c01552040609448046203280d015210038414004d100b0380010310341c0113491080f540b0001c454203800e4861450340301c42d88080c007c1401c0064440742e03103801080280c001c4009940341c024502d02c800041e11507101c00da41c020740000d08105800140d612940141000100718000e40b10360015400c88101d090b08180e07081000610180c5200040581102c0c082c40100300c154050701e0082c3d401d4001070b440d40b140445240c01090315800080080c0d200750b044401810041c2c410001507013150080c0d15068220000440243c45116020101c030300d801c15445001d1584840c9003200485e584003030100d80d1107283c400303c840a209201c951142d80e0207008401c8422500d6440d41e4480c5400b103c006000003169102da061090341d1001030244078001f25480340d1154050600660702d0307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 61094976 1250 61093726 61093751
    0x70e1c02030a060603030c030f21111207020106170c0d02040203090a050a0305070204240506160f08030f07050c0a08130503100501080c040b0109032009010f05010f0c15 74
    0x40b03415000808a91400c8404030805410450020105019a46041088420802c25100050074a8942d1381d042c0d03000032202102e01d200d81004510301040d458485c148541e9000e1b0000c450b0301951400b0141c1d44500d0241f11024080b1043c2c05010030000c01042c07408110703000302c1e4504000320320180c000c0d5000000a520144200804900503500004490071300d00c00782001042c640040ca81288a181400c01c0c081c56102c0b182d8224031003891080c0c40382002032400b0308202055111400c0d00f00110840e0038424003240e5414080700303c15000f4801c00c1c2e624600a001c05503904c00052590051107818480303500604400686c5141c51036021618559440a500c103912010703250b98002e50303251141c421032641f0144903401c07080c1200c408004685c4c550001104000580309960140d0703000400300310080020643c0741c1010b8080c02d0071044103000030360604c0c001c14083c8800360080346800c15040380810481d6401103258240001529007041c100340195141c40400c1d404401c1085400d4440c1c4c24014403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 61096226 1250 61094976 61094983
    0x16060209060f03060114030f180708070e060a0e010810020702040f020f0d0c02010506060d05100504020a0906020c06040b040302060c01110d0f060b04240e1801050405070e1c0203 78
    0x4140024440d60b20390402c0141e21850740d00840c0c4035800540003143c803003100901002980c0c040e0203e10450307041962008a141d8134110400c00382d60952152400c0012008800e02c03084e0082c00b0660300100ea0342c40c2c600103200c0307110751076070242d403c0c0c800c008010000c410b40460164a505910395003d0703070b542c901d4000500642000703e41c0e5842c9d24070010304404101c500400504001000140c240451116414141c1c03c844003111040e410030020442a0f08007031190344207907807102208000c0e460b050303110b50216007242c1000a600011030040c840510016030100101303c0961021240580303003e0034214007002e6409107200c0240914008140e4000c1c0e2502900204455144200c1c0d560329050b00420940103450107160003420070f0b141000115803550000101e43c1a690305d54105050304e0794902d81148058800000c0c04208082c0000ca11407030307034400c0299661110710000c50180e5505040405c411100040d2800060050304030030f1807002d40f03408114001d4441c00e100260250400c03400441d04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 61097476 1250 61096226 61096237
    0x60c0a0807302a0503150406090518070e010f05130e061510030905030306060c070810140a021303021c08030115090b070c030f0f0b0403031a060708160602 68
    0x20400064441d20b008036059110360074030420030091946400011104034960700000c00050001442000001c40003544007259090102005d00005201c1c6c1d903814401080365019112200544100040301001c60410000d000140240303003510a10b951501404101d404490311609014a00ea03500c13080410b0000d9210308543c05420068502510b0310280b0f8411a2001ca94401d11400350446255a40d903c00e204500502c2d0340b0400462840e03c0380e404001c1d260b040322802800500c10342d50045440c0c40140004247e2803200351000c0366001e40b001124102803002094200d23114810320000c50b00d84060580102141c0d0103581e03442c40c050201d000c0c80001c482440c030103089224004000a01d10400741029881808070303640d0424015124101c094040c4a03040e03001e80724a00f03008003072010400088080c030000b072090001c4a92090b0559403800f844404072010f8020944c0e51011180700b0340301500e13401403054100d03401c5283c40d156070b403001080d02900580d248000500b250503020010303075904482d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 61098726 1250 61097476 61097537
    0xf0c020306160f110706082d040c08010b010804081803031206041404080901080a020d0903020f0c1804140a021302180306070f050306040b030a4b110a090608060c0a0807 74
    0xc2c184a10041003280c0c48e13055504442e203400382c904c0000c500c801882500000345050f552080d07140c88a03216050030b50850901c181e00c0d800c1c0004814840d940400c0101001203c44e4a10051454a1310810048038007105258805041c180f080000140410080700c14040007401c1212903034941c3c9007918000d0180141d40c2c07160618100c1804103064000624401003500082298901e0103841d00340100103002c1c80541810380400c001150019881100030305804456404072203540c0c030785800003200748241c0704210110a600180041c07586610802c0b0703003051441075000b80f102d814604002400c1c0802941c0301c10030400f01102042080d642da410540d071b03900c0c00808480300a0054107045900d4041d040c407400b901a00c1c2c040d8034121080303c1001508002c942644401c6000000b0a407039054901d030740d004c460f110b0700c640090206035601e112100140068800014103e418007681514006000e00020500c0005106210f00142d000c01c3e001d41c092100d1810448184804002e00c0340440c00c902d200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 61099976 1250 61098726 61098781
    0x120c0b100503071a31060903060b0d02031f060e0109140106110c0d02030120250206040303030b06070819032301060f0c020306160f11070608 62
    0x3210a8005049410035a4001c03800e442c102035840102c40300f40300d01da03440e0500b80d000600c100960748001001850500d118041044480842c000504000e80002e811240100e049180103200780720f818403d070000d0b80740a4642c0100703000c082c1c00003581d0301510101883c100040c6d415402c0144803940044008111200480c5000c0d6102d0300c401c0081c000c0041e40b41310034500c0c5800001d0716031103070054080c084007000140c4800b08110302805440c5041d00d105036010741d202e034010000125246560076010003400780154030b4144006d00e141c000859840c1214174061164004000740e500c0c5412a8200c990504000401c03e100002280650240303c1c00642541c1005c20304016034985601651200070721341d41c00b0841c10b110328203c0d041a04009221440110140006111450094154070030300710703560070909402403913540080c0c941001111140d0942075240149108243c000b5461070201c8550700f8403900c0040050017160b65245c4502c2a1000c0280711f00108200c140c11102d942c8560380b41c2000c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 61101226 1250 61099976 61099981
    0x19050c1308060a0e0a080a03150b0d0b030f0a170307020114090d0905090c07031d03030f0c0c0f13050c0f03041b0806070906110118050d1b02060403120c0b 68
    0x2107038850b0310440c0d038508500d0902d4801c000d07600c008508044941e500004050911195020840003499107005844411901e11000300e4140c5c0d00360003528840b50b070014003080d1521144181418803011003091406580550620310005c0c00e51480101d40c0a08480180d4884d9075031342c0100d002d81403010000540304e245101f4002003400110b101040705800d0745921104c00d81da0000d00001c1c4400311004c0403454030600c8800d00182c41900300c003d4454070982c130b4003030100341c903000a8156442030304030440e40c600001da180c2038820f0030300c113040c61181c0880e2280f01c200d8078100030507004618000078040d40c40c1ea0310b001511b03000c803101c181d8070001002000c140e141c1c94070303251500c600517000d4007682000c482c08000198000b400513200d40710390080ea60301c956652414a0550784101e41c02000301c0b46540b912010002103841741c3c0c480340100d00650080c91402d018600141600085071a50400d032110101810056222042247c0443c0c0c0d00c007403000322045100304101d40d00c103083c1d4002000f00d881a000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 61102476 1250 61101226 61101239
    0x607021309030c050d091208090a0e01060c0b0604051e090118060605120a0c090c020f0607030203160507020904080306010e030a050601080f07050a0308090105040f0902040f0602010519050c13 84
    0x110f5180701e100d8401c5800b502c0c0540b6040d280d80f99948501d241007200136070000001460040035001803500a0048801e4a072208002800003200340c014400184a03402e550041c0521a0b5070a60844400d5a0400c05806c003c12050446000861260081e00c441d401180b40c0d02c500b584804110040d200420032507c40382c0c03030050b02602c828170406204401c510320b50040800b01107010a003456000044020031850030501301f01800e40074240105501484c421498403600500200348900650754005940307240810320165864a1700174440c041050074440c40780140c8445182c0c9802503000310b40f26480b80d54a034012140c038900c01903219054002d0540e0101045400100c403410381e400c5500f61010104815903981d44c1c0c03000f503c2501c0e1301c100c2820040002c60080c00c0141620201031600ba89810744408156484123401e074050200c080e1700080c10008082e600741e014002c2d0103544000c1c04142083c1d00c2c0102855082c0f40f0310750126a54002141d4000c2404007260301d44101a540d0b812155035589 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 61103726 1250 61102476 61102487
    0x105070c0b1c060e07080604050705252109062109050703021005160206030a02160b0f06040903053c040f0503030304080d050403020a020405041b0603021305060702130903 75
    0x31100c0d688141030043c00f0800f1481c0010031482400d2076030351200241d54090801002d408040e01071400e104041204468001c10500c50480c0c40c07001c100280707805070311741c0752240307203440000201e03e00d80d041c269002102640c00350f0500d0880e1480c0c0380041850041d68640110200000c0c51240c026183c2080c0790108500890507000700c074000c8072031502a4502c20030a0381c99204a4141410090548075428010307c0e1000146030400c1d00070000601303050024150411a418010b01604c1c1020a40c0400c0a400c0c1c00004a9601002c2550240105c0041d5500540a8000e222a0002600c1640d00380e400441c420002070051417000d00d40c4030004041a812a90164040e015030014090400350114040c140001201c1c001c60380409070903d03140009210a0040c00e015004801f103024440124025a0301d80c01503500480c01039202071403030b41d044145042e01c80302990149051500500001c48000e240c03004210840e00709032041e0340d885404e0310000c0c45c980c0c0000714085c082450100700300141075002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 61104976 1250 61103726 61103767
    0x9150c0604060501061d0103110403020d050a11030109020906120a0210091701140f191a130b010e0f0301020f040e0103150212040609051e0607030c1701050105070c0b 73
    0xa420030000390741c071280220755108500303603085d5824440e00c6e10f4050a5120743e22404101d17440241030341c2003030703101d50005500b40003440060352141c1c003580c100d40030f000007840c8024148004034002c2084610b1940400c00e004001806c15100b01204441c0c4440481c0900c444d0782c0541e4001c0c2076040710801d4410283c540c0e105405101d10400008030039a028007014400c508030540381018013609079840000c0144482c0000700480802c0e0301c2030300300010100181c0611aa03665000c004e106c6414401070901000d13405024a80d03c529003000c4182c480350740c120010540002c0e00f42d55801014240501190280c0304001781c030100c0710307800200062285810b42c0802d060360710450340d407203000014800304000e0380541c10304034201410646c003107400074807194090280c65100380191200c3c40301803a9804984034941080c2403182d0015001c0000d10359062040103c2c540740360800250a040502610101050500807035051220000e090004d000789454240014480c0e000225030301c6901007071504450800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 61106226 1250 61104976 61104983
    0x11e030906110d150b04030611070c0b0406030b22050c0909010306050714073219030306090c020705060703030b10020a02040501151b06020c0a0803010e0108030a1409150c0604 77
    0x200b80c04040c1861410040c60304859451802c1411b180c1140c03100300040c420000c2040c0b038050104081400075084041e10001442d400c50019110343c541200681501c000003000342c03103000741c100f032462091800b51568081c44188400056140e840e00c1d4101903078801c1200f02130303010800748000000c02a041d0040c1d8450441c0d03903900501c00c0543c0101c11542c0c0120f8000400180a4200846d54080e170b010b03003e0080703c060f00c1c01c04021503c60360540d05008800d13030301c0f0503110301c603c540030289038241c0118001020341080401805400c044002c0d192407160017000e108a0f070003d201c1003454070a0b0031010100200800c83c2c284030106003030107540d0303c080003803c9000f542000700000e140c40f84100561120800f83d1100c2c0d6110141007092800f03215140030480312154203100103103002c0401c00c100d9400314407503100d071650f9505107000c841c8105016030210009601c10010b0b445550740c00103088409102e03a114854440100d05e0000e220740041d612184003405021500d03105030980003c01c0ca000e13070302 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 61107476 1250 61106226 61106231
    0x1e0201021605030309150408070308130803070e0f100203120a02070618110307050f010807020f03031009060f050117040f0204050a090201030b030708030f0714030c0106030314030105011e030906110d 87
    0x403100e003010702080040b07c1c0a007e140d81440b907080841e0040504643c098004441410b049031103542c1e606458100b520300100041082c000c1900c0c81c101502164441c1d1000c0f2404151142038001c002d40d02c0c8108500e61259035a1400482d4a14500c5c0e01a5880c0c07551049050003114511250800b6110b0811b40c1512491108610b044c8182000700b06981900e60141c8558204110580103490003076001e440030007148100b0351011005070085c005076018000081c140190036103086880400d58040e80c0209503094480042000580e810005610b86035204100c50040ca540d10f0a00102c43c0c080480081e42050800f4200648030340141d01c41400a03100740ca0070040181118149503480200f03000700c550300d81c4100101036005841c080500905c62042c0940c6103000c80f410b01c0c0c40c0c21a008848a089103a442d4001401019080f010170b4104c00010548503056600d090b0009000302055064203401c5031130070844c1c9074814400d800c4444502c0d0814014030950f4154110080b940d40101e030003802c0580b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 61108726 1250 61107476 61107493
    0xe070e130b01110d110613020a0306180c0609080d02070f05010c020d060c02030a0809010902010801090b0303070611030a0606181a070515061201140402040203070201140906090c0a0302011e0201021605030309 91
    0x40720101f401e0100c64002e03102060460460780c80200801c1c0541e861000f03403140320300100c0000ca01091250181c1013907520742100518040a092030700c504420f4420940d041038106101c81c10b0300280c1002124824039240550b15494004140d0300010507902809450418030680d01b13546d0000010090744840342c0c0c0e404010303600c014405081360283c11000380069074090042201c01156000b18002c54001030603207180c11155079861044400e0048080310180020042000e06681c80c4500703030003021a410322020040e0701003442034115529000312121905905544078550140d00d094484c031541c0842101c284040040040c07950120807101c0c184903003000102d0142c003450600a20144418911003100a5250b980c01c02000c0d40004080c9011903580b07904144003040d0a1540d14040e5407200050001c9045c84500542081d9152488500030003a0b0113003040142da000c145010712442d104210340002d003207210120701a200b00c2c44410241041a27000c0d40074407030081b00560080490008030350022 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 61109976 1250 61108726 61108741
    0x7080910092d0f0608040204050c0408030d060e07050301051503040507150c11030c0d0609050c03030301300807060203180d03020c01050f040f080a030f14010e070e130b01110d1106 79
    0x903801303024020010b00002d0105005041c2078114035044a80381e44498109521000c000d0b28580100c02076000320343c2c803a07104100d40440303118086d0b000402e03840c081e840c45d818030001c641010010f4110098103c8000005024410140b2030b58000c1c01071086416040c0d040128000d1109004410540301740d94001200c03c1c1e14507002510510415001c2e11000c240f50443d01d84000515420100361180d000303c4482403007581c2c0500c000c5010340260504412003c03400c0a800303d02000d506c4448080c0c104072060803011500e04001d0703802295000801603030360b0b51940d01500743c2a501e2501c0e104240718a12040c800c054164000d04100b454030030003001940c0d11139100046c40802958007401804403030f200f04001c510614004c1621440905000c15580703c9403600800311440703e2024121808444010300070380801800b405c4e00a03070f141c035110202c443c010000400c00400140c6103409942e40c1e80182485034025000303818491134420541e9015460000b010b04540b0300602194554000c80c000100320f0f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 61111226 1250 61109976 61109999
    0xa05090c0a03030f030b0d020405042405010b070807021201060602100e03090d020411070c0303030b0a060f08060103020a0912200603010308190302040b070c030b0c07080910092d 78
    0x2142d40544c2c404180c000750310310690040500700800c40d0010085402440940ca85000d894007803441400c40d8410607040140f5426910744000102d103206040c180100003965510b400c0d101519000010035642c0c50301440050444100110100529400c100700081c9403500411041d003c0300107901c09101c000300c8000c08513143d12440105a80c0064042015000750a00e50b1080c01c01300003001300a4904032094440d145011010381c8110000380e04c0d4403403110355081110861700181403504040c6202a0412405404040700821243c10103501183c0d0ba01064071a140c0c0200030140c444900810461600f005e0300b015500c10141e02d0070241b944c000074401c0c1022000c6a04a9402c503514506000403641100455084810386004064081c040406d000f402c01c4002c02c2c00c00e200c0c49494024500c1c0d071520381c81100c0000c010111a0340240406404188168110740440c042258200e425410707209040c0c0d00ca40c0c03e03800c81d458000d84003c0b4075260a10700d08400d5001500031500c0d94049540b141c11400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 61112476 1250 61111226 61111229
    0xb0712030204080a061b0f0c080309010e0f0109151802010c05120c03120603060c12090717030702010e04020310031401060306050c03010608161205060a15020d0e090907030f030c0b0a05090c0a 84
    0x32302a80c4a840101d14034101540e080860817001158141945080d1454090b00c150443e0340340e5074440d880020084800215074000d0a115002e0100307070341541e0701c0352200c400498040d041c000103146030390422205000455001942c0c0131496203c0b00d03007003141d50752030f000445040c0c985c40190740450b0039450006262481044402d1149140c140301c00014201d501015040507610b204050000c64044a02c06410b560914100002c1d9141c3d030007800010014000388010502a500c100103004481c030000300d519050329040038640780d8040d600d0903514010661684041c008074a40010300c1201c6207002d0046040f04c0c4956910740741502c41451524505280c4844040403c5500000c100d048025811140e400038004088000b83c80d0750b14840710790380380200c0b01701c1d0058004100c43c0d6007a540020303000b84005400e842c0940c00e0326040d2041030780d645890201800420b032a100410802d8481d80c0900c40030750340548a202d03942041c0f0145070203040305803400c491900034030400c0505401c00440f14030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 61113726 1250 61112476 61112507
    0x102040305061b04030204050c070b100b04090926031006030519050402120601180f0e0706030902030a0f0b040201030e030a080f0c0c120c0d05040b0712030204080a061b 74
    0x80d00c42403242c2c40c00020074040030344120743c02e20002001d690b6901c100e6115800d100e502542d0359800d807818045148c40100104002e01000b03500b404140788020560f41560840007000904640904200b02205800800000c5064090751000307550f412080103180200c0d204140f0a00c4030781ca4500039815690122040c0340c0c01c844103180000044196000283c00a0002d0501203c0b5104020380070300300031342604012240c03070201c451389283c1136aa01c1145803025a502d0701b000400382d001c1d4000d1310350180b032080004054070355407070105540d8144000001c0903803101c0e102d0049140e5207004801c17080d04460980c0481e1426843e0300c80017801100b12114401c0790303528040603507100c050b440c0d02ca580140000c21543c0090261416114040107490790044465040c1034a600d4080c03021031808040c0e11000c001c2010a10007080030610803c2540c030250760081c030341c020213110807000310024051540138078103d1182c20603078420700c542e541c801e036a044001c403c4401d0142c40ca8030291900201501c008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 61114976 1250 61113726 61113733
    0x102060c0d0b0d06020a0201150f0509010302040c030e0d02100c030501120209070318051506060702010203030118020706061806060302040f180b03030c0601081009031403040507030203011e0501080102040305 91
    0x1c642090040d40a001c1d2018014000d042d203007002c1d1610022070304454a1040542e54910131207a00c01c85018008000f8460318002c4031845080101007a040035040c480203000d162510201000c05000ba006140c90700f01c81e6044400840c04558025550043da89407031003a10328110340c10303a07458440c0c040c040c16240b5040113800d0511307940e03082c0480900700419a20405650307003220004000c030340c0704140d4028003800082c405241203041d024041800905502e2060a040242e0310060743c0100a503411105030710300b420b480d0442500400c2c040e10405000030702441ca81400400c03184461040d8500b003001d4820b041054035101d44055089100d14025400c900c1b000b81d0040056001201d42d00e0b0b031401c503015001c1415860356011a2558104403c1400160413810050180d00360400c0012001008450248080301031f5440281560100158000304d00000000140a000041000c2001154058000c000b00c607403e000702100e0180c1011004802801d00000090f4400140281c03401d036a0464041d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 61116226 1250 61114976 61114987
    0xd0f0b0d0c0303091406040320090a0906051602060c030702120d0603050c03120f0702030307080c0d02060906040305030708071709030301090c0207031106070f0b0f010e060607050a03080c040f12050c0102060c 91
    0x14042c0b0000405003410027241289017500301d54503104001402030088050106482001d0f180c05000e607000108040c0280d5190315244100c0c950000e6840d400281d0300d0b041d160790340c49040c012400c1421030240241c018100040e44281800c2540c0580c084034002d0342a1148018084d0405d500d40c202c04005501c1244244040c00c481c04140740100580351008088925214950355050000c0e00100320044050308001c9001d401c01e0f4040c09400c0d842900400600b04034601980c010b483c2d40005841c107020881d076200040d01c007038041c50510201c015145035003146840e1800e4903035a00d620034043c2105060034101d05080031070002404d542925401200c0f01503408400080c07000780d40021000f07540002101142c4000f040d00c0000190080b00f050101403603540c10012005e00d88c54003d8a160f0103408108a01030100d02d012400107151079161800c10038588485403195001d00480c4c01004505082e010005110380c40d01c22022660351142065611558100006a88400040360030040810b000c010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 61117476 1250 61116226 61116233
    0x3010e060711030d050a0b09011203080a0f2310060c0807151d0109050705060705100b01030e101d030a08070c020103021903140a110d0f0b0d0c03030914060403 70
    0x491007100303002e41040300c2c18881110060425207006503000003c0680d2038140030001d0810401c2c450252003200075001a0310495a001884200001d00c1d03d03402c070b959038500b0300010381680c100c000b0104000800005065421030300180c0400d0580b241c004494001500140c6103005400f1001c046400071180d0342040710985030741d558180f80c0609110300c182c2ea611400c0c520020440c2422500c1286400040c1c14181072400d03070718000d060742280d0300c20841801b1400000b5000122056205007c000c0402e84051000041e405011000902082070103032030f41d00007090140d54403040c42c4c10a1850038440552030380b800f0584134400d1a80c1140082c4040c40010307801405600030b03400071441858010319000c0c420300c411000040c0071b11070000183d100c1001e14500f80c055245550070074161101048040e400c520010058841c4054000130241c5482040200302c0803940840a0b5100c040d10025980825241055050b0901d010403808514111400308134200050224484848090001707440c1904544 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 61118726 1250 61117476 61117487
    0x60a0501140c0a1a15010305060604060509040603080d0b040b0d12080c0c0102030f0105040c0f080619080a030203030610030608120306220209030705040504120810170307020a0503010e0607 83
    0xb403002640c070406200100040c03c880d0602c0c043c5089101880303079030030011032205090798441342c5d803410181860280038440d0b442004840031603006041c06d40c0c3c0e03242500302150113800140e1004c1c100c40c0000c100413100e0101a00b0540c04960211010089003a00303604000d00c0c40d829100180241c42c00013a0500007074040c8048036000009030100c5030070b001040c052507007640c0c421240341d81c52802010040040d4180b60154070f6140d151804e00e04100ba2543c07100400c0c846006058070b100b4400140381e002c624001c07001404c050107101041d00c1c48401d40c1c0c00e020396a54416107049000d44030702c0000f2841a4440d10864060300c001d00040e0100d00c1000710b900b800c9130000380159900204051290030410000707504c0c0c0120101c0341da00585c035065424201400c00c0e840342d0185001e1410301c01000002a0103da0a810003849805c08035011b48400c118201d109510307400048143c1ca03500443c80c02601c0000240c20b0051003222880c920b00c3d10f03a000d02d400da07400341644c8016544907801050040b030064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 61119976 1250 61118726 61118737
    0x1814150a0605030c0d1503150c0905011b0b070504090608030307080105011d01030507120903020a05161409070905060705010203040c12080702100e0a031103011505130e07052205060a050114 83
    0x91281e20205c3d07ea407a11000d841c10b00c680611200d5603032500c1e010458201d04410010721007400c1039034814040c0703100740c07100220141c00149014503c100003040940541e090301c010f80401c0d00d0400c242a1285a100d0707696100340c0348000409d1004000240310340c40b6050149185005101c96076081030311000560241002801590a0103001e0416a40c1820107104a01c0d130580079500500090156090060500f15540c5500151010380d08050000001c290451060301609840701d220399a2021000c4a150015820031980410700040d148148041500950700682c0508180181d007650307840b651030400141c08004080740c0e01131001c82d02501c0c06122046941c01c941c2804000003400000284120200741c00841d14003d500004240300d090900c10100072840e443c40740445117040c40b000454641d00c80315084002c40c0c68094400746c0403000d01825004000c0684000300000120514825581100d1f11654800d4900400030f80e061500642500c200c4034103031140c00449a0800d00000b450340306 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 61121226 1250 61119976 61120001
    0x504030207230909030a090803031e061207030c0f06020a0309180b090910050603010c0903150603081201140405010509010b090303070203030d0c080a060f1814150a0605030c0d 77
    0x100c40e40384450f460314103050303115281150140d0b0f503440c4110406020003a01d0742021085500500800401c15001039070203424043d05520910305a0791000003860590400141988034014201c000041001c445041015200318002001455807140d0003203a9a042c494070140006411039000c005070000300d008085070311111640400d01c81000390110710103810559150343d85500010740c0030b0030f00f520352080a4000c80210000e11a109402034000d0400311079000207482c1c4105421880203104095003c50001c50740000740e00d44500e0310308501003906900344502070720308860146032141071400d0312079181a1940140030a60503404c0000c507520a4000d05c0d40341360144010800740c0b016990800140450100c10500400c024030030050042c80d5540c09440921058144281030042c444109860001d956045e20407450705840d04080c50058031082d04800102c0500b0f00034441c50800e4070b65106054202a0b400c2c00c68203070b82e40412207040c401101c1c0114500300501020014021980114450408 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 61122476 1250 61121226 61121279
    0x303070e0f0d24020f0403030f1205010806010314151803040f0806011d04050c01080a090204150524162f03120a36030302060a0e010504030207 63
    0x800101182c981d081c1c048050340c11000e83c04200c04800c407401d800f80f0304114159410350510041079826440d0f8011400000c052000c2941c000c51800c1c41440740038066031480c401070096594407140507441b00000c0c0000c0e035980c0b103011000c000c9418001007070010f45c03618618500c1180d5800b04410300f040c3c1c0c9800315003520b01041000040c04034040ba2120041e0003410b02501007545032501040c1d8501140705580501d1444030100000700c2c00200c1c0940402c1d0b801e0034403910f203030f880032412401841007101c002e62251070582c07008150954902c9080540b0340503504090035440001001030031040f40c99102100e11400c03c000c1c1480d0100798049200c45219407004185480c02103000ca001a440301c009407024a10041030030a04c0c41e00700190030020300c48110b10383c940b45400358002d0058204500c5050160b1010741d81442201c41410341002c00d000348c001070716005440e854000d450311000d603a02400c450034000404401c1c0810310505003d15416001004210b04d440b505403144001c101c8014204207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 61123726 1250 61122476 61122499
    0x20604051002010e2404030309020409080301060302070201030c1803020d0c0e0c0d0b09040f08031510020f010e12041815030303020d050f0c1803070302030a03030e0f06090303070e 79
    0x44629503141c1c9a90841e0b0004107107114400b1085150400c81c840c0e51048074000d0404811211600c8840c0380c226805207008142500d041c004034014002600d0b00801d441c01c000000210140d2640c003a180c0300b40300f42c3e01403040c516035807004c0f03a6004442d421421700d906825010401450450036489000d80710744441480321345d60304d000e0948103134212244803140c00300042100719910386218200131490f080b00d1f095104d041a8a03070f0041091b0308280208014030000210341400c03405410060a0680145840006c03420008001d441342a0074450040369801c16a240b00c0120010403e0180203030504030050510380703001010808000c00c000b05100081d0744250300880d03c0260501c80010314040e4a016036120700e4071030494202e9000500c554106101c0c9002e004010310610304441d044000c0582c0d1082458441000a04040301548000d5051150b11140010940c140d040982c071044518165001e4800048003e46c8601046030002c656400800014030380900441c2c00c10761500c030207003030403c012 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 61124976 1250 61123726 61123729
    0x603060d15141812040e040f050105070216080303061e010c0605010f0302010807030506010207090b0f19030c060f020a060504110306040b18030c0a0803040611030406020a02060f0603031602060405 86
    0x82da5800c100da1451403000d001c000042003000c2880703108100c288010a40401c1ca5107001e443e42c082e030300419250b45070130700104007840707080801503058580041c001c02c12400c125001039900d5428403509448101190350019002c1000f10981e441960090205801d40f030030b01d0609031003500b00c00420b9050068060418020031060700c07805004e007140f0a010803865080d40000360036001e004107500101820401000000e90340841c441080701e05250010071441e010700c00140143d0030b24544190015001c0355407003a03800c0d140c141c2604030303400351655260032900c0310f0048640500603a01800540d0200035040b00041084d8884e5034440d010700071011000142c000083e06044065600b41c030f0401c1d136001449101c0e071090600780e165298800041d441c01d2210001d0319112100c1601c00341c030301480800018288407041d00311621035900000e1617903891509142c80c400079041640502e00520071400000c24802c0840b04407030080200400460030401d1480403801107000360b0768200c3e0800340a000006a0703 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 61126226 1250 61124976 61124981
    0x14031e090a02011404030201020a020d06020d020a120b0301060e010b2d030403110f210f0a05071a0c09040f06091a0301050c07030c0b10050303040909050118020603060d15 75
    0x103004804040c010040715800010149008a1044584480300b0401000140e03000130302d4811003035050360f0b500442a03441c10120700901519111404d007500000c1d5054213968803000e48200d01c22400000c0017074881c4031040c18205e904501030100038000100040c07100500034400390a05a01070341031801c02d43d06800c88640501c800008000110f0b80100c24002099001122100c030020411300038034010710380c00016a0b54603003035605120000c00300e40340810800c080300211b8a005003070b100055955854a140246154071201c01a1580180b16081904c000f80e0301214034007408e011103410f03040000010400c0010038050401a1050340d6400001a403003000b8000e01125500010b28002c40310420b2092501b9210700038801c24030a0410030404000070b4002c80503800481d005400055a955400c1140d60002501d401071a0b15200c08680000d14400c1c0350006103025100b032000703002c2c3c0719805000042920f954840258004414030001b8014240001e00c400c08034058032540342d108182c101a4000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 61127476 1250 61126226 61126231
    0x3130615060c0b0a110f09032805060a05100501050a02030d0f06090f020403050307030804020102251d06010c020105030a0f02120a0e030307090909170a0905010e040c14031e 76
    0x403901c08060b0740c0520009001c0705501100301c1c0401d20042e01101c00c0d582e804d11403090318010740b0b0b8011511840c070341c4041092201841c4904100c103080300c83e80410000710711b00c40301e00b107581b44245c000042c56040140540b03405a40424040928241494015600d40e008a148141140300501580c0c0e888000e034003944000c652038401c0001e90310304181c503484c15680131800320703011103004000410011b40c000003101c003555014500305401d902c40c3e00c0100c1c204080107614100d02300c00c4c10001d218000c4004004400c81d02070b02c000f001010341d5031414011846045070010f000c141041305840165006800a5600c000032807800107450b02d1240d1500d00f260819940b4500c030024020800c12101024810310007140010700080d0705600d000c14004207000594040c017440d103a201c015030703c2001200400618407100c01241a85c41e182d1505000b030207034401e4407070b56002a07015443e407100781c1001e101d9040380741c10300d6541c1100c0c400e00302c03003403103c541c00a044040004030502c1c80c0c04501074030000050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 61128726 1250 61127476 61127489
    0x1207150c0e010207060c03080109110403080c0303150103060501050d050a0b030a1a01060c08070f081204060b010e010509030d03021818010e06010801050f0f030f06070e030f070b03130615 82
    0x32001c0c0c050300009140c0107a5803c1801400032908490b03002c641c01a0803503044481180d0003203040d0449c41c00400075405940c6c070041200d5004135070241400804409544900346103440010403a030010011410f865031485602d021450800841c0c000d0005600501d610a00c070a5000c6810340140700820320303103405038006407041c500400828810041480506004018524140080c1c19403a2681e034600d1250f0301c4000c0c10005051000c00810030810700355101c84003c50418010751829042c8000500900c03a03a090001321052000c1d4065809002a9600410040e0051601d145518002e074000e500940d00d410b201a4452001000d40c2c0d04d5400e8a8002e605091060401e0b5142c0080311200e80b030040d080506100c60b88005001036141d000600949410031030702010050550b0f00841c0c180035111010075603e0040c0001c00407070355003244107440c42d000c0c1582180e03800503640d070f80981c0390307900c45c0280321050070b0405c0400c40009050700003101c924054a40080e130107850002e60090101a40c0c0040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 61129976 1250 61128726 61128737
    0x61c150f0509090102030106020d0c050a02100302030105130e0303151801060c0c12122111030106020d03090206030429010602060a0c17040210030b040203180d111207150c 75
    0x1d1250b030820305242c07034201541d50000c1d8199410310102948500300c1d90051400c1000c103c4080046c02000c000c0303409002c0d0050302d050055182004010080e600901806008040e42200d60600e01c041d48103a401120900000c0d60850f120340142c4221a210b0350082c9038000b5001d5211aa110590750350a4000c1c1211b80f40c000103203500c1c0c50b105c00085426403004008200410080f000b04030302c400540c980b40900d151220b4540d8a403866242d100500c40c49072109140350100f0b0516400740d43c13001b141070f1200340c2c0031296280c5404008074180c0c0c60b01d0100a4010405001150006158884c05058011450440c80d481000d400c4000c0b601c200c26030199005a201e0701c10b1100c4500e83e4030030f0401c03200c0c441c5801985412245032841c40e030400508028001d2035070702d03101e8050381c3c0300f07500010015000600555072030a25443e9810407481404d880440d078010a2401030402d03014410001c0e1015455000e050301035040140c140380e83d000280c040d00c0401c140e548800c6203092600c9001c1036545140c40d103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 61131226 1250 61129976 61129979
    0x60a140d272027090c01020703080703140c06040f03030b0a0b0d0c031b0309060b0f09070f030609020409020c0c0108061507050c0d03030e060f100e060301020f0c07061409061c150f 79
    0x501d15103240085c1d018195006403405001240b421030884112030f425051410b5545102c401c0d0300b160381705021081c0c955010300c10610081110200f00024039a000390382c14400b06805404010403041c5612a0b00e4506030100480b440844507904660988501385c2400901c05016819107500a16a400030000107580c50f6240c50811060384901903900100b558203030000104040443c050344070143c61031060156440103918079034840e80084001e040924008c0d0749465841183d08080e40152410800a010780e4107034840a5100d845020301c11580288940e0030402c441c64104190361114405940b5401603d550900e0f41d00c5d840c1214954600caa5400141c4c1a034441d0740a0401e10042d0003c0107840412044c802c640c81c0352020402560f0180d085a5601d841d00e50000f0700a02c95001c404014080101d03048580b48404030701403086441c1500c92a420060007041401c3e18407071000c03440e078000030030710403004074180d0490100b49500030144009181000b4a240c0020030402c0d0b40075410f0503c40280 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 61132476 1250 61131226 61131241
    0xc0c06010b0306090c0d110a020f0c030109020d0f11361510090f030503030708101d0c0714030a0e03060402030c060a140d272027 57
    0x4460040540440060940c244500004e03581080a004880744410108880001e403000d0381c0716904281803121169a14000f001c0065120302030005c1220b101c2c0601e6060146908041c000d600e40d031070b80140480c9154500c3d60741c00e030f03072a6450801518269105017608505807645c40111000d80701000850a51401d80303a0021004481c10702402880801c000510540006100151546030002c5551251a035500002211000c2096104003200f141c20340000040c400c000c0015030084c1801d640f00d01059498442e00083c100807072040314404500f000034141702c0c2812160403500040c8803002149003000689960110f01c54020404032950800a00c9a4610b50003403c1c940003420700303a01503c8289810380010b6102c513090b00380d075800b4100001c2d60824891045012281810801582035124002a8007920092a0841c0410601003141d0310482c2d1100040b0520b020850f4411ba10a050703890942c0400c00c40441e00c849960003050125610a241e180031003804d01c240c04103000c1d4640d03440c0a26 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 61133726 1250 61132476 61132483
    0x180703060b120c0109210602120901050c04030503040605130512010f0f0b0a03080f0f13060f051c150f0e040b01090605090f04030512040b09070b270a0503060c0c 71
    0x10381c080b029030300c800070128999170010840c004840504040404402e50585401061a280d0400400c010b1000230144e10750b80184460a004140ca035008201070b5560098403051032040d8040902650f00034041000918856002400702c3c0039000c401244243c0e036080820180c10202154101c50394641854a07080d614501c01d00e0310400c0e95201c14415a074036100480e044c2003e0b40405082c0a6001070030304441c9522500300c594026114025644c1c0da08030580362a40c2d0795440c012000080d14582103000118865414bd0700c28001d810380e48429139101094010081401c403e00403c0c1582802c00000c0c020b400010f40d40042158002d90782d6145054645640c0c080416040619198584001440300b43c45051445510803e11b480c00002c2d5200c03400d0699141c000c003454104450302e03080c03c0008109071420000d0051100b00c0440b029191500228081d0307000701c40501135140d1192512141c2586240107640815102401c1d15568a481c1d10100e420040120390600003038400041020402c101003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 61134976 1250 61133726 61133749
    0x10b0402030c070f0206041a040f0e060a050d0317010902090102070803190c030e0916021b010f0f050c0706080103030f020303010503031b0102090307080d03060f030b06010305180703060b 82
    0x884045140d45030200c0d000740b8a001e0000302401c8039100c44031042c11500c417002100c01401c40782c90b04504041c21001000c219070310078011811b4141224100046400102e520300740100d1004000326011418030003881505a2204c105038104158070100940305403044407880d02901c1030b070401694840c0e020001a1414505a00c54001c5500400020b9204100e80039420700c40d00315403030103440c1110741d82000c9400e01005600290701810580070b104041c40201c020000b401c60640947d110102a07201d10300380b030380442c078010b404918880c0305d90380d800744100d5004080c0c0580e41846420441d10b0092285031000c241c2080021440754001403081c590800c0101c4040702d000c0c80158503560500d40840d440380100180680d00b0380440c03050704012002901512222200902151040c580d1584419a80c1c8401d201240c0400c4c900070020981c1620000c6400640743c03c401c001443d030702e0b4900110003d01005205c400009511034a2204401050104000440c010389000c038141144204010511009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 61136226 1250 61134976 61134979
    0x501090b09010f15151419030516030207230a140c090c030408040b070c050303030907091503030806090702250608010e13021002010b04020d050f0901050103021e010215070c05010b 79
    0x1198000c100541e28842100740b8256140717009038090142008041d19070151f8100f80c64000c482c0c0100c0b52a40e6455408180301e090024030301e140d01c1b462007009804034030035032802405809032500440706181c4848030011081a054049410094160b1203034003030140b441181d608943c102c0381c61010303d444c00c411031541061000300100c0c907604003581d8241c1240316612400e4048040411420103114404118800034040038094a55910340301c0c8000d40c560145010f0481e01506d000c200c03000510211400905582d45615540c5042d11480c0400840d1030000b4418409c40c4501d12018400702805001641e10f4011001000b107550300f8a4009841e2207016045012100260070410002085004841180e542c055614580000350b440c0128050301080640540083c0005925610007006502480c03140010717909000e016219000050309a82c420b1101a601201841d0040030f054100c290880d80c080c0140106e80e00452000741032200c000c4203d82c1040414020143c0c0024050280918040c4480 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 61137476 1250 61136226 61136261
    0x90216110f03071202060f03070f140910030203041407060c030f030c090b03090a05060907031b06020607081003020409060c0e030109030f03020c0f010213080d020601051302070501090b09010f 84
    0x240d0001c60703540e149512421040e00d441e0303041c3d1300c1951a007004840e07003041030f0920715941e4545100058900c440300030500300005c200b904003540c0710081e01e05035048007000504580f140000210304801a4101034010ba5001e0103221000e26a6076080010000424032612a407001040c40c1c00c02802c00d090303014902c024103042204d2a032140342c0c00f4000300181c440c10941c16842e5202c041d83e031440e03c651018004c245103d45014088038440004400049a11648066400011301c0642400c2440107114038005a405900420107050091035071640c0304101403008201641d4940005054520366103040e140c90303980d5030f403e03003401b5484804900740201c182c4c02400b159040d903800420b01280c581140d002c055001c2600c080000c1c0a000740d403a507840b460002c0d034940700c4007104040801c03424403e80b0091300c140b41a0019003800860500e0413907400a058440384075000c1c000b20b0103540410f004a49556881072418002044852040c0c0030750030038800003a01c1d620420074101101d0108500d40c1d074240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 61138726 1250 61137476 61137499
    0xb07080c0f041701021201091d0f07050f0d05060406060614030f06040e0118050f070e010b040311150d0e01050a0b1309050f150403030b0603010513050601020709021611 74
    0xd181e8012501120260203140b554a00540401402805402d986110081c11440000380d40030160700013080c82c0c00d480440c0e1450a0182d030b101640c0e55405040c20009412074013003004240b601e0340c0361f2040340c14050606a810b04071540d42c6801c4c85404c8601b2103160b507940303c00388031456008200074500020129042c0c91400c000c00e026400013401060719110b1a11002a00c1c9859020740200008058038540c0f02c420a101d4500b190720764003d40300303c0c0030900c100300c8005030b038192243ca5141224203e0084510305415911990741c0c0c4110105d0807130300021140a9011001d42d130200422000e08540c10001c1d00483c10b1594600b555000703042074101904008180b20340d50f41e03404131500c10440c5510001a010403500d401400c015510140d01e489009942138142c8200c0080002c0c1e1286110390b408110b481503400401c40d031804280903250700011214a000700e040304650040e81c204405004465465070740340c000c002a640000403440c40c441044a40504015003221800288102103c42d1039610 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 61139976 1250 61138726 61138747
    0xa06020312040611040602010605100504030b07081b0309031317030a0c17040b0703020d02061509070e09090102040315092109080d09061805010210150504090b07080c 73
    0x2401103401c444444408000401d0030860f0684c028844680d1007852203840c0c41e41ca5001900074440c40c407a41d400348107140700c00460340d0b2269048900307599012500d0a402c0e00c1d51078088460b07140040c420403800183d0980c421074004404065131080c800440190f9483c10588000380300002d6039407103200e007049410000805008084151404650549004400c401803820f0543c403011a40c2c85c4030481c2040060041240300c1502c0003420785502079000c4030040281c0c868100d03502c1740100c2d20041c2c2e54203111003c0c00d0720700d003010105810030f40900d8050004640d840005910b00c0056840d0b10060303500140400c10080707003400b40e480c000841e000401025049031031b070104030b9580c0280e12100b002c100000d480d159000d2203d200c060244601100c0f1f0380c91a250000d0300c80f8801d80110400b0401e01c0c101e00501403110070b103000564070181c1c0a094200c042c10b001c0341c0581190900507000c6030b0249004036954690b4402e01c1c1005002d800c0d084031500f400b00002d400500050b0581a10810400c1011102d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 61141226 1250 61139976 61139983
    0x1202100c120c050d02040306090309140f01081f0b0306011d130b010c050709090b0c0732191a0405030702010e040f09110102010b040b01020601031101140d06140a0602 73
    0x841e5600c250114403044a0403084403a03100720078038880031500c0407501206018065000b495414426152041013581318100c01081000f07400030340da40100d071600d03e2500b5500c01c0140c02e8000c1070f00c50b0200c501d2401840100d9100b08250441d00703000c1c0000c01002a44d6030b2100310004180d10074680030000340c544002203007100034035941586195482c2e103607114259200b180f540701c2542d0401c040d5600c4c01d803240c2e580006010003030426a5859541004030314a0381c04102100c2c422940501070000d52010006803031f00c0501c680d2492040c1d80f07442804403071900010300800300f408900f17202000f0b000701c03a49232407448070005400800b9001104000c1100040000080f10300c4590242070509070076001c0e1000030090003900c50394500660134802c018080012080d6410f14002098000303201c441d00c1e10381407004650070052028016800b080040010490112440799041c4062500f1f0031900c0e00f2507502180c540c01001001c0c107880c0d0702d00c3c003000108080d80c0f4040404000712840711000d882e000e40290b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 61142476 1250 61141226 61141247
    0x150e04020904020a0803030a060f05040204080a030e03070801060e0906070e03031e09120102090406060503060a050402070c1e0e090309090a022206020c131103040f06020c06041202100c 81
    0x241c444500420b056680740c8914100a16150044a68a280500004001c0d09680c420400a456200008039152510340241e40640b10310800a2101d082d16442c01c60b00c1c000344840030b5402d401000004034600e44e00f030080b1009170450202c80512424440c172903900d4020014410010000100980d8103103590100c125821500140151109481500694485803142844040d48046052840c5200e098103401030010ba0f4401c4408120f002d03079900c0d0540301d920048900300c4c2d00c1030103618280200d00c2c0030745c0604081c50081c0c054003001911004081784402100c404481c00001541e0b0030800c0d003000c041920388c00740540b006141030210350f00104140c034002402c0f0f00300403034002c41c151910900403003d4821a0341c40b0b103c05481c0d80d50702da8001e52120311801e01c440c01713401c600000074110700040c02240305103044640c00502d1641c450f22070b40070b640303054030007120b505408001c11003a0b44420081075016900420718422031070405000a460400000e84428543d805d19500c6940241c101100b0321 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 61143726 1250 61142476 61142479
    0x91115041e1a0a052106030618060c13050402070305030906010b0403050c062101030303051b030103051e070b0304060506010f030b1e150c03030115050c03040911040902120901150e0402 81
    0x10f840c1e100002c4165028055005643e8220202c01d44186840c0000100d01d40109003d400740d035080d803035210f9445c0c541415400c0c5220a9404400498100c001d20130062405500d40000e094003641c507480054103a81c0400030640000da80070003408142e8000f03100150041c0f1146c5529407a05196545194650742c01c820454403490000c2010b10007400c41c10819080081c00340f03511201580c6901d0080d000748403e503025144500301c0d144002069241208403030681c0e40200042c0300844402c2d0070340150a07101080840d0764000e44070001501c5a00d02d02a5006d03078402c0c440460145001400108039440940c002c500305400d180c266805a22030340c9241130b10000c1d030300b601004011007078003150740003500d049a01c4031024001021500400007101035810388114401d004a840f83d480740884480c001c003400305015400401040120003810b42c044000c1d100640001800d26a03204108c1e802c0341c0001304e981170350110202c00c11031609420300c2880b070716514498280c1402400d08501050305000100000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 61144976 1250 61143726 61143779
    0x30c02040b120604060f0501080f030d09080405090c120f040f1205091302090a05060304021012060506160201080105011803020f060702120714010207031203091115041e 74
    0x35001925506041110b108204040300d10a0070149003000042c00d40c2c40302d400307410b1324180003c64a0f807004982014201e40c000c0046041905004109006000c00300003103c641c8402c000004864a50f800039a2040190580340c54555080d414000445c0d200240041d5407503a6440402001a917550045a003950b0171500741000f08056040584841c410752401503070154030545031412807440c039001400c4540055030f01105441e40d030010700900d800701303860081d48001d00d00040310f09184140004c001c00e50400002241c0e05582d0b0003c6041503210300c8995941c900e520f0b07064015944c00451150040100380307017190080d501d035004100365207640d000080c8a000d4942c45104256100c1050f03803d40c1c2e4008045e00e03407000794003005954844440c0f1078148140c4028012521960011960302c088039000380c00404040c5402c1c0e0120300a1502c0c150494030701c2d812180340440d030348502181e19040820b402c0500e95681c141080095000342180c50030b030201c6003c180a1250a01d028100c501451000105e03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 61146226 1250 61144976 61144991
    0x907050c0a05070b04090605030102070302060606030a0b150415020c0a09020c0a08030c07172109030c010507030b011407080906070213020304050a03080f09060c0307210606020712030c0204 83
    0x409041507095503014201e840303030400c04640380076118003c000b240d1100d00304005080e981d1091500b82d005003600580540c000900141180c00c0a200071544014802c400107003100d450030014128803001003004000b03031030202d414403900c3d44510394070004146500090030140e01590000341f45000c140940b841d4142c006c2441c5040c0032082040b102400d0740721030b41c00d489281280040c20301782c100c1c4405550352105070707045004c048500d8045450400000b103034103803090500da541c601e203080090120106c0c2d110800c0152030101081c450340740070b103c41d51340105424840c40b000500d250f407044a82d42075214100050000901007104a071400750040d91070303689600403800042d1204c0082c000012030345000104000401001165010b12140320f41c5a015241d282d99550303110103c0c0072034612506501080108001501c54005554072854526149850326484071440c0c80c0c5012902e40e501d82c1e6a02d80d034040c0219501845403102070704031741e90311041c0102d0948006001699401d4042d0055944001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 61147476 1250 61146226 61146247
    0x181b0f090402041e0b0a0e06030c070609060506100905031f09020307080622080307030509100603030201050f0f07090b03041e0b0718050612060a080a0c150905090705 73
    0x58800e81100104115100c59441044c24810320310b52420000a40181c00e000c1a04016002910602a442d641e0b4003001160001440740307039480507004940f07228043c400c04000a45034090312003640c0c883c603008502ca06204046c0103101c59009072070014050150780c14402920002060f42c00ba10503140e500d1183c5002030010401058003080294050042d082c0101c2c46510010b0405e01035864480f0507080182011036001405401c40c900401042c02000811000c9200740c2009410140da1416149800811500c5400b10b64080c0c2c011070141c3d44403400c00c2030090b10130708803582c071040c1900c0040142c50018801000c4954500441300c1d507039000300c0882c041c48048000400302a9060100500b01d0f001c07410004184007049800303200060f41c00c61043c40138504110088120340c0d001d80f1043c102032520800418031440140503640203010100c00142e000d00400c40c003101d2034001c0c9a48207080f424500c069079181c4030104190700740440e50004001e40e403942c8a5059001d41a072514a03100d810740d09 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 61148726 1250 61147476 61147507
    0x41103331806090f06070806010509040e070e01090c0e04050411010c050c090c0c1905070603230106031e05070c030c06020705070f090b0301140105040b0a0906080a02181b 75
    0x2141103045102e280c04110480e400040d0101484816070101d810316951014101c03003003130b02294200d00280c02404900702604240d00560510034031803040da1104d039181c44428803480400d178800b2032031940303c1c0103980b06180c2100c546414001d040e0703000e1109141a49070081902100d000c42c504000403e440b00080c04400d1001c0b480c81c0030001c02610480c100030340c00c0c004940008c43c80e40712901441203c4100c51150165a0514a17400b1026012492510000f40c008110101c42e5080162100310100406410504001d000e008240c400050344000088c44a44d5080700302c4034400c406280c102800b18854003d500c1d1b1103a5a0b242c03a144031600020703e000c0c0080c0c0038840c0c004003030744281d1340d001c100c0c1040c681091040e10000c0030100720390b04c207e900309420385030740040c01120411900014080d034207054204a480c400d000d480c90001c0382d618490b110446030349500c0120140c01c651044011890102d80d0180f03c2102c1000020542c180300d07250104510741800803041200d0001a042c0b1070780d4964 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 61149976 1250 61148726 61148761
    0x6060301050d080409090b0105011d0108010e07020705181b0f070807020d050a050714030102040605030a0b12120d0b090609060f0103061e030506070206090307060b0301020405040504110333 83
    0x14800e2040c407165241030380b420741f000c1c0205408100b4544030034050101015508000c1310b0169903030412a46407601611214401612090842c001c03400c0114594507208540c1c1c1988051403c20001403901c10380d207152501802d01e480d21803100410624007000510f10948441c1c98200354611303500c51081c03000803e840c41592008080c0c0c05140c00543c117011001c1101e5044580b00c3c031010b08103a192000305801c030b204a00542e00817a0051000c10f680c0b1190f540608500715001d0807000f00140d000c2d000030728011144820045111001407036115040e03080c05501e0069100f80e0390038880c1c3c00d0500004404400c0106018020456408988542da110b900128010503441030440044003841050000d91001d5010031f541c00c2c0f0a4001040a00e031001130340358440c08144001e54144551651030303038090803c4003861541503400f8000072419036194468680114418000800c2d00d04424007410305041d080312040012000750690045040400c601001e00070308601d0103401240d0302c441e1a82d9001c0e002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 61151082 1106 61149976 61149989
    0x9150f090d02030f180d0605190e03070305070305160b0703020a1107030b16140d06032006030601030207050a120206062d01050a1e020d0906030506060301050d0804 72
    0x103443e6101100d40c070081c8902001982911240306440040d190591122109004081090142d1064809120001000cbc5041c104103440c003a200d402003540c05170500600050303150610f5a520000510154841610b0169041100c80200250040c0300340c070010603580341c11a0704c4600300007079070030449602c03000741085030717542030b0740302880c00d41000c3e103130050200d031070814590300918501824409070041c1c2d00158003880c4d804c0c240c03110f000780000c2c040751981160812100f40c48400850754000300030300300980d03074142e03038076040d4982030029401070032545400004000c8a5400b0429500414048803249080d68808940b55440200750302072810801b800c0c44400019406003014050402c00c5003801e0501501840044640030749503920f800040e04082170000d01240c0240aa801811840c03408201c50b1070028041050380c031040c02407600c84c84002086d48100185081143c000c0c011 = true := by decide +kernel

theorem cover : BRFrame.Cov 60971226 61151082 := by
  have h0 := BRFrame.cov_init 60971226
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60971226 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 60971226 ≤ n) (h2 : n < 61151082) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
