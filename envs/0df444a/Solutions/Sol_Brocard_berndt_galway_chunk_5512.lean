-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5512
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:06:34.353589+00:00
-- url     : https://prove2.me/submissions/ede3729d-38c6-448b-8604-0029778adeb8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 991187050 ≤ n < 991366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 991188300 1250 991187050 991187053
    0x150d05280c0308130504180213060504020c0c0f0a030b15060f0a0206040309151218081b011505030a1b0503103c0509070b0a0206180d050403060e0f 65
    0x81c000240156a00034140702e240c0303001800046a6140200004d0322031001103249225101400c079401880e040c418005040c83d484030125200f41d0b0f91000034200e8001002410044d00310500b1420320b03181801c298807255008a4203201e0940c10f40c1c0360110300031002008851080701210010400e642d03000706440681d143d0114441d6208824503000b07444207019642100802e54401d0080382500711080b0448840c0d82c565107021441400c406000082e000c1e428400301804034412024002c01c0312640103107032601d494800d0740c0c0b400019420050071559039000381d0341e02d010456014040303950081100c00405411a801031004405110300f04016112540a02d500d44103446c00091034074013540041062980b0350309072480701c000c1410100600900b0203030101e0701c1d82e003041e08460f0449032580525002501c000845285503101d1032201c0b1294420402c0d0009a4441003c0011b40001894241c1240b40490094048260f44d860041e20501443c003000b42043d03207a19000300c4800703003002042d0301c40b1151030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 991189550 1250 991188300 991188323
    0x12130222090c080106180209061e18040c0e100e04061805100f030305130f0e180a17070515010905040c0f030201050f0d020d06030605150d0528 63
    0x140440001e01950a044074408201000007600034010320400c400c540741c0000d604c18080801510b24001d620403602190301c0a4103120f44194541110189010401101a0190fa030b071005103a00c05400094984984101c0c01c0459181100f540b106402801c20015a000440c00720f40c46801c1d22215050745800340c200c1c0c0351480004001c406d1002c00001c03100c100030304020984038115580c1e60750110f80140300702100b0300d40f810000248103c006207001c1243c001d01000c1141c80b80f0040340a86c03e035070701281404001400b4807181c0c0921240c001c6410034051f004051640059545565480c1c0d51852000920004268481840010301501140000c1c0340c2c10022290317100c00340c01c00104419a03003598081540c800101e04410201d91034000d4a4050311441d050912500e070310000ca9121a0040ba4082c0d0284504200b034003031341c0241000395100f12008141d0f444c021855500000c0c0c00102c0d580b1039220054840049103001c070786404070b0743c03410b41712000003800c08026001001c0740399802007680c017858 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 991190800 1250 991189550 991189609
    0xa030803130b04210e030a0f030c0b010b07060e1c140d09140601080a11040f020f0c0f1c08010504050901020906070501050f0c04080318030c0d0b041205121302 70
    0x843c90b1001036160b00f101320000e001c9880111003240300d0226158160707016640903404580780e22011001d1038401e282c02d8110241e1603807010401c150a82c840030880788003142c5c0b0f00030000140174860b9014451801400c51580382a803000c1007080c0800f64405100001410500e40701250301110800780e0140401d1044c0302a5103000415082c0126075101e180c0074010001c12541030224621031501e420100901a0410400c1044001e00d00c8a0139442e45540c2007040480f810901e5015140c050b5880c006040000100045d840c02c221402002d016001e17071044101040b15000141607040d200b080d81c0000382a6180ca8840340203110740700400d81e001802003060000c01205410492154031a41c40c00b580a45900300c00000c2ea0080b4003a4502c641c0060000072075040c10140c0c8450810300082c2100c080102020101c1c2451540c540700340e80900640080105001d941007403011601d4035460828585001107207181000d02c00900f0f00d034086800c24440105660b12001a149444004c020940b00745910 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 991192050 1250 991190800 991190813
    0x301020a1d030307021302030901150611070602030307120908070501052703030f06060a030b13060f1208040611071d07030c020a0803150619030606021b0a030803130b04 74
    0x4480031000404084201d2a503003004000d8510155000d0010280e1300e1a1110f5180a900014000407480d075880314980c0001203034959040c024140342d1118084440e80c818064105213103500076505545c420414000215402024403001e0309060400003004011485e16105030310071340c080500b25608100c240480c0400c04524101107031003580d4103440c1b02000d280719946a02003252560a203095441c001031250600c20000c00c00354155140c0082d07010130100008401c080b0000070010a10b6803010306100029903950b0300303006012090480058000560b03100f0106e80b00383c1c000c950400500350540803c811003001b0704c40c0078000c02c5061304001081e40900340c2d4103c01c00c803040c7c0d0001e42040000303103d960021500c8034845411103601803541c0d42d6040c0b01c01c0554200e103801500b101c0d0800c441c07803800d40030001c02c407001c0c0b510b503402241c442c0c582500240303000c5003080b00b041c2140700c003545000b01d03680b219501012a68010705003501ca50756020710801400c91580007912003800603040208110381c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 991193300 1250 991192050 991192067
    0xd0c030b0a061e060c030305045706051e0c0a120e09010b2a03070c06110d031503140609010c0c081c09050723010302071a060402090301020a 62
    0x1d26502d101c0d000901103c07514401c0c0c102e40318183c04901038150703401c0801d1080d00300e04d9005024220840d00c00b00c10060707d0345928000c20600d00005413403070a0041d80c0a2514103014a9000b004900c403644000d00203100400f5001e104007410f00100003a100b074010320301a81d1045110300041001c0c0c0341c660001c144c0e0b494000c2c4000c2107420303c04429808000a0149200400707540303014003014156820032038802c1303641e44603030401c61801c8500400090b40007a0140e04140c1c200c200701c047c648940403480c0101c80a241034200106220f0304050080f02c2c0d681c0040d00c0c14007100e0500d000300c0c00411101400360302d90300d03a4001400c2c050001806e40402000050114041c903481802040000805801200c0d541a0350710700500c504006c010f0000b1000b005400700c0e100000c1204e0000310903c41e13a90342c03440d0000700e038018141c6412806030340c4241c40c0c0a44001e000d501e03082c01d0543c0b07400940e075103041108031100f040390511808940031a01c180c8981d415601e030401c015008555400305000d01030152038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 991194550 1250 991193300 991193309
    0xc0c100c0b1e04030e030102190c0c0501020606132a110d0509060f070519051b030c0f01030c210e0613082a0102040b07030e010801060801050d0c030b0a06 68
    0xa428089212601c41d64010072524408030b0070303508607848607a011035040b042000e4040d0305640900014080c0c405001c0c40c040060417a407180518041a8904039400c004250b0080341503400241c1005000d455042548d40303199840340340056031441d080d000040e00030010790446086c1d003081c80e0202c10642c1241038035403d80c0c0c0000890f155001c822100305e45501c5190030088c0c01c24030034410f00c1d00c643d0803d800b81203004c1c0302ea4113403000140740d1300300c640c80c00d24520401c0c0c03800e5001488003040e110076402c1300120101c003600600300f4280301c01c2c04245080c1e4a254076a041566030381c0c00401d981e20450303c021980c581c28010440309240040c00c040a890590404107260281202103003440c40302c00218100640d00031007481c03d0003441c60010000400c0411004251050620078005503402880100040d200c02c00c102d0380c030303030b03c3c07a0070020800c000c5c8012681c1405031410050000540040025044500031108801090f403d843c084040c95840d03400101610310402c203020030390805070000008c2d00d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 991195800 1250 991194550 991194563
    0x81321051e071214030a02070312020d1e0314090c01030c08040f0803100f18050708040203060a0e12130614030132091504110f0409020c0c100c 63
    0xc4101c4400301211003100ca003030710060b601c04441040818401d02841011070b00074103507103101c0d030110340a050865000b1300c041381c01a00015000e200b044100c7c900f0380b00c8805188010564940d40d084003500c0c01d003c5180c40e87c9546d90303006113402500c0c403981107000d404120500c1c4002905001000a545048148043e0702180c00c15100001d21442943c07114455a08007c1c440342568007610307800703002d9101404100c0880c2c603221012542e022604448030003090000b0001c4041e51a44800c801100d41c05003c100401000c4401d1202580c0c0000b51036130018030140300041c5181c00128030500c0c0030204c148030317912480007145031030041d0f107010005800c41d541a01c0c2c5070403030303d10030050144600c4240100d030400d00300090440001c10081e641c280024a0107080e13140c01040140005a02ca40211080300814455903102d080500b81401045181c0b59500c50590501f0302c0302c0b0780002d2a01032800b9004001c0d0303010448151011040281484002d00544540803010b05240700a208561064050703812 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 991197050 1250 991195800 991195813
    0x80312040201030b0402070818040f090b0604020a09080f0601140f030a020f0f0a0807051e060a2f03031006020f07050603060d06020a05030406051005010c030e0a031b050102150405070308132105 85
    0x40bc031038001c1c030840b954032140c0354525503261400c101c000c0d0070a4840c5010407403c91000315544c02c042000340072124151004200c0343d1f00d040d186031307521003d01c07032018040d0995004140060310001001d0105950450321403181ca12800d01260b00000e400321001d0384408440c0b400100c00002003581026540161844000902c42c0040106c2c00608250300b60340000b81081034410703452003000e1007001401a0301c141c40d0800941100c1010108070b40d105284650400410300c01070740e0030381c00440010040d0740050b213950350080310310544514003440342d10302801c40040010480e594004688984603400302e0b0031511000b010790700800e01d800032101114030303070f14040205907540d00b05020b810840e4230596490420602d41d44d0216001e1181c6603810f03030802e0f20540c0c003200045081070034030080400840d42103200e500d814002440c2800c0c804c4e50f4010081c601090001054000c100700301604d420800b5103070344541c01e00902803050010b510a054041c0fa00d40c0c0380c140c0800050342003900c580100202d031031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 991198300 1250 991197050 991197071
    0x310051215040f08040302030d12050702070e0c09120a120206070c0b01095010050607140303070302090f0906090403081e041407080312040201030b040207081804 71
    0x9a800816100781d0000072103000080020340d41c3d4810b81021413003040198142130b5240d01083c86c2040c6100c111000c6040c11903480e40340c903040c1c414564080307605e10003456540d00c1d2403000c3c40b12000c09403840080f501c00003000d0040361070b010340c10302c242c20010048070b061075000d042c5491100030302d294080c01030040f00c0c01f0a0200d44945c00b100207258120710707a2411640b070149903000800041940b0500d4030040460440350b110102c0c01000c0300c0441000020301c51900040100c0310503071603040c0c00307803882e0240c0034041d441116208800035203900741c550304c0c3d980c201030034401c0d040603501802000601c40001040100e80e03264015180441e019a600610080704400b0050346d1101201c03415008080c040014021074070039035a05030880201052000c4045180400c800c242d801218191080b01e424039203c03210100402c0034100502805000c1c5060101d0000e540301f4024010b040a410184c48e9140c107241980c40e030f4111551254400740c0b8503a1900c840f042c030b101190056211900c103502c1c0545600c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 991199550 1250 991198300 991198303
    0x509071a0a1106090c011805120d2a0605070c0c030c0f060c03120510080a050622120e03120d050402010e0405010f061d040519060f0e1611010203100512 67
    0x303004480b40c402a140c5c0101311401100c11180c044284648400403407000a0b81d0f440342e0320786040c0441d10001902181c0c1002001500b82c8081d86c0d41280382a810008e000c600440915100901035403010300031800f604c7d0000101c400c1f520002020308210042c800001c100f003410400001180c0007040c80e07401c030956078032060b00c05491030300019002c034000350b1584401c10341d65480698400b80030034060349000e031900c000a16080882d030f4100e801d64407110a0088500c0d60385c150244002240032032241c0f682d01995110113114041d16102c050103c9919801c44596080c040d85103041514048240c40d03811400080c406458156010b0b400f1403440e20411007642494051181a01c013181c0e019403007180b8103031040b07450183c3d400d4451800e402030314084015640714090280156425848482c6618180c980c400032541c99501501da1242803500c104040400b440b406035102d0044c00e00460101140c41c0c06958503002040504015480001080023904188440074240d850554041044d8000d208125 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 991200800 1250 991199550 991199563
    0x506060306010e0f0601110111070c1a0a0c030215070c14010c02120919030503071707030c020103180f12020d030b060f0a11120423010807030509071a0a11 68
    0xe43d840c1e4460400a809071110621a540100c0185015511106891019421904034500d01070300d41c1c0b00091100203008012040034042c0803120003d4140e02e422000c003500d135120741c000b03110600c00d070101d06806050091084500c03001045004032550b142812006201c4074403084221003a110f08101201e0700d0005224034130015585030010000d60a840340008050f801c0f41070910383c0200b0f03110054000584c885190001140b0640045072112150300d0302c0e417170340c51701e21711541c00d041810302c280380109510410720740380740350207003400101000b01d01404541d0000c1101d0140020718003400480c03c01c62002d070300c8100c040040d42a1004038041c400c0450550782081440303588031000303100e41c5040442c84c0c0000e0490030f005040c00017200b0900c06005003407030120300d07100718000000704040018a00100442c00e2101c00303800f0705010444407100281c122207020b400c0c4010141d036000040c0e8551800c004100103018810000c4510703d40749e0300c86003040c1d441040c903400010040c0b1081ca240745000a0030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 991202050 1250 991200800 991200809
    0x612090d12150e1305100203060906012d0c060c020c12010b0a1403010608070f031502030403020a0303050a06080109150b030d0f0c030e120307060b09011d13020907020a050606030601 80
    0x582503043e2901202503500b43c0058101c5001a0452030840005442000301090f00c201481d40540c0740c2c98030104200703440400034819414000c3d04412645803031284d0740f07034100c7e20041d0f1022134240080a5001c640c0c015480c08002d00540c0781c032841d402655000a03107071050050403140752132012032100b180e500b0b83d0165007003142c20000142091200f01901c03d50b01817007800c00b600000d26a50b4030051940760401030740c003016400024070010306c140310201c1812001707815020410352550400785c1c1c000307585200d410700160400da03031807001c200e6124054001d000100100e00c0244455035617418081102c0c8240c0444104d06031604140010303d01740810342d10342c0c0c503071030740c48000a000b4814808e99481c105030400b201046018284101240d485004000711465040c4c0159114170341e03071608100302c6081700c1c1c01034824488040100180c00301ca00c008030085000c1c01f0301c103056484090601d510300480520084d4003507084020480b40550004203000698050b40c200d4040b42c4400c0141034443e00203024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 991203300 1250 991202050 991202081
    0x60f0b090a0e0c010e0d062a0f1d010909020408100b03070302032e05070c05300f0409050114150c0d050711220e1b0f0612090d12 57
    0x740f208035809400a0b8050800140c4841081c4041d075031003108842014079081840c0e00501103020500401c221040d50507101d904004800011242020309514841c540110048051140703041d65039201c2c0100e0300c0100b1200a00350b403501e44902800f034846071446800d074503603440c000c03d40380c3ca46000240c1d5000ca0350003074040c0c040d2440b4032424074000f070344100d2000400d03454001c0715003178602240f169911a01056032059841d0b019031a00d10300381010381218061515030081c0c0c00c066800c01405074a8280014079220740e41e4920b04076124201e0040351300901040d8540800050384400c01010f8410794202219000203680e82e5120f00f409601039005005074960104a00d580c0d85401400204000303401604210982c0c042c00340000e0301c041e0440c42802c40a061a2014100c0903203a0080c20105802100a0003401c010940c2c1010104c1500821a01c01c05401ea10009161105c1c02107801c00d04280b000141c0a00c0c10140681e6100c0c802390420001038207220700c44003025858403808c1d12150340800c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 991204550 1250 991203300 991203313
    0x1030b1e040209270f0604090c05211605030d0207140105250303140a1806020304062a090f0324111611030d0f030c0c060f0b090a0e 58
    0x801d1200a4011035807050304460041d4560f181614182c1009511340100a2410f01918014118000c0b41d180942018003450825250724001450b80d0211810754a0aa41c282d54004001030002d040408008140c1681c1c0540303291606120002c003590710580f8416000c48412103200001242c1da86032030702c54980ba03007111646d032141c2d5612803401043d155291903340c0b5001582504039581e8100707281000c03004030750b0301d455583c80044d400b200c1d15807200302c1c1e060800060305100c82000e018005000b00030000c0394004006403c05c4201e601c01454500c802840b062600006c0000d0034582d074a181c00700000c54a01a000948021004105410799a000a1061802d0310f29901d1407451713112036110442c7c0325190300009048901401c054020403029110485241885040805201c3e8000040324000d400c01f2203603a00851b00408001c2401d0000d02d00054102c07403d031822142009040740042046040c81000910101250002c0100040c112038046854640d040c0d004110303110000b40068981010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 991205800 1250 991204550 991204609
    0x10f051f0c0516080a1104060f0603111e0403030210051003020d050a02032d0c060a0f030e03120103110d02100f030204120b04030207140d06091406010806010501030b 73
    0x10010455014030a404940428000d41c22015540703d00b60002d081a6001c20700360814480301111240040b0001c1e02d04001280c1020292080c000c40c0780695018540c8400307000705000c0c020b108660562020350541141200c0032031150030546d01501c0160018451180b01e208103022500c221409000c02e00c10020b43c462456081c811001400141916140103103070745035015840a0007604208000c2008601c0c0121440b45005840603003c1c92300030255000c400303074400716261703d0226440164541009868011120800c50181149001071b2640f80404105881c26218003410103068a1003035061844408001062108190010202950114603100e0080c0598041c1018240c3c02115160141c903164490117004900740820f507003254060303000000c00041c141e041c0100d0340030709a2074490b9900503081a000800740010280082c100c02e56404407038041002c0022810900450342058992544c3d6130b41c0300c15140c400900c030b040e0100e4100215200c46280800607214040981580c01014a81c030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 991207050 1250 991205800 991205807
    0xa03080702010e0639030a150815090f1b0108070305042316080d02060c030f1501051605070f1502070b031b0c0f010f1407030506041503050105010f051f 67
    0x95107038a070403c0403d05c0044114038084a051480c40c0100c1e001d07035078034140340d1204c1007150503202c980a18405000e4052000042c045500340300640f656410040310385580e500c4a0a0003116400360308503100f110301032544908200c04250310341000b42c070b80b03143c1507071106025010303540212070091160488404107808003594008000d490356a000c100c0ba000c4801e010107859910887d0004c1c002d650101c03062404a40d410003165a1204401810500398109000301d501403c9018000d082003d06200803030303000c0d910400503261100703040c141c003460300003890500030b440b96094002ca000003e480c03040803070030000d01403c2c01c8148132240d0041c07000310b00e045c85040f110740000d0082d03091071005540503d000381034071011704046d500d24406040c50410000c58a400c65034007590806000781000300809128050b00703001746e8022110304010540ea903c0c0400034005040405030071035003a010301000700070300c00e05600690590300381c5006c03e06080d450f98104016082c01703c000c603114030106028866440e20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 991208300 1250 991207050 991207081
    0x402011407082703070605120115090b160f0b06041a060d020306040e1f051b0a050913050901021b28050a021509010206061002100b011701080a03080702010e06 70
    0xc09164800c180760310b100017030404c031050b0300820010303c0c0030916240c0d21096250305401402000440340a071144503601500c0b0039010f225034440c3d59404180041d4403a840300300144015440f503002d2000700960701c0c0c40010502c09882003801186015030642c111000071074030340e8180701c0040c105c50034403040500e610701030342c0001c1031590401d884d5090700c01c070200c042002c40f54460903402da054030f281c0512900411118010300b4100100a9081c0d0740142c80322400031034003440103521b08160750b10300010200d8121801d0072101407400c0c0c0340a0801000080c1035010f04241d480c90540c02c0d62098101c151180e40f00c03102008640000c0d0a58081e4007000f540405072a8010b1044050f44e64480c210b07000035059103c5400078011000c00001c042c3c8096905102c02d41d40030700d0407a48500f020310110780003235994006084c5440305544d507140c1150140c0c014514003551154084c803040c060345c0c45484a80d100c00700d080040b030211720307180082114140180540c0c0705008002d0300502440d80c801d01c81c494801c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 991209550 1250 991208300 991208347
    0x1b0625050708011b0801030c0501030e0c13021803030906030f07020a0b04050a030e0303280203070804170d17070c030e031603111008150103060b030a05040201140708 73
    0x8801028a400184207222000041081400004400030465094002000d41815000401a100005000140d1890840070903100286400950003442d1404540b2303180045440d6684800440c0051001400741e40040007981e80203410154078840c2d030130506540c0c0c05100c003a10341c081c0b400c0c000140920042100958000d80c60b01c101e07820000d1540716802030f102c064405031600c1d04080c42d20418140c0104028840d001d090b001185071059000c5084900ea88207240351a500e8004008004218400c005a89015400070203660790b40d40d0701c104e00c05525601031004105405200300341c0c00194010b040c15800e5803540003000c1035564405508407100004d484003201800402c1c00d03104891b807010001c1d0ba0303c20700145014241107055080c10320f411000742d00b6292044000100c1c0c0201c89a100c2c4c9003a4200303805a42c0c0d5081c0c07000c0500141d01404454204207200e203400301c20000150000e420860065000382c1b2070806400b0318514054061003501c001030001c01040003402e1440744002120341441 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 991210800 1250 991209550 991209607
    0x209030a140118080304120824150408030c150405070317041a1e16110d0209191505010c0b0711010f09061521031205181b06 55
    0x100c08044541e03c80082c0010192034002c0c01000304000c0000524140c1c5110403241403c032003524265101020391090009809044860702007114445d44901060881c48481c404c4c01d662115100d5015070b42c0c90700048145402c5106881501070440d140302a140c1c0280e401002030020350f81140c9402c14040311030040b0fa0403003038040200250028000804001109404007403580da030000c0c503a6009500601d103001d0403100d004025500c1e482c403420000000c916844019240310400d8600051200b040750000650020264010442c0140c4200c0d060845409043e03401c21548071010340205000c5050b0240501003141d071a51040420f6a41d04442d0b0700030007900d40410b000d5140c07070100b8252024500e03c99005515030f030f13106081003001c3c002d01800480e18000d03410201c4c540780c1d80f2138000f82d02031302c0c40c107030250080c29500900d80f1910306070fa492004c0301380c1841181081c10080360500c0120b010614903006a04244882d8a4140d28110703032600018515402d04881340c1c04080405040405081e21 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 991212050 1250 991210800 991210811
    0x5010e06031234031e05160606090e0a050d050301030f03031a0a0e010f0b1201060305090f0102180a06030203190c09090e0d080609010b07060203220c06020f010209030a1401 76
    0x10854402c001e06096021110f00750400f9846280241c002c80071202250301c490b192510b1150500d03130200550303946c4c5400d900d0b2007542054900304080242400d801000146042079220040c81d48005140001588540d04980d4040304210040790746010a010090402000403100340201307101e6000400780e030140d83c0040000080381030004014555680c44040c52440b150010080c0003508401400101000c03000b0070300e005000760310300c110365005005910605943e003001c16a00042041640c080400c40c800855031001c81c9003183d0000c0440340000c40c8100d10b0ba40c00400c03158403034000e4030f01030400c0007841c000300407841c45150b019107040d02c0b084042002d030a50000d510449802916030a40c03c1c02c0107071140100000000f00500d900900b044d020f4121a401003100012020403a040f064000c240180c0300d85a00c0700303501043e40c401d86642d1010201b4281101445040f0101c401202c01a40850700207003e0124018281e00402d2009645070300b2020341180455460491005040c12800001a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 991213300 1250 991212050 991212097
    0xf0321030a061e06030b03032508250b01050d03050318241503010b1f12020315030615030d08040510050c0a14030c31081005010e060312 60
    0x1403510066605860115002504014841c2c25100d8040d80e01c4087e80a5031a081e00d2100103044d008005442c140490004c40341e01040c0030061081c0d64080d0782c4500100d010045d8400720810440030120142c0e010300040000090710300c2c0208041d020154961211421560b0740d1820070140c41044d069150079000300940d96031f6130000e0500e03028036080c2d0300500501c01c0c1480356584c0070006950140f81e009a16108046032550384180c440c10b210000c1c4d9060080c40580204200c2e10740340b18609400301b00b4004001d00a18021110175001001c1e0160300321696070703440c400303005a020040c041715500364110b45c02d0390803202d00c40c2200700d50150280c000c4400303102e2007031040f40031a20111405200c2c460049a4440c0859012070ba120345071a01030380c0b49055040601c4940c201d0301c1912940f1443c10110488080800c6100a1001840441e811b2803940340e03644656141d1610018001508007138079000c00400d452505500fa94001c0b500600140842c007007421000f503941d8004181501c0c811711807204440c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 991214550 1250 991213300 991213319
    0x1030b0a1e050c0c0c0604030b1801060909031d24070f0f1415010803090f012006071101020c03121314030a0305090d14090117040c050f0321030a06 65
    0x40c0140c948640b82d90362a102135a03d5400d01408004c1d13103104410410003003001c01c0107040317a1703500101d80307800745a050203110807c0350041506521400003282080c01190505800c0048825584500035064011204440411009002c000c07200c00890840b01c400c08c11080346000030f000c1c081c0c8542000310407003c5507252660801051441145e40680001007500304036401d01919612850700a9584021f505291101e522130003001a00b0307001c2d8000c81c12155090703120b070241c032400543c014980740f2480c07586064991207410845607000444c000e002e62604c0e0440500c00c880c00c60040030084c600304019140030009404020b840c0111040100d030821000c260180136428124010700c008560b00d0300c03803800240a40c0d100a15001154210081c6c400d00240c00243d03e1034000740c1d00880e140d51352982401a90072080b04203031b40d03401900700000c0004000116505c01d00362102100c1d00714005180f0f10415646200c0b41e2405101754504510415600714500044c40c0c200755070b1031010030703070585594819 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 991215800 1250 991214550 991214561
    0x703030e0415030b09010e03030c0301031b051e0a0f05030c04020706060509070509180403080708040206220906080a031b020409060e24010f030219090c050c0d0801030b0a1e 76
    0xc1e1800e44c050401d1014403a000d2048281c8400c250019504614000319010b403039000520010b4400000c0080c810681c8411609020141c0070041175007845ea00010f0100500440f4060840e00409141002160400303118a19000b101c100034000e00c5840c0703214003803001035084004102e48044c0c58241c0418250b88085129110300801e55a00f5203901e0060704000140520100039000f40c2000001d01000c04d5005e00410390100c0507003030426264607a0b10105d1114411000003030001d0300b07005031039404040760200b20000ca806c604030a0008130340710310025403200812600140880e0a1041e8208030000e035a4018200500007080042e030140c2c07640300e000540303020703508031034843c4c100e00c0001290610071904043c21308210300507101d05606001218501c550140000380c8100c41c00900099800c01461701540500901b0006000501c903068014200d60002c0d0300a81190182000b204401e034421913455048a80103403c401080e141d428490000b010107841d11800d040d44084901001a05801034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 991217050 1250 991215800 991215803
    0xc05132601110a230d0504140313030506010509010b1c0b060d050103150905060c07020f10020f06180d120b09040312060807031101050901020a0b360703030e041503 72
    0x22a40e0f2080c0b008020309611001c01021039280e40c82020004c516920000c4c0c4040c14525100050705440700d042038103205041c0340019950707103c00110310b0b080d0f0304109081e200300c03445a8115041a601d64080143c080b078240100403082400b80003140c40204c0c1001a104c10312080e6600050f045d0500f00800c42d20703403242c0d550446907074a520040007080708003519501402c030007003c100008201580c134181c031010068800705408802007180d20a543d02d8048000340d02e0402045503840c0c411109020b03460b50f0000702140118010180041ca40c0d0344100d5080441000f003a0192500c01c0f4003050564004c1e4141c00f400e00b5041e5503100c80201078481a242602440c06070715a4000000c00c00e0020040d54103e0700404c400b82c001030000c1000900340040316420321000d0070643c2d21203024900407481d1904000001d0b00004011041c1305001c4541903c80080703485650400070381116903492040c4031907140d4095490343e48601d0082003c00e204050081ca03d003801000810302540048403210700900d50f410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 991218300 1250 991217050 991217081
    0x14060f06040f09021c0b030c1302130f060f0507050c300a051b090a050a180807020f010c1211032710030603081c180303020903010c05132601 62
    0x1183e06981c0c200e0714021805205e5044244508030348500441d0301c0754808404c4234051042c0d03090140c0d003803002c0d405880310f6007034501c48400d030f055880605005c40c042c50300c52030b0081101800d00301060341c442c004031200c00b0303007110050419004120a003c040c3c1c26034000c00046d070080c065400f015046203500382c40e869114100502040b80c15003815414181288868043c10480c1001c2d0340194480510491b03100d1150f2100142c00e6844642440140c03a003441741164020300400441d00300300ca4003000c1d0090030700a4601e00008100c550040d100c80b001488050504d24010003100c203010f10030a040d5212200c40810340c1d04045000006842c610380e89903101426612101101d030840c1401c82000b4990071071403409002c40c5103036031520682442520800031044000c41d0150004045c1078100340c0070f04110741e012542c0c0851038140200250071000c0124801c1d4200216241554400c5081d9480600100c00f412010ba1038100d4802c008842100d1500f000c048030902d1280c0001d0a1045c016050b03110007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 991219550 1250 991218300 991218307
    0x30e041404140d091a0c120c07061403070c0b040218192f07030e0a140306090f060c07060e0a0305070b220f110d05030a09050414060f06040f0902 64
    0x1005802d190040e003109081021210b020440a00407151841701d00c0d0210034002d035681d029076400760030004001e010903c1580002800e07907090070005460803c80b54543d443d56444241d102102144c1d01c000c0c0c0c1c1c2180002c0d034401000c00480c01c0d0784040c90f0418401810011604101c004500c16020116690000c0c811031a0711a41000142e00070224449151200341c0f411008400810740342d840d10005c41c103555400801c246003010300420700c00f07a003000c0c000c1034080c14954a100d41c403205500328441030300a0007000c003c514052000901085010b1200014010664502403c60801d4002201c01c0c1d40903900d414200b030f4403100601034000442e019a944603980c2920b8109407000800184c0f00d00c1c001580f4058100c02d440503003840c078254035030007031842e905110a400c0201040b4901140c196001e02d8190614040050000c02021162603179201e0320b20303c0d41da4400300710460f01c2d6011841c9460300c0c1b407000100380b40342049049124075070041c040341c1800e4564003501129021070700002061796000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 991220800 1250 991219550 991219583
    0x1915090e0c030106120b040201050c101e1a060f070b0103081305010f0e010c03090504050a090c050316150201061502010e061015080c0d090305030411060f07030e041404 74
    0x1400403584080c020b80003402001e24103a030b00c1d00010241c00014003440c50000119045a104070221003c40f151617048810340e050010344a801450310480c403c10407214031440440c0d00c6401c2c020075038400307100b070f500c0400c2c070f024074041c0a41079100160380c0b140b05508220800010385138205190195008811060301c80462a80e20585080d50360462030500112100700a05198041c80d640d109030800c3c6070250394101d542c40d003070714031041e150402030f880340c10201084810301c110750091001501542010303001c160b8850605880342d4401c4090031158030724000130310a16602510901003003110b4400010400c0d0703142c90f001100782d55009050300507512a8030005021804000443e00030380011031045c8600c0c5082c6010a11803500d030954003e02042c0d01c0020a1020004240c54210400c59807e125210083c2390080966000302d07011103604c0010700019050303090441c15140721080300c160246c0781c182c80362000d9504601c02d142146d489a150450201ca010070013054034040c03071095461122a1500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 991222050 1250 991220800 991220803
    0xe0604060608061b0f04030c03050303190b03030d09050a0c060809010515060d2307020106030327030201080408071b1419120510060311120f061915090e 67
    0x102d61021580e41d001e00f00703010b2800c0e5aa6141011115040411503881d072050020140ea40519840504000f030002000003e20001000a610030001c44c410b02084009012940085030b1319102a182c042e401402000312541030745c1d00c903541d0180038074215442c0c42882d5641c4c80c002001c50700840c0000d079105081c014450f90034040c4a8201c4500e100c2c4402409031a404a1031a003d254032460724182c07280c49480000600c3c0340300305d807800c5080d02198006e10f01040d01901805840c84100c0006002c0844010381514280b501022040981140d5514901d10b80044480f8900030f802a42d251004001140000d0490780b000d01c152100e0780f9849140368a4940840300b044041c0d10314600421002c01c250103868880c0c0504419101c9071740c0e02c081102002d0610a10f000340005503c000c01e803406c0b2011091000c010f401c1c2020040499031030350030744580110162140d4489518000e660302040102e0360704440c0040c00a0042509100007a00d0441148004c01d8541998070134031580e0340e16481140a0b210 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 991223300 1250 991222050 991222061
    0xe0c1005090906010507020d05121822090c0807090b0901060e090103080f0c010f060504110705070e061f030507090b0c060604021b0706170f070512040201120e060406 73
    0x110341411410300d2221030210b00da01c0d9008061604001c0d00258650441d03071078108510390160003030101e030450031400300c2143c00c0f0381c000050070140e05420a002010381c07030107071180003000a4801d60f031001000204040c4003e401402d008a83e503080050f00420810800c2004800805e0002c402180d20030402c028800101c0b8180c000004020858120b05000d40700c08802604482c0d002d090682c0e9035a01d1024400240128403440445508005005041c10b199801080c180d4000f03e6041041c040761480030b00081c4070740b0170000c01a0300000303001c100d10f107007071103900d684004068100d2079642c2040503500c041c0040b800483c00030940c1d4100384200986d0260b19003000d840d00c41c00e41d5141012444d0015a00c40300185078501c0f5a4000588901c1084400064410304102d10200c508039515098081d000b1603104070041c0c4581400e8000584401c0101c000e14010030a640f1504c1c900449020b20b4010050014070913030602c8144c6a111501c00d84501c552601a05074901401080c10145009000d894 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 991224550 1250 991223300 991223329
    0xd140c0d0c080f061216120c0920030601030b060403081b06062202091f080901090305090906030f12220e19090c0e190c02060106110106090e0c 63
    0xc0004003c1d103201d2041d915500810110748813a402080c10605924010840040154241445100065200384090040c241520400c103500207075488002d042d00715006804d25036044080c00443c0807080030620001d641207081031402107120818040414500d80c01544101d8422500185200c014960020305180076100c02001e17240a0030000000340f0348100c06040300c5005114090800032a213110b90455400740300c082d041d05152a54013600c4455202c9821401000c10100d400090310f20b841889072803080c0d42c3c59160b80381000b8118091001c01000203040680500c1101d81074011200100803601900a01c0710109546809250b0900c1c2c8007911001076100361800d00d0014480c0360038060718241d10401264404015011540544c006490034070800b0340312001c1148007040f448220412144902c3c503a084211022919040040c12907554030711200060700401c0051180c144035410703a11440c02541c001003104d40e120354022046078102c42e007000090b131203400703120100e0426002545400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 991225800 1250 991224550 991224557
    0x3010b0304051903050f0a030605030703031701080a0309140303091203252d060c02070509011e0e0703150e070f0f02030a0309061b090302040b0609150d140c0d0c 71
    0x9443c40d41d0301421134081c030ba400c0c1c04c0b04100813503200c1c0c400c1d11030ba1106000300b100900300c031a01592800c02420549000c03100d801c841000c000040b4141c1d500050042540d5816510400c555252000d039804030707010071006613450300040007102d805540e8a0b08a000056400c6d0207183c0d9607039014a4501e074a54908845480554211503080228900f030721000000c3d0990b41050300a9189141c016454402d401030040c4100d02e0034000002e1545d00181030800c0d610107031458441d907601c800c1100d51011180740f100c003401310f40e800248044000c0400d5150440360078140410300240d11082031a0702501608103454070940320f41048600b691104010621060905081c0c646d00340081c0025281e1284580c03050074140c4400c0750504008540d13104c01422100d0288298103480000c400501400c00d40c4802e81c859424841e280d441490400129108040010003030003803507220441050454000209094100b42e03210740fa020326200b00c03014140b150160111180c0d644640c0003081084440d080d20103400c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 991227050 1250 991225800 991225843
    0x6110a3c080a051e042d12020c0607020f121f090506150102060a0c02070e07180b0f041a0c010212071b0f02060d0e010f02040f1403070b0c0109050303010b030405 71
    0x702d02000c1c41c041d0406d411160702c5e029541211414280c0400c200c240c0d803288071220010b24144048a0880a0901c2040e1f003a50182075051040003400e008040d0702039844515200c0c0d85030a407800540c0b4184400c24902650350480c80304296003400c801100004801c2c41d19618080d040250a0180b1030748200310302c060f0021000d20b40c000035983c00c4018501c421341c544e210914940d290017000504002c0010103a00c411700e140100d002000b101c1900c50003001d4106104010821054000c01e950f0b54103902d440796400c1c00e16000001040880064040001410410201000385001c0c00140600d6405845074491800c141c0307401029408070f00c2440941015402107100004c4c20005040300c200d40454042e9114680030b0000b0000340400342040e030b219841c040f6007081944d40c64010b041200d80d4415400b82c420713a00d010b6208403965000320940e26030004c400510852a000c0d01030000c2100071800044c004000d903840c1884d550003038002c504c0070f4201100300000c03c0804c0204003854a0421030801c034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 991228300 1250 991227050 991227091
    0xa0b0403020d050f0610090e0f0d120b040f0905101103010902030430020c01110601050105131d043302091c0c0306110a3c080a05 57
    0x14021800024415042e0000b0b44003805001c00010b80f0840840d0103481050401d5006801011040c0c0f10310403e40f801d00140380c00603180442c3ea504610034201c09030010b4600c5034000c803030091500d1071200d8403580d950b06c0c0100c50b071203510842d800c0c58a60180010040c40c5c0342800c0e4a403258001580241d2400c1c0110b10300701400e07440c2a641120b01d02e03c0c01603100d442d031380342c0126801224101c000800c91240401d0248101082c0007041e00d030310b031707809481344003d0355401141e0110007248408099481140108001e502c620000c02e0607060500b400f0302029141c0c841034846542c0c004036203400310204002d21080c00380c812440441e2250031900c1100e4000700f01c0b0040b402e60804908d180c2110350110b80300c0456103a0303404041034200340d1a250b240001c0079103401c1c41c0c0c2c052240000c1d1456440c19103c1c446800c00c00c42120090546c0303844030101c1d5200d0a02c0340072000340300d810b4030b4801c1201014035213101141e048000c00c0d24615450b8a002841e200ca0783c50100d44008100d0403000080710204c1a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 991229550 1250 991228300 991228319
    0x708150f0115090902030a2a140906090909030903030a0302130603090b06010305061201060602060f0f090a300302030405010b0105040b1210030b1602070e06010e01030504051c05090a050a 82
    0x80498090500140c0c591f600e44500300001d243d0742c003106030018890a40951045494414001d40c00100d031989000600c3e080300390407440c0550000c06400c140c0801041520745411041c0950002801007202c0c50507604031b01017410341c1c00143c40c2501194001c90400c101000d8141c0290142155203000c0010300e000e03440d00d041e640c10160905050550380c2d40803c20a03160068031500580e00381c0c00034800f071527407100c000b59211000c49250300701d04400400305e9018414101c001c0c0c01101c0c4980100b1200415841d41008603042c824150340007030300003903020840d00b8105c0c0c0c2c41201d44107a884c01600c03031a080c00c010b401d480c1c0d0010441e0404c00104403c1c040c140034142036032100542c07041c072602d0580d510720340624030b400313640c1015202805203010800c425490740d50f6a6286610396083d00e400950710b401d004140340d81a181c140c0414402192182c0551096002982c428020000c480c030300c1007054196020440004017150008200040e03c1c540c03410042c030400c000701015a61740d0b000320303e405241c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 991230800 1250 991229550 991229567
    0xc1606030501150804120309050129120604031b02030607170609090706030c030e0f070303110607080703241403010c0519030c020f0106091407020c0f0f01020708150f0115 75
    0x21b1800c98840e140010046c4a9132041d40030139440300c000c0001c000d10011401d41407000000c45198101a074000340210b040884a5038004035805c0d00030013950719207540c255459969503000c3c00042005200e81c4002d680c0c04c00c0a00e024940c66114058241c0005941c4880d1500080145010700749041c00d102e602034000800e00100d41007481e0004008503281c1d4210060441001504214071401d01c484000d0000402c020b01160302c07a4441c5c10100f00019501501c0b50b80031100c1300082102100094421030007038108403030200c942c0707070381411200010014a100d00300a03008560300c8219030103c04904d083c01d110319803543c151410228240322103199000c081d086c0e1003030792004060311458400c0c1910b000700405028036030300c0701c02404070986810f900d500906104851075407142945010800c840e0012405003e03950000c1c2000458003009014403d6900601c00301c10f0451143d9180011489010711600056851030000f0140c14200004944403040060304a2040080000c81003140941c0160b0740 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 991232050 1250 991230800 991230803
    0x702090a0b0f100507020307031505180c0108070c0506041a10231207060806040c0e0306060904170705011a01092402031608130902030601140f0c1606030501150804 72
    0x100c0d0000012201113403030b8028160000d4051040803804010441101d06060300205c481e00304110b41d0741c1c3d0805402201035040c0b9007061940001e010582c81c0d5110701804c4d5032040c2c050605403108010b0341d4071645002c60440d0181c800740310544005a0002d52880c0003500040320b8011b80e65542c3c03e245812480f03075000c0024864240c000c60031410151600b8040c41e1280e0755200030707030700b8540d40d840010300004002c880140c8200d103880700c1c10354098056203440da201080900109056502d42007407160f04d8034040c000b6601d000781e50911460200c03900005141c0755104000200320031003a11088030540000700081030601c05107050a00c641d09440c00d2004d8140f445101c40b908807110031005a0452040c03048960544010340f10500c00d10100c1c82c02002d0480d40000340070800c82d47d0328440d10403800166900e90000d2420881380240940c0300002d4140d8001d00b560151034601e0200203585052201491110304841d80002004400c0c0c051103004e004100c0d03a501d0700c1d1080e40c5544000c20b081c500400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 991233300 1250 991232050 991232059
    0x10504061a0c0c0d0c080d021b01030c0e030f01060e01050f09040b0c13060e01320c1c0e18071b110a0306020c10060803090f0612010b0702090a0b0f 65
    0x35000d0302c00c2000c02540408103009030010f404a0124101a0000d0f00310740110211480b5091500c0003103440085c00d01c0c0b42c5e440d0b01c0c40a0703013544074040c0114082e00302c02c3c00000c100700d42e615414940b0f0794240103810a042180000103007551800202911400d4140c1c869445100f40e4040d07208036031650072110364000d501c000207842c95524065000c5190161f50500744c0209007582010660a8000f5000c0d00c070b01c03c00740c980041c114210001000114052180800c000d42c0c1120b2512940142001808c440280201030352403c04d44c82450080140c14200c0c002c1c00610a894001303001c1c04c081c191074407001e002c040c003103d6a280c107807006485494005841e8034520000b2100380c00307101030049105070700d034002010b4441e003503a241442406500a0085020300e402040000d03202c00e11184a903000f1244045c001e5410031499030104180ba200031007015400050030010b50001e03107400034519020b001d40004442d1141c02d2070060105000d03004081081c51450701d40344004a5031030010b80382c81c2c1802240e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 991234550 1250 991233300 991233307
    0x902011107080a060509013b060c0d06050d03080708060a0b0d0b12070e0a020708040803040f090b0a060815010e0d0308041e03090306051f0e040b010504061a 69
    0x401252a003852404150040c0039280020030040c0000c9104907420340198024011034840c00d50f02422100b0861280801852082240500c009101828400c5040281c2203540da201ca80c600c85081c55801c1314500c080c0c100028150f0402542ca10611000c0c0c00296040c0c100b000165502800c0c410000e480207003801001400a41c2c02d0f61111040340c00381c44001c032081d841d0003044003090b001e8071a181c075403032040c0a02e041c800d030600341c0001e10100b140c41c400400b28450b01c83c135a04030000d50000000341d624000801c004281c0c403900708010b1008010302007106802619042410040394130207501c851107180c25000402c03080f035001213415007024504041c00130380010040183d84500c1038070180d940000d264130041c3c06054000300030911481c095140b03d4844171861045810403a01d40000a002c1444182c0c03e0001c11110342c0f0141d8030140244000710488201942019401500d07804101007060380d60400080120314a4094014007064909020075130400c082c41118503410408200d0040020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 991235800 1250 991234550 991234553
    0x10090c061b06090503072f0405060f03010e07080106090203060a090c0c05010c03140c09060703050c15190b0a060504140103020d02180a0b0711270721110a0309 70
    0x4444804010b540480104104001032030a1526a000264103441103049860701d14844015103041c04800c000045c00d149001180390100002410003610341600b0282e400601c0300ea44c0c07002d1090f040010242001446007918200b6070509684254001509150040c002d200b074980b20f03d441003058409203000415151140a400c1b1000f2042c0341d0083c20b55030901a0400b41c264056114842040b05601c514103180d40d0f14454005603c0340c540c030550801010410600801d20940c060442c04910900303842c580320006c56206090780e0143c0d0701c0c0002204c041e40140100729107114003000489d0540e01d4000c000e243c00350140541c080c2c1e128100300040c180d500900313281e1085d07046070405c0b01c1d02202191548601c200b00035000c600b060843e070280f011984c001c5184074a0070306407105980d00081c010f42c52034022003800f03000e11044211007040c820001c2807160001d15125118407a9078166a49503026a55004060700c0100fa04000403449143c00755080006041c441141c1071031845040208003180c0ca07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 991237050 1250 991235800 991235837
    0x70c0b0304050c12011817310603060810050405070f0311040b0f0a0501051806040f210b06061827070c1703060307120605150603162f0a0510090c06 65
    0x41c0103242243c01016048d00148041403111303089501c01d0030b03810b0030f401500c3d80300540444850340601d1601c0d5109071302c00d02c2890947d410059102d8881c0e415a6040b40d40d9072110302d00141160411100085201c01350300c0c071818544220710355080221402007445500e017000c2410140306018490410a002407120f07800481d0030024075000d5800f4080c145e49941c0c503460223101e54811700a16400d43c101008844108541641d25401e031134000c0d0b182c1d9180d844072010401541c1c0412050f0445281070302d040ca42038bd541c0c101d0b01090301200a1181a5004407002144880b00c008000e0014404581d0f080c4002c00c01490b100317021108403074046a56500c03200d001a1807d0340d0780c1c0c403450890740c41881c15001c012003500300c10301540b240842655000c840c2070410100b80411548200420001070030320000d01e10803091002d0b256040d07032030580400c920601c00c0c0c14001c45d049096145030700c03219180c01000b40421200d042c480031340304104461140780c0d59031030380d0203620711420007000f00014028824980 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 991238300 1250 991237050 991237057
    0x201051902030c1905121215010311030c1903020a020309040e010b060c03040303020105010807050f0904060b090903071401050f0403080c12040c060f09050114070c0b0304050c12011817 81
    0x601c5011209110004c07480100c425075041c904590034050034804010343c4c4089402c0e14410340340b002030384255581e14403061f20303040e9229580d24105078a42000e0280d1205440003940286142c41d0040e540703000c2c02c807401c04100c200350001d008041c81000541c002075800b10685048040480b4003140060000c0c1d046030140205402c00c0c0d070310441c00074a400707200304000000c5c41285d11a4009215582e41c604007607444980030306c52140c10102d00400003a0b289001c0c11400e600c144510340002d00c1c2824007000c116000c0d021507a440c996400061000305010035800e45090101182c4c000780010300e40b8030115002d21102031700040501403203401107100b0035400002c0d24500f20310300038800c50901d00b5042c07030500f101030751080310701003040c1c064100c5529202e504840c1c203030303038040c2c461200c0305002c01000403039036200c881c0590341001d41a5011803040300c0c2c0710041d4012400364005000714031000041010684103140f03030300100c3c1c1c504083c032000072941300f02c10103665400900c10342c14200241c82000e424417 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 991239550 1250 991238300 991238317
    0xd0801060c080715051911030106120f090c08070e010f050904080d02070305120f07170702010e0f030a08101202060711130e060105011701380304031209020105190203 73
    0x4d00341d81c49a40d281816808580305001c4000b60310100020020703a0700440c0d54010b01411a9001000180041401041c1040c030704450400c0c0003e0f041c94281244044640ca135004580034540802c040000850400a043c06000780d10700d4413449500d800c416594041540c810071b802140381100003010300ca0310314180c5801d02d901b41419541d401c0a803800415a62050200c520071f81d001201240c000060840600d11a06960b2100c1c1c1003c11050f040068800d80100724404564940c0e42521900d401802014030480c0000c00541e110189142c5c05420400024802420389074181010030844540b031500d000c045405442c2d0a60320103442c00c2c41a82c40303000d10111904104685e12680c141003241e03210740350a1002c5805d0b66110790321600115405107401700060341c03101c0c549006001c00e0351246841c00d2100105403020404d0b0121440c3c414100900380c80b500b400c01804010003082c5900102c40301090b402d0700800b002200040d81c0003038103a008003400c4204881d201980c07028000e000700102e46110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 991240800 1250 991239550 991239563
    0xe0a02090f09010501090902092e06051902011b050a030b040905060610110a1e050708030301090b0f0d060519060f050f0301090c0b030709030b070507140d0801060c0807 74
    0xd240000801c40c0c100001d48103003105618140001806101c60b1003151301c1c040d4002c1070350305107407a544076000a0101881c040440b0307001d4852030034403803104185220000d001c191611a00c40c200d41240303640003210141c0c8102964140a500600600684950618585d036410078030b450700340b202411002821203040c1e490f0400d1500e030000003400000650a44180f004403140241e6402c0b000c0c0c03c88012032840c28282c0e02da40580e180d20002080c01240d9041c68504255003400440103842d107929100c2c81c0c2e44150791a0300000b005201c1560b803405243c00c2042c081d107440440070842c5020403402140d40300e02504285c0e440c00840c1c3d02401e200c100c0d20440c10029014030449444464900782240c062059900c81c3c19002080282130506000f884030310f90b000900d0405051401d410303030880c0d900c001d224031300b0481c8034400440001c1d00c18650502940c85640c41c0c40c0c659081340390884a0404c03100c1c2d902c24a80c000b07282841216448a6424192046840c00003c000c4240c60800c506005100005081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 991242050 1250 991240800 991240819
    0x80d0302040810060506030105100c0b16140f0d0506040e070e5b0608101e17070302060d02070614010b0a0807051b0a1b0605030a0e0a02 60
    0x41a5054024000395400002565681c6168400340300c00c036a0b80307200702c6070010802c0c4010041c1e0300d03200400f5640742c00c031800d0543c150401a03480c48121041150342035400791011074584912984048512108a04e410809107482e1a9080c1d907400c60085581304540b071038032500013402686460b08004680c161007001c0350003a40c3c0b13401c4c4d42e6425620440e1005000e0903400500d255645000000f10314135079684000a034003011020004540c643c0941941c0e402101080955040861020008008110550b600305a0381003a01d24600d0044081d03001c80440748104070380740200f0518544039270031584120854130700340000282450900105030300280d8000d5000c185c1d0088074805e50024450203200e42000c00c5040001d1006507440d00003802118060b040c00d0009903103c41c0203d000d680c2000c203e05040c0e0501046209045403144a821100b40c9504100090403c00c030001d600d8800071001c05008c00f810509105005003680001000c40c140180c840801e0324290a0521001300c1d07503038015012210 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 991243300 1250 991242050 991242073
    0x1e09010903020d0c0825120f0b04050c0f040c0206162c030606040c0801060e04270614060d0308100306020301081f090305090d0203150106030b010801150e0d060608 72
    0x38205510a000c00c03405400d0040c80308110300740c4041b02c91880c5415403031140e0700b0031585940590100104448258010390340e080441c5011004038415403203480105080c0d04440140410a44801c195500517401e004083c02181d4000c581940c1c040700b84024420079651903034040300c89a855480200744050fa035040d040108801c40e540301607070003081d81140c0d490b441d60300c140022140100c00d0312000540c108014030116106240ca00c001038002071011a200c481c450800014201028030541e484901105450401c01103010303c0841c090a91008030042c644200070405c046c40b52000107080007421000144211082c00324603014641000d4115100e686880d680c1d90744643c82102d492144044050503001100035015003c0c8003541540c0f42810950424144403030150039000880c2d1501a286400351140300b8400c40380d000f00595070340425900705200014114401c10303088150f208a580300f21800c000d810542d00000c044c0281d41c1c1e06c0040c8983d0400c90300408050b04810814003a4602e00c09 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 991244550 1250 991243300 991243313
    0x18060307090503070f0e041203060f0e01051809030f0a0302120f0103051002030115080c16120314060a0317120103050a060e06060108011e08010228051e09010903020d 73
    0x25682c041e000c8038186034562211a80607500c82c410500110036110010340041c04042c81c5640084030380c100440c01e145c0303543d0701c04608012038200801541f90103004224500c0c0c0780d030240034640c40007000c00c105410a2181e1944a03c501504c840070900e0000713603a484c05111b94100e41a0740400c404070103140c01c00f0001d00c0603612003888155114801c83c00070700c0344429a44210780c1214030b445811000b4110b1a0340070744071090300410300c6204032010f00c0942c10b000803203034041e94500c0c41030361500105840c1080141c100c940c52950f0b142e618240400704513880d1100a13154003500d42020b2030180d0fa8070481c22145440c41740013a403240200c038000001040000c00a030981c052889640300b404506580c9a81035a652070480d0302c107000844031001000440d1800c0800c0c0e1541060001e80782a0a40b075404103820381c4d200301a5003001200c00005406145d08006140507001d08528000f46024014a802c4125480c5072a072074013082000241c0c504540c0c040c0251000842d8040d0482d03079207094904110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 991245800 1250 991244550 991244567
    0x90a05070e010f0203180f0d030807030f110405060706020403020a0602060403080a02121f082b030207020307182a030e0708100f0608030c03071218090218060307 71
    0x440208140000100481d030140c2d01c2c01c0c6183d420341c0d0085042002c1302041803610b00352400c41540107204400325a01f0f54960411044400d8065102c04c20603081c41c00008084413000c00d81644580d00e00b440c2000d540c0e4101d4211030480c0e43c1282c0f8141c65800600b0220300903ca503600c0254000b030354a10015580c0d401148052241d8001d8035000e4841e5500381c3c0304030581c40340d6182c0809a880b517200041c0031440d595000d0a10003103118001240a4449086038036006200030b00b0b119990f895420000e0315160795280300603805107403600350f09186450b808255280c0b000d008500000000856001181c1170039481403048102e0210884500c1880358440406411828200030000742040d80e40065107000080c0c007802c0380c0d900340040080000f1345042c94020055042d04c01d01c01902c4a50014414400f08050841c60a105019682d564075501c0e01d2030301040da0403400024002e680104542500d000810700c411260b22450150b51808120307241079034000180c812a610000110078000226881540c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 991247050 1250 991245800 991245811
    0x9100e09070f1215200304030c20090903130e0903090a270b03030a051303060501060f1107060503062e03020408120306030d2006041505011e05060a020c090a05 70
    0x8401e00010728008000d80d100d808113442d20354110254217030440c03440001998030a009140c039043c042d40c00e640d080f00310000c400c581c000e000d400590482c03580c68002d0804e078204c00320300c1c0210b1500000303041d000015502da01ca0003030007039086400200404811301c211200100b00404503b0740c80e4550b404510710740100b001d07540807842890000c1c1030800381841480388840008005505111048000b200c00b40d0100014121404c0041c1000002030441d01031a40138190b95203c50705d08440c9643c006100081c00345800700c80c0c1c1e100910400207260040c0890307400660540d127040d2081001c841094240202032500e0f8410850444c010141030750603406002a01c401805a0f01407940304840702605000941310203516402c4007a0a0410718090014070300101c01502042e80305065086440b8101841110b041d43c911300710184032100d1054034801d00e805864907602e40860603178014000f400c1c18006001d85405803000095120600703000304404080c28400418000c150318020183c10042c1806880 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 991248300 1250 991247050 991247063
    0x7030e0c1807050d024312050705010f02040312020631050613060e010905061f0f150816020d230a0e0f0a241403040302010504030e09100e09070f12 65
    0x415010007198010b5800e031910311b584108080c480d080e2150155005030246000501c03000300402c0f0002542800b4201ca05805400010b131110300d90f040c18405018001010001c40d0407035010407076088554080c0202620001c0d01c80b007a010020724040340d04000780718020b0880e220300340402c02800d0300309040800c030520991091090800e40001c440c00d07540a050002d06070f07004140000c0166807806105004401e040101c17000c0281e4500d50301c0402d41030303500801c81c00442085505190364000c0540f58110741c201c088842d807010b0000000b91114204949082081540780e90240302050283c0c000c52058009408583c2c0e03500440b001800c1011076400c5140aa01d000703030507034454580889210f04543c0300d1000482c4000440070100520a02d0641620512800d0303100c0d0006011a00d000c0c502c100d01c04d8000007010b003000d0401a004074481010248600c42d484204880140000ca003041103c4545c13410941e0b07070b101c5004980c00c140300758015030000d0f03078401c9000a0b0840c1d1102c1213586a4010380 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 991249550 1250 991248300 991248367
    0x7050322050115151403040c03080f03100506030402090402040906061511010e0304140d05030c0105010e0136150e04050105190207080a11150a020307030e0c1807050d02 74
    0x3608078507107034045030b58042400000601842d061690040da0300600c2307aa140209a51655240b0703181707030840c0083c6100802c02200300310340d804001c0100700c040c02040300d08505501d001c0d0b00284040e07138014402030095031291030070000c00001e40c1040b8041c01c004456180385a0310341c071004000001e410000f025540c201600810407100c00300489041d100c14622030002e91200c8030030b0120b01441407030219154031080044034041f0f1001c3c0f141c0740c0608401c901c41d03000c3d945440c0d44d004041e0303600440601d0300350241a215090822420f20400c08102003032003c070f14640803040460100c0c100c0d45c00404400007000400c8108401944080e10400754102040e113907015080c056422800741041c000c4c20284104074015900b030195982a98040f85101250590f141005403440110010b41d001050141c000c02804102501800f43d080384001c2c0c0802001888002c2000481d20b0758a00c002800e940710110104040303034401c07001c603546002c00004c01d40d0344d000200110f00144101c00c0c014420600b051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 991250800 1250 991249550 991249559
    0xf031507122009010203071704050f040507081b0706060308030a15060207030f06020415030f05070216050f0d0506102903180c0d0507030210051207050322050115 71
    0x184501c81c0424a21003007a010728008a05002d00e0b60b000401d01415440309000740c6000031000d00c010070f12800304403803158641b4030707103028480307030847c00f282040c0303d103040108119480d544503005030f034001c41d444444004480c0b80e10030f849561081900180070b030b50914502005021031b200003540103e10b030210801c61410903202013040042c0f2400f4074001604601d0003000850f5103074940e500140d0117181d0051409640300b9441007060003441c09035010a0711441c24600d0121244241035007c40c00c0e00180030009000c00d040301d407010850240f1403080920500c1a02d103600d0341c51116a50503400000c80d142c50070040400404c10390360340300f00d4400700406080b80300180c4100040c490980d03101c0155030b055440b20b071030400303c0d80c10305c94004101c1c0c0b2690f813004402e0f076900d82410503994003800c080c0c44580d081d40140102c03052200070003018891f003049040d41e140801d0300e806600a4552502d25104d894410980040c060039101d81c9840320300f000e146405001040d03002103000000d41221001d0039586 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 991252050 1250 991250800 991250837
    0x4081213090507050417190311120f0417030f031003140c01050313061103011509090209060f070c031709030c040506060901031509020a020609240112020f031507 71
    0x1140d8900025400f07110070044580c0d0078012681b5601104155240340c5a80809003002014074141640040d02d402640c0400706000d010680083d1402c9800914100f03610b8030707070030141c4100d21611080e440003201c140e02081e000d01c00d403100740c0464000035540b070038285440101600c0714081170310303506003c0a0301203e81400007040030202c00103840d001c0c25a038420707500106042d80c040040c0ea50640351a040d05451000c00c004601a0100116051051a000744006c1003000190080d40e030b0b41e0720400540c02c49546840c00d86140340c054440c003035901d0348545040a0b81b0740c070551000340f80d20140c80c218003004800300c001e0046d0850076800c440d2108000400c1000741c0e08e090340c82d681c010703c0c1000241c403e0351280d0070001840c1070b0509426051540c6000c1035040340d014400d442e00581010b0144099608280040d0700200d0400010042c4108031103000c64503810184501392109180c3e050b500115204c07251a07080743d0f40000c00b61401c014412043c10a114011264840000c9908401e0642c80aa = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 991253300 1250 991252050 991252061
    0x30501050a02070c0b0415080606070b01081608060907052e0309031e0c0605070c0b040f060c092d081f0b15070b07030b1f080a02040312140408121309 66
    0x820300c01c800030942d047c10580b00c050002d07003980d80001080004c100454a22441c45e4003e14421009040c1c2d4841400d192210f03103a913400802c96900007000344082c0d00d000040c224160740b402c50700c90034400b00301140205401d4149001040312a4449291a100354043e4416141180281c41d039080c0100d010340580c1c11000e04040f1003010481d9061350f0b00c00f04a42d540821350001642c144191224500e884151340050200e07012112915255428001c00500d4010717041000c0d031906029040c6410244c0d003001c185000d5610381090240098080318070042800d080c8c0041c12000d091381e044081460305c29800040484440c42c90a081c01307103112050915002585c400040d001400717041000d1550391250158024100c07408140d10303130b21484056505e40c44c054244110001e241650318074041405400d8482c0204000e40c464414002013010980807444200700e50042d00d0700400c141c10070780c03071b8901030301885d00710046510403181e001d0303007250010f001008031451241740e00141c0342c2c0da0080a0103690 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 991254550 1250 991253300 991253309
    0x150106080a09030e0d0b060f0d2f0a0608100e100303080c090405010f03060e12030105040e120310061d060901120e010f051501022a0406030501050a02070c0b04 70
    0x208040d0000700708a140ba07004110b5a8481d00d4002c00104005000524101c10750f4070680ea401c0048041c01041e02e1300b0441640d40c10420350b001003584174242c50b000c8802901e02c8605000303888240003604165145034091000d410000d0000300b05507191940100500000c8070302390403000760a1008110038400c0c0d014a4464000d00c400a43c00a046560450712450060000e900f010410b2140d030340c2c60f50311030207228041c012150464910321b140d8103002d02a42c0102d001010700d0780000c01007003007043c05076003101d065a50a0380d0104401c550b09400070702e004407007950024080e4002c418003001400007102502160360580d112a00c04140c06050410b003c414100a030340f0080401051000354022401041d407042403910024520141b010300d01c0c01e40d080348940d85c20b180e83d00c01c100001d141c6202c0040c40d00752070a00c0108200d02d00d501c03504415842c0707120a01c081003048000c0078880d5549812007000383d54017200922280c01c00440d40b0703029402042007140c1205002c8000300c1d030112001d0684046a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 991255800 1250 991254550 991254557
    0x40224040603090611030921031005040c051207030b012601090b010c14030403020405070e030d051e161e4718030406020a02090a060f0f030302150106 66
    0x81c50058103500030603d59500b1210701e40c59900928074540c09201551044504001600e00280d1026441803088203100c42920414007e01c180404030014034a440c007500e009590000e450305080001381c03a10300413102040d50504c03080c020001242e0b8142c10000c031488003a01d4512041407825030311100600310500003c8403400320001000f08260030b42050071110018140886030001d01d0b1100c51504495082e00c080030f900c0000c042045061620604e50712160920780280322650700000a40c991000040c1d440c01c00c42c02142255a0304031800b1220550218910240d92728801e00e04203400390070400d5010303100054a40c001040622101c00304000090b0b110741c006000c1d00c11900121102c8443c14006401c80515810452000042030a1445401c0700900030040a1424403000e510a0843d12511250b5807c00d010800c40c41d07400066484465504a565200e29940c03001c8072002008503500100d03011a5002001908071041da043e2000d4901a50a0381d17401c4000d04503940c01c0d01020302c60132000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 991257050 1250 991255800 991255807
    0x15030c0a0518061203040906150507030215090712060605090f060918120307021e0c0f0d0f020d080d110403031407030c05010e030c07080a03020a0219080312040224 72
    0x81100c448505a0701001c024850f854903e26503861503e950040d40110b000d0940c8c40b00140300f01c09682161140c04c0d5800d01d41186010840d5030000d403a00c006e081c200b031030329010001260030301d4003c0c40701034042d248180d0b0000c17980019003411400741800e445514007404502004c00c00c0c81c103c400406101d1003016010081603210240c4854510511444011650140c5a030050501d03483c8801076019180540c001d03d0900001003160130b401c41030841c1e0700c3d0036600510042113035446107109200f002c4012916031000381d1150500410380d184903400254441c581d404101d0400034540081c0050255840c4200f00d1007281c0d88c401985845540809030205822444101d5203c95400060005c1c512a10342858014104d64440c1d09580032042206155040421b5080036140e040180e20000e1886100400040b0026140a91200c055000180c0504d288800100082409103141d000501800044a589510b03201030401c1500042d2000c078800e8000c400e0b15003181c00b400650300c900c01c1050b0103ca14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 991258300 1250 991257050 991257079
    0x101401320307030b0f04060f1e05030a06060603051312050d02090316031e020a0b0d090f061a0a0e06090c120103030509011d2107051203040510021207111815030c0a05 73
    0x1003c110342000310030b080c0524840400c03192010b000c07034030033940b1a10002c0340b01c074184400581650001854035451081781e440500208103580d61040a401c0b407400c0c01c0c0c0d80c40e5143c501314000fa11518030b5068040c1b29080b01402c1c80001c003d0381c001120f005d447c080c6110b5207030100340f141480c500540694810300005060051400410040401040e9070100040a0341c407680c1c1c140340d078084c8001c140c800ca542d91620031030703203280c1c11039030a21918111070988006d03050140d84041d00001400190061a03400002500280d1040c101c81118440303075a500160740e564500201140e104040d2507000500410085690301c00614070821583c40080005400840603500d58080c0d034400312100c07001c4d10031081c000400d601d40300c242c00c00c400c002002541c2d035281000144803c0041c10782e0588215800700c2228a403016204064a16455102c400700c140981d07100001141c075200c8208403c4490110024051302270710383c803d42006102c05034141e4141a41c86020001030529134444c0302e411aa82030a00e18 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 991259550 1250 991258300 991258319
    0x1314160806010828140601061d03031902070513050a0b041107022202130e07020a0203060f04150c021e0d0903060b030f07030308101401320307030b0f04060f 69
    0x44d5819032030402c65100700303181d151071a18401c1310341c0c9a00030760402e10040c440d41e64454003207450100c015000c0c4102c01807680c08240d586c4a56040c0711086c040c1c2400800c2224802d020300c4008080040c0000d110840c910340d254004c10080d00c540c0b110601d810071700039039401d0030701410410320050f15007541090303016000d20800c4200b0b880f00c090105035030035a96080c04840d1020341385140841da07800400b1410310301407184074240540800c0655000710742850042c0d4000070060343c07103000042c060300d80751500d24042070010180012402024200800d14407001e500059003419020060b448524681e1081d03005600c40015100e40000104515424000309169411000c40f0503c050100c0d200e000038290350905107000c9400480000d00098140300c12081d5001a00000d02003034208039494014540010b01901d070001c04002d040380d049014040c02920f81001200c00b08840740d1314660302e24003004010001d0000c02e0f09288999501c0b03030000c050b0305003032050100b030324640d064440d9190705140414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 991260800 1250 991259550 991259593
    0x180c06051e0a050414300c061803060a06150e061306030c09091116060905011a030708011a0f060d1e0c02011b0813141608060108 57
    0x100856010704a0140d60482040c004104046150359550707140c605000d40c4039102c0304210090340c4030780e00a0303155410021040b101e81c00700c0d209001020803400706541c5224207081000d4012907102802145c18003624440142408055034200c06940d8156120b01811003192554004e903009070502c5104500001c3c01800744962036600205600d09200c1003a54150100b6100d03005200026161204006400c1d0089481d1014001d002000c0c01495138442034a48076018100240c07141d00d0301c4408000507c140c07a44541159600311000388070b031002c2c3d058403100c250311404402c0c0c060322a00e500004c3c00d210600c58004a04403248030910000c82c2d0204202110300003191140c1d001001704008044018148207480259612100c00316001180d02131a404450700322642c1c40035a4100044c8069081c2c40940c14000813002c1c0c208a811501c40002c40810b50a0400004201c0e100b000d10710414198001005a515080242000102902d901c005502c90b80d0178401e0041550145490311035095004146 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 991262050 1250 991260800 991260817
    0x1801051003030f0e190f06050a0c0809040609090c05090601020f120a051228020702130e0f12030f06011107030b310201030b150904050a0f0e030a03180c0605 69
    0x1315a50a1082d80020701148000703071441410b41d2841020050346039807411100c000c0160307042103400d0241d1000b002d820230b6415000142500000a0581c0b0f541e602da42c050000390a10320420443c9011625100c078030b02c5c2240c06101d03c240340340800542103620020f05001101241c2d0060441c20a9801c5510b0403900051490000e024081c82903140c070000d003040640c4182182c813298000f20107030711010701c1c05004000900450900404ca0341000d81c8981091042501d840c080c005240e100140007117040440314441c0010074064100c1c3e00052103448000b6501424400c0c3e0a40182e848400041d40c060b08400000e000a822180c02000841c001c0c01c21198024841a08440c001404000e60b00d247c003060060b43c012203000c0e112680a5592501c101700740c00d00107031110f03a0202d00030300e1044594001c840a01e442243c80304000b8140c07025a1b08007a09032544424140100c0f2502e908094490b008806842c00082c13070711142d44645501c00140900701504070350349000507801e04800b22915448080e8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 991263300 1250 991262050 991262057
    0x61a0d0e1507180f060806060c1510031b0515070819120e010e060105040e010608010203040b09100209060d091a10090f02030c0417070e0405061801051003030f 70
    0x4010781048121440c25105212540d503030200c9204030804001d40c804180c016070084000e0301c106001c0c8a811240c1d864001c0422194070340c81d0450345031110328107410f00e0304404685402c0c20a1050505682d445041036130311400d4000d50020f12002d040004c41024419690f02c402c407404046844800310000700081c900801c401403811300380f000c400c60a0001d001c000700024200e0003032140b114a0350300c00c410500c0103d5009110180c10003890b10355aa4040c00780c02e100744c4c2c2d600c40c00708500000350b110f4801801e4481c025074807407030503003840d902c0c0403021aa000014052400141201d0280707100f00c0d0b8000100a225904103603c15480c0d01c024544d050007161441c465250301c081d0000e00d07500ca070307100e6004488410800f5040808002c2620400c0000d061a0750050080c415000c003500d05880903100c42c1e14504007800000c89245180550715031006100c1014203080c4004c0c0680481d00d5441810404510580c15001c2e980c8182200c0e02121100c0c1d0306e080c480c0d000e00000f8840c403002c3c540759141e4034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 991264550 1250 991263300 991263313
    0x7120525180e03040501210c02031b150c160c080303061f08070509131805010c1404090c1803060e01181e02240c01150e0a020d090c1701061a0d0e 64
    0x90500d82101e230702003510000b60703001240800313880c0740c40b510b0550342541c84005022401c5006403801360a55018042d44c41d04000401d000d000c01c110840e641c241c061b084500d00111a90341c0300240d450b68002e403a601d00400c5c2441451240c80250b81c48076002444d10307980c2d459140d894540450f8140c000340c200691010001002008181603400784182d034020307002d074500303c4450030320f086070840d20140c01002c14031001880d41d941c21300c204405d0303904540c0307007040104850a81100466800c0c100f0742003410410f80002000c01408555888400d030242c42c00000c0105212628441a040000101c0204a140340584041d5055001d0b41a0080c2e10310103080420501d00d05000522011540c5c40700c0d040581000c0ac8150310b10809018040c42d900038400160701d02c1c1d0400984116100c4010490306101c0c0e0002007a100d0300643d035010711201900200086e15054469508800c07518155020212642c03c0040c003143d1072108a411220250b980c4140a1801e02c3c48200d0364017800c601e144050a40c000c58 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 991265800 1250 991264550 991264607
    0xb07020a0b0d0524030712020a0e1303020f0c0a05060d0b03121806040e04290a090312050c1804020d020f09010906030c0207120525180e03040501 64
    0x49019140b2004001c5000c0740a10b0507004440b903240381840311208800301da60610300540c5002ca4130310183e94148041c840e03038035150300202c1c0c102040c40d4030000c840b107003520410201c84e20565004c2e02c0c0038444d5003940c070300241882c0c015035118001e018255022000030340810992501c00300600d20940e4181010401107034a400003810500009205111940d00080c40d00046d05000e101d418520004c984c01807c01d410010508140703000200018641c01d00c902d00d41c0308941c0111040700b1400b80c00c8a95481c0d900c0c0600c10782014022080003200410701d8010100400c5401d4000e6900c19140e04490038204560f6010341590072a40100740b40e0880d50030003261a009080340001e148200100045030380e121324010004050350b005a0000d4201880c1071101001c1e02d5010400c4012100e5090000d0001d440c1801d00c2c42c01d107951425011000080c00c04951440064191400c4c11035458140c4102e50341644007015041e103070603030226005604100001e101643c001c0715034102031030104100d0382400009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 991267050 1250 991265800 991265819
    0x70201110715030b0301150b1303050a1b05041a06030703200a0f0c0807060b060903010509061506040501080a27060506130b1c1104060617010b030906010b07020a 71
    0x2150400b591540741c4502c030760340058143c010454076407070075002040044840d500900d0003100d00d0140c0c0808000c0021005040106000c2e6a40950b4100d4296410010349241851030794490041c0300c0031841d0101000a60703894588074490700107080900c084000207046041040355030005140900349651980d000a0f8010b446040c3e14408409203041596120103e4010345900c4140c10f0000401c103d0f041c403140003c04450984254a078005c0000c10000f00940005141d03001d4a81075030f400d503190004009108000045080c01161b0b00789411200d0031503082801268402c5008150124000b180825101c2c2c0d0258003084100704404192000000e10100040700a80459010f440c0c080c0c07600e080c400d851802d015602400454184100400466036011400d00c1d051070b04010080ea400100c0c00c81800030492411030a080c00038400c000e019110800a4044260100101901070380c14002040303040c4400304403401400c0c2c00300101030980c6818180c90081d48444400c07a046101c014000603031020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 991268300 1250 991267050 991267063
    0x31a06060d14040605090708030a050c010204050d08031b0c0a0308090f06010e01080c010207030309050d0302070f08070e0c0702030c120705090708160306050906060702012003031905011a07020111 86
    0xb01c501040301542003e0624a05130752000e809100c21b5000580b0400025800004984120000381443c54888035200c0d6110b009000f5540402c1d00203000344002010054604010740c0f044070708060100340c0c1080034404083c6409000c0d218102a40104c0c01940802d01540c001030b07109107040c1c100e41c030901d501007506040c050281d000c0d099000506005100d031000a1002c0d03d1030b00403c0c8002c120042c5540c400411503011440b82500a036070b18803840c3d040c07600c00d008900c0503090034a205600c2e1542c03843d080d5603130300c1c1074452021f01010340710202d8881c1800b08101d54801c0c1d002070003000780701409020440d03250442001c51b0402c2c451110001191f44170201168455009520b56201a141c0901c68400003c0ca00301405c0c101890310505011503501d86c08001d40251058407000e40b5140d00c0d1005032610107044104488c0c1a50071100c405c0100d40c00801148241d91b0070444500c5440140e0189094070020f009100210031081b44500181c05510043e00d03c035801490003041c00030140c5003050a004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 991269550 1250 991268300 991268321
    0xc040e0304230a1505120a020c0703051f02160b10030f120305070206040201020a24020418060e1905040303091203090506092b0c140c09060a031a06060d 67
    0xe6040c00b810005142a81d000f5005001401c1e20850300c0c00100401085c0e07214000445d401040307000d02045400d01a80d0640f600062258102c404050312820290307991764005400d0210207500c0644068496054001d4440181a82003809007c040690343c40c0b82294004040009410030980d000011528a022441a55005410708034003000c40620040950720300030314600942d40648184030050340d00240b10500d013034104054582c4907554a85000142004813102003010740003080c085a440007641300000b0090269400300502030352000080c4100104a410001b140109031800800040da40c00140c0c2c024840d107000142c8040a036507404c0446820303034142d8002030b1390341a02010808200821074000003018020940c1d910203100b40344803800c20089401402d107a10f403240800c00c1c01580c83c000441d40c4408525502d0203244880c45d625000c505205104a96800c0170460700d040c803501020649800c60410001d40c0c9100c0105e00b19030601610080c0c0040f4100150541c0c03140902c942076000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 991270800 1250 991269550 991269599
    0x1121030c0904180809030c0a0e0f04021c08180d031704110a03050615030c0d261231110f0306010621020901300f0f1d0c040e0304 57
    0xf8005e0400349031401221039581402602c003150180304030480402966884160f1460b401459590752012a5000000c070119404441e5640449010001e50030003074000000a0500e903825160f0010030844020540e00d005000300d0031100d0409010800c20014550250044107442c01705148007000c1040c50009910507140d980010040c8040180743c80324543d59180708500504401040e000059808088a00f00801110004035103000c880e0300008518902c14402002c20789034081491001d0700017a046656001e40500d15868020b0030107484403422121a03280c00881290206590300c1c50180398410a8540c030800464111010703640070443d450283c10142d0b80c0d42412000104800507034035800c0081c040c0c583c01070001c0503407642d21040042c18084079281c401207003c0e0019092103850507290180040508110b0280880c190581000030000c1008100b00200d06010b89000c1c140030341060320030301030740020b4840600b500e415000b01d07a10035020b41c1942d02d45036803003030380071612070b0b05205a0104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 991272050 1250 991270800 991270807
    0x1b120c0302090703051005040209010923010f05190503090a060f0c03060f050618010512090604120206070801060302030603010e010509100633050d0c1121030c09041808 74
    0x210b040025480340c000780da50400b40854180003850079212040350064500680d40820a01c103582c1c880c0f403401000780403c0c030307030001070180b804a10440313100c400a00c03a0100e00703c0c020707400102d88a10b04944c0c0e0107405018100c1c07400f800c0602140d50f076001504100061045034502004282d052180c1c13422205808400140c0705d00c24680501038980035070080c00da2000710b00081003c1d80b2641c0c222214070040809600c034a44440005940c20b0060301d0002d207807140e080e4204210030300d0000382c050150340103415803000c8070900c0c681269103001c12201900011000c0004118aa0094001d150022001000482c0048010102c41c0c04c450080328600e0b003039480343c1003001001d5403030700c5610b001e00042c1e024015804165240300b10032290044148940d00c001d070080404091113a010303a201060030030014480746d0900138000784044806001d14081d0b01030786514100b01e641540c806841d00c41c003a40c590381555520300c6030008540081706000e80042d00d50806c41e0103501d50101014078144a1a2082e44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 991273300 1250 991272050 991272053
    0x1a0106120b031002161401020c0c0405060303120c22091b1b11130203042319081b0a0c0807060e060702040f051612060308071b120c03 59
    0x40c2100d1880d16a1085140c90004002901c0228000115580030100981da0320035140700d0302022a030801010700003411050f000403403848190020020302c0020f00807250340710300f104100801c0314016501c075603065004021501a080440741215401441105642e042c100c2145035840300b41c1000000010082d41d0113401d00000607030b44101944030100c6100113650700c0502102401040d40690107104070040b12140ca4100031610765002803000d8040c4c90900d46556200b4104082e40090300c08a5200e4180301c110124541e040101d40c141182c2240141100c0100303040d041c529412610007919400c0e410442406503030311450650b1040d0b207580000300030707110341402e00052400582e0804e0065030040701040140c00c0c1d10004c6040c4107401100c43c6a40d411442c40002c0c02402c4c01e4144070300c041e0410b800c21030305443d02028101c031000310351191040021046040d5044a5090000800e01441441100080b405454040c06e0f01c201018601d140140c13102209001d4000d581400c0740c1c0030382d05ca1820300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 991274550 1250 991273300 991273307
    0x150e1005160e120705030102030a0c140705070303051c020a0e041404020a150e1207050a060201020304050601180207142a0306070c0c080f03030103062307030b030a06051f08030315010305131a0106 86
    0x168840810f184a050000f141e80d8141c40312504d0c4009020050301013081030481a101041140b0000128030843d074548807003601030268200300100c680301d07600e0141e4100c105d000400449104a40c01401c2281c034a050250011310720009403456010000e10110b0001d0036160b041100d00c0d44040c107401046038038070f0032040001c28449034103d0021640180309100015000003010b906540a502010551240c4029400028050501c001d0054403c01281c075044020114501051405851481c0d40b00e0301c588084c0101001e60010003501030748944c001034200c034401c1d440600320714441d8112081042e40c50752020300d04801d1640710310320303600000010010420313188151158441c140c5421280c0c000461740c2138900450060580050580318a00c07424566024811600401e911000030440f03801e10b540c04d01441082c21407285030400500001050f0290000b05480c464460159084904c05900b00114041c180103025030003440e25078112200002d91400c00c0d920300c440f00984540c125890164000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 991275800 1250 991274550 991274567
    0x921090e0a0f14090f1501030b07270905130f0605072607030b040c0e0f1f020a060b04020412060b06122806180207150e1005160e120705030102030a0c 66
    0x320328592242150306c0c0d214160320b07001411a13401604482055803100d0381669180503002200380d01c2c54244640c42101d4a0035110702d004d032405014100010f51b40d542c4005554100c0c2d85010701200c1c0032496480c00a00c142c2c0001d5805811803428296904d40307212050300000140c501200c02c0019101007001050341846440c491902c111018003e115020b032000d407140305800381c4180902d000712810651a1103c003010032000c003801080c42c1c1c40700410344000b5140ca00d8150b04031141343c2002c40b160203d1410340251000e60388841c0c034586d032120540d9551001031000c10750003a04910140011071080d003080c0c007403074480c00e03419608080841c040d0800c0c1c0403640210301c1420a0070301d498400c0c40060018004a42c01c5000e0070001039584250f03050004030448500d0025001c1414090084150f14000c62a14000181440e080c00903489080c0b02c9000100400b2042e4000303a41d0007400e80042c0b500061074444510224183d03981280c071070020a003a680300301c0b010303078201380c503001c19059140e40300005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 991277050 1250 991275800 991275823
    0x9240b0706050709030206041403010b03060709031112070b030a0905030706090318081f141e09010b24070609080414040204140f15040305010921090e0a0f1409 70
    0x104d4100d504640c0010034501643c010a0603a07582621000d9843d1000d500c00c041c120001400c0700d14610b80740b03800410040641c081103420705031204040000c0c1c146028801d803400d5000c0c0140c140c1c103042c0795188103150001403402e51410f4940ca030f40c80200381d0900003000500d01403000442e0002d038504000c1c1501c046c01801c5064640e0040f81008040008a44406292400001c1c00c5048120580a0000e400d009050b1040c0d21030003410720510b441300340f0019484698075041d1900c181d681c0c441d0b80d403c0364002c440c03040d0410f1180501d05107461030380f0b10b00c55010100b02082400e1a285844031001ca03100580111151540000d0a22071882e600c520800080c80c2254158602414a100740d00080f6155040034012455504036460311313910401d0307400c6c0b0b010003800c030262219900d0814601909584000755800d80091242072085120941c650160079a907072104102e192811900c41c9034040c3c010040000c46a541c161580c9810702802490b0840c5001d06051485003040c844140c00c00340029070703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 991278300 1250 991277050 991277057
    0x203010306141608060103020d0f02120604240b1b0312061302040303050d021b0f01090606060e09070f030b041802030727020a12050a02030f0105060306030709240b07060507 76
    0x466420f651004000d5848002842c0140e20f407821403101c080236140202c1031400041c0041100e4890f00f64410555125100885050001241e000b41140300c47d40d20000141252603c24010b00402c2c40000040001c00b210203421a610301020701780300e0660f00040032a01d062003004040c00700703c1c40c111440003903d202030a000c504d89403071550090013074880d401c08165075035008100c04201c1240080d402880b800d0100c1a14046002f141c2c109000b800001c1d412500c10340340010119400d0712070b032003031903c64002a24050140c0c80d000c0c0c2c10790b170400ca0065010f0030107445004d00401c6440300d00940092001034544507140000c50b00c1050705141c4643c00c405c0291810000c20800c0f80800180d0843c2d1030550440141d42e4100e440084420b480e8903044002c0050610060295020042d40158031418101ea40c80c203090340c81e0010011588000d9880d40d41c1a400300405000b0300916034030502320a1a0401c1c0c12a0744e207804054480c2e03203d4641d1120200303190124024051080a00900f60310000b20315 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 991279550 1250 991278300 991278331
    0x110a0f0203090406151e17180604050a0c0b1305010804050a050d05040e0f0c041e12080301031209080309130615030212090319030e0a061109030f01090b160909020301030614 76
    0x5002000b911800787c1c1201c600700e01e10b02241c0846200041318003030306010002e441c01844c140c20800c1d40c0b61401c1c082102c0304140c0e440300241903950081956070303207000e0242104003940b40200448110344081d04c01e985500442c2c45010000e10304000b600590082030704c0d890745880c034102c0071040c00309000340601e4014100b482003012014944040314259000c42c48034810a80c1c424402003281401500440e401c4015020300c0300500c20040d010f14100e0784181d17101000c04482e03040c115003800403485000c0721380c1d00602c0a44803620f0b001c13017080803c0140d000000b072110f0f910015101d04070b842d013900d0000b00c3d80c0010404000d100a1a60940c0b008a203c015890f0a428500464034007840380640c0c01010b81c1c40d8a400c20714201805400d012580000d81400341c0c00ca52195030380c2c5031f4402103403d4031a00c14598001102103060141c50309194000700400d8180c0e46041d41c48030f100100c0307540b0000f08039a0000c041080181840607501a5002c2c0c6000100c018000d90045010360000d486a181d00e039085 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 991280800 1250 991279550 991279607
    0x50c070905151e0105070804152a020f150903031801110703050339072d031403190c050601240f051303030e0301050703110a0f020309040615 62
    0x241039194640801703181c580d40c0e61185040032855406584c0186210141041d03851120796440f040b0a07007101308195a418050030030103543c10040c02481402034020300d2003950a042890f050085001c0b68102d030b83e001d8036181d6090000f0f030541d8801c2051503000b040b050920781c0c455a2240000c15050000300c001d01c0b1190035522003075507070302030b0108801403250000b84080011940c030034100c3c1000f84481c400c0b220000c2d5a03081540710f0205008900d0500c4280300841c04090188040f07400c810010341f14030b420780381552140d0380d003696000d4442c042403000300084507405c68017120058410380c2c9a0b40c1d602003a03100d8076003142000810303032000d6132020f10f003001c0440e030000307a5190820310703205400c106030004140f034003e4440303010f181b0314210074555525000060603000103016410341340407402002540d640c070005400b01c8016246010400c1c100b40a6910307298021007000c044055640105c03070805982d80b0015003070340c1d0f550300a07001001307a1100c41d501403908449581c0d00402c400e468901009941e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 991282050 1250 991280800 991280839
    0x30a03020a080304150e0f060c0310060309060b0d08040e0a0209010e0f0d051009030e0402040b12040c03080d020405130b0123070609142e0c050c07090515 68
    0x3070040241c01e21400002090401c9210825031420900c0844117200b414803901d21a92201d4038600c0e40c2104e4011880081d46019039441241d04c06c81c10829425000341c103045080740145030f489012580141da4a8440300039540e50300e401d230500391045901560321030402103680924040980405822801403201c01910382c0c00842c945000d00302a21090b51303007901480010440f803120340c4082d0150094600c2e010101c0310541128034481e001c0d4079000c450005c040c060004900c030301c5c82608450001444400002d6443d000d0a50b002070103144401c0d1500d07100e0b01c403010654047e40320024641d600180810041c104110705018006400c44d0030841e0800d01e0f400a80b050380850360b02d4034142002c9001c001c1680c107900aa03803c0710f8010344d08020079049440d00c00355105061010310881d100360705911106a1800d044900306504110900941e10350080c12103018141c600d941c44207100007030000c4118818200130000044c100c00e200820642042c103070054150b07003803507000f60143c030703181d940030361813400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 991283300 1250 991282050 991282063
    0x160e0a05010c0203010b2d0109050d080f190c03091409042607200603010f090c090305011518020f040b070809100903110406060f030f1127030a0302 65
    0x1001c0c28041e645182d00d00c0041d0041c081100e41a80c000000341191a010b202d441c04100c41440e40c846400308020000c0042d94805030510420b0b62203908114020b0002d8800d101400e500d01d15500c041e8100f44441e0720103c0f0941168002400044240c11384000f41544003035100c00a242c581c04400c00044032101087c41c0c803034014130180802080040c0100b4407000040a001482d001c0c058094888280b031621200304142034103007042d03003242014045d2442c640303103040724101c50100c020280c41034139204e2a000509000c900e02c81c01e00c40c40001c0000411000c0c061034412202c8102d604a00318100000b241d52164214403002c0c1d124414811911400380c2001240c00340d0301084d443e2038881d512440c040c241486407104440e044201e10602003c081c5d040902d41d0142c9104512004020940000384001c07580d2030300c00c40d0005651108100311541c000e070300880c640c000a5001003240815508400102d900001120296126241040a5158200300e600708400b4046000e4000c081c034bd0b8500039038414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 991284550 1250 991283300 991283309
    0xd0909020306100e0102070504060b040312031116030221071208070516021315080d1404030209070c0c290f030f10270b0108040c060c020102010603150203160e0a 71
    0x2a04c42034000c080c1c0e0080090000824008000b840a0f03130300c90992080c2500325100c12601d04050061000307500f0300034001c0602581d04125003070b041100300e180100d1448031288080c2d0950007024103c0c0482c00700d2502c1c800b90010603d1000b40d85442d103250851f100b028542c005030800c070144050160300c0342c2c40022145540e8102d60100a00c0046d800000c40e2160b184490781c242c6450860501010110354405804075094041511004c0040b0300c410383d1450514000c00c1d001202c200014801071415a111039009100da00e00f070400c116090755403442d18021a000301002324042060034500060002c42e020b0002c403884600d60501000b0101c2129902028104100e010103007000500c04c64403200e4000014a06442c0e0200900c00c100340c0091403280158040015a042804e9000700394012514a8042ea40c45482c10341d40b20725012040361001c0c04a00c04904554941000101003018070300d081d802c0c401d15010069407070424445400350341003009412003e01601d4000a40503660b030450650464 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 991285800 1250 991284550 991284557
    0x3052e0618080304080d110a0201210b0904141605060403030528090e1305060601110f03031e060904030509040506040b0d051b06070503030a11070f050d090902030610 73
    0xc000d4181e1240018a40082c00310f4030000c90b0025a00f000010b42d280d8100c403c2d21000d2411100c5036078181c03651348616000e0b0101e00c06890707052002e80030030820000940b402c40d0010b50300d00c0e5803001404444042e5016150348807055040241c013501444244140e03c0e40c6030103a8011443e00380030860700c4c010752002500740b00f0085070705002030324407481044214515080c16404550700c460302a051061a010741c01002d40030800003802030b500b20480e000320300d801c14014044c6035030780e40044500c2d85a590f084403031409490000d4000d0302040000e540a5420007090340c2e8103919200c20903145803c0103094611814100003800f000c282c0060448980c1c8000703a401041e00e5852a0104000d030003242d5117141c0028920415001340130012450420b42200d41800034810301607070042210710300440301c001d0b000307810420202e42c2c43c013007552003024007461440c1481d0811107261510498440540c4c820f4070b09400c08a0213a6059501034410005442141070850541c2400b002190b081da51040c1d100051 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 991287050 1250 991285800 991285817
    0x2010e04020307090e04080a091406070b040203030d0212010509130c12051c050c0609070f090b1203040e010e0a0603330c0201020a1e0f0503100b03010603052e06 71
    0xc030744035100c0e1001405105c110099541483c1c41c0c035504683c03041007180005800024085808400300c002021640002800a81400d14640720000d0862000d08104c0c3d251208022984000965002420f52404051280c0b0025031401090000301007000f031050482d444805040703c0081c25034044542968540c401c0c044036003605103449450700d8680c1319000944480420951000b40d0300c817006054082824090301c00c1612103421403580d665090084d1514512201000c3c030225069034460160032000401c800c50b012100d50742075003075500c40d42003170383d80070140380050001019074100607811140380042044540e245464003e2203010170100b141d030148080004443c201074420f00d900d0b076003030a074108104219105801a000794002000100411200e05140c0010244900c5c0c150303444e002c84c0c0707808906c3ca1340f240c4115102e610042c509800802005004a640c20b05031025501811144d01c0009a908221401c900075a2040200205003074090304402c0244180042c01011a000c0c0d080200303c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 991288300 1250 991287050 991287061
    0x90f0303050318010b0612040221250902280c081b0f0d020601080c0103090803010e061804030c0b0606160602090109050301051009060e070813020d02030604140607030902010e040203 80
    0x503100c176413007040c0d0000001c40c1c0f034804c56040006280c041e51003140c003036060a11110015090b45000c28605403290014061000820309004000862110250142808588441d250b604030303000f40e10fa1300e4030b01c611a0303141c0e030784145a10001ca001c441e003803c041d041a02d01c1e81c0c40c1b0f42c262055000c00891409200200644204d080020700c4995181e282a60407100205400a42d520400d1048441034402c2d210807802d654017901c20000c20341e0b00950381078179503800d000141c04001c20280a0603002005c90042642d6546a888600d008a04c640d445004419003402e09001403000a8000d502c83c1600f0420a951140308007041845030b41d00203030168070f4207604070040ea40688540e002641650a0004000c0b010201c44140800e661101a08029098503035140520b1110116440004503c2c00701c042000c1c0303445040c60000c2c1520040491090b0305103540071900b01a030948045640000e0021000010b4100740241c0b58002403d04d402c1004c0b01c100c4d00001c00b0140114012409503500001140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 991289550 1250 991288300 991288303
    0x112170715020d0b041d060a0b0f0405090a080703090f051f1808010603030201060e180d081b0409051801020c03040b03100f060f02010515060904050a0605031c090f0303050318 77
    0x1024424000e05c104111002d00c0340d04c519001b540861000e140c006c1c400082c900d1411032150788440840036004040c0350500390706000090002a080083c20700c50810307044005218000200009882030382ea84403a5485c141c1070641900841d0826440b515403100310404081741d061200c091820a8030b84004100504420058085040e812940195081080100c103141d0150880412540440007499265454042040400140e1030003d00700741c01001e00c010150707224091041e0003241d41000155140d158106a42490b030050340a01c541c541c5640400c114180e0150100d90300307201610096103401c0c1d1a241154481c483d6000750001c0b49008004580005460749a0744040c020044080d54107030b49401001e44064815009880158200b200040802c2e042d0115144002c0002d0601400d0019500810000d05002410590925960340b0002001d03a010040085840c56542c210540d0f080700c40c100030208016500042c410546402d81000081d40c80021254010081110b03030304d0541050100f035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 991290800 1250 991289550 991289561
    0xd0605180706030e1002091807030b0603040605040203061303120e0f03040b131d041218141305062b0501060b0301210f06050702150112170715020d 65
    0x185603100d0000702140c0e1503096803102000180b02d41c01c4400f82e0a400000c00140d1045158040d040b03a0703c05144080c1e800c001001c180c01079070303e003404540e400d403880215107a0b800855080e01e80346d441c2e20503c011750500b4040c85400c000d038070310a1190ba504540300508220240ca040110b00380d51815088000c520074460000421082e0054940e15552810203541940000442401d0025840c100051003480c01c0e0480341d40c1d04507085c8403103440c0e959840e00303d00d111400b403000060066108011030722220003a5504050b0401400001842100d4030074080300d064060721684225181009201055981c8541c00d14270034100e1400c07028210314003860740c60114a140d40200340e9803d080c4081201c225100295040e40d048280c0c046c400a60b00d000c11020384d68889024001d800f24489000c0880d14907044035501000a00454001465a903600c0502d03541c00d0b4040204182c1a0031160b0801c544451483c1c04009442078040c00c084064540b40310620b11002070042059000614210f00c9040d0b4100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 991292050 1250 991290800 991290841
    0xf060405040203100510112e0c020706031a1f030e0613030320032a040605030a0b0a0806241302090f0108011a03180a0f050d0207050d0605 61
    0xe54481c04c0c0311821030004403550080d00d1141100703011101c041d52103003200c403458031a40c0004054940f04c030400c41c01c00f0100e040150182040c40c0403458011032650283c0910103145500401c1c6a40c600034006040b95401012000944984003009500e03070f072081c1d2001d526103601c0c0d2611100043d401400c1c2c00a054501c2c0c1210240100d01c00c0000e0549520000e5005501175201803001c04d080704084404d424800c40c0b415021401440426202d00b0140042403241413550f5044415040c4003d4000c01600700c4c3c0e000701c001440000401401c01c1c03c0b40a130703180d2000c0a55110f44564140a196611441e000380078200b480d605004c0300c5c045001e0040b002d018080080c0001c43c81c0170610900d14040d40c0000b8000e4001c10321045071882c90b51180422034100c522031a00354400c00f050758030220880c1d002500c1e0000612059030340107000e0b6030901440045034031500042841d801c2d035103041c90910b18800250380030b64009207020003654031480030038007102d50b004000044076a2000014285045003664 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 991293300 1250 991292050 991292059
    0x5010f140d0b010f0303080f0c040e04260904060b0405090417130f061e02070504020c120a270518060121021321020d1e0503031801020a020c0f060405 66
    0x85130b45041102400741d90180d6120200fa41d40d0b100da05100480503240880003c00c01c210411406041a00703080c0c100384542110f40c0340e122000d41c2d031001003400401a809403480098054540d140a108010040100c43c0c0b000341414039181c00900030100040000d840810500f01e0f002c003000c01038040302d021403000304c10340007d03540f00c0568002c1c07034919000700c801250240005030808512a8050b1420b400300780e004246941c242014880650031032400c4c00003d22944907203110200c01c01c0003030071101805075142d256207030728491011701c428148030144031500d030300c1e484c248482e131146014800b01721121072603400b55071038690048070200360600b03105a01c8000e1b644100c1d050151a001040c4200c40c508440c0c1c4c413a03031980300d540810491703008034030540802a1043c030014288015041da1890041c2c04c54210030060001d4004407002016040703031030750400002c22244003030101e42400c806031510021420884100c0010350b5580070114614420848001220400d039103410417a4041d11002c1c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 991294550 1250 991293300 991293323
    0x408070f05060c0901030e03131a070507290705061515031e090c06040306150e0403050c1501060804140c0d05010203090118020109090c09031e1505010f140d 69
    0x4481d140700760006031000380003074200840c0f4061f0b21b1001090711300d452a220706100c1c48902d40390901c2e041414680c2c0f9843e4200050095001155042c40000000c0241000c5034187c8115072807415102040100c40408482c2c00344601c0001c181d0002c0d42a41c446044100d070b48212014900103401c0701d0300400e041d0303440d000000800006081e85a80e1a9019820b10094086600c5280c15661174100e01e001442c0c00032403c1c0007c001103003807500014086180d403907081d20415210294070310b10050840301a004104002009401207004000340094042401004c07101941003c00040c001074015101422186181c848140803070030510513a0b2806c0401452986103081c5440c101d030103500200ca1001c01035184c0500b0007802120365010318800c6505039980081a03082402c3c0c900145640e01d600410000030840210005001150002544842c16001112072278141ba00f400d00c06805521000d802c1e04000040121001824031036099075408100c4403a85911000865006101514007410b10300409 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 991295800 1250 991294550 991294561
    0x90501060e040e010c050f0d09141e070e16020f0d0905030c0a0b0a0c03020a0f0b150103150501120f051f08060402011b0807050d020102040504060611060408070f0506 73
    0x340040780040001c1e14140440c83c0d52240b01400c07500e050128001040301004003140c000d4000f8000c0a042c1285a4005482340d0303e5250340307024580507102c8900d00c2d40440003000d061010304554034a8041c4000c000c24026050044180f01480080c0448041582074528403000320300034011203210303056200c12507441ea080d20300014402e4104c0c3c450a030190240c20500550750404104003010340d5070148400e854070461340b104542c5804440f0040c0e08500951102400080d10009851485030040300000f1480c10300c0032142c080d1b012420300d0a8149881c010807442001281c01d8400225071003403c1ca02c5c000103030341812002a0492182c11700b0880d00c2c1c00c2c20400302d840c850b05002c040f560f0044075510b500c0e45a4441e9a503601e0261800b0f80441c42426014441074501039074120160710640d041d80c140160f81c2d1340c891030480d5003c2c140c00581d402241c02d00c440d08080c4900001490390f85005000d0303400c1c04540646400c0c0213040509101c034002802c60a00846031540104243d0200441c5c0c01450301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 991297050 1250 991295800 991295807
    0xe01060515040e040f02030f060c19020d09030303051005060403050a06150b040509060105040b0c0c1009050607060f11040306020304020406060309112257020709050106 74
    0x5000e40c03485040800c1e024030404484400381c2c0c0907076002c440c0740301c096201c40d11000ca0070381c9689001c0340d15110320158201c0c090000e002c06030150b07280024031031711222115140700d041c20707401c2000390865011034400a01541e00a4202c804c50390181000141a1103070781c1528809006a0841500b1000004001041180000e800243d00d8001c070000c001407800140d01c851801e049201d465452801030209019604d0f2048046405c000141000c52405582e040340d00c030690004000d201c0300340c00000041a4a0501c5a41c01c42141003c0c641009018104000142d8034000d503000030700030135900e915090f031007042ea6208600d69507184200c00d4a4070380d0f81c60914003952048500b02c2c00f882c107218001440a009009003101c0940c405001250b065031a0144138950800641c070614488184501d0017140c4500c2c4a001c201c0c0c0080b0003440341c41c04a11010148007031304480d910580241c0245612110003081543e0050090110450b03200011200c2080b80b030144d00e50011400c562810000081e103c0e00b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 991298300 1250 991297050 991297061
    0xc0d050f10020c0304171f091203020a02030a0c110307171002160201081b03190501051002150403050c011b0f0c02090129040602030702330f0d0e01 65
    0x140e10302207070244968a56a2000e9005880f603e5181d0f5105010500034031906c810344d50044c41c0310000f12816140c80501800d42641984055880c1c0c0e940c41c42c101d400e1210f00c02c030359200000c07141030662400c1c0035010000c2d9603101d04e584100400c44000413078010000c03943d070311201c50306004040364292525240c141100d1180143c0c00c1025208000807500544114000d85c0c00082d03d20f0b0362248199040d4005444844008102c9050703c0c40000c6a400340a4188015601400a40d0124001c1d4105480c6600848030f041e0451407042c640560030521041e0b0010744101c503c941c0664002591f00c583c60103507042d004240c07100308294249102c007070f08480c00f840c0c10640040310399100c11803130220b0b42054a91524621010b5041480f00700184814000d5010182141720501110885c01d20070025032102e90308140c000c10016080010300c14198a040840511707510451031140d26100c0c940080c558400780800d0412684582c01316440103910141c03425a03900040300c036024444e00d09440b00b03050080c007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 991299550 1250 991298300 991298323
    0xf0f0c02070f060504030b041a190e070b040b0702130203040803100b0a02100c020a140708010b0109080c0d060f020c010b01110d020606041104051f1716030e0c0d05 72
    0x2040101c00241045070310304400441c2c02c55151546814110b41f115604800c000700140c3d542c15041c20441040e41d409c0d001e0b644542000e6401900425052a141c2c080c1c407074040010340683e01c1102c4c180044149801142d0444007604191503841d201803000c1480c23003400c0e8840f10700c2d661000c42000144020180114440c1c03017050586c170b15150700d0b141c903448107000e00311104005078065920095016200e0344248001c0440f401110351481041d610641c20101c0c0c038030540c0b90fa8100c0101004a0700090050300200c480c00d0070314000041c102a0016034804481e00c40ba4842c945131502481444100c0e40002da0810502100707569528a4100c4c0c1400b90040d110704900258000b107a03604244000f15001d00c040e400c0d0760140407640c8401c02004082e000f001d1108681c608100800505030f07440e29020906600c19400640c54a040f40e01d014001200502c1240c02d01303001a400c0018500c44820075100c240164100003c04803c41a0034924104100303a00f20340001a80c80c10500340140040c08142e8030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 991300800 1250 991299550 991299553
    0x6010626040b060d0c21140319031509050109140f090a0314040f060816090e0402190806010603020c0f071a030c0c03030a0f0f06050307060e040f0f0c02 67
    0x405122000d0030a038101200c000e8042c0001c0c1000c00c2c031a14210b070118040b240100d08805070a40c44040902e48004030203034103000e81380285034071310400014501034101c215108010714182500d4441d5941c0840181c0100c6007015a1035807002046c000840214004d81201001001190784810401000b06500c020701a0503100e90400102e80201107a0014441d081610141800e071215a4055805d4107015540ac0c092440c03d100110b1112101300c0510010f100d01d940e811042d00380003030012400c24021501310304101c4915801c0c869400c0c2468034a800c568140d9200f020a0181802121804107540103a20316001d010300000303d8030780c160040c0620b507914005440c0790856441c1100c1d40d03840903226000007600c00030041e801c00c0180c1d40265a00814440c60540b0b4031400090706400c6038021a60040c606036220302183d0070340035911030700500b0f129170181041840e040034006592955030388544020403c640f40c801c002612241c0005480c10101001030042030100340f10000030381080440c2c407005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 991302050 1250 991300800 991300847
    0x10050115080f07121104030609030e090c0c0d0806040209040e011a010504053a050138040b0a0f0f0e060604031e02120f0a0605010b0a080a0c11060106 66
    0x18055201c090382d000d04030b02d446090302c0c03010b90848075005e800c0001e039000c00311409000000c042120b502803421624401d64034408800001c02c2040f056900182420b481200c007404450140a0000340040224445042c41d0940703036070303440006e8043d12030500d030b858105040c00d91041448205401902145103090310721455a01c80200448640c0218450160301640d064516030701c41111441922400d008080c000444400c100d008440720206840300302c4cc240c2d0b6030b02c140c00d00310a035020f20b6807841665580b50b450030030b5a4110308110050360784403648141e84c0d406ca10b80c007035035440079408002d1282e50304141001e566415074058014452040000c0c546040300061013625100c021581600d41c404400501000c0e81a0104800d801384001281c00100a846c810500c1c10100903850510004e1001806003148a24000007980c40c10ba1010b81e034000c09101014030540c0155031b00d98032400e1110005141c8464840444181d1450450401180681800407944c540d2181740b540004a07544403000b403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 991303300 1250 991302050 991302061
    0x50d09140625050d0506040b1509010f050f030622061e08120708091306180e010203070f11011410030c0b09330d0209040e0c0a06111005011508 63
    0x40030388410300d850b0700007041009110302d8200d40d64440754004034013a00015108180c1800300da500503010701d10402c01080811012000c0da0b002e0003180101c2c40c1460290305240881d20420710500010342400c3c0310302c403290150b080000b03072414000c803498000d01040c04550350b1080700c0710700f011424020b801181400f86000c10095000211a41d0703864903245100c0c034102051f05c4113107880e000743c0211355000052800541203c042401490090001c0e420091500420015182c0031070b40e10340c4510704180d005100701f00005030440e51100d0756503002c1c1003e41001c405003080310700500050452200c01c60fa4401402203042c0f0200c20003060b40d114492001c1000d445008500702c074015107413042e0744001900000121014013030443c2a2020781401600d1402030180c02c40803840d001041d0b0030600a502052a5083d454103020750540e15140c100030700800f40c05880032a040011300d015142c24010341c1c81072405600420400814138100d020405c000b2075031920602c1860b070340c0551301000001c2d540d002181 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 991304550 1250 991303300 991303351
    0x420b03122106090403050f0c0d090801200306040b040f020c0f1e060c0a020c030106080327030a0821070207060f051227010510080d0c03080403050d091406 68
    0xd0180900520180c1d8a1303032a56402c4815500c030350800d1402140910594440d2102001b88494642103500d9261100d41006195403c484c4400400300d210300000d40c4c45a4284031400c101c030380210341038501168070718254004c180501032a05000790312038070005211582031004a40a1400c42070001580c541581422541100701072650103000301e90404400314546403018001007403100740b180151644103501c040041e01b141e549900c12911a040000d06d01d05d040400c080c0300208034036844404100e80d451001180d526205440010406040058400d04040486010b80141409440604d92625003000000e4407a10141f0a40c80030400c14007140800340d0240040d074242c40408500c0440c01d42d981190080c00c01440343d101460312042c1d58403400000d0080c05170521501c400c188900481e0b00d0f000c0400c2c90110508400801c000e04c2c0d220590000c2c0e0b0000c0c085400940618101e512014818100c00c01000014001420070a1090110101400108180303120746002d51130000d1501c020350828 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 991305800 1250 991304550 991304617
    0x602030709170601060f140d0e070839100509190e13060204090e070305150613020906250201020c010806010507060e0c0319420b0312 59
    0x9800b0350042401444510320a20045844400c1341c42c040d0105219041035081700d40c03100c50013500ba82e440d41001d40c034440742080708c040200200b000800302044888010110b5607000a15400d5982c1c071b110189841c1039201e40d841c43c000da0002c0c0300030300203c180d500141c19540402100b80c0180300040c0380046a040c0710b4048422509003188e8041d071581c1c1c502c2e8548800c961036804944080e428000800d180c17091344250b40b582642c450080042a046013081d600d00001c001c5248080b92440d010030426448040e410304078600650f0001d61289230f5000000e515000f403286000451a41c0003101060a90301540c84240900030380944207840b0000e40110b1f460101180d916004c00e071b04110020002d42d49a04c582074051802e01510070f800d070340100280c02d002d40f0400c05948a101603140200380100c6900d0101c0062050101540c40914021002c0c8004018601d80070342000c1051081e10300303841034000c14110100203099403100c58041700455000d822000202c1c440d03207284038581c6940314409095 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 991307050 1250 991305800 991305839
    0x80d05130f0b040b16060507090e0f040503190504031209090e01090c050613050306071106090102030601020712030c1b1a2a0f060705030411030a02100302130509040602030709 77
    0xb06283c103003000d680e0b01107507000100c0318014181440410300030400500c5594010207032580d4180c252460020341060300c0101800c130184402800c814040015000011209031540008080d18103000303402007900c51f400303560310240840c0c22040d41304c1641c582c0312400301c082da03e2142c400c003e0301e801300490a00300c40c24080d0007041403404103000c0c0420328002c80640300341c62204001b1034070302d0b442c2c00c0803c2c01d2690a50703c00c404180244020440104148026075011203008002c5056290040000350303194090b10070302010480c00f03403526041c140b10b42422156590459000000501d0621005080400c944103196000e10081030910303400342c6d64400c035060440300b4403810815040c040c803948818061081d6410301031041c0505686282001c1c090b0360b01c07038040350711740c5c81d00ca03d014249458403000c0459694031039044608800c0050343d41050b00b00ca0400c0f14540103840e03103038683d6280103e20f0581c0015611480c14010001004880e40007948540081c1e569482c280303565103000c101c1300948480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 991308300 1250 991307050 991307069
    0xe070c050a080315060c010608060f04051518030309060114240f13150e09070807030e0f01420314150403050c070b0901090618080d05130f 61
    0xd6004076695401079904031981001101c071007a00384001a94942c491b6400103c50f0751900010018403d003400107d40c082c103c1007203004546000c0e5a440d403584403e0200c44000c41040000c50f418101559031b641d918041142165941c0c00e0450550703070303104ca09108400c0d20210b04020b202d60703410001184200304601c034621007507070003120300c0020140d04103103503000c6810014002426402c070f400301c2c200b005207022203601400c840b0402c001014903074220520350050101101b4820351a80c80521260300c03201c2d501d030005a1400c44042c03142000002c4215808a600f0859900b507480c00740d032118912403036000084e003040c2e5112082e210446082803090010490300d601e041000c18102c0c940f041495141c4c0c4162240a13804015002500c21b0548060b00050400300b0f02c42c0d4034010410011002d0125819803038108091580001c0c03401c14640501d0003000407030040241d0400c03010089030080c043c160b0540d6942c0d1003c0384000e0403500700a843c92982207140c40d002903a1803010720000c0a031540c804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 991309550 1250 991308300 991308313
    0x11062701030606120b18041a090601030f110f0312280917030c0a0303090b1506090f12060901021314060406050a1808060a060602030903031b100204060302040e070c05 73
    0x152a0307001841103682494100d2074040162554159000c1c5483c0304034800c0342d460030400101e0b03182d10f00c0004020161271907580100300610200d022001a9100e240d80000b580c09480c01100104685603401c000407901445070303150380704048103464090026200361110706080384a54041c041c998803200c2d5216004100c81c01c0d804e0102d00e80c00c5c94000c40c0d20841000300d034a461710304685580740c40c001c0e4a05134002961501c0302401c2001a554480d00300c2812400200385003025400104140301d4a15803038880c811900c003c0740740f41c6134150300c40c00e048404010750795107103054010140070758804040001940300c258000301d40b003607410070000e640e484098007860415080113420b842c1680403c1d008020310445110140000c00900d00200c06844584050903045c14281401c400b6505c0d643c1100007550028000703880c081e03c00006403240b1400700c0561240800c2c00891075800d18141e404294242400003e01003180d1350180c00900841c1d1041d0713031840d119030b28400219068521448002d040d900085e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 991310800 1250 991309550 991309577
    0xd0c0519170411030307080d0b010e0f0906130b0603040f060606090f06050325090503211920010203041109060904061d0d0207080d14030106080411062701030606 71
    0x1078403d8014210203403c99151914503101c01406030400c0d05005551034035070381c41d255a568421040c050704802980c01d61220f00c28000000d01c0b0030030080c0305030b028591507510f01d03091085641158480c0000506181d80c0ea00f40360800b1241201101c074180e03a0107040040000e03001d4820802c48044507012005086168204801100c4075800500009141c81b00701d10b11140041e10002e6461078920745032078442d07a040c0380c0320034141401c0400140740c8409103100d40e0300529a009008441501821810800401d488180180d40d0340061001d040e0011100091150341d117801540118001c07405840d810f0440c540d40c0041105030941282c40e180c000800001040c00101d043d0002080c01c035a042c00c01c4100c070040f10780a0b240144c14903440340107a00c01142000310302d0081c000303c07555124a2920110513100c1c0051070003144010310a40c01040081d42c0010148000c6c0140c001e034222000305696a14906480c035020b007c0308040e42d485c41c0c44d88074010980d00d1340c083c0c400c1c0b10480e14540c43e50421410407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 991312050 1250 991310800 991310813
    0xa090606050a0816052704020406050405011404050c0f0702010336111e010e01020a0210091d06180a090c03060204151107060e0a03150606081501120209060d0c05191704 74
    0x47c00c00c0f03070402c0c0c03206000b0607585d4a50144902801c499a41481c04e103905004000623203001804407460200e081200044441945040b9a10150207007008601030344104e103150b51201ca0400c0001c401241c502040d031100d500030566002c458000c0c01c521000f8401d9030100320600c2c1c105c0504a1407103015074481030195000300d001c85650130301401640c3e4800040d401103a255088444c1e00400100100c0091080340030119107843e201004c040f900083d40b801030f010a20b2039044030304010503005074000040f01d400f16034200c0200f042d4010226103040d41e8074601880a50424042c103440d8485814103404481c4c4a000d81008030203824009050062a0040c00d8400403c0d941815400000e105004400708040f50034086840c01c0e20040011000c0c5404001806e40201905c8078074495580c081501c9070f0381e400402c4120340a0414401640c815900740002d03481d02c10001c2034800c0700c1c10141030302166900080500007413a100450211031b01c60218007103c4003040c01c0b2486d40403595500c0400c0c00f084a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 991313300 1250 991312050 991312129
    0x2060c0901031a03010908130f03080f030903041205010b090604050f06130917040303030b0102030f0d051005030d09060909020f160512132c0a090606050a081605 71
    0x3c94503240c420400e41400401d00752850001c00b52042c00c1c0c0082d07a002043c0350060024014411381041c0c504083c250741e1008120f00c00c80241c1c0d41801008001300b40070f0030040c41110000c3c4183e44040c80d0031840d070314202e4082c096400100c1d10030010100000c1590406001d2248501d031401c0d10f09a00e03607105000c0110100c01d401d111281d1a50f18203081001403440300c000030700740d402c5100b69916545140350080030b4546c40d070401411508144440c3e580d0b62000c80985d41c00175200c000200d0301d95689098480c81040070791015a261290103ca41007294000c0101ea060b620599030b580303c4240c54101c0501030348180010764804080c10030861f04048403d06070180b0051240d000d03039051140141c80403039560040345c04c0c5007200f1000001040140ca020401112016090602e010b243c200390260045a10006203240c03d5070703441d0907a010801501d5482440542401488141741c6234455460641e0307a1101c0ca46040b1403c912000401c1d54035049403a401d01c06448580c074500400301c50080310203500f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 991314550 1250 991313300 991313321
    0x105131b120b04020f030a0605010306030201020a0b061807110c09090c06070203160e16031b0c14031803060903070c12060e071d0601091a070c03201002060c090103 72
    0x954400d01e005283e0f850307000030401161030504250300d07810001c2e83e0700d04a5031542e20a13814181b40c02c0003080181d03000704c1d11031f15040d045a0f920b8103503600c81011071014207034040c402840c2080c040c01c01c40f84c16003008000d005449810304645c00c1d262514203100030110300341c405a49540c070502c5403032894a006130050580324400b0b42560802070505010820521281d0452032000401404101094112442035203000e256840c0501c0100c1140240003c03545100355035500700300c04031007118180030608400b030300703c2e144940c200d03656110a642140208010b400d602c603c207001c0c0501189080000000741d80506800901d4026803d180402448a0201c0b06900701d034040c1c0c48030014a11880f060008034010041c50743e102140c044050b49082807041c00030140340c18040c0340f40d01480900b129007103411b2170401601c015030303680b0040d0034071a105012580c07008149480c4144100c10507000c82c1003112000c102031b00c6a160614136402c00ba610b40c070048038101a44041444003000300e6109401202d0460b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 991315800 1250 991314550 991314587
    0xc0906030f261b151602060c07201f081803040b1209070906060e040605061602010806010e03061305060609070509010309020a03050109050604030809030a052215080105131b 76
    0x4c918440442840749021210078603280c82415542c0171842d01844040c0d0710149841505151851540d02c01c1c09002c1c40c0802130414950350b0f0340f00ea00ba91548010000c1c083d0090752064512865560000e0038032100302d80440701e00c0c945a141c1d100d850b000000303682c140c41543e03850506242802d280c80440a00c0186000a1440742c9400000c5a24091003648007170001592407203042c00c0800117010661382190700060003a2400c10440d100e2454900c0c87e00e03901d039070929280b15181c680b0001215205032500040340e00d802000188140c01d00f0800204442d113200c0c01c02d540b040d0740c3c0c1f00d081000000e01160b034540440c504200090a0f50310030b07403210402510007021070343e0654072a00c03402c1c00c5030070480c4119800d03031002041c0b00615070400340807030348103a140008514241e04541d0050090141e03c88040b181c85003400303040c4880b80480307003000c05003a2141d032411194682ea0002080303903400303100340c901a001b00d48800c1d250601a010b51100c00c24007030703ca05c1c0c0000001c60100c401c00c40ca4a2800000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 991317050 1250 991315800 991315813
    0x2030715090b0903190801081f1d0705040b010804120311070c0305100f0e0d030b06070b07020a110d11010e012d1103030907120c0906030f261b 63
    0x2c5110030b4190107402e4100056440326a1500610100d52008039441c3c180483c18004006120000032a03400014048040500f901c90380d8aa0700c004c1c1803041c84807081001c00305541c021850340040c00130103c9008031010301201186100544440000341c501a103103140031582170500d10b00070b821581035450f0040015203014070503103e00000000a410885168119081141d0134400a000303d001d130f01e0402e04101b010b800c0003800d29546802c41c05100c814142c903015040d05d41d030303602416036040300d421000b4107800740b4244000940703a205408003110014800580702e606401e00c8600c551034035034065483d10a10144100650302400e81174000e0f41000000e11036080c05c101104403c40360f00c1c0b0708000607450a600390704040c0441404044842e8258070602c2008a02140003030171408840140b44000c540d4089820841d00500c0342d50000c021950074004000208450646800c001034010580d00c003a1182045030704094000d00401103003036441c1401b0700c0f01001c90340003100e080f07a500703501120072 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 991318300 1250 991317050 991317053
    0xb09100e07170f0906180717070f0602010203090712020d154505030a03090203030708121b07050705040b030f150901141b0702121516050a0203071509 66
    0x74255045942988841c00d80c0c0c00e0281d214020802c45d0707008400412024116910390b45415038900040c0300c1c1c60310803807503050480070840f02440030102901d2003540c20850715841d41300c080c0c040c0d442542c280a10344200000000c04d400c42c40100001d195004181d2018442151180c1c1c030300c520716802149609580355400302c3c2c09000d600403444010382c1900555a142c000c06000d10300d640c08002c00f030901d01407518101c00010804412070f0b514409a0a00140c400740714000320b455401201801409600006a4180380d02150120140301c1c8241100322805203058640449a0b805580340003440c076801000188802d00e02604480f1005501074120340c104000440c605103000081c9112109040c0c500050041c030301003e01070620b03048060f0040c0e030300904110725104804202c11640c25000980801c2c118110360b2081d50303204840c440141210303109904031140050070345050b82c8070707448036082c002d160701c01350300820a681000c1940e80103503003800380d161103000005444600030a1501e640302007400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 991319550 1250 991318300 991318337
    0xf02031c0b01050d0f1b050901050d09140d02060114060c0a30090510050325021c050c07150c11030a0c06110c03060103021c0c2103030b09100e07 64
    0x403001c0040010102c6d40382c0d200910041d07000000d04070401000303003c10074400c1c0e998120303040740c4841e0791255001070720f40c1030f0341080c10500e1034410503440180141e45900c9601540010300c070341a074000891402c041607203401004071a21410290300142c0d0040c5104501050048645c8160104060b07004081f01c243c1c0a40038004040040c890750100318091028000d80c01c0061000198449505000349542000c5001d0646c64031410700c03038542c014159405000d428401c0c042c508006c03ea500368546810703036016024000f070704415515000c0d8811000700182c4503444203068002c0070100c1d1195400e103041d0f501d500f2524072030151150327007600c10840e410340007585551025000300556900d8003060035108a04509150169040c03612941c0240f0050001d0380d2160280912080340341403200401c206841e10036210141507100028001d02c1a00c43e00007005003031001d5054501c20f40c3c041117504502020000312810503140b003030040c0a007001c1800003182c8072039450f4010f141420302c1860003840c1c0b8000d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 991320800 1250 991319550 991319561
    0x60f040b0f090f030d15050402030439030b070221030703020c0129091e16030b12030d060b0c03070807020310060f14090601020a060f18120f02031c0b01050d 69
    0x1038170010b07030300e45094480f070398004208005010304403001e5140d4100b80c0c0315a450400c0005425440803401a5031800b1004103c403031070300d601c0700d400c10002055944e0030041e189400c00c8030703800d000d40030304031488484c48621a1070504408243c00e90b1400d544a9000480003504150704601d50f56696040c1040c1c0803901540803140c50000200707529855482405000213120b01030f01d004500c02c440c0e280c40c04503121001545910804103440e00350400007100041b0b0140102a560303d42140c880ea465140030f40e000310090200b40d1110300c051050a980e007441c00e816200d0640c05d440c25400030700080c00029000c100400380c55000504503030900c4130317241d4100d0407038025900042d0111030090007048641c4d4400703d08404200100c41c00c0d61145003101c0040d446030301101c00186156560509002071900503844109000d084808001041986161401b134449201c00a000814030501c1082801031002040391080c0020117200c01d6106107404c64040600031024000d414041d040c0016150116644540d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 991322050 1250 991320800 991320817
    0x403050d02070b0a020712030e10030606080c0703021509071d061f23040807030807110901031a04030201021215100810180603050f0d02060f040b0f090f03 68
    0x2400088140d42000380c0350001d02d603c260700700c0b00148440d6610580200702d00048800e2034a038042c0d0540d0501d4101c52600a01400503440140135561080c0fa80d410b034008425141c0356201d442c02074480840e40340090107201c0000b00140c3c031440b5140805507086150326000044031080702c00720b5407a24414070040390981e0f456070440c2081c0080200510700040d94441511141040c0010301c580882d008200d0b149141a04001c8011101019149001d000c222802003010f030303050300d481c1901c034074014141d07500243d81a21071031440034620f92246040381106040326840b40c0e020f2021181100b9032488040c1c02030045c0c083d55800d00000240550002c1c115109003008902d00001c5d496820400422890f054014001c02c44410100b109000300200000103540c0c041c640d900091070f4450145014110581005280380a100140c05010a00181002c042003194090380c1150b514005041c0d00c0362001c4402504580a403c0864003141c01c0c0011a50848248030680d9409c0c40c01d80e44440ca1588034920 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 991323300 1250 991322050 991322053
    0x703020a030e1504060507030215090a020f09060a03030f0504030b10230a09020702040e03070804170109030e040b03010b09010b0406200a030e030a06180308130c060e060906040305 79
    0x2028001c041d401454540003040441c0d0300c00285415030542440d074021405900c0a00c140096031505150080100c5580f58601e1500721a046c582181c9098a521020320124000c0c01141c03015410f525061034440d109410240503c0d07002c51440c2c404440d84500810000c0c00c0c40010400880420701410145d84a000c0d1200304040c000e2400501c55a0b00701e42c0c07481040f044400d115800e69542c0d440c074030b80d0100c50003954096100d1f00d150001a00400340c25a410500e440001480810014a44041c00441d0b203140e0704164424600071a0341d0036980050002400954046100d49203131a00707903c0b04000100c05400021020100404918041003e0308080e90044000c82d080040035400035448540130401c010a10342c981d40f0841150351810682c03002005e1054a00c3c0062035904c1c10402011400d422032003d1069000c0f00b0764a81c00680101c10a5001450180019040c0c0e4400b40f4000b0820754407203c40c12006152407400c0300c0004038078004960001c0100114120340e41d8a80180019500800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 991324550 1250 991323300 991323313
    0x90803043f2a020105030a0609140405010605030d02101e09030c02040e0d2309031204030b220b0603101a180f18120a050a08010509090309041808070302 67
    0xc02409600796803041d034819850081e00d1420150148400c0030b0708903420300301075840c1e807a00713010704010b4480360f08080801403501c080814035500440540d801507019500130441941c5503424962604069880103025074080c0000d170890600b26400022144141d9101c00082041700c010402900c01d117140c15400111001ca448055150900c1100c619020a00041070700041c2c00801811000d180902e840601c45001d807559500310043c02210390303d4000505880441200038003000d49034115001c191461107165000403080b44c1d030780410410075404c21a07594a4074030141d9982c0c07500f0740024a02501405802500c00041290303001d01c407906074008400c10203031405007091003510100c1006280024080100340286001030441c1d003500440d03405012030b155242201c4103441c00b8407101210a01610010b40c4d4408140d200780a4007204402e903444001036682c881c1044180032069410250b60380081001d00040d15242e4000c0c0c80c419940c0c4460340417900103407640600340d040054141c000d85c0004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 991325800 1250 991324550 991324673
    0x2121e0301090f05100501140c030405031f050709060e0f1201051504050f1e09010b06040609080f0a051b0418060e150c030f13020306090106050f0409080304 69
    0xb130045507400b089080740240c4072440c00c40020b000107000310341010b84032070000300240800028001c80300503001c040c3c01c0303031202404c00000c50700c0d220461701a042050301c0c00300401c080c14842c6d0006001c4420035aa4407840d1000c0b18104030520469280c022346c0245400348400e01003401307010301407086001c207918045550085041c08103480d4000c01c000080648841044624081800f00c14541a00d00e44449190b03628410f9150062414418240e4804000b01d800110315521911600507100c4101c107079050000d0b0003155a55030008001c008040303070460362800004410300240542a42d0004002041004c00002502e1100000000c16242a625458500c18a4800708608100c101d00240c0300c00c840d1415241600035400054950591516060007140007039441d019100ca00030740007801d581c0c80e41400740358540201041e12545004103062220810107203000d20a0034642504580c2c40c0386590350700d680345002c000c07490292a17480d80500c0101902501229410b80d44400101090724020b1001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 991327050 1250 991325800 991325831
    0xa0507031802030703061d06160f0c05060f0705040504020d021209070f0b0a0e031911030c060d0c05071505090c0418030c230c09060306040302121e030109 68
    0x60700490303407421903100c0484010b8600140c003508480d08001c001810746044025883d94103400341031032009100f00e1083c8161000b0300804c1d820701c0300300341c3c550f44552001e544040d15594613400e805821a00302c807001840c41c06c8101020f6502460307901d0500d15258541c00000c080b80c1006a1040f0096030219800200052100105400a142c04010310301545446c1410700601c64900800440000c08104507580d01c0c05041400c00105c03000b01601c1000c50702046003401c00422035400c0d50800d40305070b0700307050034103011175011441d26020700450703e8914090511b4002d882440400400c1160411040c00801e101001d680c0985002460114050030500c081a03d014000e401c8580310700c0c40c05420001110120b02c00d00300896041c204002d0f00d00403410090544c11286038210303910700c4200e4450058000204125071000300845150205865120a0503600e840c100d400030050f0740100d001410703c60031036000d0301d002c140340c641c001c0b4100c004518910107a002030b030042c0c92a0752615880c281c82c540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 991328300 1250 991327050 991327061
    0x911190e2707030b1c05120403140709051308090d02060403030206150f180a0b1e03100507080601081005030307080c0c030a1104110705060f041b05010e010f12050a050703 75
    0x2d45010301c90b1034240c00020305e01102d00365404d8503e0800101c040d0401c00f00b071110a034005050715101d03803196640d08091030002d07040b4800c01200c0c0140c01c8003069240c82c40c452540251708402210300c1181c22940c135010907038081c0c88901c4c9c0c880c1c1e203d5690700c016070391400104061807199001d800d50703003420807508461600001806114aa003d02c5204081c2c584c0000e114440c001103075510701036143d110342c91006101300d4442d20b411840891403c40d074070380c03291005180c0c0070040d0102e80012002001840031240240c0e4810300281c0884041030241d03110380240c6804c130035580540150195590000703455a40850000c5420030782c04102d1400d100c000344008101d400d4240c006d040c0030420b540d036484801803030813007042c800d45e6114900c1c034038070941d0400d56081070b9004007201c1c031b00c0c10103020041000c00c0807101282c1c051420303081c942c40d19461418080442d00c041c3c40c0c0445581e00c105c010740e038541c01440b1000400001581c10703100030200e8000c03603006e42c0100700006041e04195500609669 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 991329550 1250 991328300 991328311
    0x290c0313080d020607050307050d0524060f07121215050a0501020a0b04030305372d0b0f0d03090f15090e090102040308070b0f010911190e27 62
    0x2003000b00c0d200c2e0030369000701d075250b4400740301e2400c030b962951540d070b0644241c0108410080103e01c0d02d404c001d05804002c0e4880544443d120003801440302c0c12003000454403902003e030355000000c4c4080c000244c0b111141030700000790f0f401c200d089030800d00c90350400c41d410039034002d07040041c51000700102d05140c107002001d014280302900c11000280c841d1800d80340040c1000b03080554581c001003a1080c0c240003180c90047e00e28110080000705004816850220817801b0074145c0750506540c5503a40d40403840d10b00f1f075040724195442401c030f00381103001040c21140c06904252101c00f0305405641b410501c8140f10b00c1394680401082c00c1c2251480f5078005034100328800000348011810345900141450121000000b0128403582c8440045000e030007140e10043c444540440c0640800c10300c0c0501920521601d0900300703880e82ea825180b010340d10810380e402e00042e0b00308a00500080c0003140400d030401d80f420400d81c40c0d0460700110307032064000d030b04110640700c1001007a2501030b55a11800e4018 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 991330800 1250 991329550 991329553
    0xd240e010609060507140c12070f050a080d03050a0b0d060203040c211b0509010602100b06040b03150a1701060311090f07052d07030f080709290c031308 67
    0x114280440a01140305882006d0b0070150489440f00c40481c00704894203a082e406843c6541c03030040031004036501c083d28007a820306101030007808a040e040c040c04800845101e400141005000b010098000300720140028540380d8803140202034179124041c0140025100d41d0005030307240303014100304031000001e410015050040864290404d0201201900100d0f0030030b0300c1c100f001d01c142d2424240002c041c0d21464005c5000000090442d4000c01c89604030032400d6010b00182c1e410004202d010700c0f960050b00d011160a001240540301c020100c00b4420802500d190240d58640e1102a00e030344070250052100d031b4590078148100503c40301e60080c110707400d0750b0019541c2803120445072030b0500244040d04000000c0340540c1c0310070300180405e805034150b03441e03007000d880c41540350705590344900d0f416008a5a40d00c100f4076801e205442d81482081182c1c0c03010100360800d42e500084c2c0d05001c200703410314000200c4032030707036003403098002e0010290410085079030f400c1007030526a561250740d0140480717 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 991332050 1250 991330800 991330817
    0x12180b09030f0d08011a0d0f02040302090f07050a08130615060210050408072a06030911061e030a060506030a1d06070203091c140a0302120405010e060d240e0106 71
    0x144c02c901103070306440b00351404107a04d50707015201440d240501c174191041c1a0a00952110710400d03a0b0003442602d000b628040012348d40d4801200b0b1001c03068505500049080010702555071160800075044040030842080114251b00c800e030540b218011040c40c00e10140200b08400c80e0104200e400c02d500e000300031312091500e9219111940a0400041c100701e07c030402c641d040c0d14505503c01040540303185401503658407184000e0060000c200200e555482d110380388071940c60820261203a8105942e82101c00141500c41c036a01600080e1041000c25103d210201c0e1070b41d91400034600c070703100c150000500500b5202040642407030013100d42e15580c212030284002c0c1c99020040300d442e00005d1b600d80f402c07242d4200b0f410540b0002030a02074407002c00004032150700707040803a072100c00900130b074215508480021106c1d64140f080e44983d80c0030031034401401004e420300e03202401100e800c504d400184c6001c0a0417400c0080c0c8041440c08001c10218400e205510f05445628050b141c9850b09150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 991333300 1250 991332050 991332073
    0x708010515180102330c0306030a02041a03070315050124210e03220602070303110708070611010c02070b07080c12160b1605030412180b09030f 63
    0x3024400c4403000b010402000260545690003003000b0b550301e01e00c030119402012400841e50942070b0289000b05804596400428500710f500c02c15203010301002400b41441e41074039070820000700301e401c0d00100044a8440c03040d00c43d580611103000110b00580055042825a483c00750480d201604803015100e0400d110985504460807020350260f07150400a44418803480242c06d42e03801d02d00e88215443c20142d1450543c0070210140030aa001001c00004545511594006807240c9000b9440140d1010b5000c0020920448048a150999030151403459465408403424050700303400050108a003800c2d0003007051001d01c900c440c004da00d44040c0c114241085003460840c418224082c00a41000c5540141e88505000e204042d003c06046541e640c130020741c10703250181c8942416922a103203000001d5840c07454864030320003404a03035101840c55030f4a50381ca880100d009409241001650500f041040c0e00a11824001c0c02070b81e00c581c0e40318135200b01007601d00142440ba85803590800030355882e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 991334550 1250 991333300 991333339
    0x60b18012604120302070503042304060812090111061f090606020303280935091507050f1c030c0c15110d050121120804030e0907030507080105 63
    0x36041544212011860f00c960401140680200f400c00b0f0414000018005803801031a03002070086c1e504c2200301c0001500d414100401c43d140380c8610607554100a2a0b000361404110081100210504203038070300f0003044134001d04e041005c44442101d44082d1805100409061028074010142c0c41c0b0b080c4040d900b0081c009403240000303414038074041d90b10103c1c40340342c90140200c0301d0f0001c00c00c1c004000c01030042c2050284042035a251440d04515036910030590340440028408441c04850003c4c5411014002d02405d24904842d41110745401d020800010f0740074483c2c040350f064608000e0031402405a520b0140e6091000d905d01854548141a43d01c1c80d0044400050990090804c411101410000c80041c0220568180e5003c03400180c0807440c500e203070720440c166103c03000c1040e0600c1d040904490000900c2c8006440c0342200b12460044c01e21600343c80798803920074503051120640d0040440d05012042d5407440100b502c500c10403840c80d500c00d044a00401044641114502ca03450604 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 991335800 1250 991334550 991334627
    0x1050d0c0510090902031e07020c030a0b10150206091c1d03030f0d020c010c02010b0109181b030b040f050601140d021b0d11010902060904090303060b1801 68
    0x1a005403400b6000d921024040c4080000400b00b00038250740d2854401d80c2030340344005501011020140b0440231070b0b401480050003062044002e00100880c1480d9283c142c4c0134180140480352000800740085100e40b1448499141982140c001782400d0070000790700c40c1002c80c0055002601000082181d500c03592201103024007114a01200000c14070110100f411343c454506902c8481c880020380008546003680200034030240e210003048140c00038075040342a03405000120b400603200c0c0c10240308500305940c2d0038081c0034801d64006801c0304048051001e00c1d03240300d07442010940c0c0308070104150030035002e13400302c10040f031400300505d142c8500007030000c0c91201d01d001c29100011400c0b1500c040369904403080210200c4021540f1124106440d44c0c80034915019030024005d509400260041405110101a801052642005035a400f404028000070300280c3c1010380740d1100040200031070300140451000040440241140c1e00009801a40c03180321403e480c1e03d000e043e0000502801b902e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 991337050 1250 991335800 991335809
    0xf0c1507261503010b06040f0f0f06020d1d09010b09040510030b180109050a051f060e06010318200307170a080c150106030207060b010503070215100b04030c0e01050d0c 74
    0x1041e1a4161010209005080d103070182d54006c00002000706180003501d2103502240d582402d221281526188061195000c0c0c1c8030b98405a4420100843c0aa0140804460340503035039568004508161000803031001080e48201810180020030136140e007040d028059001240c02220301070207140d55182c0c01c030200010500d08140700740604400000201b0341010001750307040001c885415005062452b1100504581c4040c48010148180039a0580b801404115034000000d100302da41c50b4401940948815400001c603210481b83c810300040380c1c82c04441d40c034111218046081140101414a803500e940c0108162a40c4004c000b900c15000240e496202940520010317213804081b81c035180340a0148095a1502104d080040342003941a8081d16206001d041c0c2400700c049141c0056030644010703551000103030000041c0f18400d00080706060340041100c0d0400c03070066a03440d0044603d81140c0c000301d42c1d66204040810201e1170140780b0700e01421040750382031445030031651203007602c0903907105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 991338300 1250 991337050 991337071
    0x14010309031e05090a14030c100206070e060c06090106050a3008090306010b120f070e04090c120f02031002120a05090a0212031201080303100b0f0c150726 68
    0x6610700c454440c505403207031301c0000341003030903503d484480707004460f201500f850f4001e00c00c500700a0014a454096401c404400e500941041d80340c1810440d030f80d0710b440101c1d0741c20650810200c5030303101c020440207205502c4c035400015401e0502d82000850f65035544070803890103840e4011000620740b003c00064803542c400c04c01c040e182d0700d0f151013138280c001d82c0100355050162070700006050001e41d00412019100c41116583c41c0d85182161100510585d0b480300003030040303d0310b6070450400d41c2c4403919060040f07001028032a075410203a01c8115000e0303811a03584030717814001c0c0210305040120b5513446080c0d0000b5800c05c9181207a40b8248800103028012864071038002c10000c1600b0701c62140a00e4000e042e09a5440524032050340d070b64002d2140948031103404000180e20f00020054034010340902c1303151900303940b4010a01d01c0c2c40c1c004480807014058200000d00b41c0c50001c21004186801c0456414181d00d411400502296880451115107008034900e540c50400039118040c0d000d80f4058 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 991339550 1250 991338300 991338347
    0x1b060f1204060b0d0813120804060503091e0c0123091e0409030324030b13050f0d0206090609010b0a0e0919051b010203090a12080f0706061401030903 66
    0x5191014080443d1029004883e4582580034440000c000f0805094101c0942c0741c8907584100038040c0019012000e00403a41c24402488403030b20400040d90000d12807422100703000604010b01c000000d01032841c91540c1d000000000e030550b0042c02d0b02c0d9070209122515003080d4440903411929216407181c047c8140e11400307110186c1c01175011284010a40036004024242e41481c010b401460f1143c0907070000c01c0300500f600f445d1404202e01c4800c4e01d03402042c041c2d16072954042e101d010340c800081108c071409640603d1501c0c5004108585448500d03034001e064508028007042e041c0b401c050415900350b414401815582d89400310201c0450b041c1c0c1000b0442992802d178024100156a008a41d064002d1b031800403d00000103081400030f06111104411240340da0010780c0c3d2485040d040d1904544030f42c3c003c122105040140041007402462004e10342030b107034a54140e542d4800c8808032111503554505114a0b800c840c0c140c000d07441d013802c0810245140f41c40181c41c900000d03003160303502840b42 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 991340800 1250 991339550 991339553
    0x1e0b01020705031b12070f061d030d140403020904060f05070c11060307090b0a021501060f080c07030302071a04060501050604121203021905030618161b0b091b060f1204 74
    0xd01703440c0351140c50700b015078440719120030a41d50785c0341c1e0034030445000038107405980c08440001c1c0c01c00b00280400500900d09403247c18015101070880815132220980d0507c030000c00340c0c81e0080d009101e1441100b00090b400880c100c050121035018122204104a100c18107001803078000178410030f0070045541607100e40e036010089803030100c1500800071440022860824064001a0759203801c1e04080c000c40d8160b0301d40c10200e610054a0040b18002501c1c030012030041e01c854801011024001d1601500c0c003070303441d2141003003e9110410705480303000c1c09040006000c2140b00c0e003400b6000842e1124981898460f2401c9002150341001e030580340a01d1034803c100c1c1c026030488855120a003080c1c1d48500b5161001f80594004840042c0a007203004c1c000061462403001c1c840c4540b00701c082c00f6281221b880011074048640840e070203a9401c001920740c000c550b44041c400d00c10b08051008000303181070b00700011b81a000e54401607014920034003800740589400b000707403001d40c0c405400e02086950745 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 991342050 1250 991340800 991340809
    0x4060b060d110910030b030c0607080d0c08040c0e0601050a030f09020306101a0408120705010209041107150506010807031a1f09060c0f0b060d061e0b01020705031b 72
    0x300095850030340d242c85840100c040390080030b4011088125030f040780c02100c0c00015401d0300c80c40d00000d6071640115400e00040c0c94020044c2c48001c0c041c3d4006801d00d00c10070100421280001e1900d0302048400c4100801c0101043c00c54001d880541c056690f54184480040e00c1802140030744400c0c10f40315208034400300704c1c5500c10b20b0040d4009080740d1341c9003010940941603132101c0c085c141d600d09601c0e0b2508100f0101b001201e0403144000c0040101c0c3c030340744841705000d80001d070003140d50b950208150010741d43e460080c52500c4201019007940c8006c50302d4142c455103030f0485030b00840b90130501000b03620381c1c100300d0711503102c40c00303050204025900d010f20109200c228018582c0c4000d10040c0580502412550120b040086454001d00b0030340795107060f070365038602c6400140f020458030311140004a00519440c0c00c850017a0940c02a004030741e076043c0c00c1e100141c5203035400032241d80701d0b2110380c00140200f50080c482030015164845c104004070b500c0d0802404076407460b4400c403141d81140d449 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 991343300 1250 991342050 991342057
    0x71a0c0309010302071103010903030e0c1534050106090b0117010b1e0705070f1a07081303080a18060c0c030803071404030303050f0109110a0e0109080d0804150605010804060b06 78
    0x100900030864000271703240160003400c41260382d440da8820b00c1e0102e5414240141c0070b160540901010500300000d40e03007100102c040f40148040c101d4004c144030f01d50810810601e99040384500000314496080c401114100c5010131402410014014500040940c0e8111000e0648020891155640c06060380308614106a00706040d641a0001104d03001c2c488082410019940e104000b000860356815100c18a001946c5904444880820038040040c0345000240490800c0c0b1400003041a40c035140d000c1aa0032060703490000c915101e401500025078540e00c1c03005803080741030695041110b0748035079003e9102c5010050000000101182d0756174000ca80e011480d80d0300d820355664603500c038a0020b0251006451140c4100d00c210008a0140c100f1301401641c4500c8008103801d040f0281411030b6021102c082e083d0611214841c0031618071030a008403607118005480707400c21070610f85400460305036000b400000300c524081082c4641d0380c0c44104150000d41000022a42100342c400040b054070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 991344550 1250 991343300 991343333
    0x316050f0a050909060a0812090a05060c0105090705040c020c040504110405010b0703020c0904030e09100f080f0615010f050d0b031c180e16120c02071a0c030901030207 74
    0x310046070450308664044010915030740d054450940c1c035102c050034071211a145010f0460340e03402081d414100b0f0000e00c0c01038040c4200042179950025a958040b89469106248400072651034004000c205101040103c0003081d00b42c42c100301c4162003640094403540130881c003034071554031040482e007400f42c054500044000d0040040016594030000316489074004038080b0090b010302140c2011918141036140d200da600354603555483c1140c0001c1281111000301001d408030003200c40800c29001c002181c0300039041d29001080344c1c4d00703034400d03041c5851001001a40801f2807c035900000303981c08032180f1036020710703424101e4803998408010400741161340a10703030b010300c01e104103401c4085962900350000c4480e40c8414180c0c0b1100401158a4000d6010b0015058a8440861003038014400c0d031400c541000e2500d00d1400038407000c1c0c40c0c10342e6130814500300180d00410081c0300e4050480020201c0c1e41d21401c102c6d02c1d2400344100a900c9024400a0071f0615a02082c12014440b09580b81030905 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 991345800 1250 991344550 991344577
    0x1c0c06060512010b090109050408030109050604090f0b09160302150a02030d11091516080901030b0d05010902312d0606030506030705010914040e0a0b010614040506031605 75
    0x246540c1e0400e0f008001c1d0080f0349200741d4184000203000203491107050700445d00b011400340b031603003054420405004068249500140e07540300c07100c0460300c0c0040300c100c000d03c1500d400c845c81c20455007c0d0315180c1d0b0b200c0000b0f0380f04d40e840000c0006070703643c1301400004400340c03002d20380310303509404107a0460145441400c440c80c03c0c40c1e040c2c6400503064006000c5c0f0f40d002c40b0201501e50413144029114014a200110118004840f02c4089035001c8003820942e40d0514020a802008501041c506c01c0da000040343d8582d1101c00c00401c5113000034801c000c07485030911080300c0000005038400c404076806074001c0c81d02e54462002c400104103010009a4012078101c82e103514140684a0004240c548140c03800a441c20000c40d43c1c0d417038089080d4088400c1603644600035410030040c80701480c000340300c10794000d540c0c811500c030001d414000341344014010308202d8030940c50210060000c0d00442c2a403054590100814002a80d400094a80010140080c035080d0102c0d50801d841c1032203a60110b448a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 991347050 1250 991345800 991345819
    0x1403031c051003080f040806010902030c0d0b0316120b0601022a27060907050c07090b191203021c080106081b0423040608070501050c0115061e021c0c060605 69
    0x10b0038a1701c010000c4490741c1e0201d5100d81e0382d69051504a000540c0c000280706001c0060f040c0045017504400c155540003010f40c0e43c01d15504149015a070101c0e44108003007d084850328082c0324503030b01896803002c401e0001d4a1031090a0320401201c6104035120a00c0c242a071a4540e11a00c0d000344c1f404031000e0086c2800920040360700074075001d01d401c48440d4440c804010000d200584124240d4038400601130081203840d00b0a0102c00103092102500ca401010321806804503012403220741380180340c01e02d411207519179a800c000f4100710f030b40c01074000b03000e00300e4000048107540f203900136045400a183c108802d454420504d603048003d84200400e902d000314012410100c00100001c062001c1d20301c50011100c00002e100a844052180010035046058200415400750000384a4103080400000e110203410107100c0142083d030700080000340a0040003000c00646444514803109640000c0c5054803d0401c024840d4824103403034030801402410450400c0311582110028180c018441001d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 991348300 1250 991347050 991347067
    0xc01050c030f1e0a0e1606050c0d08010e010e040302011b02070f06020f10110c012306060910030b1215070f08010e0402150903030d061403031c05100308 67
    0x21600290390b000c650000c00b60100300c403140000509030419610040e02e0320345543d180352000040804140090460041840034080300c014480d0410141c000c83e02c409459040c1d941e4140e207818000e824010511580c4401804212010320301d56044844808041c03005035a0f61800b04d02401c0124070825844014081c001052034011802e0422399050702040b6000c583d40d40000c076626682c2440c548940e400c034108098050102d504000c1007000541070040c50508031024403403c5540380300601064500d028801600008041d540701e401c00811607045081c00b4082c000610301640942e20b02040c9641d070304614405072148040100c03403000000954200d40217014800c40740d10000c848090019000203000a1010f0140c0c0c4114162500249502c5065507564280070302014600e10005401c00c040c040110365030b41c20801850f10400c4800003080c65031819071424420b103042c41c08680309030014003490034800405a502200e228103180080b949845044034155911041d8001510005c00080d4420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 991349550 1250 991348300 991348321
    0x5040e15040f0b06040e150d080a02010606050f120403090f0801060312030501060206010e0a02251209080316141c080105010801050d03120e0f1f09020a05150c0105 72
    0x24100c5000361014004030480100000456200690003944140140802d02500300e07001401c99004111412403840c81c0b0749400090600500c6c0b0400719043c1d4000902800c17420b0742030240b03070003d010500704541002c00b04c42501201c1c2c020b0000024840708483d0004080c503104498600083c10000100c0b50146e4071031880343d0113001035000689003503c003500f10304580ea22a20807036040712a594050a0740d0b03402d0a24000e40c42c8400703460300e0569502445818199018034a4061001c0c401900c49030b0801000d01d8401a005d10180300d045c02d0141404082010b60004001c5030340120b08a104400040c50301e151502c9400031215400200703100f060075401c040305d9450500c00c150023080e00c071b07075a0303681e6210011102507209004882c0c1025503142178800190160800c0e062110703c0d1800403810b00400c100c054600b0030402450f45840e032003d07410481d284010395034822050005141440403403d980c000c640c921310540f05440c020040b402c1c12810703000358101030710201d10f04107009102c9420b01142d4170 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 991350800 1250 991349550 991349581
    0x3040305060c12040b04031e171305060601050c0f101e0603031d06070b041101090803091e0321090901060804050a02040f0b13050a0510030305040b090105040e 70
    0x1103420303100720030116204403070080903181103880040702d40a0644d02ca03079448420840240080f41403000c0c18160080f030010200b8100c0c1c0145d4103030307a1174840a04842d96508040005015200c041c00a1b031846000f05d000810f455034081000e0074034503a282c810f40011071034091944881406809111060701c0c00c1616904280c0c1c812030900121403c0101401c144822a01d144c80010085010400356178151403901e0f4502c64a480003c100c1c0d800c00c249a140c000346508210380031215200d4405c1c007580d1540e0010702e01b4000c1c00c03000000398141151725000c00d110b15420480f004400f046942d10015542c0d040143e101e501928000003800e00d10442140c1910b90000071045101b21407080003c1107152045409a00c2160000028455900141c09100041100c0400004025201d48aa803080e458000c24a01c208059400000b0710b890158410030442e5400b0b4800403944000c1c81d41040032aa01005a4041c0c8c1c07640307179201d991003003c00010307502441264040d0381e0280c02c050800c990000b80c2041c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 991352050 1250 991350800 991350803
    0x11040c170f0f060a080a1106040e0708040209070e180907031b06140a0c0b0402030304080a1b080d0807210f020d0c1b060906060816061e14030603011508030403 70
    0x4104143c40320f0041165810480c0900d0909034401400003010038040300d107004009101800c00c0c4d10f0103880c2c4050040d81390782100e00e040850034400901c000c50610010b0564824090700e0300400d4580994001081414003046045016a054001c621b0003182408004e0055038088609445209640d003a051074903a02d1040030081428184c50b103000290706e10480b660400c85aaa10541d144255103616921101400c01e0707030544000d12011130b44007420410300800500cd0105c072420f07400d9100309041c120400f0b800020b42c070f400403041b2032181d90300514140c0c0c0003020303428100ea07007400f40490134200c0b0f82c002c9400080740b4140610b80c0c60070b41041c0e0040c910401d900f0b42c1800300540c5a6000d4600710b1245042255400803c0386030ba000c5903272540700b10300703080c4a85070100f0700c1e036a1100182d01c0e0000e600309591954000c44000c010054003c64540707580d00841006012000c00a40301400d1a030707401c0140c01d0711250000000700300d65030a501152200703404188a60905450781034240c1d032504a03010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 991353300 1250 991352050 991352071
    0x1e05090f181b04060e09090c030f1509010c0f0c1a131515120204020918010f0f0e19150b0307020c060304120302070510110d1811040c170f 61
    0xb5002c016400c0c000c4a064844a40760100303026055014032543c0c00000304054510f010b80783c08100e407503505111985110007440010b0070a80380081110b0b5001101034140c0304039a140030341c00800103400026100d0155001c1c1841c0c940269582000340c0b40820900059500070205802c0081007054014030402090040e0041d1a1940c1e000d003415084540d0804000b48282c181c1c0c9040002c401102c10102c1c03c0d0348040c2c8054185401140401c0344140050224884610311000512840165840c61001000b621405e80139441c81c00d003092450f0003018254183c00c04840d441343c407040c22942c00002115204218580406650b001c031507020b5042070b205280140544002d9004514200d01500e0280c5c0d003200e410004000d0f4050207030000e602600301183d0398018015002e032001c02030710910244030342114456554141d40f2041d0000c4032986e86580c00c03018049000c1c580403819004800c1c4142d50103407000290b82e4002070094603c04000100004030f110a802084a07000c80700002c20701550460b00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 991354550 1250 991353300 991353331
    0x3051507170c032a0d0b09010e070315120f030206011d270f01020409110a0518040b040e0309031e030a080a09140a0201020d1e05090f18 60
    0x22040320011007415a40100707039550404680002940002550081a400002d500315075155032544080440402944038115021841d082842441e002e090f02102c8101c4201c0040e40c14072110180034600034000c00101a038803039030b84456000c071641c004d0140c03100d0095180030b100149000901050540d50450040c001c4000016403040c100368501d95102c0444100b51341913841c6441501031505050a45007109006850081c161301c00340007036000d02203140700250380d4a0414a4250550f9215040c000d0042400c1040d24101c69000065528a91140d032051143c01d01c1da00015020b44800352400d81e20510f041050000002e000005007191034090381618800080341c0c9060140383c280d126400400e802c100320282c000c80c461a00c0b42d60101d440440020481c58940780d00c4511404078480c82003680c4040019401d660701003001980d551014940380404140c041e220100904004140c28107104011490380304c036544901e029040028054000d082c45550615010401e0348190741030140e640c082d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 991355800 1250 991354550 991354561
    0x501091a0903040b0d06030605070930060e0a061d070509011d13050604140f070b190c0b04060605180610111516092c060105040807030515 61
    0x40e400610400744030000d54286841d00d80107000c5a480111440780d03d0742e80300400702c0001d500788107550140d4083d5907250846030400b08104051219181401140308070449120390b0550552645969517911280100f0031781c020b00c40d640e1824141440081445041a503106055000030004010034544e0200b2110203550f0703003082c09081c0c07000b8050902c1b402e0301c4064000d4144055245d06400c60210040032402c868145ca89908000c0c00382c40c1207405c08034246401400550410800e0040c500010180111a00d001c034102514817441d5a9140000c050080c25000c1d02d008030f91259000d84c210b54400442d1070546810001800c43c3d000e502e101701c43c1c0c0800024505a81c0b846c003442054003500d406046290000f0a941c040003c0080c41d03c00c5c4280450310071801d420400031801950103030140e44641c4c102040c05003004004c1d4000007900584c085090074420303032a218100c08080e43c0e184403100b5440344001240c681c825608035001030320079000c00008001d40054601122034200070303901c003291100b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 991357050 1250 991355800 991355843
    0x2070509060d030e130204080109020a170a12030b0303030c1207024c0b0f030a05030418150807030302010605040603121409100206060f0103290a03020d050109 70
    0x5079155070b00034401240410000e400b81069000d13a2400070500f00785141e49402d01000d0743e225070401129039455507409411420140301c00c1c4090490000b4600e00800025025039890300c5060024041e844107001071440180280c0c80002c0040c0d02500f603c3d500c2c541000411599030041d14415400d1007100d0024068502c0848c0b2840c03008822034286840380380705403403186465603003850b09000c03103010504900c04bc54502070b44070000b0780c040c1c404202c0201d018100580f900d03180701e03683c0c0680c10009190000500c080129425911000030f44010604c500300002d00808580d100020030720012000442d00040002d910b070226480381c0d000340091616001408152411844000c0c0038260703405844903058040d02040d4130407100f59803150700708000d031710004128010780c1740d01c800543c0100d000d0003000d007001c0302254914002800d00f07008429107074005000c103180c03680b800340ca010003c08070000c0559501c54060000d540040840c0410303001410590b00815008070126084284003540d0181c0000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 991358300 1250 991357050 991357069
    0x2509031b0b0a030c05040e01090b03070503071809050c0a03030504080609160335091201050705030601210614100905010e0d020a050d03031e090b040212100c080601020705 75
    0x8007460001d0411105520607030240080c0c1e440c001c2403100500020a03140701070711a55009140407400818400079000c241401c0c420070342c11080c02504543c2081c024911408049110140c0500d0009aa9011418250f05104d80340c511a03900403c020000000e0591000c094426501c1005c00d841280d00e8028140d543c40c0b142502e1880c007105132080030070100f00c02d508603802c80c00d040c0f804444210041d50480d180d6144216034110004400300d07800c0264148000c4403640407542000800290a0040e800340541c000209501d04000184890382c07400c0101e24543c03002295403000c20302c400341c2c0b030385901c1085080410a9502400000d0b03030b001c54603881a4805000c072841a110340507400d50890a020f5440146402aa0424002d2030006242e890342c081d072414650090750009025109940701c101026010852505460701b4140554007107075081400722340040d0704507210a050354801841909020380b0301d01c11070031946441c030354105081d007010080344101000d90913900c01d140c50301d0030412b4808 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 991359550 1250 991358300 991358309
    0x1b010c02010305090316120e0d110d081e040911030f013f05060c13090b04091b03020f040c090b030405030f071b120203060a052509031b 60
    0x20068002100594000d0f400160400413400541e03140c0f0807007150086082281810848a0680e0404002181d80d4880441d60294508544028030000b035510360200d04140c44041034810105000c0b000c08120405085542c0124ae14100410a0303401070030780b618542091003407031451130501c0c80403040455804200e0b44035a102c8603c50b48943d0815a0f1500c1822103928071030000d90040000644044844c0c400c0d103141200c43c81c43c0700302c08110b0302e815400c0080c00b8044529041080c4070140340ca445d045090001d8070407040c030004050070070200007030142903075010142448182a0502c0100c0300d05605007000c0e40c0c001c0d5036500e41880c403031007840115074255000c440055025041401100d404130b00031a0421b0180c0100ca00f89002c2c00102d20b540d910000048508040120818074640300042c4024020312000d44102c0080d9000e4001c030381c84000041c5000307070b0150b0341c100040e804803000e08642d200d1000e00940f038000c80c041100c058411403090100742e030b90f402208d03042c08008819401901c00c1e078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 991360800 1250 991359550 991359557
    0x9060b010318062c01050412230c0307080c0a050c011d0d082101092712090e0c120906090a08030703090b070905120c03070b1e0414031b01 61
    0x800c85a15454010054401203a0b10300700440300e8940c0c2041ca1007100421644144c0c00045c2506007851301c82c80c000e0740812403000f40186819100c180c400701c92907040340800e00e079103100c0c3d0303a142c2c2d100701c94214030803000c00a15000c40400c003800705150000b0000280e900c2001100d001200c031100540e881800b41c21200701944454460701070342c0c103100802c0754015105507a0f060805011048400e8440f51000040034002075000c010007100043d402016074901c0800f1141c0200194080c41204681c0d0b8510701601c00f060f100290060144107001800041004000089107414261111522a802255910606034064011455001b0003140c014020b0303958000500000381140e4540716982c000500e1481419602c0c2141c6011451101105100301038698400340030030b040034204002c0045c0c0e0055003060380e2098000e0805906c0c0040d0890580d241c80e49140e4a842c50092440d98a03003140ea407007808038030003142c0015030b1001c2c001c161f0849a01182510000300060181c655220119548207000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 991362050 1250 991360800 991360841
    0x280e0d20060a060314010b1f11011d2820030109030206070906090f05100c050f06040c091505120a0507030506070e06030c0f0f09120a120306050a05042d09060b0103 72
    0x144107200000c40303007280743d40c1410702e124208580b00d9400c4132f40c10803074440401210401c40c3c0b2040020700a00280c140c03100ca80829501d41651044a80c950104008100002848158800c140c2401c40b86601080050090001c14198035000752140d074143c4030a00800c130342120100f10079004401385026030f0034200150350b00030314200070000c1d0b42611142d54018000520040300200714144624030030640d0080081c100307400d180c64914900a115400a424607140099941c40940707001046d00899000b110b11482840c1000d00c100d0a000b0b00032002040341c8201140003041000c04103516210b03803110f483d540e500b06201d0707050090f81c0c03100301c0d650310314039104100c40c80d100907020010f4401c141e01c01003403605112400002c641c3e02001c40e200100560300c03100e010720800105022500703081c81e8915040c001d4a14042c085901c10045024861107a6201e03034250110000000359401d0102c095103240d613540c985994413100401140b0b0050b2001824000c0e8007000c1e5000c0d008445603c41c3c1110380d081c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 991363300 1250 991362050 991362079
    0x13060b0307210c05150301140f06030f040221060a15030510150f180c05130311060c1614060313020d020301090803280e0d20060a060314010b 62
    0x200326400b440215110b0003030348004a0152100c640c0c0724041e80c0301960f4a81d480d414980080c1c0005040d8488505c921805104c0c007440b901e80380244c0c1d41000031503c90000c5901c032840080c05802840c00c42d091022000c9005d140c45c4840010500d004581d0300100704841038048820100c040c0660101414685c0b285010421005d402c0d0306c1100300200c00c0e00160201600e82c0303682c41c8010903070381c4101540001d0450843c00140a407003400e400b142e003410024038010080700e02030800c4c200c0707100290801070070900d0716550303480d60412517900100325020754441000d98565010b0b803a142f070245060b40c01c2c1652881505050080071a80903810050003003010302c22075400c200101400d0310301280c0554a40303505400040e142d80280d400b88528071a103892102101c0b0ba154503a403060341e10780540e1403c10702441c01001002c529520352f0804c3c0c0c6003002c60101d070798802c141c11503003001000c2100e1290b88200101013503a9804403003034038400c1d4040d00142e4840300c030310350076503d030940743c1d40d408140d1444848 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 991364550 1250 991363300 991363349
    0x15050d031b021f08100e01050f01111903110706020c0d0204020d060305061e0c0301140d0c060806090f070905011d04020409230403020604020405040303110313060b0307 74
    0x10801c070482501680003901640c0815800d1101164501c1080742d2008000492a0003040707003903200c0c200b4080e00990514000001e034080b0b106104036400380c00e1107100c10300c440c0d10503041d40200c00e441000f101d000618100040074014040f15040d0002820050340f0040c2c02c1e8003007112000c56499a00038074000a00c071080104d600c2800e2000c80c4d0007075080204032900785003402100000c6000c0c8002e0111454240d221503040142034804c114246d0704507041080517038000050361f0540f503192014142250446010411300005400040c15100503000f00140c02940210414405c0005481c4c440031a16030302c640c0d20000c202611180080340081c0c5080c4075552142c41401d0444000d503500405c10b0081c02d000c01c041740d01c950496004580c0340c3d8001c2c4480600328080280343da140d407110000c186410f850094851b032002d07100920850302d41f8045814144070742c10045183c0841e840c681e980303007810f00000010204807282262503074180862141d03170349000310b021030454004220150030820070586a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 991365800 1250 991364550 991364567
    0xf080c10121116230115150302040f0306243c091b08071704020f06030a050601121104033512090a032a05011109010315050d03 56
    0x200c9441e418822000c080b010b0080c1c1031200d07030144030100d0444c0300700d032001d08510114181194450381013803000d81e040940310429034215a0070f002451041c201003e0100c020388100c0e804405150000000481440901d078803a401c080d24500c0d8504000150510201c003030f800c00e00c06c3e203044005152001e03d0780c10200441c0c40c89801141c200f079250204440d0b80c0541c19200b5000001901e40e074440b8480f243ca85035410484482c11070030041c0582c40c10a000601c0351071590b11407034900303605070003103070031500d540802214448008112603280e19050144200424049402c50f0010704494418240084a88074461078002e440c80c00b186840d04545505c074411032402180d06850703803220584030152050100c90314002031150039050352180004604d0050301030180100606802504c090000030380c0122a8031120060942e59804000c0701017421004400800405421035003011072191400f48603c00624811000341c904008890340100c0102411016005150300000c0608a803c01b00740641c5e1130 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 991366906 1106 991365800 991365821
    0xf09040b13082b0225031e0806040b0a031110051b16060503091c020a021005030109060603020319051b0a02030a0306091e240f080c1012 60
    0x9012410400504c82d083c1c4071405c200c1e4008150292484032178014448629140034251a00c01910580e01110054452881c3c204144041c0c82d220381c015090342d41044071610010788005c10b102d02182d0484403182800720601c400d6154041d03104044d0010f004a4014103020010800d8208000342d22f50010000c1c1704c1c0034000c119200d1800148010304d400c0b005c03d450405440e5280c00d0f410151199000703504081d04540e04c2041c82d400100450407a41c50010400c8040d80d1210300b01c040780410750715520200e00c403804140c41262075821190700503164007940c40800742c8007000f0f0111540700b01c1c480000368001003111608a41c0606c52000103000c3c070042408070301740b401e80d10341d1014882c2d18a412443c0e500c505c0481400d0142d0001e441d00c0264028040c0000e440c0c07058031052040c14030a08402d440390513448055428032650350307069417545403100c0070040c0c2e4000b0104050044101d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 991187050 991366906 := by
  have h0 := BRFrame.cov_init 991187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 991187050 ≤ n) (h2 : n < 991366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
