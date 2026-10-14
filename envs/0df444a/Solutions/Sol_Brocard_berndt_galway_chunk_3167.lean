-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3167
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:52:01.206989+00:00
-- url     : https://prove2.me/submissions/b467057d-7c3e-4872-99c6-e7d396e93fe0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 569424460 ≤ n < 569604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 569425710 1250 569424460 569424467
    0x8090c0d02060d0507021c0203030703050106140711010e15090901050103090c03110f0d050f011d10090c05040e1b060301061707031103090a020f04020a0509010c060b09070f 76
    0x101085011918420309440550004096200c0c0c480c2c4081025103500000f01820300901141c40c4008041019001207892804029201e82c811550100424a81400410840c0c8121061880326103a00789a0b4903104150b2168240704460650301410080d00400c1a045515100d4a0f03200b5041044900c80d1200b90380000c03c9940f000580110381050301d000d408002040745941510112900003041c00c542d00429408241080880c41076240c000d1040140401040780005035114044201c070000c00c0381364440381c02c12400d8052107400764800d0344048420310003005180e00c2501c00601c2003100040f100e40d100c012505036407202041c811503801030000b41c0e00003d1445240d0000c000121100c0d443c641c104000544882101441180418007250004a00314000c1d881045c0b22600c405a5a45919141350100e80d103800c9260101d004085100c407801c0c1d2410540280ca1035081245c83e0303d8107050503072004403403503622130005603200e0342ca545e20070486841c0d050481e03020f0351440d510042841362005014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 569426960 1250 569425710 569425723
    0x8010b0a06082707140613050904050309041a1c0b01090b0406080f1c03060f033e011403040c060c08120a050103060501050f03060402060c010930080f0c1b0d0809 71
    0x600864042247c0b05040804a9040c010348034100d40c654403503240c5003003141c594002d1a5034990840c0c5000501d0320b0101c00000c3c455440d1500315902040c8421143c410f541032512280024060b501400052101c0340b15a00110000070f8043d0002a42540e1040031510702000702c0c01d0741286400451108100d0903206501d80740040d02400c0610065140c503904182d94245d611014000c4c8030392418a031101e401ca1011956220b0a0205011000d41482d145070105000d0006440c0411040c220504040b42c4020940c1d10841d00f06000c182c02d14603140090300c510080500c102c843c41c0e010084d8611040c6d414103403500928506200240301d40c11840c5c00ba04440b41a080b66124210b1261252180d40e40080e8503907000f60705448107500d49000c400100c0c003502d001d14004080084448120b0070910542080300c80b607044c0000e1080c1a0445090309652000c0244c4050f03048051840000c1e00010540c0003c01c0002e0304c0c903070160303a9080c40c180b0341428040454484000079080c2801d2148880c01081003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 569428210 1250 569426960 569426999
    0x10309080304080a180f030f03050d0e10060501020d1b0503040305030a030b030d030b100c021906030e0c040e06070c1a0901050603010c1103070308040204060e011e08010b0a06082707 80
    0x140300f10504100c4c0758450300304d1b144001801c000c90f995520007098460030030344016a030002c2061182c40002502591628440340d03040354000e2410302d00081c2076100181c50703151a9000d4682140c0c00554030320000d00c10205a10540b010300c010400000000d2041000b015032840580c0c0000341c0340c00e03440c20107080500311180e42c001c06040802d0120705656140004400300c1c240d08000c0e440d0542c601c045806148210582100100740403400a407058140d00081c3d0304200d040151070f10715882c2e008001c01c61f11442d080143d1130307100200285a07940038080303100343e00d4041c501c5003030582480c0d0440b24100400312407a1665035180c01c10b0041074142406491920039075810b01c210408115401c540c1d8030b002c1e82e403004d1304000401c00805c0079500d4075401940541903950080c00e035981c481020040d1104401321801a60b0020750000905a42c1032180304501c600050801d0855440d104c01116803403805441c0c0d20404280c01c03450840041240c40402041c1595000b42040c00e16000c0e600b40e40c81482c0d0003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 569429460 1250 569428210 569428247
    0x120c0c0614031503010608010f06292b020315011205070e010e0d06050a0c080f040305090402180a0f05030706021b01230a09030b0132010309080304080a 67
    0x1c07240682078004056960050010311440c0380c0703240c1c84002901500c119440541c0652800356040649501608100117660064003180400d0a0b010300084030710741e0ba00f001054030f036014403542c4580308507684034010f40b030b0f040d10061000c100c1300b10b400f00481e0302c103540d41c64030b483e200101203046582002c1c000c61000301c0150304000f249800100a000141c06201c668104a054050025550740e00419840482d4000c1030401c038926240d2030b180000c01c020301d0300c0c101041e01040040e040d12022180300b0300c101e526640d507a00302070683d41408040d4200d5002c1d0042c02d1002090b83c00e00fa01c07440d100c14001d0079003584122450745420181030130803103503410000171508002301044200d21135541c1c141980b4828a49030402d1141122000d50b080034489002c3c000f00d500080205056a00802100649008504608260342c0c0e500d80e445040060141c0d1882d52056032600c03103c0311703940c6000c80f907190806040c00b02d03061070300c0e69400603564801c1341c00300d4601c0300100b4030b10380301944408440c240140c020b2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 569430710 1250 569429460 569429477
    0xc061a090a0219030c1103030408090901050613090504060b030a030f11010212011a070503040902071502160b090c0a3c0e09070f0620010b18060d120c0c06 68
    0x2100c0c40f03840d080c001200c0c001d0580320b0074441c18007449001051003841040c0142c907101d040c545804105544180c900305e100d9a1207030300100b02c1b13140c044220355032100000b10102e0110f1400400303030083c10b40188165441030b41c550400034952814400140e20610980d036152500c0101500a0000f00790000300d503032541e10500042000f00030021810303043d58040101c0d400071110701d40303800c00c0381d10880c00010210b000114001483c040150040d2041c07074407404042114448511306182240280d64601ca500010508601c0c0800c017000401500014108203035642101c804002c240342c0c1c2015800040055081c3d03000306c10150300c520410718052002d00b86038541d4504040590040030503409621244105040132034201402000790300c0c0105110458881d0b401d90310280a44014509140901100d8500c2951a000c2d40180305e0190409030041c070180c0405400502d000c183c0200030110707a001442c4180142c0807a1003094500c0001e031095558100c45034003442d12039800b01c21036120809201544 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 569431960 1250 569430710 569430727
    0x1e0a090b0f0105070206070f0b010e07080f160c0512040f050603042a080610090515130906020f0f210105010f050c19050d0908120d0b010c061a090a02 66
    0x40303110300c41c654001d01e8040e4980c2d0341400002d803144203814000f884400c04c3c0341914200002c10300c40074125400500040711a55490780203903000001140c3c03400d41e01d0045000241c245250940160106130709140002c154181680c1315881d0401d1404610702010010908011803111540114060700381900c42c5030540c14140d0f118208801580e03140000a010140340321001c0c0c04503618003005003207480454801c6d0500c42c6081074582d046e4019186d03820b007400300181b0f0004264498684c1c558016080c1000ea5802d414898000c04c4e020303404484813078080004444d01c41c8074401515500040c100c0d59503840d440b0580016191400d56685100c003500b050042103203a8010104580804481c203006030b951611400141c10072000a0355607088180c12826a001d2180019850304250784a880e43c0e00358589422a466840003260000b04100c0000c20240f40c90701443e410034402e100f4181026001841d25982c0c3c8000e07107100450522000c03000c40072090030351038110030154020740183c00c00c41c45c0c140d80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 569433210 1250 569431960 569431969
    0x327060405060906070b01270902090c090a0b04090608010c0c050a0204020706020c0d0f110c0a0512070506030406020c1204061209020604090c200606091602010603021e0a090b 77
    0xc074819648102c502040100d035607110042200c0d03103550b10610880241d078542c54941c034040700d100354000218070901c8030080e0720250f922811140301e8004001003da03640c4e500001285030f100110b05500404500800609035005c03002801c040d0628a001140c0981055407a50031203003928200d000704054214084c01080001c00c46511803030b01580d02607030703800c03031414a50040d00c284548407406206802d921007a03d40e009031102940c80e1141d90b054080d401d00400d9a5907108200303038103940f0a1300d01c00300f0000d40c600f100d002000d420f0740b0810745000a17550070004241e9001201d06480481d00024000c1c5a9101482683c60010801c424681444e0420700010103190040c8005124030380d4580f00103041d560740070f0039203000304200c50091100d155120340c000c01e0b0140d08100000e0003403580800c04c42500e00071540320310491004d48124642e58511111210422082d2001e4041d135507229808070250300c910495817a40d540306800032418104030024441c0388503880d88101d0301a40351007501000c0b90303139 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 569434460 1250 569433210 569433217
    0xf051504031b11150d0e010c090501030b1f080703110316030207060b03031b0c0301020412030f030603021c0b06041b0311120108010c0f020a03020d11190302032706 72
    0x2c14503809040b40c1803441c1c448002102c407820a94006a540800c07000e5041d1000101001280288148400444405450b00b40d41800c010900482c900400a208651196028104640000303050701c601e403401c070310400b842030004680580050b5040c401c00c20001e415024090b8000c0a2841c03180c070f14070b0710314041c2403042c0c5400700d03030300825400061104c00c0c8074054006900f110801402c0d84e40d100f000401081281c41d80003503440300c81c014030300d4040e500e20b010700c00d4804a4800c008100c0300701384955411240d2040c80350140c024160703070391408405a25445c10000e159614029824010109401c09081c52000240f402d07100301c0c01d061846a40c002410001c17080c650340c40c1808504a50091516400b034000c0781001070040034004000174800700150416504003045480700e040c0803980107012038a038100c0382d4010300982d202c1027580100030f115071040c5c0380300707020072041d120304628200e040d000000080741c090340164000f18102114004030b0641c0c154200f80b44904645016044020400c1c034003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 569435710 1250 569434460 569434487
    0x150c1205032706281a150702030613050304080a0501050f0603010504030906050a20011b0813121103160203010501080c090a020903010b0a06030c090e010b072a030f05150403 76
    0x208986401480d03034002e40b00071000c8828a0505120006802ca21001d1001030051001e20171b96521821002180851003120211600900540ba06070f40b003484000010081800c01c8810b80b00400000a80680078000d04103c00d1080d0000f10301814203500c401e201c2200503126038840d07450102484006038010700c88904485443c02d16644820b2240e00559100d002e001c41801045200d1329000b1803000c041d07000d40c005c07440751008001c05c0154508100c0b101f2204030f8803c00903814039901c1c000410301c4141d009071295807526044010000c3c04002608540100c039400b41d01000502e01c0d2400c52600303000c1c00d03002d480d840c4d0048c03841d076860b940000c0480c0d001071318110241703500041031100d64400b034001201541010700840d000075599400280101460990840000d06810020403104920805030b4105e41510000c282440042d80310700f16682c80700512a8030960b8500072841d200350450f0b0807000154040d0f10110041403041c00c0040c1010a01c0042403007945c6c01d40b081100283e0480203400025 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 569436960 1250 569435710 569435731
    0x1d040b0d0b0a021303081210180b1c0f0507052704021804030914090c040306020928080f0a0515040c0503010614210601150c1205032706 60
    0x1d459491200b8000d204101d0f004124a54056005c001d00070258010b14002c083c1c0121301580f41d440321592000a001401141d40441c0640c1100c00506d9041c0c0095808032402000010300f404240500031034901d41d0181141c812072310100340c60501c081441170000410f011b94103030304445c0884101f001e40078078403c0450600e07135884001ca0155110717540f060590000050350004d03181040d04024120110a1140d00b0310f40201091140031070420b410581c0c040c1c0006049a82800d055176120000307500009030180d040501c4081d648903090104140c01c4a030310501d1032059446044c40d45032810900300e454208002ea0000d10746000144c40000d6000352038092201c1e40340c85c0d4841381b412420007030640d4400b56040d0308000000c90b04282c60010b079101740c44c0403240d90000081204500c00d1545201c0741014003900b10708010000480c40f04150040c2408074070700f800540099a840c00044a240903464000a002104000c22910710610303251100c464402002415903800003074a40d521001012010308 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 569438210 1250 569436960 569436983
    0xc030b0307170f06090604150b060a080405010216120f0315090504051e030414120d0f0210060308070506010b03010e0c07150207030815220b0f0d031d040b0d 69
    0x2c4805002c9000d11461007829a401410710a0305241d980070140c0d016500d0300c02039821088180803501c909200820060669414152001c400b03039030f40381000f0b000b1b4499540802640c03842544111401141c24841c002c0710040681c60704004003090586081201070601d418010030490184508103002c884d103a540200741d5035920b01c0c0003420295603400c2003071181e450320508a2541000300250086e280c4070b0b010000c0c41440407081140380b82901e00811a66000219030100e003600c603102103510307000c40d0b0045400c400d04504124040364080e034001d84000d000404c9901c208034040c0032513401003059060b60b60075541000592250007a000c0c0400b500e252b0001410002c1155a82520305030030642541152510003a0801400e1100b0032540549486503c402415907450100d02480c1e100c0c0c0c0ea040c7e0100c00c03190340c100040c02401a180314035071042c50340708145a10fa0381c20240310107041c403d558041c0386480c0c0c0c0303041165040a081d0418412801c1110a900303680b12034540c0300c134947e00110071148 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 569439460 1250 569438210 569438249
    0xb0901020424091a030a1109060306041a030a0f05060702010b10030e0a02090c030604060522150f17010f0b0108070305130b07110c04051003170f03070c02040c030b0307 74
    0xa6408140c0d0101c030041104c00b0508a01040d0380e07000d14403460109100f8480b01c0840d040d4a480c07845480003c81c0d010303405001180080c2000d9008110001c030f0b40400d03c0c004500e000c0040d242003108802211102c94405044007000002c1c092940c0109650000748188403802c80010130842070006007504140c1d4403075240c0803040e4100700381070707034242c0141544c0c50701e091010760311900f03600032510079024034105500090103082500905100154481c0141800c0d00c80d444103101600c101c0d55011401032140c240420070b0240b000030100208003a411086158860031070f1203080d201ea4011801d40c0c2031400500c00c0c0181d8004466650240b0107180000e6270b0360310380f000907650950614001d041c030f0040300c00300020076820006d0941d1001510040b134011701d80000c1008260b5004035805240c00f4001d4104000150000070050425a0100c001c9800e15800e15106500ca8000301c600100103110403107990290b003028810345c0346c800740e0303450144104400c40e00400d940302c5480c0b1980403400ca5400d0f0110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 569440710 1250 569439460 569439467
    0x8030c0d06060504090b09010605042702130f15083105030306030c0d0f0b0c0706090501060f06052b060302040908030609010b04030b132306040b0901020424 69
    0x4000c000412410050592210360060040d001070146040c0145048400072691070b18214450490f03505580380b43c605410001d18890448803a0941c101a00b286441c400c1243d4540c006411b0011001c412461480e141814007a05c4441d01d41c0110542e2075000408000d6960000030310754010100e0394500170036102ca0b4000b03006800307800b410340c03170b0f280c0c9441d5032408003e8080015130090904030201c500c4024140201304c82200d0f604001480c0c091001c003140c000030700d07251f180c581c00300000a400d4100205519080203480004604450a940d0b80c17409100d074400c0842c00502a05e42460414108809103800003200c04489105a0040c4030304803001440782d107903800807405194054030601c005401071404006503007003980c070284203100203c0045034000b1803406030b804680d0012031050250f01c40340040c58820101e444256448090b090002e0341d0146004119203140d080d180c02007180d4500b40c203007448240c0002e8504200d5900421080008940903e2581e1101d440d5841c3c400c2c944041c2038068 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 569441960 1250 569440710 569440717
    0xc250b04120c120f080106050f182b060c0e0603060415053d02030403080d0b04110904140112150e0105190b09010f12060b04111b070803030408030c 65
    0x50860080b1031644203c0c2e5030003d04910307030100585032070050366200d5900359454003070f0380702181e410042807000f601c5003000340c8010508000f014010208282003211104269032401c0320703510060103003e0011041010360310994400323444034604102c1003140400050341600c406403019104540b20100a0301c2e000400541c0c1c80148401050200300b900300c8003410a40c1c440003044052584000e080602c03070524580c01d1840041d00a41c0650328060941e86c40c034440d0b4002e55144e180c41580c45010748402c0d200c40c030a45003505421180aa21802040100016541800308103031020206e640108107840500090090040d0320524000c0c001469843d024024529004000b0700c0350b082c00140103003007400501000440e0b0181005001d490850700a01842542c28800c0c41039030001d5040c10062000e9608051034602d1003071902050044410000070240c1c3e2028110511454000602c3c011000b0500b05007100301c081603014115052804001c191240001400648079500000000c3c000c9041c1d00200d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 569443210 1250 569441960 569441963
    0xe0109052407081f0e070f0215070512070c0501060f031104060b09151213020a080307031209050c031507090801060e0103171210030b2203031e02030c250b04120c 71
    0x617403829281c00e2400810740b518514015016000300c0a0311588004150281032050b01d9644402d4642600c2c5c81c503061010000400f290200451401c01d580055070a00442e00200380c0c1c816115042c0d8151b00303281d5200d4840c030000c0c0744514076001080201c01c0d01c275800d940700c1010807500380652002c40000174003244030381011156140c0702ca80400007070201e01d8402c0359605009450155601c0e4a8000d070030f55922078140c01a000c645551002070755807005801a481070b611540594003011122070209240080c1d440d80c011008003084100300240d58803800c070300f000344100340090100d2450701020440a20060001a00b066003001246204003e20012200d0060041c00c0b500f02620744004400b0a0a01da4041254552940380100f20354181d0030003604007404074008440440d801c41d035415001015a404100480000c080007804854a1403010b980f0905609848035038504880200340410f110040c42c4c9040346c01d08950a1000c5074000c21202d500c04e43c080d0100d94a0b280520301510b00306980b0301c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 569444460 1250 569443210 569443229
    0xf12061a03090616050d0b010c1202060601080c120a09080f070b06090a0b0f011215170f19030c230a0b0f070f03020d0e0109052407081f 60
    0x44000386140322500440c4103901c1031060700d0558880c4c1c0031851600c0c90000020002800c18040800b024640b50301078000080c05041c410a01001c42e51805000030408544201680009042240558104816591014090f00c916150084c6165018944207020b03004c401d01c4d60380e41a02c40704203d1901d0071200c1c50b4042082c8603441e1401031074408101001112618050100c0c0000315400044500039414007604c0104102030f0401c01500440780f40d80745580000c1c405449101038603941003e1080e60014000d44050720b510310302c450000c1d6240440310591201103900c0607400c1d101d41082626441101a81031504e902060114285100301140d4200341c045a50450501840d018ae80020350044281c8241451404d03683c400340d170110342043c125602000701c0d00001d0000e00080c880d600a001c0c040040c040010500d060103040750071035840388402c07210b56100c285e40100c0507964494016402121011b1b501d0640340c001d00040a17508050048482c1c002e2490310520403a14a00c0d952024004544 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 569445710 1250 569444460 569444489
    0x181a03011b0207061b030804021f020a110a2105030c331b09130c2118060903120c0909060f0e041e0503030a020304030e03030306010f1206 61
    0x254801d0003030003400d420009031041e0240014800e00590b504121400d0068441c0c040300035035241500c21010042080742e000000711203141d02c01460181e00740ba4011f950b030041c0b58000440c40c1c5a8004040c8040c03880c801c0c3e807100020000100b44113440c0d485ca0141d0820401035140d81d00d8078a02c0c60160800f80c1201e0700507e0105005040469903507011654a082c18001d4948402d00c0840912400c0c1c59074000c100f2181d184807698030704031000303054108c40034001100c1403258804e007208036003820700c007100000d00c034240f14070250842c5041d861009000d40020440c0110014580c0118001584c000f4945901c450404051602a08030300c944580d464a0078040c0c08840d0400809024a40c0504181c00f86449404036502d00221503d9041d58004005c0780115100d503220000c0002031825032003803e058100c5580e0005806002a41c051800401c016032a410f19181c0641421300c141c3c60540039070310910402a40b603034800c1415040c4081410300042d690002d50101c0042c0c03100350440349001c1c0516 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 569446960 1250 569445710 569445731
    0x106090e0a0f141038060a1b0807020906100c121101022b020f0417030712050d06090b06031602030c03070f0c050d08040b0a02010209150304050106050102030301181a0301 75
    0x640201403442c2001804c601442d40b95250900080d0001d08403921120860054803103601b0403400030314008841d4203000010405241e0001207440181c00300b12a249408648d45003107091101c5031030f400039000c4070300342e0545040541c0203060400d1620040e004101c0383d1442c55030a4040c1d20080341c040c1003a00295690080b2140d036080350700d05540203c40340c0c01d0700e1040c0f01c9291194400c0d10302c1041241d00c05807526180090f0000d5034811007200140d00d000c20000c601c0060740505410f8a01c4003551952601c0e0700030030f44640c080700c85a602140b1850300306416200759a036944120b0341c3c40061111b4100c058021010105d00d1401200c5c5007420620000804900340078035211120381d680d101d090a0001c040e02c40c000e104644440460051600d4000d001c14850340c2d0080001e40b030050f03100d02c0014181440c0e200001c141c1044104510400040007051200f0b0040a0080c0000761034207000440ca594581407010300c1449201ca444080310b5030347c40d101100442c40420043c41140001c0c000d22140614 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 569448210 1250 569446960 569446993
    0x306041107030e0108090303010b1b030c0109030f080c044e060e030c03030c0c1005040309051c05030f090114040f061b0305070803041b090209030106090e0a0f14 71
    0x95004030b4017184400c400a0480c01c400412a8140c2e14189446070408121710042c905114a814101c80c140c0424080505e41e54402d105901d02c01740250390b2000503101e40b071b001070502e80d0058111aa4480e0404c428800070103060000c0100702080301410904400c0900c204590304003001142001400c0c461403d0200c14822a0011410740100700800407210f814130040d580784550242c1d8070068000f0f00001c0e190403001d001901d0682c90440c10303248103030b03c130030880707401c8480454048001ca6141c5009004506240381d034103059001e081e641c0207580300c89440b6070f80c2e07a0041358a003503401c0e075002502c02100d03486952003514048407542c0aa481d10340711802d03810180503600900b00041c64042d00340b00700384c103040c0c4e52581c5240c05403103191510580703498110749548018400c2d0f98102c104c90101f07480d01700340100100140b420a5005032035200c0c0d0000c26080d10055480324900c50304000000081e01d10101d9009142d65105900e07247c0030070b4174642240d03110045103442c11030380a51199160201c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 569449460 1250 569448210 569448227
    0xf0305071b080c0607051b030a0b1003061d0703061104050604081507090e0403050a0318150b010f0801050405060a0302030a0c05013e0709090c03020411031605030604110703 76
    0x42c010b0300c894080c07450601031540030317400c1d002d00194800002182c542024950b0900081806001d60f2000012526228280c40c01562141e0442c14170150030010301c043c0d03126103080240aa104941111080241c0641d038a9140c08064a407903038840200e991604e9030301c101c0d801408082d010f51b449503a10041980c0320340d801060240c8605800d400075220500ca13105c560169048540203103a1501c0e6605c040300e66401c0091807605240d906c0c1001154003400034000c0e1042d5118055032252546444041c5040e10300c0d4503030081c14007503001c04251400f81c100340400c0c150f40c0251000141640d40c1400150030301280c1c0d0000e5094001c0515810602a030f61011100340c41c1c0030b80b11040301b86011035480c001048040107072001c0c1e81301400c2d203a00c00303e40341c4107140d00c03810301e98100d070085a107502d111030032130f1031140080307a41e810000c50400c2141024007881c00c903000d40c01842415868202c0c103402c9a0805162107030200800000010160b03030340c5602c100301c0e8103c0703e041d83e0344480d002d00c0d01624861 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 569450710 1250 569449460 569449469
    0xf111002090f090402010f050c03070c080f0708010c051605011424010503281d01061a04050a0b031e040809180c0a0e030705030f01360f0305071b 64
    0x2c10200c060021800c00b9412103000b19410307900c05e16001ca840b44102c0300c40c1c2003030340004000e0104000320004141c2d805401009442d04038040e2a0300140408824074000090b0310603030b601d90501d14410b00b43c075003002c2610214a200c1da074410700301a442c6001070040c001d0b0311f003110691303c4003818040620080b160700c0b01c00c00502c01742954141e82c01001910b590004a85940c071103c18010000a0405501c80c02c41c10130801031001f040c5030143e4041c0400428480c00085002d81d500d042c2003005595000b50f2050400e0f10021403442e003814680421144078080c0140c880401d000404a60704c82c0a0a11003100c148242d10000d0441c100340c5030481e540d0344035810480c806c0003803001d40340c0080750310098640034210f04c42e12240740580e1003600707856081d48203400d0b82c2d05005960313001541d92002d0082008100800000082602c00b42050224034030104000d069000600314055001e45080080e01610a401c0701e0302004145032481d044499119024000300f0300c11800c0c1141010207440b03102901a038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 569451960 1250 569450710 569450719
    0x3050601090b03090606010c050114180c090c0f1b0304091422020f0612040606080d0c0b010603051003080d0903090902090916031401030506060a050a060206070f11100209 75
    0x3155200d09910b000e0100762603200e40c40e041031010074070a40c0281710900c05244200008190100440d030800d2060000707c440311203038011070f03c03643c7c4c202105209064404000b200c1059160034000c0c4070354440d01070345000c078403010b40018603c00c00c01e00c0020111911480711080300d9580b901c910361103000d040000c1c080c2c0c02e940d0581010504504901e18202400100e403465586480b4898080000e41640010700c0b07900b1040400045008a0030344242510890140201141c1180750500b008d14007a0070946a00130003c0c180c1d4080000355200e00c0b1141100c40c036180c041055200d05032038519490040c0e2001300500f40002d600d012200840c0c001e940950300a17116200d80340d94913a0342105038441c62482030780c0240c40500155050603c0b81c0c107608056250700c0e00041c16070401840794040c0c40c00ba04299101e51024041049514200742d904020704401d903008203000b40340040103542c5074006030500c001c2c8a214940030154a1240d503044800c1941c0104070703808101c207050f114000354041010503004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 569453210 1250 569451960 569451977
    0x31215011116090c050a020a1b080706090e090712060f061205010c030b030601080d081005040207080c0c030c0901031e0b0a0f1a0604050904030507120e0f0d050715021c03050601 78
    0x83c1341c0590195450380040750007400c14080641d0300c0300803010140b11034414007040020086081e4a0820002c0041d2060340c8a0380140350810481600079007004000340641d0344000028420000941c2c04602c030154008004200c0928180400000c0d25494004048480440144070700303110054000c0341c0601c00303c0c2c50403c200b05684003419110102409180c05030b51140100130071703651180890300d500020b02c524144403d51500e00050990380446001d40f518080420350341c0d520399040c4240311001030b00318002c080c46581c00010488400d4144000761174a18142d119140b1044161026040707954070102d69081440c01481000042c064450b0f020103141c5400d80007810300d003c85460f14095140200f9150602e40b408040290020000701b044081100034030503040050010301d0350446143e0140c4171084000d03c1403050040342600b41c088a445105201140f1003c80c6010a5860590310000d200402e2030410039001c2c1e140c204000d11980c01902003051200f03a00303a01d584601d0241c00241d842440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 569454460 1250 569453210 569453231
    0xb181902091303020c150c0601031a0f0f0a0b01020f01090506010614070b0c0a0c150b04051311040c03020f0414030705010903050303130f0b0906010e060303121501111609 75
    0x44010111801001350f40440700e18001450919021101606100f10f0107242408003000141000020317032003100c20b000303815500c0b0b84840720300800c40c0d844401290b500c580c901d818075804450420280c500300096994a101080c41e074400c1c854190410400e6000303000f0220f051800179039608091040d000000d070f40d0005001c0d0800408125000e050f0003009283c240e0f20341034440790459000340518824818004544000180d48800054404503200000600b030800f50f030500c02901c1005103040f611019010100303000519140c0007442d404c100fa2400502c05d00054010380017849218400c5810b0356010800041c1304e091242c0111034010305500b504c0340c066907080191031030003060100810a40052002a14002c16204040466801070f000808486800c1d205c1c84003104091707441c00519080304e030041c80011169000903070401002e03030066243c6407201d004041c841c00c000d000004800c5114045400e94ce00c81c524022030f04030140142c40c14031650a10702065004148034013003c09081c8a107818 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 569455710 1250 569454460 569454481
    0x9020a091a12010e10020306180708071806021e011d10060915090b0d020d050c040c0f05091c02031207030e0303090f2709010209011206030f0b18190209 67
    0x841c4422281300a150b94010f0014800103500b00070030300f9410940d5128040154062030020320b00501960310b500380c0c0c0d0b007000340004049402c400d042c00100d01030501c1c10044540c6c000b07603094901240c540c04141900c1020400380c0500900c81c402214405090303c04008488007060490fa100840c0e45e0070403d1a80e0b0700c907054150f5100d611000a0480081000c10120a030354001c0390440c10000c1200724282001ea000900c58a41c4600c11b488940c8044410070460420344610f441c49502c41c103207055a420030010003031040c4240b40711903015400d081200c03400040354112420902c3d5000381641d540040e204074000241c0c12800c8286e00164140d003580346141030100c21100502d6026110744d446034015018000d809421080c4411011031882c605100035400c803500a0040030003500250740c0d42e80d450001400790314a00107904d00d40703181038010400240c0c01c83e40401d01950249440106940c5c0308408401a00ea10749519528040c541490211001850403601e1240c4200c43c080241e1316205280c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 569456960 1250 569455710 569455721
    0x110706050f03040f0f0f140f1b01030b12030a020706030501241e1806031506030b0319110103140601140f0405120f06010b12060409020a091a1201 64
    0x1200862020061040748010200c01140d0013801881c0e02140021a5a1100d2003a49600006e80b10885809016020000f1404601c007907420000c0c0106045084000910b403103000d11841d404c20f00c101070a00c6a01030340690007840e090701004001c1000c1c60140c5402644035400945048018050000c0201d4018000e101d1103059030030038040807100c101c810591030b6010258036040310610030584001d41100f0014200703041070903107507548c88401301c010780091182068241c00400c203040c14000e02d10b5051903803142020480e05245404202006c144000c68140808010200801c8107010040f009203c2c0c40582c85040000a99081104070b08039520420f00315400d40740e4500041031441d00a01444280c0301800e13032002038886c80313860155284006030b40c0303140381d904600c0d41f0f40021200f0741004c1030601c04a030040c4506100a80340c4143c42001c500039040090807144519502d2080d0720540d12440184000f812480d001040544080088203441e040c9201c4443d21030b401864519142c2103040c0900c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 569458210 1250 569456960 569456969
    0x13020909070314120406210509010c090504091a04030c0f0803191a0405060604051806040c030e060f0a090b0901090c0501020106081b1c03110712030504180f0218011107 74
    0x140d003040d0034a86c0886d415500d403d01ca44072400652100610381d0600e00c2014010824031000040c1030480c0003025022162030344c07050b80300c1d5140c01100c40c0820308200c20103450700c4081071503003003960300d0303181c107a60307500c655036000d41f01010b030f807515500b0000e481c0015400780072030411150213000001d00c1e00d01524040035000c001081c0c48586240076007426000181c101c04001c168a0800d03440310b000c50780703200e4040019224402e00900780400c5041c01c2c803405018009918043c403200c07041d24061555008040c114007041c1010300d000031f0800640754404141d440d8880c060240a08160b0300890281483c00415501d80071900e00000b80c07580148984000c9550110103003012620904000482d0590200640d42081e020001d2200035483c064030800c40030300c240c54a100000c0c96002007450811582c01c02000701101490365004660080d0a8604681c8a5040b0030444861b20608201504d8080b2140761714a0000c203050640751100c075070792014810300b170340c40c60244400f04042c10303a106000e10a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 569459460 1250 569458210 569458243
    0xf0f090a030914040b03030a051e1809070e04060303080f0f090601090b06090402030112140c09010b07020118030b09010e03040e0612070e0420010e01021513020909070314 75
    0x1010409a0384440001c0f003141c400800000c0c0098444000c641168020300d0303104005180081c2e0f00c9800c80310060502e4110758005070460400c0c820b08205440c410211f000c043c400c40d00c48000501072445040000d490450203441440180c1d0f0b2464082d251200958280030380ca45490001002444060360315446514444000c1c00300d030b4070385400e500050603464840b54012208001221007902c07240019030007040a43c64001c0001c0d1a420103080340c0a0064140c100c641001c45a4545039a81649007410340348511785042d41c591051006172b501910500f9400c0c14400712140000030300c04145212440354000724001d000400040402c203449128038090300074403105000c0441c00c40d05160f8502d001031104081110103103030b00c4d508024138140c0200c404a0741d6a1109030340c0540c1c50010780022008110071b00301003d661440a002039114080310724622901141c2c4000603001c205610040750105401030000b08940c200560940d0321005c0500095a0b01101d5501051154a00150030076240c0010f00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 569460710 1250 569459460 569459477
    0x60b0a170f01270203090f070602071202040b12151501090f1406220602010b06071a04150e010b090108070305100507140301060509090718030f0c0305060f0f090a03 72
    0x503900b2059006451114031048460340c3c0d440881c5002c0d100a5000d00700200003004c1e81081900140d1500255800601c00c5411081d010072221850b941956000e0f513040b5404501c1481c1d40c80800c90209003440345054900c288030454501001c0c5200c2e181c0196148200d40b103450a00c040103699144603441044c1190340802c0042240a1040c0502d1246400c0200118980f5500858621124420581c11070030b21031519401c002080d024401c856001c0f030b01b5030b8118200700380c64440000149407101c1d00c3c081c1c140040c000500b0024003c10328101d02e00c015504004055956040f64000c2400e811624015122580003041d07030f8000041c4801143da000c8000c14030303811040e00d050302400c1d002d0304003001d020030030383c203c0000842c040c0618003030141d60b9111170719241c4c58010488003140180144051007070464010420160580e400700c06c2e2034028804500409007840e03c01100e807002e40c07014205000e15010300840040500c00d180c007035000300c40c1071517040d2141d0303401d00e884101221004002c580e140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 569461960 1250 569460710 569460719
    0x1b11030702011b080310080f2b0309050609070501201c030f0c080a050f0c190c02030102030a0605132c0f070602010507020f01090c050f13060b0a170f01 67
    0x20f903940c1c401080c80d4001d150042580769110b801c9034009076040203000c80c20070b07414410000c01304681108107549100505004000f10300d45814150740e4240600d485071080a10543c55009800c0390031015071140c1114010302c1c1c100c07601600c0e00040c4c000d080c0041e0100c1c2c1c50302003036580510090b0003c19100040c003041ea8030000510100c1503281f0340c10b820315850b040300400480d0184183c40215002e902c401c4d0340b5113884110a01100c400074003000e83d0b00500d00a029840058400b510200142401c2c1d840360070000200a031042516090000d6240d8000400c0051600c500e0700403100300c45060710090303407a600d105240019140013280007000d070240001c41e285514070740a000c4082031600e1003900d000480c007103032440c2840c003190400320142c0e4603941408496541041b0303503444070300780b6002000444515950805c0781040c2e07100307141c0709120030413803142c3c1c3e41d6800c219602034244000081103903d2b991440800c16400c40380c140c10100c2e07054056803145040780c02c01c0c40d21a1081c1e5070208401d0b17081 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 569463210 1250 569461960 569461967
    0x106080c0618120604060603060c050c060720070f06030e0a110103090204180b0402101b02060c120307030b090a020304260c190605090a030801090b060d0f1b1103070201 74
    0x12512102c0c0c0c000d410f403a004042000520295004a0051101080481c210f00301441503541560004080000401142006000106001da00041039140092030007c200ca04030a04418941e000211801200c40010b10361540c94213160440e03207140c80a200003d0002d00c011344444048c1c1e4050a5450f10f070010074540e61207036000302c840c43d20090000a00d0f00c0b02e44010440c2d0701c8085000c80e03940b00d0490900c0258075010b000c80c244207a19141030890468a00c00b032245e644031101c8024040c1c0400304410341000b405102c0004884455080c00c5d480e031400d200c0080207482036107010b6028a01ea28045642c032402c9008036840340d40c01405480742c14240fa500e048421045440c40f00d096030062140c082c03802010b22070381044910305069240c80070698144201256000f0b0000e0f84554030010041e000a604140340c2d0b41101c40ca00000504003047c0000b26245101c0e03145529203d91400701240c280800075441a403020141640500fa07405090a007035801084107826900c20740d00a20404005610 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 569464460 1250 569463210 569463247
    0xa08093a08010f09021c020a020d0e0907050909040c030f03021f0209060304080a02070504230a02040509070c0302160603050f4213060303081e0114031501060906020106080c06 77
    0xc000b00400000b002e41c6ea06800700d801c012207910041e0451840c201125074800301c0c1c1e046184003104c8840b2542007080010713213980704d05c1c021103004064440001d824050b401e07260000a5421400038080728540b1310b0025200c00300c081142c1104800070340108003c0503248255004114007400591440c4c566880e03c02c1070303801c010030440446c850340d000032905460f03d01601441d80b64100307908052049007a00ea441c0900c00804015480b841400200a0703907803040e20642d00701449040000d600d61160404030b00b849500001c544ea8002c0340000003490035071507840039205a00d120440c0038952030714403200d040007803400340d24506035403080ca02003030a0013071140802c40d820320407010720303071880340d0001159a041d445000da10b85030703644040402c14160030140c542e0740a0702584e0f0f50300038280c40f01950761900506003c1c001c40080708001c1031800c1d46040011002c1c10b0381e00724408840390703500c000007460b520460003044019428072400081d05200001e421047ca2001022282450381d00400c0045851 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 569465710 1250 569464460 569464477
    0x90702070323030d06180b0103140c070203190305090a060f0e1201060e090f0f0604030c11010e0d0f051b0303030a0b01030605060c21030c0a08093a08010f0902 70
    0x108600e1213042043d02c254401413010301104040649400300740c1080b25000041c190516051480050b801e101c40688681e00040f100c100603103d0810b4001702c1c0c5080703148401040d80c0010200c824040c99040b1000e040840748c11190445c1c80390701c0c4e4500f120005a282170304070206d014661005001e00c0c140c10601d00e041c1d64400002a4140d0f81d030304207542c10030140d43c00d8901d0740200d0414000e40e40184200b40101c0070140042c1031340c1c00d15541c014021444070b240a8450041c000c011040c90b0f1098917a804802c0c00108082049080b03410801c60700140918212050b110750400c011244601a0766901c0c48003000380503500359a580150b84001c1e108100405041550312000131600e0342d900b201402160b90b42c0d80040c1840255004041d00803d5681d82c505d000c5481072040100f105008000c84100d4945460607181949400c2107031442d2800800800f42d01022880030401080c2000b007084c449218096601c0c0e061042c6000d080c3c0d2406400c1c001e00700c0c41c01c04140f090001c1e4446400604030003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 569466960 1250 569465710 569465713
    0x906120604150b07171306030221280b060d0203090c0a0b04030c0b03040f03050d20090109140d12020a0c0b030a0b030705013609020702090702070323 66
    0x1078140e034a4084000308079402031181190081445020b10551407481c03035100403603030412031400501180101c86c0d12098030035541015000550440d80d82c0d035841d015028801d41d4200b020f0242031521400e0050380541c4000b00402d0303070b0a00401c03034800f4140509400301078060712441c42c0490300d58820010750703c0200014058821450741e0802c0d5183c00343d443c402014008150798595017146043c034040555030b40034201410f0240309010110f03003482c40116034540e05061060b59620f061900c44094480c08030002510300d83c40d1545c10100c0600d80c002c049000c400da961601c03c1e5142d8003445018040f00080c40d8000304c0b581040400640301c01c80040100000b030040341c820340c9056607002c3c42c104c0747c0d402021500102000b8003404180e28020b910311108124050300f0300a00b0900024481d0310081d400e444090b8011050003101011340805803045860a1018102c0c540c075050008040e5200704000ca00456150001540140c4045440f00c140ca41c0403110f031880c089141940080300c440788070640307850b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 569468210 1250 569466960 569466971
    0x2109120c1b140a1401121e0603030e010905031f1e1a0a0b0c0a030f0c0804030501050403141303021026100501020109030806040903051204030905040609020906120604 73
    0x20154000540c800802c6102c1c400394a6252850900080c40d03100d90007541109003800c803815a9a030014124100344c0320070b440020f42c6010300b1840b6149182100c20969245141400c04000d06a110705907500d4580282c0361540c47c1c42d900c9045c5541d480c0100c044190f05000180705c0f100c200c2054111988070011801000e0840c0c041c000340101b200c00a2070f418180c000305c80c1d076400880c20a54020401801c0e4194910f00348100081c5140d1038016125000702002040c00c20101d402e030049100c085039640294466071115140e10f041070017800f058a040d00410302178003001000501010445118840100f2110b00f9985150300303111030480b114100405103c00071b04403622100222008807512241d081c3c0240050629503002e101e01844d80e004681164104014400031a400a24960304a0410b8a000801d0080741c10102c03003a002c4c003030484000900c01424031003490392021294041d90030031142000b150340da0303a00080403071003020346094128405120002806215040d499449007016001066 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 569469460 1250 569468210 569468243
    0x40c02160905010305010b0d0816052e0f0209060f03190906050a0b010e0105090f06040b03070504080706020a12050a0e15040311060a020a08070609122109120c 70
    0x65154a034000e0340107955284010030600500f4001c05515070416030301181c5220094549001500c142010b1448080d40c0c0e4107a0b80030880108480c034000064600c400221946100740d075404405000181c143c11800d001460502c0f40c46442140d5a00354000c12443c40c1207000020986039402c0200241c41c0c7c01076541c01081350001500404051500c10140000c081c42d00800d40d900b1a81801c03031035070400c0200f0a40301082d0b6002011a8110a01103c40d070032074840040005d0514400c0b078000041603c03000c02030105003a0401e0251064885801c103a03590036403100070403661001d003c10301405c0c41c1134010f05040034074007a50091242580d1840c00510f40210440400c0011122002d0290311100029040084c0241004110032842c0200c0d002c0386000041c01c0e000f980c030079100001600700000020b4100c20060b1039840844e045a000010071045060038001400900d101020340b49020305c80c06055031403202d40d1140d040c041e540600019440d400101c2c0417507444050342000c5890103a481601c10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 569470710 1250 569469460 569469493
    0x50405030604032a17160503130302100f0c1401091b0911030c03162c01090e0702072c0a020d150f05060f0d05071205091902040c02 58
    0x602c01d500030b460701003051400c410b01c40304403032441c104018410b40c1943c442c3d0005200d6041e5549001941d12126100c514202036041c4200707184000614038400000c03510069103000480108a030300858649851210803401a1083c03008012034000080c0d40d4081000020020301042e13481c2801840001051929a61074100c402c40000c06075010b810318031010400f903841070042182c40404180098154203040816107814007010b441540552007100504000c00d00c21801c0d40c0415282401c00048050190441080a804089583d0010700e005801181c00c1d041c00d000907000d441d041d03008015980c82c060780d981a203c490741c0d0420155111010000c004104a86034901031484098016070b600031081580c0202c070018101030015201c44001000382c1c0c03108030b403c1404c44001b6240c4582e2100b00d98450b0b5094480c2c0e11042c1c801c1c500d850144102e0550040d985a2055400c8004120075290080c0c0c0643d580d802c82c81c4109007070180c8180b48018103154002032250641d50040311541c181e2100e00d10b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 569471960 1250 569470710 569470723
    0x6060305030a0305160f020a0206090103230405010b010302030c0d0504141002180d0203120706140906390d06030501050f040627110307080f011508010c020d0c0305040503 75
    0x81002948841c107100f4034480c102c0c0c100d41c017501c45007402c5e229000030742c0000e9101c001103207020384200404030f40412141d000c0c0c1c00c041d05d41d50b01c442c1c1980ea115118558003d40364000d46040e101c0d58a468481d40c2654000d2080742d01640d410180d103810440c14010300d10143c540240102c585030302d0801c1801c00708604200700f14444440040168440000d0700e030265110b400144200d101e04480d001d02e201680340440d80b00403081700800005c0d42c079099428281d01a004e40301200102c1c555920420541c00d6000c50320a000e00401110f41c034449042c0c2e81c40449140800c066141026416504803a04c1415140100b60746c40468001040b5203540344c45035800c407201140c00900c00d410820420041182c14030a01501000305403040542071072170340c0c007408203184414004128807200208d030440c44da01005228010a4080100e915440226103d0307030180920130301a1103043c69091012a844006004a68540807035500a211410b20300108651010381c080094090101c20000400e045e1002e100b82c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 569473210 1250 569471960 569471977
    0x60e0d02011e02010608062d090102090a0f030308061504210203191a010303020d030b0f091504150509040b340f030515040b0a0b030f090c061804090606030503 70
    0x5000361074100303014188000104500c950790100185040140d0f16070100c1034141c14801c80d088e00707607610f0f1003009009124040c489076200340c07032500004030107428500034410b580c0709030786802c090b40390320080c0036060410009803040c408040c03006010513800e900e01c2041043c0742120b0100440310a03004282454100d00c0590102c00703100703400d00c0030301c00181c1600210348407038210b00b0300c1c1350f1440e14001c0d1501161101c902c20075032201003000c0d07590b903030701c8000d80701c1c180040c24040e003401d20380c2940b550070881162150041d0708201c1d61513102d40798007080c07004035000030340941800da66650b1804184803000308019200b891301001c0000f100c11401913460084054900d9070a55020304c02c001d8441c60034040c00708101030034541000295075401c030b134807503180c502a5000f01d41000c0b110001542c4201942081078503c40200400c2442892120002d0180807100d0940b00702c0717480f50041c4010750fc102010710405c1c3c02c3c100302c199a03174201f9500007078085015450018000e40c50f959441d0039603010080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 569474460 1250 569473210 569473213
    0xf020d060602120f04090b130203090706020f0a020a051c0f050307061b020a151d060103020a06171923070807081e1005100210110301060e0d02011e02 66
    0x40c4034058040085140b0348030800450f90030aa5100000881440f440c001d407000d003900d42e4244003041e00c84010400d25030640400079900d070310340704200302d580e1149441210018464840740d05180807010500758601c1e03401400d80080709081c030007805902410000c9011282101c29251404110000c2010b801d151081000d19540c12040c1010002d6840d038801c0e520190310600c0e4110f03070194000507024125030388521002c1c1c007110514002d03c0100030704598104848442c1c0e003441381104011407807034140e9208a44042d001a1101c00840e400711000c40000f24412458001c500140204284e80c9a100303c0c050010603c0d100702d040710011042e800310b15080282c0c107038090100154000a05542c80107003071030000202d282441d0400d03403110408004040c020811804a1150003600703040801422028214000403614110000d6441d0342d0403008100c080c2ca002e000550300f6145000302c0703040301d00d1031756082401e04d4000c041000110307610f2004ca040c050340490201d81c0d00b05014090b40580b88940 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 569475710 1250 569474460 569474471
    0x906020a1b09060b1309060e15010c05011b080108010606050427020406050901080603060702030d36050f010209060904020d0f291203030c0304020109030c032001020303280f020d 78
    0x641709500c1c145941081d200182444c0e0240701c90300c10580256070104544050f4035240700d11f240140c0341e04810000c00f521650a01441014401c07070310060105c90007140c1d40300c41c0180c1e40d0341d1440e8222003490043d9000520108010071450310071030910340d40e200580d48507502841c50200d4500032640076520900214101080100c941c1da004001c540c0d020509501400e080c3c40c043c08020f441c0c0c880c44049801c51680c40000041c03061004480400d100b0803290803408003241009002503403011101d0072a0310b8855000340118660301030094920905000c1c0a4034100f0340407004000280d0081089140b102e640c503420031189040714016019200c00849201c1e45141040002c0c0030002c0035455554010700d8040c90950315000001308036031748101400c1041c0e4494440d4401243c17002040da10103441c400c171704140402800249800d040080c8416020f00076600248030040e0785074001120800350280031498001c001801040d82554041300380f500010304007031520074060403078010721105164940d452 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 569476960 1250 569475710 569475727
    0x130b0907380c07210203010e060919030807082e0501020d2303040c03020d030807080a050906060d0602040b0c030c070503010902090115090b0d0b0a060906020a1b09060b 74
    0x6940e46901c40701c2004403946031112100a40b9900e0829208012289001a42c158515102d44980313500003a03000300288500e00c90030b00101e039100303030507505107106010f044485c0514402441c0080c0510340c0c0b686a103007095694503016218500000c00f1541c01210459507000394a0042542007401981a80c41c0200da500b044002840c2244106000083c45450402c1200e4074104880300484944900340a540d41d40c6d07185081c070204580c66000a401c5059000c0c920700b015041091948100c00700e07038511101c0e80d9041c82c070030141d42c1d050702c029095402001c007087c07240c00d0002c60100c065024903400f40c0b43c15503448034541680d102040c0ca0342c00303400204940f60b0341c603403d0140c180100001c4000340008161030700050301100c0c06114074840c80d014829071219660207030100000421242100d292185683d4140001400390080c10501c500046440811541e01803440c00059030303596030040400c0c070025550b4002c0d60141d04070748407003910100301c0020101e04900441c809030400b171100d1760300d89149 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 569478210 1250 569476960 569477039
    0x1806030109060f150803030c2b02030712180f0605090a1e03080a060509010b0a020a05060a0e100c1b0302070e071106011a09090a0207062f03130b0907 66
    0xb135070000d8600d90410070900c03400441c204140c4840040d284e11416800048161011a91183c024030202070350000c41002505e030b800a0080d00c6c50b0500c504103110b025030b400140c52100c460071000614080000000b007020031119404241c1c01006501250803d9a0f50b481d24650413921200300036065060042940406501a81c0c3d6500110001001c1c4441410070001601c803400501074806400300100344480f00c0c510030001b480c2c590350080191840c9081c001e0540c40500708803401d00c022071140340000c1d4607003003591040d05913030100b41d0380b0b0084040c07000c1d201c80401100d590f800d87c00c621400c1d01c041703100d201e011190b0f8098459620780b00c51020380002e1082c108034050384154401d0071600d440850744a462421584604001c9940840300c2e03580c10311600c0203010382040500410b140c041d84868140010314020341c01585000d82c40c03080c905a80c000710b60361000b00d0b41c888003403200c1500344000801c100041078003d14030100381c0310000c0c0c4035030f41000050226501241c104441c0710703555040808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 569479460 1250 569478210 569478251
    0x18081b030601121103031c05011406030f01030605060d060e030a081e0402010c06060b030a0c14040b04050603062e0306050a0b031f0924050f1806030109060f 69
    0xd502030300c840d40c50200805561071105201901d03403907003044140c059070741c10f0040350f800600910407149120300c140c41610041c9001d02031507642034885080c103a05858540f0540b440fa0303404a400c1d1040e40c1c00d5a0790b10010302000b50072203030040c00b82496840003c0c020b000b603c0d41000039070015030b114010020000d110007c003510201c412019254098044101d408595500135020f0815140078095883c10000a00455100d4590083c000c01400115070041c1c0108000390070541c3e503041511044000c540007845107204030b040b541000c01040066040000143d6440240102941f854584101ca1020003440700c8940a00c10b002d141c2c0c2c2e40c200789405110b580c2c0600310642d200c0030150b0419442500c1440050040c00c241815101c9030040c400030307815590b0242c261403400780154841d50451003016502c50480d500ca0301050b810100d210305000d0000b00e8011030041005980398118041d01e10f0550000e400795805540304c580b0080480e98a02441e6940c24543c2000034600f603281078068100c0c103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 569480710 1250 569479460 569479513
    0xc150711090702030a0e13180201030c0f091206090501090c09110703080601030e0f030406020717030c0a0206030907121110180618030609080a080c0c06070f1808 71
    0x8507002800711032a400025030340c001e80c541c1000f0082c040090005040c000d401000145844c1c201200d0740552017160811214091003070700c00341f0076048020b01c1514000d02403000b0000041c02c940c000c0000704c400b002d10111150080c8400119042c66454040c2954050721041c0e501c501c0c0c4880400c00d4040c1c07446403810350107203d0501d1381442c0c0c0350b40c1c0042c150f840180c9054100f5454007249081c40c8010f1291291403101724040b41c2d42d4a40d80c0c072003e51580111300c201c9880d660880d001840c030107004811142d04205400142c491020190300b000501d41000d0a15000c40c460310402041120802c0b140134811402120210441d001c0c43e400c20140c140c000365120100000c3c0b0710902800101140003c00303440040c104081d4410710030062542d03204c46940080c00700c5051400400a121660004181c880d120703946442c2d282d6941d6145040c0307441058101b0701a60b10000004440d10b1050302e40042d000000d00d4400b50480303140c0361040320302005400040807074005584003002103201c04100d42c00076 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 569481960 1250 569480710 569480719
    0x13030e400626070501140304061e1a180a020c030408010c03060e09191e240c05030f071d03011508061f0e0606090d0302010504110108090c01030b01020c150711 70
    0x1c1c1c00c0034002001006d2000401c2000207000c00494100011900040c41035090001e660b20440d954a921001900d51047c0c0009020402c0f560001641041c20b000d441c0440540041d0520344c4910550304029031041c0c1803180207000c14000422019803c0c00f40400b016101c0d0340102d00c1508000320400744020140c040110ac0d40324070a1594042081d1590181c001e8000140e81044588042c080c262004180f80040100204d0040c20b4101c9030600340301110080a15030821a040040c4415621440242c40035580782c01c9903000510150b104019803c9085c0940030a112050030318404079080d42d1015425020050003407006001e40c050030040035601c64a40c10b50039403482035014000c030500507103002d4a0342e1502c071200004c885848010499103807101c0901041641710709418000d000300800d1740c0c02c84500316070114250441d031045400702d026440c1180a403001d4000540190b0092504800c024154060b40c0000c181720381c0d0f00810440900c0506c003200307641c0d85c40b030300c1d081d20004802c3c1c0025105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 569483210 1250 569481960 569481973
    0x1090b0a02100f0219110615130c03060506030a0e0c1909090519050d020d1e081b030901020a020c15041e050913030e400626 55
    0x80d40011481c2c0e0394907108600183d11641c00d000c56002e4420380701c0c0d120130400045203c005c5180c0c006420070703485001100380c41c4551554000310224069012003241d218161544001d0000042e600880080040f410300181b010f0f0f0360000b04d1402c0c2c100f1141215015503a51440c1a0b2500901c8904071a0b4001c07a05c250605100d03020f0040320083c81d000d4540b0041d41c0c1d5080c80c0c01c21100f00700030031030b10034403079401c1d49070f0051407038a10303a500c2c4a60000c2005000b600300341c50b00c0034020b18221048000c500388070300d416402c24200301d45020005010000015001602162a910768002540100c02440000d80c1c1c401c402d00010f894100002105c501070599403100542c0c8031281001c3d030303081e260800030b45030b581c803d00429041c504065030030441d8011080d000f07102051050240c2101e05900c04e464580700040b40070700700403007001d0705440504203100606958148400200c1070325008002c07401e4001003201c8400c040000c40344140c200000d403460040c006043c1c02c600c41c864985283c1d850004051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 569484460 1250 569483210 569483227
    0x7150e151503060709060320030c040501140901050d0b1809070f06020a151e02040e060f18041401020d020409090507050306160c08071b05010e040e063d0501090b 71
    0x600301d45c0e100d1002090b0780c51b002030300c40125412009403241d04d01c45c51651241481c44006049911612569001c210f406188030001001c10041c0c3d0100da134161038090070440c49400302000341948850083d80001c2c0c0c8110f190301810b50b04c1c8424050521440102402c90400704512059015a0042c1056500c4215108002103030a42e40444180355944041001c981084120880a05010007042d40c02d00106020030314031440c43c91103206d01c80444404100544640a00140504140000c0c1c41c815160002a0118568a42a0200e095200001481c040b80303418524226000754200a800e5501c4031411000e1200810000024110440181109042040b0000c4078003071010b603e40c003402802c00d038040901c07081500f500c9490f0b0b04503118090654500188140744a20782c002e050101c0d141c0c50000000b820030b071240d16085010400200303000c1e2201c05c0c108040d4a40e41d1803d2904285102108942c00000c68480c04072a201d803c01d080b40c0341c200350016200408a41200d024240180400d10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 569485710 1250 569484460 569484467
    0xd14031b0d02010e2a06040605030f070e0f010e030732040509061812030901020c0601060219020103180f151404020f060a03061509030317060607150e1515030607 71
    0x1445c0c000e1220342120541c00254009944d030070321800071b034403a01c04140040c180350081c1c0114401c0313914610a016075600d4400a0b202483c0c4503200e140c11030307080110354140e03500400003001580d00c000d084a0b0066a42c0d0700208410020614401c0c0006012030107044520086181143c0f01d58104d8090049191a020141e59280020641107044030380c40c0c00c0c621010310078061003e45c41b510291140d03407890620b082138003130341c40079451402c50710420f8000900140f000c82c5481c04030030304070034040115095070011005402407082082c451403850f0710540001d542e910f00c4040f024070034100c5060f4005140114400c80342280d0103c2c000003040001c00c001692446060100d000c0d040350495114103034010210000c0446421151501c3d40102c5c1d002940f61304914840100c2c0d100e0750b41c01035404e030044062a52210140d95241d0042030600800e03001813400c2c9035031003040c80d0303e00001400e0611250840d242c030100c0548219142d40c03600c10700104d41185040e5240f000d07170039001080582131803e0000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 569486960 1250 569485710 569485723
    0x1502240f040803150d0b16020c012007150810090b090112050102070210020106080c0103021201060e062704050a0207050a1e020406033c020d14031b0d02010e 69
    0xa00301c050001c001610081c00d03402070a254200541007415168580c542480e4880054030110800110307c0c186444040c4000b0b45100c0000041c3d43e100200190002c5002d0062800412602c1c036001e00203004c00e80c601c100305490341c1c500e09955100c095042944404118610680003027048604150001ca02500c90854440c1100c812050b8550750020504195009005442d00250f0000d5030f21084002103905402c41c0c1c0945021800380c1d8a0346629a005504a03c203211800b0244503000d4010000540141c61420074a02d018003501e2a00a10740070002d0140011004070000450840b0a20041e080901c00d0690115680c0700071440d202d51610781ca9a6403000784401072101da0a000400c13200082454210041540507000740300741501c0345440c2e1080965801c00e018883c110714020b03500d50091091064612083c00e4848180e5840c940a1240341c4207a4030f010b4504201d0b1040301d0381140b004100910303d156101910780e888503105028641048a02050041107a0410350028085600401e61 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 569488210 1250 569486960 569486963
    0x90611070308092b141912090b0703030f05070c1109101203050d11070201091401020307080a0c050c0303191211040608040605240103020307091502240f04 68
    0x800c0c0d140c610200009214a9001442403070411030301d00c0868040049491044e821803140c4d12400022000307840540d59003911000d0541e03107000028001020407524030100f00d0380180c03460201d50b050b45888044141f5401040c040b40002c2d03450000707440c462104c1c0302c0c0a030048800d14209091480c651188054000e01011282c0318100d40d0012904242090002d0b1004094819402c0d2045003c0e00300030741150894010145540c0c20102608020341c1e0f0b8404540c40a50305840344120f080c104178005c1c0010310a00d0b1050305510007040747c0e1b070210795280044d1001c0251984d030104000914a8601c6c14001d03140c41d05e40c0254400e0140709840041241407038104071961500e580703001c06009942d405800d4013410009a030f400080d0104900c1d40c41805a2311031400780030288859298100c202d2481c3c40e80340000700c10040d1040c034440303141d0320036002190000d460b0701e000e02c41c9a44565880040c2000100c0b00c60240c3d20880c490008070b101d80028041c40041300c401c0480e20316101c0703010588107400820 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 569489460 1250 569488210 569488223
    0xb030406050601030603021201150f0e07050c030f070c1806230103180506041407030c0b1b0115090c050c06060114220306060b0c0a0209070201060b03160906110703 72
    0x9180384d12030350180c0c1c0110340041c00c86a10780600400e450007000c8021104e42781001188011441e0603040c0c1c008000c40c0c0090728600020351340c0b00001c440301d4001e606100341500042099051204100014005181c05980c0d40c2d080d07540361052040c12625101000309615007000c0040044042803440b41e001c2c08a41c1100000c3c04d001c01c1c0040b0010180317001d00c0181d003d0a03443d002d0500c01f000980601c6140300345410702d03000070320384600d50362402584401001f45605070801d1001d0070340e280280050414040f0b802034a10102c190003425500d102015001000318035500b040001385030b0190b05450101070405501e0455004031150701c5080041c0110b050202c0c44604100a59901c002c0303d03040c01101e2040c2c8480d80301130b5407a0580000da4801a41c48600345072012445208110803a041145a24003c2844c3d40443d403d02103a44001010031066540c0d482d0000344654146000310f1084240c0b080003100340c4080400030701901c0c01a0480030130008014051012440d00050000c1603d07040715 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 569490710 1250 569489460 569489471
    0xa0c06030507020c0a090e0f031c021c02070609030206060a050f0f0303040e0a1505010f0c0308090c060c100f060602100f021e090114090d020d020a05040e06041b0b030406 75
    0x1000381d140010310141c0c2604a684450700203080f0107250f0040c0c7d03081c0003903800c0e120111070840300c6995900561000d074070402014030440f414030f02d241e40100407000c1c0c034280c141e03449016010082c0c202c1c2c0203c04140c13441c54490019204156050000c2e551040046072000130590612004c21101140200f10798002c003041c94090207140c0d820070559005041c04a104441440c103416980050400d00221284407400c088000c50b13a0b40c0540440e03452400c096450203421082e503102250083c50103002e50300c10380138031042641c09072200030040c83c0e42d0004100401165903001480c0c4101c1c1c401012100c511450004140300f01c82c0d01064030740460300440400300f145403118101600034030402c0141000c58000d6050016003105404c0a82901c1c44240c8176400510107aa074200968400c2c1500c05910081c0e1044400041c40c15010542100340080c140000e6244c548000c581206d2101e070518135103901100801040100288ec8820070303069032041c05010a00e81002c483c45800042d01c003c2c2581c1c0c440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 569491960 1250 569490710 569490721
    0x3100501031109061803011d0606013605061908150d0f0c080a350d0e16060c0b0121030503040f050604060c110604150b061b011d0a0c060305 62
    0x145101740308500d000700200200d201000d9845401802c0300d85c441c0c0a4010040060303060740c01092481040700300203890000c46985607440082038184810074010a607821000450503803201b1018160060456000c1c44200980a0001e084068018241100303030700b40c0b2000f040103071200e0f950a010180d204d0320010308040d030751807e00c00c0d4041030f410276a80e40c42a4207580301032243d542034003c2c0c41c008040d20200d43c3c00d010461491071802d4200326207140c02040004681066841e80005185001d840030703540700c03034101c0502c00c0084d00c0c5944082c000030203001401c801d02000180c95030041209119a50111142000703024101c2407181001c0c040c804d0204c00681407102c1c12134a0b800303c541c0142a20900d180030718080005041004501c0700103050040541c0c00d00200060309030284e60440204000c180d101d0000d84060300340c1e92140340e00071800b40f05030131503d09040118806440c041c8004601c0d48555030310141e0860170101584420f40c00803150030b0114501c844000280c841c41c1c030740801d00d95a40f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 569493210 1250 569491960 569491987
    0x60e0619230109030b04030e18040f080a050f1201090b10090e0411040504050f06061005121506031312080601050313061e020d0506091014010915050310050103110906 73
    0x41e84d20150101880c00d04010401d58050400600104111954100c3c0400d0b012000d2400d203086074010022402c5180242c0881c0030400544840811440c3c03042c81c2042101030b44520750840e00c804020440000010b00611440f40034441c01013006441c0704007100d5191030001c0c00741d951031003280ca0440e0707150049400d110034403104100b11503002d44184000c0c142480c01c1603440e16091012400341c022100030990a1920501400d400607a0341c0e41c0508025807a401e860f45c169016001c1000010a8070844501e0348400700036611030741207041c100c1449000b5051400b8229021201001008054020000d460f070308070b019241c1110309590000044501494104024035201030141c45501c581c00031801c02102d90b8006004502ca41402405240c903040140051100151200b201d50307040d50405003c02e100c1002c0040106405150451800c2c2d500c03c40c9403052105641c8540010b000082040a25800c021203100140002e103030030084900d10605421090289807441c0748180400030391850308186 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 569494460 1250 569493210 569493227
    0x121801021603080411120c06181203270904060f0f1811060705030702091308070602070318050f060c030d0204090203100905070c02090403020a06060e06192301 70
    0xe50740071001c1c4102207041c06420114100c1d000c48202821324001d111508000c1010700342d41ca0f1407001080b20602c44020400541c0005003011540c896a101400c060341d15014040300d240e004202a659951154060722980c144002111072030300e2070310b8440080f50315411003490307200c0d0708400c00040301c4030420100c102038070104110b10f02c21800c00078070139080d154030210440d00d684500382250a070a000e03801d1050600030b0715000740081d00709100c644054180801003039032080441e149800401d81690358540e05401064095500941c08510482055000035002000c440da4003141e0a90174038000018140300e0310038540038010b40700880d40c1400390400300190340c0d41d612003d07002d6465684910b2801c0007500112850280340204100004021811780320302802200795644228494095809004c10300d9009841102140b11f0303800b1400100705c142c49554040c201c0100c0c0542217062010810407502440d60012003482d00d012020000d14003000c00c039408a48018050030000307405400103880034013 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 569495710 1250 569494460 569494477
    0x61101060e07140c0d0e040b0a080304060e0a0803030a02090a050910091d0a050c0117040807121b0b01091a180702010e03070f060614030c09040602090d0f05100212180102 75
    0x800c40c280085c0752600242c0e8100e00032000d5a0030441c4008030f40c00c110410780c041c4a5014590800c00013400b01900c540d40f001b81c0303800d015141000c40d1b951035101c1882d40e4812104001d00c03560200d501400e918140048400404040b50944041c0c1851007402c0c40440c914032428400310396030f10070341005107001d800e01d244080e142002e031a45909941845521501302203009030000c0c1000b404805e011400d42c50103806036400c412410b0514080b5030b00c00d403105601140c075100703004598590458604500c804801070910540c90415154541455401a2a50b1401c050f00030145007400341013a460b0b01d80c2c180640300c561022130005450301001640181601c041001e00b90100007102d90600540c000d600011a104103801c1140c255100010454040e82464455042e002410f80c2c016501e088284140c105000700401481c111f044800507a1160342000b0495040f86035007103070001c2c410103101243c1c40601d0791205524250418801c042c21000c004c001191403441e1a188001c6e521007541901c0016 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 569496960 1250 569495710 569495713
    0x5061905011d031608060a0f0c08040305220320030304121104060509010608181f020d110319050a0504080702190b031014030d120216020402040906061101060e07140c 73
    0x94991020315200c1600700c47c60325043d810315072501008402449035004110056030b03a42002d895650781100c0e01e501c62030690342610341c11140c080283d84030b12100c0005510414814140040c030304524940080a4089a84250000d010030041d8040c110074441c070069100b08182d1f00d80414034005802000190002504113070340d20b001042458211400c81e00580e0200c00030401c0704901c9120942da16401c10701090401c265018502150445401408064102c02004030b402d1002c1190601c00c0c0d0422030349141c1521408603c66210030481c458590015881c000a00051030a0b840b400c6c05e500c94030500a000306032000c40448107803100008100509106111240d50f400c1041410803800e103140242d0580f2403600620b100c891170001018034100c80d07162505030000a2a9010344005d400c88100b10030f000807001d65980060382c4610080c07019040c0703604001034050519034000d010113071b104041b200c2603142810a1101c119003041d540d0b032240b41883c04c0010808001c0c004141d90041e140c440034103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 569498210 1250 569496960 569497003
    0x14030109061d1005010510080901022206170c071202070e0406050a0b03030304051b22140709080c0f060d0e0a1e03051e12010905061905011d03 63
    0x5800e1081e03640d0400b460034040b101c1e4401e103800728404890083c45520b61051602c0d00007014203006102065200c072404000604080c070302943e403800414507082c0b4a2001001d60741c240f00c1950029208982c1c80c0e0b4210100c82d0600d44000030f0395051252600107040b01c148001884045442040b860014140f2027070240d0072810249008000b41a0503122000900d003003d240003058140041503038401c41d0000000d02c0040c0ba0000d45d9007007000206076131500000100e2086034007403c0b00140c0d240a0920400004e10b8104900c0d40001950016001204010300c03164208152540020b00d928140f1003105c03030207002984400010040d00c210702017040b24504090090803900b401003510541c00f030150b04c003141ca000c015109402d00301815a0001d0100d441071040110300c1303400d09295200c00024801d600c0c43c1c220302d0341043d40e40c00c209901c219a42a1100104000d50802c98049410340d481c202c184c8150a0400340007914040e0040140350605030040e4100d000b59030308200011701504404c0b401c9c0e80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 569499460 1250 569498210 569498231
    0x30f0212031204110405040201020309010f03111215010201090c0b0a0504030f050102120c030c0a030506192907031d041b0509040e0c0a06140c100507020d08040b011403010906 77
    0x5115800310390541300c2c0c0307038030070707603500c2c80d42032600820b485154140c4c0510b14008445006684e01d000508a140400da40e8020400e07805980000038049803a10005642d40b500e84142c203400c1d0080303122903680c1164145420100010780c0d20002c50180c0e40007802c13030f0b601d03482844011925030003503a202030030f070303449030001182400019402441c01d01c601e103001d03541680c0c400700201d10138413055460144201041100b69500c0c0d10a9010755000980240150f03142d8110141d82c00104101d80c000c0f0380c0ba02c0141000d410f242031881c3c1c00225002c0001006420700f415a2030240140c003840314009402540020300007090784d10b9607c07000721501c020181d004644811032004007540c102c1d080941c040c4e4901144040801e00005441c480c400008020f0940c0723500f000070072543c840350182c01c0c0d04404c0041c4600c0304030300070511030890202d00541e0001032500c0c1501000345000140f20080041c00003103400c1c00041401307008041d0540f20102a0285124440000700b80180840d0f94040c00152406d6018907 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 569500710 1250 569499460 569499487
    0x30c030c0f0f04141e13020c010e03030618130308070c020d050d09091104150c050a110a0b13091503082703030c061b04030615030201031b0801030f021203 68
    0x6030f540186446010101250034820070900d90500c00c1c41084c40c488000900780f62681c2c6984801c91031b18005418040c90038200c034290f891030201d9110a4001100b044a281070002c050b48102c1c0d507207144910301d41401c2c0b403039507210801e844e406010804100006031049008012610003180c0c054501c03181c044035414240d032a145010300e000300140307081100069800c080c1c044c52007501012030b0a50b14003803a20b14191003503003071071394200c00f0b0142900218000c0b400c1408000c00603070082007201265802c33030040001c4860f2903085503010010a00c001c6c8207811000480d102501c554910004014000c42510703070801e40039500060142c00c0006850500c40d1201d00e03210920307032583c00c0740304610002104141d124000c5003180f060650090b4005111b141078a003e0440d9801f01500f507615203500c0c1d031281400c0c1c1e65060103000880710595010021560305101e4040191400d8420760445c162480e0010001e180611000e84945c003031003040802c4d59500c4c107030050003804074000c407540c80d021100c010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 569501960 1250 569500710 569500717
    0x51f051204031416141f05040f0b0a060303030f02030c0901140d0f0608010609140f100906170607020102160305030915091e070f031506080f0a1b050303030c030c0f0f 73
    0x221030711582c2e0041803503586000202051046c00708000241444030b00031440004150080c000d94101c101042080003140c000840c15000b9000b034000030600c0c40c25402c016003a6504d000001c100c0c107204104001003000e0703c0059982c05030007441c0109411a01414551643c021145075448483c0303480b010008842d040d44c0a10f040f81c54500080c04806da0340c2d040c0400315405103421020700c400e9240000da162000040b0b207540075001e4800e072600380351a066000c0858040384c100e1000b80c0004000e81408180400c869580400ca070701c02585441c1c0f000d100d00c12007004000c401424000c2c0071001c902e081d0307010302a01c4500c2c01850910740007880c2280c071455071a442c210010442100440d52581d0100c0086191030603140200c001c540f0080c507542e248141e12948001d40036566541720804503030301c1411b0010b042e00c10385000003461b421000d07045c00b0cc18100c6100038010420500e120401650b14040103495201e1800e0100301e0702c1e0340d140f002d4103800d8418a01040d0124000203001c9842a1403400075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 569503210 1250 569501960 569501963
    0x1505030102030a0605012a170f0a0c0b0a05064603030813050309060703020a0c090b0f18040305070201110f060f36010222051f051204031416 62
    0x2002c08030282c000c40700f010b000c1e4201c850300440147c000c40c5404100750229a006540340030310024948099a07021614940014030741500207100412502e0078854101070064101d8009402007210b814000c00140c4d03410060034041203184a20104002c0f00c0c00003242010448041d40c40c00c00c080c8100101c09180d00d2618002100481c0001011507182d42040000340d004560000c000e45c0340c800e0601c04c1080b507800c0f46c2e10480c1103209158066000503070590080000b02001d00000c2030f1080b0710010401c00b84580c2c1401d0740104505103020120301c0801c50308030340040e0075050042d9551803600040700c51410301d40a0751030070b100e4406c9000038820001400d612400ea9441c09800310f8813082c14065034880b0340d2581002041100b940907540003000c0840a480100c480001413400c0d0f504184800b40c407080000c846036a0310744200420950a11303210541100b1524940340341134102d4400040e2075405010284802100344200050406014503401d0350b403612454061074403202000002e403000441c40340c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 569504460 1250 569503210 569503217
    0xc0c150203161e0e0f030a1b060c05030412020612010b0309100623120d020c03070e0403080415090b010e0601030b01030615080c040b03100806060a030201080402041505030102030a060501 82
    0xd00e10450329518500701c000080e03c1049032050701242e0700030420114550042d41920560500c0c4e03010481c10026a00c12030001049811046030200102c0507940b0000c00d0183d200c07072a800180c0b0120494041e9420600301c54080c11090003c1541030151090f2010460a080004171709030f02080040e610070480d40b82107a403442c040f28042011b88115201c2c2c0650f00606000c0444002c0f0038080021340810040c10700e40c24000c1c030080c0d041c0b600e0400368401d000358101c3c00702c40310b1500342880600e0203000d126a200e03480341055540200361341e1000b4405070807170786501108904000c00341c00251016800200494280d6103414491080341c2003900d0450200f40750070390780c0d034043d400f80c0101c90454540011031340e4051100395041c0c4410300b004103209403207242048046a51425000694015440000804c03042800d000c450743c940500030b000584151848101000143e0b84000c00c650b00c90380c169000306d40c84a00500164001c40c0d544c0003031390300d5400030081081990301079020000300d650036038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 569505710 1250 569504460 569504491
    0x7080c160b040303030f0f1d0f07081507020102120109020405120d08010b07020d0203070308030415180201050903030c0105010303030b0f04060803090105091512010f05031f0c0c150203 81
    0xa03010080c125548641219140144010808680250b100781da02040744880803c2c6412086081c1c000c0740e42501c4950030b170041d1611488210f85081091504850711680249405810501c039a903580348908c050b0103011150f0400030340458406e40607154422084c07110300c2c10b2561149901c030f0183d0414011309004420781e040480600b0000916500011580d031903842c0346909102c1c1618440d03015100690b00f092401d1070b01c40050b101040b540303000354011085c060b1a8107013031801441014000042048a50804218404000c040841c01d517810b942401c00c651340c0c240200100303043d805a4079180c54135500c1c1900020a00d50075420407148581c4c21240c4c0040c124440c0100401ca80c00f601981659030b00510030003c041d40680011300c1c001c2c2004000400700c0900e18226003840e0b11201200c1d0044682700c00402840b280c03e14010301070f010440291541c0690001c14108042d2000034206c80903454130503250321140100340c0000b016820401d10941070310354442e10b03006540240c2d16200000c8010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 569506960 1250 569505710 569505733
    0x40906030b01180b15030c0f0d090318080c011b1203090c0f1202130b03030304050a020a12150f02090418021005030609130809060a03090b07050f0409020f0f07080c 72
    0x1413256803001e0000400e40c0300c82895001c040d03841038100421803212004100403541680203404050305243c25400030202e0100100d1400914200842c2200c0001000003482400a08404070b06c100e40c500c002c0c030748141a8003280480520b81c0c0841a005026000c10548a1142a50541000c100c5a00621682031207642d18426182c00503800e1280001e014002c0e080382c8010f00d403142904210146140002c45d9000b034403400241158401e56040721190700c141000380c11030038007041501c02052843c1c003002d5020425101d4016036403203410f8108120383d450100d4403406c10243d0641d00450000343c01040038a10b515260303201e2221001e002d070301c901035500d20126014400c900302d900c60b14000e8207410b4941c079117110200c2908188442200c0e40d04003444021107549509000e4094601a5900401d2030700c1c031410441a0b0410140a034000c002d01001100c460410010441d01102d841c1e21005035190120001c6044a01807000342c80708074000001d01006020301c4002a00d0404003071001c4c0e60000c04070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 569508210 1250 569506960 569507009
    0x5070e010f170a0e0105130c0e1e040204150b0d0f020a0905011206031703061201110a05070c030b0702160905010302130b180c0d0f091511040906030b01 67
    0xe960101c00042640d00880d0041103051041a003103a0b0000d4041405549406503509440e8110343d06440400800d40e82020301c60000722210080800080948440c1480c40c18003171403a06800c920b40074a1180008101152038079031029640240c0704d410f41d03609646542000b082035010503034401405060940ea01c0200c0000e100b102c030035108540b14103040501c2d11006549650f400c000071008165540d2002000c1060291030f203a00e190042c0c9041d41e240381030010003603600401710140000740c1c07400c04401404518001250803152240c18210380b261304d24a0445488040c6130030043c0001c00240034086000d80009154954a0482d4030241485885090040484009100c01b0f98024101c883e030040d250041d5100303140c9004003a00b0b22954100301e082410340040191421041217600040d90800360400d44585103061354000d6061007074070302c50b4032a84541e91507200d0380c6040070359503c0e01085020704070040b03800504180c0018006242d4901701004607203400d205520703d12506103c01c44903c01c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 569509460 1250 569508210 569508227
    0xf1e0a0b0117060f2815030608030313080d0f060306051602060417030a0b040218030c0301090308190b1002010609050c0a02030d0c0509040e0604060b040203100b0c010f0507020105070e01 82
    0x4050b01480800300c00208000c0720401401091380d9180785040880c802000d00000c010282c1b204080480400380e61420060494810b03610924150b003060080c041c0b080156006e8912082c0c00c021080d031113040300e5010f9401004c00c07900e800202d41ca012000004c02202c0d03081544030340890280560310545540007a43c481c141250010915055288070400001d41800a03507007002001900190300440400818103d0b405001d19003c000a01100ca41e69440c04000155104509500901005100e50780140805c1170117000c20a1440d14900546840c0482e507000d410300c04030040041d0700749110742030f01078000d210a0141d400d126040c00001440c841400080724400c400c20790086242c01c07402a0124000d010302280c0008100307041102c0301d9695168050b41107210b101c5070241c44a400c107441d08104a074560a0072030702890061042080c111440c140f07910071109032401182d5100401c0c1c00407801411070140701a001450802840701d480c2e815484144920f446480319481034810400540390640d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 569510710 1250 569509460 569509471
    0x1614060a030f020405120f010c030b151606180b0a06060c03050d06050306070201020a02010605030c0607030f171e0708060319031e110d090e0f1e0a0b0117 68
    0x1008020240200d4401c0c0d01c1824544000100141002e4590000560102c1540e006101a500107040c805001d00c0078851560004081d05040001c42035080110380c0012038240980381841c00440d42040060700d401101640d5a80803808006600500b2087c00240481c0d110950b23441c0700c040e0000c0d8404038603200349001d449464a4081000600341d50854203984210300200509444003c005070980303080000d180030322100e030005a2500004070009003121a584c0c86248070343d0040c80400d555840b40c2c0211040c1980516203440c640110f0300013515040401c40c004000810031204104c0c65040c1e01c4103907225641810840d0748179840e1345604440c4524241e40c0c156040d008070f220310107050107007000d240989110341002031404000111051200e26603000c82c00200b04030503100d680c540c800f409204c91039486414901d4246041c030039020b0188500510a00340741904802280070256200245019610381d203011808a1800d41900009016696036482c08512607801000018596004032845813 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 569511960 1250 569510710 569510719
    0x61b012a021515040912030c030e0c24190e10030b1302090d0501050a0902040b0a0803190509192105030906030417040608100608070e0907030e0f1614 66
    0x548800000c0f0341e03030400c6100704952240e80d5940c0c6000180030200d141c022190203840010328020051340c05426503580c01400d410640090946280030b907144c50707114160380501030951100e00745c04c103411540f03413190500360b01d15030301c0c0e0844c0c00907850740c4054050b007400030981e20031582ca45081801d600b41d85402800580c8451007041e4688030580541c050601500000c01c0780d00e10009540381c84d400c6900580d0402202030700d482d000429803c1c64011590101800d0714641021340c90022415205e005804c0d4424050064000000c002840f910035202102e030010700c4202c000743c1f41150003095402038070424a000d920a60b070043e522030705241554446800c034010314500602901000b0310399100034400c4070524821981c0e0603415540d00c020304003821301c5071100e440d642401e5295445039402680701a041102d45020058425448807540e103400c4002e90b8040340c10303100d1034000e4014280940e4071081501c00c2e44014090507030006003150000b01180d0382d0040c00b540724003054915200702e5a032503401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 569513210 1250 569511960 569512003
    0x21005030f15010e060403110a0e130b06010924030b01090f05120102040e0405060106030501140f0d111002010c03110a05040e0a0e0307080405030d0306080705061b012a02 75
    0x910a81e80092440c9010500d414401030051200045c11034005800a50708250800401103080c11b2020700e041c05041c0125411815251081401000e002002001480c0b144c420001c103010340d010b800e840e0702405141001c002480318020603000d21840c0101210002402d1108204d02940a4240c020035108410415031080307007480700340043c0c01c007115141d00d1903642c02c200005000d0481c0781e2281c001d03403017240a083d0951610308001d040d240113070042d81e207907242003070303010700a5039192404400008140c50b410110308903802c103100b560000840c9503030460a070600886601e5819440205044503540b410403040030803114404007030250b02800740200383d0401081c4440907403003880399800554440d0220712185c214401c20b0a54204c10012143c42c41c01040034031440c90140300e00e0040c600586000c01ca15490488040d95489040c42110700600c0f0000e0380414003c007a070680035111340040000c0c004062130880c141c500c2c07a50701d40003400b500d900c190030421243c40494802140303090308035110791 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 569514460 1250 569513210 569513221
    0x6090403080a1e0608010207150203070504050409050c0409050f0f0a050615060d09060203060907031a01140708031f0e0405030a120b040c1d151806070212030403021005030f 76
    0x1000d0f120982c42041d900d02201c1c104002e09030107958058006440050703102c0c259450f00840181143d2082010580140200000b03254007400f50f40c110340003100c009c10102114213245061441c0c03c810fa03134209050401c24801c0c0400040c0c400c01e5642d0080c210340220350601d0f02a501c6000e6268010030355041400030510b9128845500f090110008268602d4502c0000030350301100c0100750101ca155402104200042c9031418403554040104e0405101c00c2000c0d51035000174440c1690143c1c18840350343c4005100481071005d82d02c2c195440300800759681420301d65203003001d1020030b01043c952075020f00030070810403004a8074001e03544078004508212403c0c00035140100080c42e940340c9169103002070700c0c0d565901e00411301c07442907548440104c2c5001881850a2005543c42c1d2801103e1a5003061000785440080b219001e0b00304440003420b0714820300054072445028000f0791701c00c0451400c1840100040700a100301c078403c9a0700400803a00f00020b4800d4002202d021034217005a0300003e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 569515710 1250 569514460 569514481
    0xa020408060a0b0a0f091a0103021c05040c09020f04090e1203070e15030720010e0a17130308120f010609050f032d01061a160f060c0c0b0609040308 65
    0x1022450003050840c00315101d0b040341190625640c41146c0c11078440c2c100405c2140c0c901c03142d0400003400c0c0f0b0b0661074a048041c150600808180e4060340e000d6a07a030010741446007048196000e0010003000b90341d41c0c581342c903d2804a400c507000780041e4a280c900b941880ca000081c0480d0302894009010b0f04684e83c5440a03116044030343c00751900060001c480141540c50100118400d0600340c4a02c1d42c80618180f0240090100440e100e150b6032500e4007861048000150450780a98400d0302040042c01c0d002104056000d41c102d030394440042d9440220403c11680050400c181e5068010125075441c0805100658002c0c4a180041140318406000710f0030403030300c1880d0402d03000e821a21069452103007981e6024411260312a800e880180e2036076a41800c0c0955401008210a0328410f040762900001147c8140d203990401c1210001d4400c2c200325070701c0358620501d50048004c1200051a802c007405040341400e08907038071100f0034001141c1d85080c40a00d80101d406507582c2c00c440d5503009444 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 569516960 1250 569515710 569515721
    0x10c0e0a0915051e06130e0702060702030301090e0304080d0903031733090f01080d030608030a08060112020c030a033206061b0309010206091b040908040b070b09060a020408060a 78
    0x4003074031541c50030111056145e07a801801c01c40b8a8030b00c00e44000d880c0c0080300e000014007405820464200b0005e00440645c0003055070705507010890000f42c072000c00b82e40c0501e14821507008844a001e40c000c1c0340401c60300304c100b05d41141d0003916844403840e001e05001d0b6030140d00315800145001c080c4003480081100c032480b444900303007518802501e1281d0800041000c001110340c0e04e650030410b0018070001c1e4050180000f000c000b402c044c4281424810307420340740d0044100140c1001400c00c00a8542e80c03080c49503401c4905616000c640e200415400030751203910880b1400082824648a4030f4400c010300268000c2d19096114001207000021580703100e03100207410300c1c4d4480c90178404d456401072005d162680b644810802940d6410300000007a080c108000e010b8003054100c1d41c85440034854045080b883c852040307400140c0411145400031582c0151380282c03910100120742d41e010032110f0864036004001041c1101d04650700c0446581c240c3c411805007049580080000c40c040d0811038100c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 569518210 1250 569516960 569516989
    0x60e27030717091c140c0d020307030224070b07260601080c041e08060c09030d0e0102031c02180f0f1207170604030305060114120a0e010c0e0a091505 66
    0xe00c280d4840031510041004d140d0381a035880c11190204c01074002d04020400180e80203a0700c00b5000405900007a80740e000510011303005141c410100b140e458440d2110095a0a49000160f1580c226040044c44d0000499600001c14505200d0709945118200b20a403000c0c000c0700120074969820004580148010781308030f0000b00c0501010881c2c2c0754100414080501e1001050000781c5444101c5203003120160000d0302d440d608111107e40d0f80c030302044403040c204040c00c1c081c0425041e100100d10718071440030b00304c0c0c002640801c2c1c2c020302103480e0014004042c18400040300600224100000c4211030301003540e00014002d00001e45040a058240c1d01c81d01040941e10400c0d40e51403034a003813550901e240f42241d0040780410081541601c5880d410401c04e2a2030700e4009100244c0781c0540c4a441c0c1d14a44e08101503000039107521407500f0244096103400028002691b08600180c908410920014860b80400c440130070484035034420020100d1220200f0051140ba08050085183c4106107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 569519460 1250 569518210 569518219
    0xf080112081b0705060a030903030605120601051017100303080a0e0606130b0a090506190b0307080a0f1104051315060f0c0c030803150105120606030604060e2703071709 74
    0x40011340d85d500d00c2c0c043c02c6c2041c226200842e0310801c0d4a402401c03a0700980100307103d9104455000480b8100054240c15a201034882c0c2c407580e00c151000b0b481501750000d401407514071314010030040462010300170089074481e856100c84c0b51100d8000344245c0f50300c0c4d12202820341c00382c0c000aa0a1030700c022580000c001d5100c2c005001003000021814841c156003003034601c20b440b8000d004080c10f20b81040941040085560064142010600005440040c0c242c0d403c020700c0d60041402c80703d403a0300c41c60341171009610402c6010390310105e6407642e4015100b001d1142c4407001261200281d14082ca881d802250340b202c071000c5003002804d842040b5840d0030380c0200008000c10380c00040d8600c2001e8040c40c080c0e054552a403401c4101d64021641c0c20380d803941081300074803100340f454404107035044d0003042c01c64401f5201c0e2b40343c17030214005041c1d175841501030340402c2c0d05028a0761400401a0144403800000d4020a401c0741061035980c403c0800043c8000030028080c3d18150f0040003a0290740130090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 569520710 1250 569519460 569519473
    0x6090d020f0d0b042a030b270d0903200306010e130516080c04090b0424060605120711102a02010f05090601060c0b1e070f080112081b 59
    0x21504821000b00b200d04503184450170107071180b41d54030b100c0c0b100101200401107403413117400e59540c1c03100100042e051042d11410150011201e200100c039607071703040201d401280c1200c059503000034540100c911050356020380840080704504005800b551222001900400291340380c0030b4042c6906500a04601062041903185030001d00e040c05242280005000090400760808529a06040c2c607010715905c81c51a0901e8480026020090281d100740c12200758224071040300c0401e4500800310000ca000303d4036120f00031440390742050241807004400039686c04940e813600030550380001c603142c42e000e00c2c0d88041002d00e131142c4503070401e01d503000c81d0b280c17007034401c02c0741c07603500d8050724200d200400240c0d444000c03108007200588500740c0c0c0a44040000c0005524040000d80101c45c415030140624014000141420012020302101c480444003a40000e20300341e01e00424401d03445403064001140000000741c00c401c1c1030191114a90801c50072403400791804841e140451160590400601808 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 569521960 1250 569520710 569520713
    0x81e091002030907060f080f06010c031e0c030e041a060d020c061006030f111c0209060f030121110603150a09020301180204032a170706080606090d020f0d 68
    0x18009503006040102c000d0904c0c074100070b005046040140b203c40c041092207000c000d81c2c482c04c0310805410a0b400c1c01e1034180c019003410212132900410300b130030514003e114850348500d40c0c40004140e0560003590341d221030165000811007541c40d20b202c030103a00000e518042c0703a0f501e05440200401401c804d0018501554010380c1c0e400c001080382d00741d400c941e84080811045404d40142c40000d84c0280c3d0800a4402400200040e40680d0030a08030702190008012303520301c2150b0454520720304c0100300b1916001c0381002541c0b00da000b401880800c501c00103407103c103095030030071031141e09521481000c04892900240103094000500220711501e05180c0000640c481c0401e40c40980103030500560ba940c18517601c0e91010300e00c51265800b85104000400100d010a0f100350522103158036203024028081070400100e41058100e46240ea110140500c00c140c1700058450880d0326986800b0f225990301d07401c12416001d090708103900280700041050061501d1150341074800c10080400c00301e03a401c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 569523210 1250 569521960 569521993
    0x8060424050a06090b040207020907080606040b1b0d140901030b0604031e120f081b040e151509010e040f06080a03020303040519080d0b030327090106081e09 69
    0xd0b1442c440c8035a4034081030154400c2402404106801902d0961134005035501180503400010540001c1040c090f02041051703075140204c500a050051800f622648441440326060304821105412442280c5045042c24060101d40c1c0d4001c03012207916060203000001036014180307600415074000f0080002100089114924000c5071105510000700c2903418600502a8400440d0540600c2890b041c2012030951080c00300b544000550000220320040412020180c0213580050600f00e11010401440250469030381c0113821044400e0300300200d402440c81401d21030031001c02d0006451043c401094140740d08548212207109900042c01079940c2c03280307400e14000001c2200160000810b001c1840010000642d5134a2011700070280c0004940d1540030358400c034288525515102c003c1004203230740038020340b10884c8007141135102c101c500001114a00c18108038a61045035448004203035688600c003a144284e45003803201c0301c0d45540710510201d420b0010205001d900c13403043c081800040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 569524460 1250 569523210 569523221
    0x60507031e02160e091e07150c05120f0f0901020f032a030a080412020f0a1203050711120706020702270703050403021b033c030408060424 61
    0x650b41c007611440001d00620704402c1119403090398401400018030140000100c0c1c41040c03010300c1642005540e203105144d40c20a03105a10200821140c00343c40d80e401500105180403141c0301e001540e41a0306070803061b4000c1e001d000141c0500c0300b03092080c80100c7d05008000c0020b050140125803801807000c3c04a803031607000c1d6603d14405a40c44000e04414a9101340343e58400003018065420701ca2940c400501401c002880640810341d101140c0c52843d00a000c41c007030300030600040c0d0f00d52500c94100010a800030558000001b1b180500040b1240e20071018405c4144e021400f501245041048143c2c07e604a144240c071056030030081c1c4001a40c0b4595094003420b402d0890350f00c1c0d00b00c00c00585101d450018102c400303040c20442004001380d4040f60004070304a030364228005140c440e90201f1304c5c2090a0b9401c03030400040001c419540180e03005a09140e80070007414240c0740c25900d581c551640120f200709610b42d4840e030702180008602281c80c2c4182408064407408171640310b01200b0a864 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 569525710 1250 569524460 569524517
    0xc0c0801060e1008070e1f350307060528050612010e120c010f0204090c02070e070503041209030b090c1c05030f0d180b06040b0604030f06050a150806101a0406050703 73
    0x230110021103000003940001c400b10420801c100e5819042010740d0a9101c0c40307030280041a40c1ea0b524000381100141c008007555100c03604840d002e095500c04500001040d06495861040880c0d03000c80c40c0110050080343d41c080d112001070a03003c04440c0c00031030300ba00501481d075119500c400c0d08030102221071007e00003c1144035404a18009010006030070007085400120b42040140f0810008981140031681c00c182c2c0301024000321401c0e11000c5450b108250801040003180400384100000000b910b08501001100e03604080c202c84104c14100f1a405800184150002e1203401a0500110040c198250000d803000c5007001c0d05000d41e01422940c0301007110603102403802d00071a030400d8451007049000c1524128038060441e16003195041c44060002d00c0182c41c4e1000074aa02d1494203c0c0c070f04140d07002320846185446179411900c41104440c0e01054800d40000002c1400403c0362000b4411a41c150843c83c007030034494103d680340d0205100f0750030710070801c1a06101d005a80901091403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 569526960 1250 569525710 569525729
    0xa170604120810030807111c0c150f030b040905070e07020f0102030c16030c020a080102070506130c0e0c040e010303030b03010c0903030806100c0c0801060e1008070e1f 74
    0x203160615001008109441c55081000034801c1001152980c40180c0402e580d00540100d84500d55440c3c1420b1f20034250008503006400c8407002c8401000c0321b4183c40c500303840b40070b040c40240e40b01c038071030301000022040e00c0c000600340d10f003035400c854001d84c80041c1400d00604081943e00480d21800e01e0400300c1c0c1d01880c941c40300102000f080301e070b05001104080301c01800951a40c1080c20381c0010502034040d43e2640c0d03d2840580004050161106c05071642d8060001c404c2c40e984c1d0900ca50003500161015144c5014030380000744012016410302000345d90040700100e50504040c3c00060052000780b4102031b0305010480841d2403044910503c4c001c621a80c0e01195000031201171500f924020b054420a100204a0510009402126542d80140d054030301001e1200d40f590100c80c20440303500c01520f5111300500210b031040c01074000c0d03000c0d58804038401c441034445c698484403140d0ac91068440a13005600240102c100075a4a20f8206010a07143e40c0b044041110407a000d0352550700080f0342 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 569528210 1250 569526960 569526973
    0x3050303040b060a140f01120e0601060f02070801110403061107060e030301060e090f04030807032910110601090b060f0c1b03010207150902030f0a060c080a0203071d0a17 75
    0x81340b61082240000e044092446110180100042100540408046414802c0c10000c0b040200e106230f029011a0241000f22810395a6a07103001d060304e1240602a00103028200300440c2030401402255841e4a01c0340b0720314039003132547d11240010039800300c595400078010820365002c59190701038140c0141c004806142d0b01e51600c07c0c041d01440421800314040c1c40d1300820411021640d80d401948540c02d801e1600c225a1074400071801042c0d542c842c1a004070b0808205000b1007807200034090404011b40740c1d00a03078030303100400b5541a07406100c018165841140184102400c2c0d412003040740801070f114a0421030002e030015107a410410b03c01c2c0040d44030480710081010701d40d1444034525819002140303001c0c1140c5400b82c00501150101d2a82e5480354001411510100181c4003045e1162081d0b420003661450844054004442c0303a40c005440040418965100340c4203c900075045522080d00d80c443e01e55540f9411a600c0c10b400340e0146801c400000c041482c4410420745c4040e00e0064800c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 569529460 1250 569528210 569528221
    0x40605031501110613020a0f1707050108091207060f02040e10062f0f0307053301050d03271a091011010615080405010b0108060303090f030703050303040b 68
    0x7888061009020304200e203410300d8191030000403800e00e800000c000014460140d00d030003c1160b800e415400351010400d0100e00003011160550138441a03060101610001d56a800c0112010001560b03402c0058210ba41801070aa482d0b0005203d0135104407008503000b44284107140480c0c109600c1315601d040d2240400401d1002403070998007030704890426442c0812912400d41c69900c00b00e05081600300390f032000b4050084100044e02d43e185801045aa4a01c1e15252103511a00c0c85810700a9a0a24403490549404101c0d002400703590100c4064200c0e0b840d14080056544104a040c4c2c00d02001e90304009031440c140307104083d14214080d2101080f07103002ca60301540865002000d003001000d2080000c1c6036100801403110b44030520b000030055103403c4e200c81c010450b81d400a0184440c1c4003001000540100340c15200303034000d02c002c100030880e02006581ca003900b11109a4550800c001400c40d602c0c0c1625002d0301e007c0040c044510007a241d42d181ca26640c001d680598442e40705508110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 569530710 1250 569529460 569529481
    0x150118050702011514040605090a0912170f0705070215031b0403020d0609050f0a120801150206270105090303061207030302030706052e080106080712081e04060503 72
    0x790001001e1008010824182d000003010070b4490081c0c407000892413007141d5042c0e95503008000901401000a1254100f00e000c5d600209003040702110400c4044507090310035070140390906a0345605084003075543c0e890303402000801400a05a405200081c0011009038030b4520300b00c010608420442c035543e041200c12000c0559014030380c3c01c4841e004000500041c2c95004008101580c4488041580200361400b10300703154041001456520641c103541041c003000c00c02e0503144000c1a151482182d07200c030003000c03882c0c203c0f118120160384010041070402503020095403055031160203504810b01c500306418292a8156000d0101c4d60000c000e001c200e240c05075180000c0d421140c000e1482c00c0ca16074000e0340b0b80c0600d2a000d088260303070b1000105850103e00c01c00005001480c51300d00c40f101354016841003a400e81c000c0c0d207050340c0303400404100d4550004a00003a41d01d28902001282c820360b582501342d91020070079210302c0300b446000f2101c81900340d01400240180f0f4882c4c4d5240c2c03506c1c07580c0e038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 569531960 1250 569530710 569530721
    0x31f08151f060507080903120c03031504090209070f020c040f1506050a230405060318010f020c0712020406090507121113030f0f020a080c040e01151205150118 70
    0x41c024040341001c000154001d811560910f03488020240c4824140b0000303410038201010501001c2d4000420701c000000100045d80b19181c0b4141c61046611a1400d010840301e410704001d4000800d90041402c0d64050a540c000b440b000348100c07010006480e0119040e070701031400e083d8072182c40b1040760f0b2440103444c00074405030249107407640c1011603000c00140030340c18424608280045550841000c072004604550250070003400540e0390b1308180080004581411480c10304c1ca51030000035004036600e90085828a6510364000d207030043c148000d4844144561004a9000d9038405002865000ca4002ea5209600b2034503210598896a50020161074082000315989001003010000200d08035540342c003503039040b41003222400c4107442c015880c6252200080d40c80050481c000a41160009001c0c0f00603400380d0301840007544e246045400d036200440c80758200306048409001c00b28a072015040030074000d400301c49012012072001030710445c0c280c2041c08000c613240003200740f1035003d0199 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 569533210 1250 569531960 569532001
    0x210050606160b09010608030a0e0918030d0c02010216050c100306031203020a05130e071103040803180d0f050a171c0b040b19080c0108010308031f0815 67
    0x740b403820241d41c0c4842c00c0e0140e0014024000244040401c1298400b5031200c2d014041c2c00b001c80c0e0359200600300150011030304420385031150b1203020000320300c2c04000011001c852100c400070360a0000000b03a00e00600303d100300e94401c5645c00d20808140d50410114000000e01075400340ca211402c50050125a114058000092604010b070410004425030140303840092170f49401a16071a038601c04448a107e003c2c11341140840e110030200d24680603071421400381c11951036408011074402480c039100e0040d481811656003043c009600c00c200041c40d14031660100902c82d100209183e521268200302c810001c0d50b031030b80803154032002c000501c800d0800c64440c103c42c1c079080c807038036242100f507072554995004041b9464040c8070b5283e450341d070007489020600515010b1a545444d9030049000f2091040d00054401c000c1480c8031940104d0046050780e81115425141d6500c1d03031031070500280d420207051148440e021740041d082c0c40038000e40c034804200054014560412030300c025101c8140021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 569534460 1250 569533210 569533219
    0x30306060503070906030b1503100e07110c0906150d022101050319080d0c0e13020a05220506070b0f010e0108030d110c01060f0e1302010824060a02100506 68
    0x1840f810541044103441250198030300494911082400308603d95001540c846d0000e00200502c1807007814041800240d070920340312aaa203039540700040700d05103c1c8225211140c1c0200260300802c0c20b04010300c03503000b071010300321240134041010700050720707401500e608a450f40d02150a88101040c50f00d4034002d41241c0051401075414440040d40303c1d0030710b1000100613400c1c41100420006a8016a0311040c1754cd038040150800c02c6402801401210b82150700c038a5141c0b4001d6540500c602c2507490003c403e980b20b80c1004110f0350742501488569813076071481c0204010010f45036039000c0c0200302039032080050f0703d85800d00e040c80000940040e00146000c00c210401801580030010a4404c0b0081a1703601060740110311288851504c0340c100001e40c40c0d42803003800301e030554000c2400c0c400c035001050300d42e1a179a102d508445440d0300e0341000038001044400070400303d44d484e00c03682002d01c000c0216950000b281000040c0035501125040c00035802c103505641d01500035109144d80400c00380c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 569535710 1250 569534460 569534467
    0x70306060c1109090a020a1d09061b1804050406020405041b050315040209120303010e070203090d030e01111006080d05030609060105160b0405100f2a0203160605040303060605 77
    0x2565900d0b02c07111201d01c10b000d41640382c00030b03460280c00c009076040140c000d0030045c00f80342c8070714041d00500041d1100099440045020460f9007400003800361045c40d401040140404100d0070001c40e5900c2440700c03c0491401e034200762015070311841020300843c403403600141e80b00d1408040c40241c41400013016031340482104480c0210b44c1040c1140e80c4141290340080e844841c00b40010001e000d10304041d030700002d0350b07808000c40c40c0c80000103606941c0703a0402d2440b5907940d030328104c0e175900c1a11805074000120000c1000003c1c05802841600a41410800e400e044002052880c041c8c00c40d100c0c050480d00d4003c104041041441904a4500341e441c00d24914070308134020400c4540098a000e041007000074154540e800c08002465034107074001c100c8085030a0500f003031036480e011505900760a40c0b515280144440307241c80b520420604d41c003980145907044210f40f080c000786044102040d408200140c1c0b1125000344c2aa4040901c5910f001445c0d05142c1402802c4030710780c0e0482414071a042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 569536960 1250 569535710 569535713
    0x192016051c05070308030604140108010504110616031803060c18080705010e090405160603050a0f0b0d470a020909040f05070905040305030405010b010905010c0602030a0e070e070306060c 82
    0xf10b54030b8180da4101c000107030b90b07403540004a07005001c4452614501386020001080081c410340002e0f000e54010100074500c4040e5804000640c881c0014070100d10a40d0000341c000203000c4d00c04080140d034000c11010a1315903d4031102c00f0358505400d810001815403c3d00300b1050104550903000e0034a00f07005158032401c040000e01020304000200707100e4140d1b0700c0041c00b00031040147c440060400407503801d0b100d41d1010050042c001c25507402050301c0c100b15603210031809900c54010600d00081c400706040019131a29410040700c8510b2281d00614048403c01000c044443d020782421030398234185e4800c80c40b101d03c0390802c0740500049850b6004021010b141c1e50b8008280b500310b42c0080038021000300310319005140100d03503484156003609000401003416040805144202d006074028011143c540004464904680c0901808a90301d101c501020407404e60103598071902c0b03404c00103485149452507515150f200d41c41206c4030f40d840000c02c0f02c0242d150040a000b8100c50a003040201d400307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 569538210 1250 569536960 569536963
    0x301060f0513030f0510050606070201050304030e0d1b060305090106060f2618011805121b0601080105071106041a04030e19060201060803192016051c05 67
    0x4002040104003022a101c5045100c2c0441d10009603400302610405a0040c0b611940702c0440341c0759032016603e020006031a81c2440320484000c6c9034141d5400785180c0e6165010342d2613004a580c142e0f004011741d203107000010440c00c45038403007400d9003034040140c07840c00f0002016120300500f00d000e1a41001707002c100e1650421111080310040d414105403422154004684507014424514030703045003803060011031107080d0303e0402400f81c0c040081c446030802c3d4030200030000244c1c400526a500443d88a8401c610b100080c0981180f4100404014007104081070300c0c00f078003030300301c10a05c0c0d54803028800e0305600039608000c20f660700030140007030785131540b0b9050850202800ea03c0c0000030100001d01014401d40c441c203400d413001401c6202104a00143c5d800039030090180001562800401042c5d40344000159076490540300041c1900c8104180122200050f4848280c0071410b00c8a00c1d10441605200c03003d842c80301d980100c015130346030804100c00c19808107100d1618200940034a00443c50 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 569539460 1250 569538210 569538227
    0x2007032105091c0f21140c12130801060311030f0f03030c1b0604050703060f020f030a0c05091201050405061302010f030b0609121c050301051c030c0c140114030106 72
    0x240c0b0340b44150f00d8858105580251411140241038034001c18182140c003003084404e540000e900e0b5100001e0310002901d041d918490b800510140740e10111002d00303600800002001e1254044100b4100e007580c034240c1c2401d644450f0012210315030100e043c100f5a0904100c00307415040c01701d0007010304100940c0003a8032448050090318114130300251a00407607907901c424000c1200d01c002110800d19103418416201d070f0301030004844442c2010130a1a00380801c1c02a00c094001404000b031660300c990043da0000e01001205906010003804400e07519a0303454940a0303085010b03c00070a0502c2c041c40d2003400c1800050030400302c0310b042006000944d0340840c0760210300c0701c681400a03810f044040000e2560050b4010329600c442c000503c90750506022501300c00701d00725840341c40c0001201030003c3d5401d002c2401107903044040700c4080008500120403d40c000b0340241031400a5140c5510744841020854106602c44002c4404948003540d21001e10302405000d2480c1c40e0565040003001002c049 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 569540710 1250 569539460 569539489
    0x6050606030f24120307171801050c0c1917011a060d14070c031b020f0d030309060227040c09090c09050402070507050109060903020307030201200703210509 69
    0x1014420f101191508010802011600007054a18814180c100107544caa0080c0411100421910060204401e071074090b1040030420282868052060500448281e00400c501c0c8640f8801c0020520094884010130008010744042c0032480c14100500190910760400e51141e560303160000c40f4951403000100f4150000701294019170301c142040905014003500300c40218440701040a22844a800c400b00040e65031180c0c407003810b03414502025060780100464007a400800160001e0b090341f4040400341c03121407207070800142ca640d698072076508a0304806d5141903c5000e4030852008405031032600054040d007290709000c1460000402042d80140c1d100d6a000c0a485044c60b02c0610300405a04001d088050011501c80c0b046041041d41c41009104040c08240110300110343d4504c1000c210040d20f401a00900202e403441d80115118015074540e0700906140035405610300c43c0a20900004602442c40118000049070f0798200389100c2e6521142484420060260300780c49800381140e00e075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 569541960 1250 569540710 569540731
    0x7060b0301020903100b0f12100c0917010c08090a020f120c150a080f071e05091f0305061806100519020609060109290a0f08060406050606030f 63
    0x140020a029010f8000d5559241c01485035030060805154800ea140c010121208102c00c520361040c001c0e146068602c555058002010176100c440389a000032556140c603203448407040c0c0e51948208000c091900a410591f510380e41c2c1c0c2d0b0812a4843c0000c2d0708002040054a500c1a00d64002100700c240d410700d0300e018800d8200040031f05c0d8411f010030031010720040c18811a1340c1d440400d0310144da10003502c0d131000c244060081406290b00e007107410320440c403070f0f02d4040075040481e03c407031980050020040c0800200f000349180c0c50312809500c062580349200c94080015132104081c080c4c9600510080c000d820f0501006000111110040d40082c400e58454880e41c1901200b01c42d548070f602200740b0251420030404550b1640015280e00c10481c2006039181a600c840c6800b00b5142d080103200030307580e11120b47d02146a80d203c044852140c0040400398450b50300c0348200000c0c0e0013580300242c04c1e040741081209000c070601402e640440100c805c0342c55440c1c10610001a01000b51483c500d6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 569543210 1250 569541960 569541971
    0x10020415200d05190c080706020d0914030307020f030a090905040618150507030b090601030b030703060f14090a0201410403050c01080123040617030c0d050f0706 71
    0x1806500d05041c00c8070301054140d030b50380000031401030241e80c4480564458500f1542410100c10301c2003152444043e448000a0302c2c2480c640c440d00040c1d04104494035443d0b0352070710700d400002c181d10b0443c070742d10103481c000e1903c0b868510703400b03410001c80e40107018082d04204100c0c6549071b80211140b041c0d0b0181324000803261180d040050017891002c3c08103111414880c1d40e1814402c0e000200460115000006d200594800341d00700c06503245400714680004001c07003c5000396029070412081d444002e012211455600d4441a0580301030103641c21542e07584d11109442e00240c80010b0342e201d43c0e440c00034150f6a481c0c1c2e0008108442200d01c111150002d886039590110340080c5102481044076501485450b00d05040c21095010f80710031207092003000ca120081d94080c2a4090403542c0e0228035079522070410795082182c2d42c40c07101003175103e82e40b42000301e4501e1848185036000000d8400541d03e6141c000102803404d0168030448080c054103001d4044d41031841c1e02180d26480e804000401e8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 569544460 1250 569543210 569543237
    0x1a01141302091302040512030a1403040f02031e120405060403080c1006030507060e010309020a05040c0507410c04090c050919050c0406051206010207050a031410020415 74
    0x34010a81003e07070110f10040312808001c1c01d1307009401030300d03c1107400415981d0143c260b80d680340300d0a105400031550702803042280c2c400c040040c551007801907400d00c5c0c0300481c660009050003034140200b403072400c0c043d07100080b01c0d0301005100c58407011515818581424900051110b01641c40000c01c00b280c001a8807000304400e1210554145844d0703800e0059a84a207003c031303100c19060088000182d9004030384d140030340c0310307010351451590042d00182165040405200c00790403e034800f8002c1c00001c11a19000448015400b0310904a02069030490030901c1190130607910001a10f4841c8000314080312200c01c008584960002c100f01c4000480304070070710b003400c4c0d014000da001a510078002805c11032a25042600c00000c400180d40c108001da1307a6035062314160180d406041c001810074041e4030856410301d2407180e0865414011921901e907100c2c00a903801009410032508001c01c416540352034a02041611541641c2050560500b030038100c0040060540003060001c100300342081c0503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 569545710 1250 569544460 569544499
    0x6141f06030c0203031602190f1a0c09280f0f05010e0916140406031d120f03060a092909040f080d060f0f060e0306040b06061b0a0f1a0114 61
    0x14010081c03c0348103e901201d40c00e21503001c12720b1400075030760840c40c400008859010302881c00d02c10300c3e0000155080103007150034800d000800244400c2002230700c260703980c0c1c154041008007004000c0202100d54403401c102621140036081d41c0590305002c1e0002c03c40d012603452081443e4404403a000403a2103501050040346d184034801d81c1c11489400005012460340d5254000b5208054400402e554003204000c482d650743c441c150b043ca20100303050050070310840c4042c00841d04144010b14a516554031020084101c90b24002c0400500b5001c80219201c04160180716044a1040301c040c4400e2805131a1740c072a04810700c0380280085800524000114070b00c1e8415009040080c00300c050460315105801088111401002c001c1810f00c0303e2440c2a180000713005204962200a0314029291802445020740200a21100c60304100c2c050030341d1140100100300009000c1c40c41c1a500d03013181d01780072040030341102102507131121000040c8041120910003c0c0140d4042c3d421a5aa480d140d0051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 569546960 1250 569545710 569545723
    0xc1807210603060c0509091e0117010603060212040308010909050325060c03051504230403050408062a070209150d020301050c070b01060513030f06141f06030c0203031602 75
    0x403e4240f4000000301030a40c060003510024a090780d2250054031b13034901c019400c103c600324500c00305828800510a811000300c9004d540c94941c000440e16031b031240e840340181d800403c0c50001c0100002d04002c1450343c0210744500500341725208003c00304c40d540b10f4649034440e101100c40c040980c0101052004801c542c24403655820100400000360000002405004180c0c4c458a544079290303503c00c041d2401d4405d10540704401000c85070030203001c128030740880300c00030419024001c09010005140c0c00070300881c0c2c40341c4000b1008064038100c43e410f00803808901c0c01c2d541501201888100c0041c2c07142041039400c0003480580c00e9049400000055809801c1440213415500f403605200e0b0742c100b46406060300d90b120310164405070303882d2542264140aaa0b0303000c0407649130224100003055500303444144c168020741c8041001c030700d8419261440c03001a105080b807140900031103102e04404200c00005804a448e040c0944840a20029624007000e4410300407020f078560580e9980d1f000700681c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 569548210 1250 569546960 569546963
    0xd06050603191802120604021e06190908030a0e2b02150405030a06140702010504030f110312010b1c150620010e0a1505040c0612110301080c1807210603 67
    0x105d510b072001c0d011501e800c81568101c3c050700b0322490a0800d82c80c0900c6107016003602078901410100b0070f0b540c40205207010400c0380140100c04401040c069824401044580c1036500c131100031601c03030303414402d501c213035100307951028003401c1c10301004403415070729220f503903174048073f4079040c03c131605104c5c20315440743e68400c560500c0780100613070810129030081e0041040c03001d100c100781d60703070104140d0a0b00c07401c42d4014001142c00200c0f021803801210645102101903080701e04140c51a5400c9020600c02c2c0c000e110f40e1035011402c08031248084414081f140f0514009201440f020040f800040289020740b505100303000b40d03030070394001e003c0322443e180c50307a83c0c0001d00540007a0301580d03440c0c01da00c0a00b80c4000316007810009044000307028080c020751b030045008c14083d03e8074108070303440031203566180101c40c1c951920389890900386026501a00001c4c0241100589200400540c40c421b100c1c5111140c43c030204102c10290003040d02401c400342042205404408001d00702c0080125400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 569549460 1250 569548210 569548219
    0x3080901180909030305180303040b2806030b0901112703010c0302131a1b0a0212100c082202030f0303010303121a030a12021504080d06050603191802 66
    0x2030000b8249269040a14030394000d460070081c68440000c4401304460481142c01141d10400129000890320410365a002092500940b1080c10b900106120069200114010f640d15140c003403007840311a100c441d4000d000c3e00003c12800260703803400240f5020312514001c6d1062901105000f0443d02089130400d410014020026100b0784040580290411800030604076614000460062070950a1040740c00c85c0601c403d042000c411074070030b0b10344030844040e81359001d00032001c401030310b41882c10200554150040d140d9154102456400c0f9010b1070100010441d00c6010301c80041e100700041204007080070180701d150310442c004607240c0750f080707100c039485484004000020305501c07044000c1100c91042e010701403e200065501c0010580c6c010700c0740c1c1504080948000507080c840e0f05656660180181c44042680c0d501c01e206410085600b40c82d20074000030102e101f00380c9440b512024040440d032040c2103041820301004a016201003100e509030f0765041c4c45405460200765030304000d90090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 569550710 1250 569549460 569549507
    0x40b010c0f051c05040b090402030c07060c0e011d0a051c0b0108010c12021224210c031203010608070e1e01030f022110030503030f0f09031303080901 66
    0x5440c03583d6440e03080382000140c0e455154900e425200d0350490b004c40c0d400d18112030400480b10208402540301402d4143d00716030030040100026201d004002c1321a00ea5240e81044110500c00501030703c042c0c5e1146152220040d1070b183da141e580d00c0f007041c20303184103032000c44921713110300040010761103807000c00fa00034050a0000070b011641508548001a403e43c1e803003400c1d0f50002d000800381d0244600d45a41c004c5140c001895441c0941d201004030014207541020801e10311020800139505a010420351074070103001042d06880c10407074100441d805800404000d088142803003554003040c05007100700043d0102180300e06206d00401d00803810000c004001c00c0000070a41084081440303506d502117410000161603440840c825101034950540984002e000107026800d0f014130002e155001429031100080045902000a10b201e02e074600081c0c103a0b810180326850054000814030134180d4002c101d0091251501c41d03604084036809803d4580b40d050060040c0d41c4c9009030003101d42010000d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 569551960 1250 569550710 569550713
    0x19020304050a0c0605030f060f0f190f0f050d02011b0c0b0301050103050942100e0c0403030e0d06140f100504091101230d0203040308150a05040b010c0f 67
    0x4a4030340c007860300c11051803c03d00d568800588060004a03480c4500f503003680005041810401d07542006100e004007010710300d80c0110009504034030760302803825180410a00a01204114444041c060a103086040c6807141c130b4500010100c8108100080c1044400030021049880d01c1180c1210180d0025032708070620349804598203180c000b40304081c0002c0c14400410317080c2c240403130b8080c40940442040384002c1e5075200a60750f448040e031100803030512810013036514035203000003035070150034502e46d10400030b464624101401718015280d01c02c0f02d8810841080069000b03500e010714228103035902c181441b49070034018000d00100c6e07800b501300b0303c1a60810130014581e800d048d20420100019008841d182c03010f20003190708400009085198001d02c1c490258020707400d0340040f81141c409888146040080703103825400010310300708016000301c00d22003095040640c16900025101c8a580c064005400155005140d4810940076640c0e0306c3d05801c42d42d10400c1c0c411500c94000304810a001d816 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 569553210 1250 569551960 569551963
    0x20306060d020a0f080a030e04141501020304080102041e051e0f04020c030304211103030f0c1306020a031d130903031107030801240203180d150905100203010f0902031902030405 78
    0x81e17840480020f941e108d8a19980d140c5485848141030208045031026590842030030981089544168154403041c13000145000090000308041c0040c02038003c82081d0301ca540021445080d000355125803c01030302a20080b12460101c20907020481e008602c01c038805c0013040003446000e9107010540000010403090044400c45111880524100310400100c01d520403203c00c031840c11001c000c1d820801c0802c25041d03005004030f17004584013030400d01d45070242c40a541c14200300e92140c400b40e00107500960901d130b040704e081c00b5105028131629054100c498001240c0e50341e105980b0840d265111040400c0c54866480504c001c9940c810031a6104404d05014080380c50174415460f810302e85541d00ea807070b500b000600500d004001d40040d07007441e240040d50108080307840e41c42900302c0400868580840d50300c0500e14030082c00c0c100005156280303070403c41d0400182c2203c2041840c0100010440032140442d64022200b580a005807284c803041ca4441404050303000341280c1c980040f0900060200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 569554460 1250 569553210 569553223
    0xa05130611070b250e040b0405131a06010c02130b03070b0c07080f0d0c1a0403260903041206020403020a031b060806100305040311060709060912020306060d020a0f08 73
    0x600b01c3e80038550b54032240004103c0007440d0b0540702d403090840703280c000b80103114031222903800400201d080d4088001080403104106d0f14482041e200c040200180090b404802c1070108184d5880c0d042c52810f040080c00759030b2902c2c802405841202c01140620207950b00c100e102280c010180c8524980c0e4074001a0541c02529080045001d0400001881030780081d944030f06088610280080340000b40f030548604580a81c1034910707041d0104c410407a01030601d00e0f1480b8038807c0d2070f444685010000744082003140056100340010380c107424003408160000c1034a0440d05543e540c0038041000b80707048000fa00465000075040350720110040100300108400354101c3c00f40d10380143c603549c1d41300000c6550080540c0e05540200351a8030100d000c51081e0815948240641442c04149095900716844d00c3c8003143c041d400038115503c10b01c02e40c0e80c0705c22a85c000340078640300c81010380a1500041c0d103d400c041d01a0f440b640c070305860f05c1c0840d207030581a94010320508041b5408a50741e48003141e10740c070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 569555710 1250 569554460 569554463
    0x20123090706091511030d0204091406030a0b040803090c04091104140705090609011b1b0614030a0c0e0d0b0f0a0e03121b070f050c01090803030a0513061107 69
    0x581100440d000c1d205815510803111901255003228448010640d01178450075400e042a000c00c010340e6420359002d000910082c25500700c0002e500d103540da80c0014445000c1c054500c250480c950f000701154030348055680154020001c15074a840d030b1134281d89807101c0c08900603042418a51040284600e0084032a47d0102c251800e0041003c00c0d0b039a84060b01c0103ca48501250f014810120315040c03d41c06172000c81018141500c07803010029a04915882c100001c4407400b6900501b0010b030120092228003c01d030300d0602800c0d000815107042841d0000503c1780034440d540d9000401200c0c03281c64000c181603c003034040c010070300150400c0002d200045035800c213465031220200346518424400c0c0c502d0704014502450802007903140c018250b50002e8403075800680e50b080b02254030032011004112140c81502022040c09852804a0030418907110b954140070b4000c40400c003400c40803048aa00c0404800c002603123555420f241f4400c9141e1100140c02d070380c40e202e0104401d143e4200100540c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 569556960 1250 569555710 569555713
    0x10f091a0912070501120e01090b2403120d0902270a0c14160c05040e0c030f0102160308090a050a080d2f0a0c12020a02120a05070b0a02012309 63
    0x3011842041a50f94a0138450240010458440b00020004075449245c400b10700100200c0c1241c0c042c1c640d408510001d48900000300280c000c90074501c0b40c4002101801d02d411360280c039429080801140003801071121181d207494540b58075408540d030f2941c904043d40725003405001d0302204641e10320340e00391342114814505460b0032550100036000700c40c405850304009820702e1911016038006600040c50079802c4590b038055034004600c0c0d0761039004103070300041141c2c02400c142d83c0c1031041600e0818045070030b40e841d0340304100d40c6050101c6103040000e00c03909402c0c030b2142c51b1a801c1401d49801c65000c0080c103d4021400d4000c100241d840041c610368051107814048003500072180750b1400b80a117011020150202d039110075840c1d078000900030407801400c0054511000752540c4007c0785c200b06507440160000d180e400300714500646540c0702062490014a54003000744d54444c0d0390360042c014501d09a202103090051a03100750040d0110007000c0d0075000c041074803c410101c99400907129450706 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 569558210 1250 569556960 569556979
    0xb120906071b0201050c031606020913271502070b010e0c030f0708100b0c0f0106060503010f03030c060b030f0c031903080609060d08161718010f091a09 67
    0x403032188418070004600d10340b19451002c0c20750300550340ca174015140d490131800f0038403511380000c01c850030441c0180d016100144e6500560400c025a240d0202000c07a41c3c10b20348041c0c3c020340ca810801ca5110441c0c010040e00c8000302504100c040c845007200c02044990000501034200141126520304030b540ba145604042c0d01c40400c0401c0a00003241c00048505d00c10002a0019200384411500710021041c0c0340f031110344500704c0164a91000d030500380e03558440d94450b400004240300b00401000c0300c0c074041d0700f90b5050440391101c0c8241d13844080c08214402d05540203124080d80410103002c4c009040b55024101500603e8a481495100b03500c28015007545074400503803100080601070b03050761040703a950344200c20480c00e2080600341e00e400c40d009102881c00507a000e0005c02072001c92214a10302920f4078078181c0300600a05150a40d010000e1005010040c1c0400f41c24000540c02d09098070310207144602107501000c550b1080601d2458000021034940a110080100003010303036030f4651 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 569559460 1250 569558210 569558221
    0x4090e0c0d02090a090318060908100603200f04061403061609030204090f0215031807050a0303030f0b03011506080a09030e061318020306040c0804080405040908040b120906 76
    0x100301d00303190040d420100541c001004400554420180a0320a04040a03d801e21040501005005400070b00100c0c00300309050241400c1008200100d044401c0240a41400d59881740411041015170b20705252070300240c542d81c1e5954000c094176412000c1c0080014640c2e941410b05070300b10540d600d5019001c3c0f90b0109000e071020042c071800030b0805854070b007030b260b18642c05d02c4010400310405451305140b0a11032001030b5950b203a00c80440004281c629201c0c2400712501503d1104241c2e00f52072680038141c100020b40340e80780848101da40600b40020180605e03c4800054002500c880307600d54a8040403031f070b01b4a0b0018858040d07818960f1101240c1c0d641c1d1003580222169800068042040b00d00c400240d403a1000060070729000b0901050b482940e1a07801c500d81e90308102c0c02c981d5240e004020859142068843c400b481c1480d031500c0d00980c1060703265000c492040d4080d1901950b00d480a0805002c041d20817180184080510740313a81d0300d000c1881201540b815100042680200b40100d80e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 569560710 1250 569559460 569559469
    0x20f030705010e061b06070f022803120b030708030406030b0103020301080307020d0515070c031e080a05070201020f0310051203030906060607151b030e0d140706060b04090e0c 77
    0x644006841e08014440c1880c200070307030f0ba04035143c171000c03a12640e4021000603906000d074a0081c20383d51140910384120f100e000c1d0510580a0010030f500002035180044c0040c204500100c49405007001440c0c1170340f0088580250030200805500f611403d1400074400388000000e00881c2c001d5035080001d4035031040110283e1100b8840c0300e4860740b06101c180090b14104000d01d400c68807400031151041d601d030f400c0a0b5900c004860300c4021824042c0400140f54020702c05580b08207080300d0035050300e0700011020f443d02d08064204040241c0d24400070713030490b000350304560f200c41d0b02c0342c8156242d10302402900b581c1c9080c0d025a501038601554101403079900001600d0180303118502a2445540701f0b800c0c8802500071240644568002c1d1000c4030b81d80e06203104807980391411032200c80c08900818405019030b002104810100c3d4480311466584980c0a820600030b00510301619540d42c83c0d40c10044003030005900b2914a404c00014006007c05042c2e000c804030103000ca043e2658080080b0420 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 569561960 1250 569560710 569560723
    0x10b0f030312061c05100c0c03080403141c0518011b0c0305040b03090c191a03060a0b03180d0207030c030b060d150207021306053006070c020f03 64
    0x1960554000d018040500b0700c00c02199a0040700540340031084d6042a0400c00c40701c12003481540e00f504040da814085800700d0040f02104032960030540000c01ca550740040c001e032001880036082203500680d4400b000360420813102101400c0314607809003454200750310b000b00707000e0704d404600b040e4a201254030300d1010301400f034041e036251192800c103880c4d0103000d82d521070030703d0380860801c0f8040201007901d602401c0910300848191b070060800e1000380003840384151401200c00240c5d802032000b040140d030450034000300840d13900c043c26204c0d1110b002003040b8212a8104040c6460302008100791882100d05000c18080c0c0d840440358600c100d4a02030340c5130411400080d00f0541044810b00204006660707041d0404406403000000f905181c407545403e25030000d00d403003290380010780d04d000d52400c00b0780e50158450510040210614240c0040c1e09030740740c41314419201100c50a80c12104d000702030308020b42000041550b0252905020080038600c52040492244074100c2c031240580c140005c00c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 569563210 1250 569561960 569561989
    0x1106100e0f2802090a15020d1809090318031103070b030114010c03050c1f0e03040503151f0605090103060902090a1403010f020409020306090606070b041e140708010b 73
    0x1100c920180e000142d0781d2102d0402c2c0c0c0005408100135501c61300c42011960003055164200302d0b660184100007030800743d0040101c003c00c0702d1400007218125002128800315041d034400018406040c2c58191965010b9102c0340500d90b0901c0d000005100c420039a00501c814202c1c281e80d81103840724214095400280620350403045d40610012455004115410240d030203400c2003070a111101c60510719103d000ca4007201d802100e05001c443d090071038041d0070310551160000e54202828000030a5444078400c542c4072000c003800c400300302c0030511101842c803110301024890010b1600c1e0340b009080795100542041c002454100300062440c1c40c1d1003580d9040d400100102480c0d49403048049458900042310340e4595a40c80d5180210f03a460310042004024040003d038403403810300f041000940c8020130080c080d000401c1141d00243c00c10705442d5009502ca04240c56011704079251503d0300c203031304030b0040c00f54480940340034045c14000754940460707881d031001b403102108001c14000d812454021 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 569564460 1250 569563210 569563231
    0x4020d0e150709031704050904030e3604140a051f0504030c020f06040807081c02010b01021905010906021215040c090e090c150a0908070b03010909031106100e0f 71
    0x101400045c1c20f048074031007400010303810b032424542c440b00051012102a9000c9022401d40f101001d0303142000e2203840d440207011510880c01c42e925110300074070300051441051460460000007810040144502c850082058003160704254940c5405503681c40301c0d002e040441120044076400c02407043c0112881030b40c2c113580b0705010710059800d00c4030541c000803500381e012400340000328150804008a034002c043e44c000403c405408a424a00e03d0f80e6010701c001d0459041000202c0c160340c001131120001000c900d0300500c41c03180c905115004041e4100700500460000450a4540050f422118061031a5050700092041c04004000480714024442004903c40ea0000c1240d021b54020031750340706a00c441503800142c2c103c400140c0791686258090a81c5030042042442541d221081001404003800101000ca050231709ea2402030005204000c1842c7d1290480405c062003080d40a80e040c0c0903800b118641e0a1a039541070507000719004c0c500903800a1000100040030504845000356412007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 569565710 1250 569564460 569564477
    0x30f0c05220903110d030c080903030411011b0b01060906030b030a0b0601030e070e040503040e070801060503060f031005010303031a010306120b091207030210050c0703200c04020d0e1507 82
    0x225440054100e24a060f4140560002407040003541070104000e13030380031030b500059103054490340640304c404050514801580f003032040100040380003e0608100c802401c100e610091002e240c8442100c0a6070020412178449000088190b0868041c20643e2542e803000c0c0004417095060507902d145819025150741c404c1c20119245502a41c40300c040382c403121050b1019141c490f1610742ea1329030203480c00c6459520008041100414420f0800d4015959190140403540750000c0200705001c0a040e143c482c404560380542180d80410640b10006400c0d0400d2145603501e0801030020603120800c50a1114030350301d0507089620a210303490544170200090ba485014035246c210036500c00402c0300644c1e115220343d542c244400c040242c90b81c240720350b00030540303003004440007025a8000342021031244418045200042e421000c4080303603e213640320304021500146189442d0600d00d0b460150014400281210303507016942102c0c0f80c1940d8a821640d0090080c0301c01d04030008100c5880d000500c400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 569566960 1250 569565710 569565769
    0x90c06030b06070512092b11040603200f0102010b090a09140715030b0d1112031306030204030b0106020c01090306090206070b090102090a05101d0d0c030f0c05 70
    0x80d03106441603030002e0706440c2011450303a5064a08001e08000c120440d02c0450468064079200041d11a111060318014a8000800074094500042184020b19a101c400c20281b46902c0342e600103070007590005440350f400c110380b4040b42c5820400c0540140102c1340c2038101c0400c0d500502405e03210290151a0f0505951115440c8009103a1100c5c222035a1640f041d4098410130f0810000e0003400100003007414a101c8030002408403002101c949000e410440ba4400100b4031040c03035180b1007a000d80c3c40c810540008005141140310328414141c503038070301081c0803c2540d4550702403c10307244207074100880399072200e0003071f41d861070171164103400119480780901c001a9180c0000c80c08505c0601881c2c02c104055a8800703202c01c0c04c84201c02d039694003146045151a1842c99034008040580b801001141841c10081c1075801000c103500e0042d1a1403a51b0400ba101c10320b1388500c003034200c1c80104a0b544c40f07286c1900d4044540006031000c0300c2e06c11000c43c9510301010540c82c200a1048001d5409045 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 569568210 1250 569566960 569566967
    0x7140c010617030a030b04110306040203040213150306060806091f0603020a06050306030c01090302150a0c0c0e01030b01060f09030f02010e09160201061409011202030304150509040b04090c06 84
    0x2164600006548403000003038001c0d03030103079807107044040c101c007031500e50031042d030020105e64004810b20b2069092654841d42211094110f0380c00c50802e40e0f016a41c0d907140c1c00800c59003410b120f5000c4419151091070100c2c0420000c00c102564851401441190303620400340356100400e554085203508000c801ca080216910340c00c0d00d018801a2003ca811552900020009a44c0390302c498041100001002541d280a0080c4a4240400d091114080d0b06507000304000c41c80ba0001c51221160000300807003207600a40c545a0615440f02d01600c041e41c03074242c141901071b001e1104441e9042107000200b00c060284000321400c1020f680c03141030040c516102c036801340b6480c100c16814010070700d40b42000c0ccc3e202c10584510811544001c080310048010340242120030650102d070700701c8154031000429a8800c00850304640c2e40c10655551480f85000103421449180c1c092400005016260f0702600e420501a04205a04507420092182254103000c252141540c0c0100518000b2a007031161501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 569569460 1250 569568210 569568217
    0x1a010e1b071a06210a0606090c0806010e061e07110a06020606220c17060418060c02240601080708010b0706050709050d0507030b010f08070e04020303122802030714 72
    0x20000e15038201d2003104c0d0030000b141c1c2610b014035030f2036810802c0f58005001c0c041c021403008001c050002c01c402010b48074014550b00703010300164100b010100c2c07084080c2e030b07401e001e0362070500e10604403401c0f00381c103011503003104d9100c3c1030100c40c20b40c1e000302006151f10300007014104540103a0003514240c1c1e540c0007080490000c807480d6010f90a05055650300381c00c0c851107000b400ca03010340c490310843c0d100301686005015000340320a1149041c45100f00481ca00791004111407a0b0249020501088080d01a824469080c03400655030300e41c0d8030a151f8021105549074000d000c04e032203120f1a500d5800c01199440c17001d00641007001810090300f00000c125501465024800703241c641103c070744400c00103011624010090365139500420092080c80740c2c0c1c000d010300405c0704150740e600f803618100401ea107581c1f452017403c054008800010341507483c00d0048500210345402c980d1201d284c038000b82910310452a8207000d003604c03050550101b2a445100300d1707014481c561035071480c6881e01a5414083e50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 569570710 1250 569569460 569569471
    0x801180207020d0b070210180501060f05061c020c0628050112080a030902030609070602060108030a0c0305030405010f020d0603030e010201090305040909080903010c0305160215040b041a010e1b071a 87
    0x440c1f02030001c1e0300b45003485643c3c1c00e88207012003a40d2080c400d04001d801d54020b500321080c0c0d8010075074104203a503a01d4040780c000d5000580d1880c00c0d2056034513050003d010b16031504155009240401800802c1244000034110140f00800054081214800c04588090041140e0310007081018004200000050422094280780c0400c0c941c81c25070102e0b0400c0401d8440309100c0c0d00540060080b250103000340c0d409418004021820030409000c0102440034041e070140030300c2000070102e400c0c0310081d00000b104840b02e900035503031900b0110030300c030080285200c241c00090b00c01006058a40c4107024803500d06815682d201d0900e8241400100282080d0600303e8141e00200507412940c0c5080c01000e06298141d01d000940349807a200300565803d01200700c030110f4000c903030548182d1026055003038000b508140d200e0f1041c1d80b185054101002d03484112490502d900c0d000041010364070b902e8502c20480c185050390b2410074886042c0003402007c80c02800c443d1404644035150507045009988030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 569571960 1250 569570710 569570713
    0xc010309081b0618061510020f120d050c0901080610111b0a0617160c0501020c060402011808060c0a02030f040306060626161e0801180207020d0b0702 66
    0x19008110381d1100c0c80070b44182440036000f02c000c001c80201411242030a1070750030005005245000b1000494001c2280c507000e1244003903424020015200f00010425a43c0030750440307146480380b1038403074400d8024039518100e01e42004001400441081c080e64050f048c180c4580a00f5241d407801c00c800f03120403c086404201c1c400064418110b0300300011801c4980300480c4000000020040c440716004542040f814001c1d0a0a4162900040092194031120f4440040b240d9400360204890481c403282c1c002e401903001054809030305001160712400b8070710036250452218000c02800b82c02d0245489030b54600d8003c0400900c0b1520310000070140491340780f0607640340019007424001d090300035420035200c0030754a40c0e0501c1090b0308100c08038540700c03c804110080a00b05229541070400051018060f0300b01c0e201184d9006002e040422070490f820003174601115010300d0000e010707000c2403090a0801c4510000c516604400e407003100c00c050f4001e000f0b000025083d86500002100180010301117 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 569573210 1250 569571960 569571967
    0x203070c060f1b150c03060806010e012409050d08130608090309040b03030714071d0c220b0a1106100506041e0801020304030c050d030c020d230a081b04080c01030908 73
    0x244c2c4e1951080d0b1050f400359441c0028000e0602c0030340b51604c54146c0102c0c1181c04000e00511005e22011004421400c00301c40b00580305a000d002190310803515488584c110466981c0c0d0010001c901000c2e04c0d03025004006042041c0c3d42e454101d40701d080949a035039040d001040b00508504082d04000c41090010301281d140c0b16080d510001c44d80f28401800d00d036a0040c1200b0322041d41d100c541c0b910381080040c02410030b41031100b50954a44106441600c110302030a48840080d030b0300c4a8940020150204035a0b2500c0201d2800f60801150058800b02401100001100c1c05401e108039002d8a00c06010181440c3c10030840645604030281005500d1b04103500c00a0310b103c0c01d0001b50721541c4a81e580264806152514510b00001180c0b404141030a1401d800c0c0398582c00240d00301e00440f07524150521883c0c841280c07030328102c1d5402d901c182c1e04c1d000551507103907500280610b004010070510303d03024140041803d46207000f02c0c005c408085c0c2210500c1c10780c941c480d8200001c070f103000c0c1c40705918 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 569574460 1250 569573210 569573243
    0x62105070f0b1c02030709050d0201031d03030108070807080703030e1906020a060c1b120c0209130209060117010b071106070b01170a0503090915030d0203070c060f1b 73
    0x140c0481d180d00c01003099100068014042c0d6062001c4100165481001d50841c10002005420350740c040c040e05000c2c030f8019442006580c800d0700905442030700041c00c2d0601c0c0b0301c0d50142c41e4883c1c0c024040d03181280b00d03402c0c0000f0381d403000107110350072902e049015089990441d074040300d0800041c0b42c100d034414888055429a44095110400101003030b400a048444203460520b00342c1d10384002c8082403061085481d007034288030301c0d54062019440300d044495245400c0c02503404440e0607a000c0e400071842c4040080f48581c1d0009095030074000c071410012952135500449080c81d150745a200c405d006540108200d03034101000d07000703552003a6409004441c0001c08102950813129041d156041600010004e90344501000740005c400d20001e00201c48603500d03820382e64400c918a6500400c0d01000045502c44841c94083c0c130f82400500344c8e00a40310000d8000c1d45d982041d0420b541601940b80005041401601c2c0d10900c0d404a40703d844100040c00c1d059400b440001d070040d504a90742201098 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 569575710 1250 569574460 569574479
    0x1802093301020c060a030f0506090106020c131104090b15030702031207020a02150a09050402041a090f0405042010080606070f05010c050c070b040b0702150c01020315011206210507 79
    0x405154170382d4000425000a04e94001614406070056020b0400c00c001441a2a400308145680c180c01359034000440d0341c50395203000108044511800000c0c00490003080329030041e000160500c40c204c031114040381c21400c0d6010640f206403200300141e401040400e03106603101041503444195401911001c20701c540100b000c0c2e0545070181c0c450103d001038620b502c0d030b1300842640041d040035181181054184813a02a40505180c034030000514081000340c1d442d95201e50f46000c12001400901040c200342c5040710041c40601031a01d0540d03038900080c503560610125031010800c0039600c3d00d0003a2100018444150310003c0f013650201c00c1c092004022400074000d413030ba510441e55a0503502c6c5002c070100b90602d00545c010b2600017004110400c680104070003903409494040b00c0049002006183c0c0348240c0c03140079100383d8607500100810400849046076580300c60001e03280c1801c1d00324102c840d0021614070303000d8820400c0300106000c85148100c036958444500c40d004487e40103850380f00c0031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 569576960 1250 569575710 569575717
    0xf0703030b04050702060402031209030111040e061c020604180b191a0f030f1801110d14190f180b010f0b0c06070e01030f1802093301020c06 62
    0x9401007521040c8045941c2003510446600010354801b4100e02c1c18070b580080e441d902c5050000d403800f100440d8401d402d41c0d00307500c030602c489089034282c1e54440c0d440c400b2400c00c0d1001c4400501c217148801a80148403101060020340590045c2002d14050512445401e046025801031340507513901e100c50b80076520368031483c00320003000c00210b406031440d00d070719154007288410100b00030101c03d0003030300d001041280580b43c109510000c4544a9910845988141740c0c40b400c03440b01a600b800d1055071200100e400921090741030b1079040c0801c900006591001220039a08940c6032072044405500799800c907800310745100000000401d502c6554200d030640b9090040c41031b1400d001820040000c4041e152031350000f455195110340c113140c0e0b458005500c810004010034203009c0d8224549545a1090380603800c05c045c1810100611501404401c10059481c1b10480c0544801008200a40500c07400f00450200c1e600707aa031403110303681c103032034442d10584c807101415031099050000c401d0713031040f018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 569578210 1250 569576960 569576963
    0x3040605010f0b070f02120f100c030609110d0f020c030a02010b1018062318131506030e070b0a180914162a03020106091802150f07 58
    0x209095041004842c0102c9090748000c20340c881c108410740001c0c1e420003a610103250100d4040c548250040d00391402e0440c022500786407070040c44d104412250720742d0310a8941c1c0b2043d90b820824661138110440480d079420b6101c400702c19007408140401c0f1000e412500d040c90460728050b0601300600400341c235640040f03941d000035135141d4141044604000e280d0b040c000c203440c0303048145c0e840c0381ca2001d402004036000f008100141250610090355821902e00407030645440b299684d02841061540303d00b0340c1140c0c59100c0e01e0800700131401000b05008400c4280c900115000c01c0d249040e00640081001d25036002681c001c400300040d286076000042c242d0009140c84494035000d011071248204070481c0c0107060340b1450036050003813080655646c543c0c03101560280c44040d200700c14065071000c0c40301d190b04489051602448541c0e4155490443c1034901c25002481015200e0b18500103503040310b44125095800003d2050142c503105080e10301c01142500151b1400781004024041039200403070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 569579460 1250 569578210 569578223
    0x80d090c090c120b1005030c21040218010b2b050c040f09020307090b09211e150a0c050c01090b06100c02010f39050c010807051215060304 61
    0x102031054680180d400c03c940030f070188082007400a290000f911007540a00b10303904004012000130b198081c0d107400c66600000360f80c00e044440078485514120400100e4007240030700340102507241d140700038000f01070586d58400030300d6003440170403032800e490600d41060388000038004c4440c100c01e000b40f5204440c056082c2c1000190381e94100101000d080101d03621100c0414410010007090a90200000f4240e0740700200305551842146c00050001794545401410f204449100150402d40000c1618003804048100300c1c402c24a504041c2e1207011050ba074002c0c018940d40001e0300c002e03d0340e000d0707403142089041036814070700103280c528215500208119038070301c080004c0c45100d1410380013001c8415018640204014050390000300b5820581401005000d42e00705000902c40000c1c000c00c444038410b4900e01440340c20740d44103420030000f051054030b8070f020f20f06032551194400c101389440707030343da50726110f2803c000490907082d8048028a5207440818101c8440078070780c0c0b00001140594003800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 569580710 1250 569579460 569579471
    0x1903020405040c1a04150c02011202030a0e0115030302120903011e02030103020109090c1704170d090204051812031f1401081f030b090316050d0e03031204080d090c09 73
    0x988441301c400d05480c284108003c140810050b1186001003000740b45814601011454110b10043e02c00820381c0c04813002142c004003c101c4010041c1d48000c0d80e00502d41c00a02030400074421203900c11030540009401130b001000c00b0340038100003000500050101030000145003103100380c001018644648aca400d00b6030000010000e641c0d02000b2a00078110701e5400308000268000041e0041d1609a00888103003040c5001500340180e000e400754021444c1030480c0d40c3c6449040490008092860003288074615120200d5500c4e0300e48280b41136505011001841108251381c049041d64000a2010100c41c80c6441c6e0781c0a41041e0207203200090084041c0c0d4102101c0400015011800041801c0341c108803001e204002c4c41150700f1003500712908821840c103d500c81441c0c65040d4404c070381c20b01030b19184011035041000000180d4842c500c02030b0340c90030300c070328098000c00d9106c6c403d0304a02d40d115070841c400718011030201402800c04911036680011300800c540e07a10300380808141e02c851007403a03444 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 569581960 1250 569580710 569580719
    0x510051e060a0c210807031a03120706060e010f05150702191508150d020301020408031204140703081b0a1401020c0d0207081903170f01090b030606010e1903020405040c 74
    0x80305200080143d901840014420f801d4000b00f05d010011b10901c1055102c5505202d03c08181c0d0b00c6508002c1c0181c20341e4030b445403001d62070f40940c0c07111004941e401d1500c0070004503035811a03005030503160b99a1801e0b81e0700e071401003000601d000d030b40f10516207000d040025000681c0c1f14071800790f4108080410b611101d10b8410171304100109107842c0c105205149041000d542d256240500b81c500c0b00b211981035130402c60010034020b01a07500001e445200018841103040400644148194411820196044c98030420140c03a601c40348402041c030740003407001c2d07400030301059011040c03074105030b0464031800b00c207482e130311a9004c5024440801e42d40c00240c4540d10f0a092010b5000d07400390340020031240b0302d090308440d80d400c0080e0036180c2d40040070440b10105031080014a9190421101c054040e080007902c680a44c42c0038841d56209516100c030940c8141000329030b4074840d64050311186521520700e8140182200c200200c070300d01c0d802c0d402c40480180e07540c1c450940198060300307941a415050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 569583210 1250 569581960 569581973
    0x2010504060b1e100918022802150c0906030f040c0f050d0609050304050d080909070c0803060906041d010b03010e030412080d06050a03080703120510051e060a0c 71
    0x1000d592600038003d110708010031016500d0401c51501090304c24002000b1403031421111003c1c1c980040a110303a103c0e44003d14810f21307070068405d170041c0300e8071168426000400a8040d600900710000035030041004900005044000964032040000110f494200341000103030040c0c1c401c40e141c0041c030300c00809010500020594650262010401c5100310505010010750040302c1200c0042c0b038140c69258180030040b0a0041c0c40081c000500750040158440c40c03c16030720b030882c54405000e910000c0001c0c000500c21103040c15040d801c90052850758803010280300400a005203ca50000c1d2180b00e40002e40805030070580000300090000515000204201800d4958043c45218907520520003404000701d802151840d203980002c2140e526500350903000090038440c1c0c030607a844512104c5c00414400c1c1800141081072080e62032503d080c0010071035000701c880c240c8800b15100480c020502c41d60410031031a00c40c1224226042c4441203400c00084c1c01e9a0110005400084050f0201410400c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 569584460 1250 569583210 569583221
    0xb0406021e060c040b030408070519060e0111040311040e16030b0606030912030702160f060206061509060c210405100203070f111807051909050a03110a0b04060201050406 75
    0x4180000c0c140b0340c00c00c0c0910031198000d6024617095480004040307000c0120a50440c0c4610b0703444070581d10a040e071040035022028011605682c1507040c04140002114103110b00b6000b505010003080c1001e044d070b200c402c0210b0481c540541c1041e80c0300603050351814200320025410320780704443c504241c00d500d0090301d500340142009008450600034400c41d00301c003140003107240d142560450348035507030300c101203260002c01c0c8a0507203a03541c0e8903404225804000030000c03d81c1c0a5408842190b12407000b8011940010703504040c8410050128090f985042001010000001c42c2110461030f204c0301c0c0012505402d6007108a0924001010401d0f0708150001e00e0100f262400074501340000c503141c40c050708134034030402401d200d40b100e400442c5907141e9030b80050040c0000780f804032902c2d10402c080c0c00c0c0d03440031525048184211490041c1b0718400e0303620106680300981108005841c580d2104044000c00f00c00c1540065084404983c2800000181004218680c004035140c101420030008660 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 569585710 1250 569584460 569584513
    0x2007061d180c07032a1515140117060a060311070b07020a02040501060e03150709080303011d0601080f06040b060d0c0c0516081f110a080a1a030a14031b071802130b0c01060b040602 79
    0x828ad002042415958840c11000721505030901150003981c0070099202481050343c014090303640b810611284690020380741003650b20a807020882d40e40c0780d0900f910b202e58081600c80c0c1c1a0300010240034001c10145425810119609000300070030384850603241560000d030403140144d00c84247c5003214409004400303820803020300340800c0c00d040002c458415981300608890186032507100c817001300c0e21440101c5620907280c4008011150840400809100c5803040503159485000d003a420f0005400242c3c5003202d0b0004000c0004c0341541c02e0950000c03543e00441910503036501030300d00d1003e60301c0000b40041205680d621080f4a03003104503100302c40e00c2100b4001c04103d4004580d0f00f0ba100024012802d5800082d992100441d03110700a28520900c07200c4d00a105803110f20a02c514400520003042d201c802d1049040c48461b40c01f29012405040c01386448115208400c0201c00c0c1e1000080c00100003500001c90419101e10704d90065a026900550040e8040c3c5516645001d40d4800648500c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 569586960 1250 569585710 569585747
    0x14070911210709030f0206040306020a110105280f1d0325030504050603060a030215181008061504030804062007061d180c07032a15151401 61
    0x2801c000b240185204000d01005000803a504509400d55070381d00d0556004651240040d540c1c2d01d44d0060060101c4422480700d500d41d07080078045110342804000d4055030400702c6191002640c161150100507103441001d0340d481c550380c1c821818100011486049000703400750b001b10b5403005216803540c22618440d0b41007401e40361030b01d442400032b40c1c0403086070200c1e9800c440207922503d071100000c2031111389610096004602c43e40e140c981300480c02c007a0034261040c006441c54a4014410300218489140060700081e04510018000e890300c0c0d0360410728010108800f0b42050348940c0c03100740c198095002003020500300260440e14822480d10074824162041c081c0c9080362510101a00c94122440c80441960940703107954008c1d1902a030300851800341c8003840559085c07006110708998040e11055001130841d0324211800d60310008051040c2c00c911110442080c3e1f691511022820300311202e81600d5290b440044141402c079428502030041c10308101242c180520026112007680c0c8481f00c00e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 569588210 1250 569586960 569587027
    0x501090207140105010b0a0c030219050c0307050405040209040605040c080a11100c020d08030603030904090b06280501030506151b0601151706010c021003091104050103080714070911 80
    0x1005556010740c0c1602c078031f03424030b4618548186816410001e840e0078030025028071504081c10300c40c0000380f0b0304031070a0035010b03260810b07203502c1131200350b82c030031100603411200703000104002851a90040c0d9000e40a10060b40b5004c0d214001241011100001960030100390074020855107031200c0c1e40e188255181c1007410440d40c582d0302041c604080b0b05000b43c01a2001f100069035604c0c01d008a0300c20440c0244104044410362070146200e01c0c0540d5080e0141c044140c014900310500001c0400d0007a07100c400d42c001501d0721004601810780200308542081000c882c100185204d10041d1150003042c004c54144440752545031460004141e20085a051800403170340740d125042148010580c0902000c64841c1c0d0b603460050390144903000b0002d4000d15011008584640d166011240d410306c00c114154202c0c10f120104402d443c400c2c00082c284070410014000016206a80a040d82c00d82d5000c2d104000d5488100b403080356240c08500310410700c00a40700c0051303d40b60410100c1589549a040003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 569589460 1250 569588210 569588219
    0x20702090604050403090b12040c0e04020312180a0e070e060a05070314070b09150a061404150503060703140a090c03120203071704080d02060c0a21050109020714010501 74
    0x54580300589918022651500801e090620648100c0c2c054848856890b50395410b081d0804a01c640031601514034040011000c12501f072003480050156070005d009020281440c0f910424a50020002c000a4545c0a040103115161080280d000348643c170359a888a00d08920058144911412054410751080241d114080e80100c291903442c0d030189001303c0f070305c2403094a81c2200d21401c0310250036001c04504002c041030000a4690180c4c104540850054a03440304e1f24080e10900d0054801c0e080003141c0310400e9050607880034504102c88020240e00e0b558580201781003d40a446550000391128071099102951218203500b10810071420460340c0040d132201907203031a050000800020312a20481d80f41c920070020342d0210b41c0c1104025020303400310b0044a11551261081e8191400380c1080a08858000305409101b5004101c1c040d24151001c007046810342c175000c0d100e121f00d000181000d80000002d1150354080c0c040b41c1c0c0b0040e40c503511070600c0b44c90f250340310581c040541c0c1003800600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 569590710 1250 569589460 569589469
    0xf02070b160503040315020702010f0e061b010b0d0503030a060f0f060813140606010806011e03020d09050609070e060d0c1401030b040912030f0606021c0309051905010c03020702 78
    0x1d142000c0401c41c5140c0d9031191410a00714401d40d4000f5219206245202011003c3c135402482103a01c03d0301c2d10030900009900599003140b400c1e0004e54404030a01c5401d030103c13618592140346016900c0000b840b00155000148154081072007074615500210800070409114070401001c1c000ca540000c040618000c04400c40081c1c0303002c2c0a0401400e400482d4100f08400412140c40b40e20500d083c180c08801060b03a0346d41c02d005c9a003140011400c002191441d405064903040d14036010090b500f04c1702e2001ba0a40181d442030b1000c5001e01e03690300514003c00c505102c907a00070640c4001511501c0d240c81c042d0b5613850303005040c1034442c01d01c00c0c1c1320b0000220302e0803150003150f0105124031b0007142240e0040c0c0040400c1180250090b0412040404000350f00d494880b440c0300ea81c03410032070180c1c840c214004a990b107008803001f41e40051143c0d078210706400c1d40481f03090010700d03012506400c01d56444d13003018010102c09143d407100030b01c3c1761b040010030700504c800000c0303500e011410641e5540008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 569591960 1250 569590710 569590717
    0x50a0306090c030f110a0b09031b1203041e0923060d0816120509030d0e12031b0f06040c03320c090603062a040503070f060f02070b 58
    0x5103055924003840c0108060b4001d024021504088000241c80301400c0c04910b8400c1c400c403461040c600c0f030801290014001c07059070b1120343c0103801031802c42c1d00840c0d16003008034403801480d4490781540006004080800040001e80b40c0601000820078690b9412283c2d1000c85d005503551905000d1030300e202c000c0701890710754560206648010151140700220321502c05a0382e000e011b9110000310015a036040c225a0700070203104030303001c1c444a40800411101c900803640d40320780c990425600b41c2406881401458921b120052440c003000030042e0301c00380395600c0700e4599580390142c9440000607400c24415201340300c1c00c0d40d0180c0010b16141c0d407403083c2500c8a020042c007482c200c0428981c02c1010003241c0c0d4600310400c0c0e244040807020034016076180c0201401c1882036020000084450401056282c0a01e14401d0b00034a10b0700c81c20030200000c92440c44070440e1170b0060200203150b03078042003130704010034221000d08401420070000400c0420f8142c80b11007998003440013000409032400c2103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 569593210 1250 569591960 569591963
    0xc070f120f0308070e041107030e2421090a2307060f030e070e1f1409070c050111040312052701050d02040f090e06090303064c0306050a03 61
    0x107940d25602d401056035a20301d0407403419002803904003100c04115200c00180701d140d002b5129207031142d20000401036488481b802180d50381c001c8080b107200105481c0007900b5401300d03a602a518070700311700058000404084540f0019070344100c2c500c20500803205a181840e00181c0040070040d1f0744181a00c0d13851070303940310700c401308210200000069403195120140320712042050724481652903030640001c13001070b1b660307040807a000c01c500b880c480d00b0b90b84080c00b100c507540c00a2001c0f28544c001c1098034003004080000340310101410100041080c031034421074122540c19652242c1c00d50819400310204050400c06000d401c104421454100da15403910848000e0f14004002601d10012079041c05126407032141b8a002240c041003c2d0010b0b002c10064900c410000c0000d100c01072081c640d1100c050b1101801038201300003040031802c0140e41030b0a4001c5a40c0003e00950700f040d400b0440d0030f240403180c81004244140007000e454031504814503075140e8a020300100381420000b408101c600c3c4030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 569594460 1250 569593210 569593217
    0x91509050904140d08221a0601050c0703120806010e0f19170a02030f150a0509030f2101090c021f0b150d05062b060b060c070f120f03 59
    0x150800440300e4040f52985a44416521252802030340600848000d940503164580c00345111151007011288650445030004049012001d000c1061114800d01801c0b686c100481084a145090000c000c010000e51140f00f00c80c1041c421404001c000f0b1001806c0707581000728009540403250b0302e40d111060179200440d1440c004685100540c10195820703845919040c243d4120081c40080218000f42464000d500f0365003c600781c0800c181d11009118103031039061007a100811010903190740015440340043c2c1c12a40341a8000e48044040e803c00000c0b060705944010310b450300708003000017540c0104542442400001f00343c2c1c002075120030f0400f0382c3c620740080d04522141008902d81010a0007603015142c400007074a81c02540344550304c1407082c0e2090f00d04000c0894158200781050380703c8588400c1400e41e88004500f2201094900038030180c0743c8a49516200c8026a00c0708020f02030403010f8401481c0c91441c002c030781001a181079000800c85ca8901c040300d0b02042030849a141025810715 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 569595710 1250 569594460 569594479
    0xa051014040906150e010518220507090603060b03120a0e0109050a1502060108060609060105090612010609050406060203031312090e070507031103090109050f030a06050f060109150905 81
    0x30007090003010180000b510716800d0a960a09803004603034a8020b030f91001ca405444c50380c03900709001c0b0310300143d04596038000b50000014100f00f074840e940f841441c1e600480440e220281c1c0c460500c0c1040036040004c4240c3d49000c02c0003006164881c00712803010940c0a04051041d4084403407842c0139041b6040144201e00c90000307410303032060301d099002d0032004002d80e5031192036102c4d01c000e202441d020107015104074000441d020b4400141c65110740c80041ca003280b184c4c3c4007401110290804004190000b03420b11040500250306c520035400381035241e50b03c5016614200170041a40c419900c0346055400170002d01884070002c1c841d041c3c110781c1009800f41c6a0b02c0380101143c044a00c2d0340000c864401c1d04051000f819400f40041144a003e941d0380902000d1807280c651300c9106980c491808034690820821803400c2c01d010420031000d004013515480c0c900c1c1d80720300c03003680c0b01183c104012581d03a004222496810801c001c0180ca030144031280e50400049018042109500405200300c0c4200e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 569596960 1250 569595710 569595749
    0x5011b1706150c01020403050601090e07240c081801020c010e010203070206090f0a0303031a0108090d0c05010f06061806020706081305010f020c0a170f0f0906130b030f0a0510 77
    0x5003c452070500404000c540d1503503070342041c50b1603074004e0198040d62401c3c10100a480c01c00040e03140141c448103600010740408400190400460b208000d1043c007170303c40d050304049180f40b0094401c5509034021080a030b00c2010009051010051006051080d031014078000e507640003051b0b0380420fa06456290350f8801d03a4002944078000c0c0e03020395901480140c000302c10107074075801c100344410440c1e0318044880c082100644411101b241c0c201019070080b19410f000c9845683d043c440c843c0244000194110344080541c19a500740d04a1004150644150a14461050085001022280301601c442400d05500819418001c1c0c461026102c1d90700780e200500c00c0a40c402c03000e02c1c10307101c021551540c4200c0c0494580c0c1d103012060b900e045490b1a001c15070140765040340c050010100a00c0e14017141c00356080115040850041d8114030248180340ca02485031031102c1c050041c40da51540c69180048818245400041048046a00f80740c1400002d4644d280c1d00c00076541400542034501100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 569598210 1250 569596960 569596999
    0x90f030f082206200417010209060a050304060906110a02060a0c020642040e0c0f0d06110301060206040b01081c0305090a0b0f060a14241605011b1706 66
    0x82405110704035942d9500c00301c0c1c41911354020803c031682e0108200302d034980c290007a403c0380503000c019500314404102140c083d0780b0840c025984107108020000e039003501a210366044541907200301403100c1c0002141d204840d0100506ca520460104e07003030009081c28030000391901c0b405400c820700b14a1036401e4440380030400140400882c0d403c0341e00001c0c0407402d100030003651801205940101d02d460000007048c60041864250310001030081001544040d0500019400c4c8020584007255182c0c1000f0502d01d11200850080165900808142c01c0500340b4082c0c031501030380000c40b1135001c4440003000000c0d260110240700f8060900061076602d142c20541020820480104240d9500e003c0103288558410341c9406418217a0b030001c2c545413650048055002c00d085031950000501da050340803402914828000c0c800b059000354107004112407090380c580700086080b540ba9460341201008124410b00340b541c101ca407440c00b4000c0f070001c3c100e282503040303025001c14024498450884014104c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 569599460 1250 569598210 569598221
    0x160b0c10050a06150e0a0303081003020d08070201090f0e0c070309150306090b190b0d092108070c2301020408150103020325060503070e04090f030f082206 68
    0x48101808a4903007940400000c29150040c8940f4030130b003640d40030216119070401901103001501c440c3c902820b5840903511540000d02203800003011400201c0140c60300642d0846c102d1095580980380d40140c40050046566900000d41d915001042000604225081c0c160018058052280c5d200418101201d8585070740e040303210840408500e8810550b4180c1c041806c0f200b1110741000b0551140081040b10705460606960410005d44284140c214000c02410880d001c4c03840004d00c8000360351000c2da290700030f14642164051003959010001d4100c85e40641c0501d082c607260b0504d040f6036a441c2808905d102d01c0c1106500c15410120a0072025030484018180714000c035225001303419519a01080240803c9000b07029061880c0e840c0322084421509000300b10f0301c4008002d0801b5002c44e250780004200d0010040309401400007902c81d449a58100e501031185501d0340341e100d050107043c2401405028041010031000c100c4010080521f541c2110b1402501c20071210341404c0400c0500b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 569600710 1250 569599460 569599483
    0x150d0b030a1a0a0f02131a0c011e060b030601050f0307090f0801020705300304060f050f010503010c080601020c01031e050c09030f03182206091d160b0c 67
    0x2034042c0c8800c001c1d103084904003481802121800d205003506503401d02d060f402030040303081001c00c0f0141d060101c4031003c0c00542c03100b1071400907181051035005810782911101511014510314000c902032241255002c3d0310041c3c40d015107020303c0c600705240002d10380c1c800c06000842015010010a0714607102d8000d030001815402d4002e00d1036603e80c0601e0303000350f0069204480701e00c0750300c2010002003071620b4a01305a51300c80c500030b00d000700755022841c40b0764001041210f180f6540d008442c0c04400ea845100e004104144060300c50b9810300c1b0516003103414201803041400a40c3c03003000080c1c0e07800120929950000c2c0703408240004a840390020012038402442c0c40320b03040504020a640c40f5001070039a80404501703c5807000d2158605940741d12411078850440584100000d02a041c8000c805c101c00103009440c003000b02480300c000080b145103401441d102516a00e02c00f0903541c09803c080e08501401c00074110180c04800c0c1c8900240720f030b10901024000110380011408d0050007400240c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 569601960 1250 569600710 569600723
    0x90609090703020c01230601080403140705100f02030f0103060c030b12060403030c050f1206010504081903080601090e042a03060e071205031206060408010c0201060311150d0b030a 79
    0x2410081c001601030f4200045110243d880c00c0303500b090402410408001c10845d1554545103500c40c0b6004440078a80104140c00380424404c2c48201610400d00400305c884c09600600a1601c2a600781019503200d04620b14540c0d0052082c8810b001254104c01c2c11030398050f900080146170500c040d001381c0300c1c1c4046a13600541c2e503852500c5e0250041100c9208038070030303a0104820501d140b0107a5407801081c80c0d4030100d100922409600e041e42445250700444141030041c100381e541c1c104e0038030717210064070303040c82000741840070400309900b0040c0190007440c242880f0381450f05000e501030a4a400810241c420820b141001c000710030b0320240204020019101c05440ca502c6e801c0810151010480011041c492200001012581e050500010700c0c0e008010b18502114600040000800508403c0e400300301000700290900302441250902151600040348047c51400c0c6210030800f6907a10600410301c1000348910065070030210340001d82c10f540002074405c1503c000c82c0c589003200c10014181c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 569603210 1250 569601960 569601979
    0x100e10060e01030204050603060c030403050a09050a06020f060a0c020a060504230624100804110603090c01110d0203030118020c0a06141e060609041103010605070c14010c0602090609 80
    0x24401c903146410f9a000740e4050015850300320a055680700211031200300104141f002c200040c1c0700340000d01c502c091500c1c24030040c03074451001481c0d6900340c0d800351015038490000b407042c8000034400740c0c0d80840413136000c1045054001000c0d44803200c404000f8002580d400c0028204081d0f0305800100d070301203c04040005040300d414070780e02c03034090b04c08200b090600e0348014080407429040c00c480840250054108116581d0191004400a03204641c81e43c08201144d5140c0c0303440000c0c41c801c00e60300c0c0060072086d10f00c0300054203103034181f030680056820144c08954501d4002045904458001400942c1c55603400b0583d002805401443d08aa020705162681400303009d4004200c0c0310f85403100c183c442d4640d01000102d0f40c80d2203200c80301d088100000101c85140a070082d0450507000f600c0072402d188141c0f0002c001d82c0c02600100080b03680441c0d80c03070a01c00940d0032680070307000c4141c00000050a407800a0a000c00000c0010b0507103400007010396850b11a91305907102c040300078003800c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 569604316 1106 569603210 569603219
    0x301171605060f0d0f0c0201020405041a0d081b030a03020909010918030f0c0c0806160f08012304020d0b041b12050403050405030a08040503070e0108100e1006 70
    0x90361103010f28041d803503e0080140352000787d07000680e500d01b08800c10003204c0560316400701d5642400024540c40d01c94000400031203401c4030350700361030700100008034000c0d2030746851a8800340004104030000c035416401400741100d086034001c00301d84c2c03620900c20403202c106500205090680100c007021038000c00944c44401098980300e000540240ca4101422040364002c801c4d0b94008005c20070003c90541d880180c032011407070100807440d00548020700010040c021501100c0000000920303207080c4600d44071007140050710641d29402c04a05013001130800c204018000c9050900b0b40c1c240b20308028405481c1d1000e41c640b80d195001a10300c100c010480108102c0500c1401c1002047c0f9550400060345074501c241c220a80d03480c02c1c03006050416041d644084a14250000103000727000001c1850201d0b0a50100000b407005800c01c00c061070b00c0da64118070704e0b0342c40c40c140d1b0206 = true := by decide +kernel

theorem cover : BRFrame.Cov 569424460 569604316 := by
  have h0 := BRFrame.cov_init 569424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 569424460 ≤ n) (h2 : n < 569604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
