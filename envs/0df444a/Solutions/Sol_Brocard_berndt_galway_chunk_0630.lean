-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0630
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:49:24.003366+00:00
-- url     : https://prove2.me/submissions/3fa52426-aa2e-423f-9c9a-8087a0d80710

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 113129496 ≤ n < 113309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 113130746 1250 113129496 113129519
    0x2070b09060705090625150c0c210c0611090315040c0e04110405010e01080613021e040e030309030909070c0c0501081e01060306051306030c06030e0f0a0602090901 72
    0xb00d4150311400e240c66210f84c288032158008569148844000804280025540e10600c1d03001c944140955050a1074140480045a541c0e0704803804220070341c0d02003c00174043c080402000100502e407070b85074081e00d0000701c410000241c0f00501c2142480c580c01404a0200042c01c00708200f1415142032200302c00c980400c920007150040c110490359001041000d052542164115001c0c07000060024a100082401e542081e0320010f0101442d800401540310700f407003003d82110260030000c80c9524680c00082c1c0c02c04c5011020b55607409202c1d56081950790301d50000400001c240e0959032a8036000c914203840c0e40103000518003032005040081e201c80e1213a64110155640040362940003400d06e401103880180040200c01c00e00700e11000c3c4004101e01102403802020300c1e42d0049002410710090000800f0b8000344800300900f864010b200107482c51641800f81c1c0d1561800140282c1070320052864500004102d002901500c09145c081c00b80d25002481222401e5541c18401e036680c4150b5020f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 113131996 1250 113130746 113130751
    0x150a0f050918060109030b070801060305060f09040809060c0a1401060e010f060f030209031005060f0d05060a050c0403020d0c030c1505090f0a05030d26060a06030c170a02070b0906 79
    0x140040c1d9100a441c10440b000e00540d00814180f4007181120740b213942c0c0c8980c00800340c41c8a00800d003280010405182e0500800c0e0740b011068403c2418a021840860000c1e0401341c0028501080820f04c041c0940703c040c10b4030740345841001103694101c05810001c40400182c140c44d442942000c0c408507603060303000c2146040301d120a51041c591440c000084031680980f001c2034041540820058243d40c0d8100301c0e42d0b90080b82c4a40025680c1010340811440964444600303016010007540000455404184c142c2c2c0400c070b544000c641e680d20881c1d80d109500c100d0704025400945070115070248102c1103500700c03d9038495140040c80b580c482c10304902c00000c00307241030000752007001080600c0c00e000303001e00401840a400c1e0310f601070301c800c00a428441702c6948c103400a220107401c00305440c0742c1c540b1400360440c0503400c1c0041d42803510114112041c540142c00605440e040082c0603144202c204042420142c4030529140c10444029006503001a5098403460aa0700c081441031a011508a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 113133246 1250 113131996 113131999
    0x10801060219030203070807060507080a18030e0f060c150108070311100c080414040f060302030606010c080c1207230618010603020402030a1d0c01050306010c060b150a0f0509 77
    0x1c00c589940c44002c802c4078103104110118001070140e400041e0700d55014040e4a44903250102c4c2c039203051030000b0018080140b4494055040200b810006048001001c0b0229010b150803540c10700d00c440840c5808000e500300a412050003d120006500082000861400100500c06042e40d03a040c90716640c004900002d17044211411202c070640c48c2800d10515420854142113074443e0258864405580007a441004001d80c56400c1e000c1c1c520b0b1a1043d2402c200004608108042c15074002c00c2d81d860b0001c2a447c10302485240310010b004025084d208480c8400c012240740041c250303990f2032079401107413003100c5400600f01701c8440b00c4040e00d415101428558000c0c11140d907144035607a4502010800c14800d55a00c100100140c0c50f0703400218803568114070003042204075a014800854600303d40e000d00b0323802c40d041450082c2c2e8804206da030030500034601010b100c0021708203400286030f4404212362040800103031440740b8a44c50301a0030899195111824504c981c2d2005681510441c200c45 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 113134496 1250 113133246 113133253
    0x2030403030822020a080f010605042f070f030315060503041106031503060c07021c030806040b04141015050c0303180f0303040807020f0a05030a02040504020121020c07050108010602 80
    0x2480d0050748100760303501c0c028a00c2e43d2241c0040039004901000f10f2a00520a140c20000e0441c00640c030174000c600061100703a9007008410f104030122402a19031016643c108a12a8049511022100203032f40c41280c0111000d855100300e8603001c0d00528001007680004028a5030005049010f0790a40b441030303400080080c80840352000700089540010207045050407102c03030082c0152410810366200b215030012481e07a1706140d00401c86c0300322180c0f00551113000b02c203240800003684440d02d103421440580c0c0120f148800320001a001d03290115081c9085082141004480015480c80d0000c48041d8489984440c60391074040702c884c03144402c0601c0ca82e000b040402c0c007034110750101103040d58490041d112071211200342c0714110f620035a01550b6940e00401e402c002d51903e030200341c41b4003504948034010145880e012079101c3c00043c00203442903681e40c0026066901030b02c241c0700320a454107032126000c005440b0000017500864a440028403a40e03c001c100d6502070f9007118162074158000b03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 113135746 1250 113134496 113134501
    0x30b010309020d060b01110d030f050a0903120504080904110304060e52090b04020306010804030c05070b0301080d02010f05041713080607031e0603020a090e010605030f010605030706020304030308 86
    0x1a04003a251701801c02d0704002c4151a0806400424000030540e82503035a0080342c1403114038527450540c1c0b805020300302501d04d000740381c0002039000245100c1118041304081007a40d00ca081131800390080c031404075046805c1c0845c48480c150b01c9002503104500c0360800b006105a500d20f5159a030400760505000d5815600d815107816407134400607040d1010840780b81d81e5010360301c00300b1103908041700034441c20050301d050288041003c07401402c03929142501c045095180004c00200348050281025052149501008050040902c141005020a41856640d03940e4582e13179141d946641c210b10030019444d04035410110076860180c03e010b241c2240198244d2a850403103403005601c0101c080d0076060356654001413041060020500c14080f5440028070400b0010301981c0707030b110001550040c0c0d0f02e03004062005949400018003558004500091110b002d84030085c01041710b600255810320074501000c00c460015000030b025180300350103499201c0e9641c1d105994a0185000060104544000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 113136996 1250 113135746 113135753
    0x40b0f0901023906160606030b07050f090405190507020c0123031512010c080f0106020610150e0d060e01060f060f031802090928050c040b0d1e03030b010309020d 71
    0x1d412a01180051104c1d180ca05030807000306503c908554115030f01511001c0420910108039110350b40035200b4204145410a00c41070302c8494400d4031003849c46156581e000c212001c03100b407811115400940b508011600741f080300a5030720041c562010f07001030008444e19105248100000000d18003010105045486150b00c0707222890320110000d8200c5101d00344041105403d001e0b01c070340b5022035181c0c00402d0400c508403100d1510142c00c000190740c40101885021413206589104072540081115421030081c101250021810158186d00c0b1f40c4000c0301e4410702c00c50340e00070308503050214000c00400d5502c554150210150303126140118074071840e0003401e41d001ba0048410383c100e42c444800ea8448650020741c418500382c034903418603886034440c1000c8085012540e15945000c0700801d40c05d040c2d030703a151980c5410b1f5079001401151649008800c40d152081500c030032580c0400006813030040710001444003c9078190540009040ca416900c41c0d5000b80316a021450b00545001d0861075580c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 113138246 1250 113136996 113137093
    0x40c0201020a12020702011407030c0b0c040501020a030806061314031501121416080a06050601081515040e04052505060f0c0a12020c0109080d0c0b070302040b0f090102 74
    0x1740c05034103201041c2d0100115142480c01450500c1c803d072242c82d0305036528100042d0b01e800081452036107040410007800b0aa8000640010581e4145003001003036035400041003560051b000e0030030588031001c101003046004100f00807152441a0215407003c0801b40c50310407814400e210754100e00d102c01100001203060304000e9101e03111700104075904840040c140110201180d8440402038000d1400030741040341e28091550000360903c1d000e2024140006070100c041c5012100134410550000c8071301c08010130380290b0300140011121a0342c41c2c5441e081035a200c1d14506411b01c5201f84080d40c05140c4484161000156180901000d080c90601d12183c0d402d03600480744401c481c411482030100081300318900100c04e03603042d03000d086884203c800143c6900040c0c1c1049131540c1058954241865002c3d460840d02c2d5041070114100b80c482c150290005e2066401c8003000680009191090300003410080040f64002e07821549900c5090000b1120100c8842900c0e941c001c1d05110003040c0c00085 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 113139496 1250 113138246 113138257
    0xc0c04022703300c030403060504020f03150c090d060c080702120c0a030c0302151005030705030c030a02010f090e0109090b0109051009020c12040e010f0b07050d200d0806040c0201020a1202 83
    0x802d00036113080044001a442c0d50815401210503e80f9481040218100109510702e0008280c00500604003080d68030851400700403d210900880440d140d04650b680078400040250040010480702e0040780c1c0003480c0c001c003181c085016120b03584000b0000d04140049882c1103412001401007140d09135000c81b015050450181c00b144a003111100d00003802d0050319002d1305244281c546030314506000c6c9420000264400c0d40701e0740010f003401d5190b03200450410600c0e40c3c2480c199070303180110300090f078512b1444d0b0886a96100110008640c540b143c0d802070391114000d401038680e60307036102c1ea03010030354004440080190100000030000c424464010b0205805d03c00194cd005c1843c403921510550007a038444460b0720042c2d00100505c071900709030b0602411001d143c5074601100391b1a80c1d0740c1c03903061043c8401000300542c507010900c080511f213480105460016102600e41220008002e0001510600e210b18940703241039015500500c21110850342c0c6807282c3c090100b191903048020f4029 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 113140746 1250 113139496 113139583
    0xa021f02070b1608030a05011811030c07020d0803010306050a0b0906031903020f0d0207090f02040e01151709060703111c0506040905031611040603170c0c04022703 72
    0x3c00d00c45100080480d005107108034045400002c1640c901000504c0c8045080b0120011603d441080c180004c03c4000b100c1d030103d911420a59140c103141301181c031030210724401601507038011001100300441500080d0150310f48410034040000200104001d03210151101a0703d5440341c03002400d84003850303040303c81440c02801600c2103503140c091160b05008140c45900d0041c0c0141c5000c0c00070400300d100d111943c02c840c081c218102410310b19080c3c1c0901c01809510084a05403403032100b841d2141c82d40c40c50460300c00004003c1030030401c5041c0d40d220003d5072904007080c00c1203240c00e41201c4030030230356034901e43e100e480f681e40058000307080008010140440350080e440e40c40d00400b0030300810050510100d131404040407120142013404081c1c403101d028134170030f5040030420008101c03074a43c0d2840d40c40b5280b182a64800d50055100e240c8009120820741144c00404e46070210400b084840c003459510b0f01454200000641c00c1640300da0151040400380c10000c081c1c42042000040c1d1569190352 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 113141996 1250 113140746 113140777
    0x61003150b10050703081005030a02150c0a03030b09090a02030c0d050a02030604290c04060509061c020406021905060f06010918020a030e030a020a110a0e04050a021f02070b 76
    0x4200000c564038a8450302c5090100701c00103650070030140d00c0101654440388000c03002a4007410100040d84440426901030322500c10301e0f064800041e21101102c3d1900222412140c40c3d0b40c0c00d19007d006451284000c43c0719108a00000d01c2d01c100101c1c124080650013030182c42c0079150141000082d40f800350007950a803044034018001620304000b0301e805140a0981d030b404260744500841c1c00c5517190040a0701d84440001800554203825050b5002d40300c103410040c0d2240d4642c00812024002c1d41040345005001c0b810318914003099034020010745216500b80da0725004d849150742c0d00f51151010050050b80103c0000d1480c0d008048403d030040814500610015542c04083d0981488103017020000c0f580000c003c0c00c290381510581c0c1402c4001c3c03014608100c85c50002130740311104110f0140502c440c030030f414001c507a80c1e01b9130b80c400f618500312103400d9030030542440c4e540e036100c09200720301031801c0704480070041065039001c03400e2200300d9000b0291a0b04244d0188116004040c9404000c01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 113143246 1250 113141996 113142011
    0x10608130c030506060f0a030b060103090809032407050f07080d11030c0406170f0a050a020903010f05040b010609180c02100614010e10050a0c080c06070c1406100315 73
    0x2201204075a00441c05003000f070003582800e50801c61805241b010242c406e0800c030300c08000180d29070300425845030090a00194032481800c08030391501c140c55103640d06002e0030903442c02400f1000911030302c0030804403303856569240c0340140c03100e100b0041c4caa1540402444420300061a6130000d084400e82400d0100c0c2e0b2070840d010083c403542040d1072046000310081024400b0301d61210310603402d520080600382c0c0c1c9003840b0300120001480a45284503403911400010b003420b0481e01101d00503440a0001c01060410520880c02081d094800301d542d00111000043c0840c41402900162401c1d031a06d500303003001284130384008061200d0940306602903c014105841101d1140b50018468011b24040e444a10400141415040c003034191140f040100c248001691010a441500e005400d00c1d544001c00c03400e0000715401280300c807940314861603040040e081c2d400000d4000c20791041d070090b00c40c642009159610703000110b40c151461116103400300b0210300ba0035854120701409540010301d45 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 113144496 1250 113143246 113143253
    0xa050402040b040e06030d0503070e0409080a02030a09090510061b0f0b0411090405060610110708070806010909030203090609131118010e0f0d0201090801050709030606090b0901060813 81
    0xa0300942d00181458101040420502e50040d40c45030b4000c0080b0040c21a11509910191240c0409042001000034900e004d200689403588202c80a5801400e01910b611248100a549030302542540c00001e440d000001420001402494080c00030b024209844a0421408582e2440c400a030903012401021401020410f001011029640284c2c40c40140e840c00b402c108200151410301c40c2e00824000c4200404a280440c0c0203800540480d01c5801c20003411104440c0550180401c2005001e0000c0000380f0100000d800b40c22191860709850b4180e903122100b004032a100040900580c00c10002802c2520303002d401442c2d01c95006149241120501103544c04031132444844098403100010000e00314104d01f00c6c105400c020074a070480d01c0390355107008101101450000e82d4002c180f0003040c0c4046a0240080ca400f81c0032483c0204580d2034100703001402041c080c0700039034450b40f40140110302140280a074111106020f0041c005991078000c0880c1c1c614402020006129081301c20392001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 113145746 1250 113144496 113144501
    0x120403030306032015030703090b0a05010906050102191211030a030608160317031b180a090c0f121e02070c0e0928140a0b090303010609090b0a0504 65
    0x145000303a80000310141503203488001c0891120204245000002c2c0143c02d0396a400700d10001c4a05c240080c64803030f154074600f074000e00f6007103074001d00006030702007004071440f00c560003107040f40e0f1050824000640e603400160b03250304417100e00c3c3c001403105c0043d180104810150313040d111648c0d40780c100040d00c51000e00c14155085410404006a103813a0200000301c0100f269200c10782444800790315840ca03680d21f0041c808508026840401004000916045920440c54041000820800307075540c450700c003c10012120700d0f101034412001c010020030308240522a04035a0740c15916001c92018407400140c41c105582070f07542c1d1450f41c998402070b42d250003251a00a007041d6010000d6111070745450700010604c1c06030011442c5c40e60400810180101c00a01c401c0b400d8175140a0540403852405503282c880031080d8003a01004a0340080d6448100c00609200400d018200401c0c00e074881d0034a1a0f1240700a205420000b60902d10a1105007500e500800343c03132030018840e4020071750305c0012606 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 113146996 1250 113145746 113145749
    0x5130b0f130e010c110c01030f0b04060e0103060507030b1e1504090b0103061d0c07060e12030703050603060f160201021902010207050f0321040503070c03110a0603060e0403030507021204 82
    0x1c5036100d88945840c4a070900038402120303494100b480300000300040140d075654045100034101031326081d4004480344154080c1c4100400a401444855281c0c20024007001080c402194070390302d40800504614032034452440f1031a4000d15550000c508145070660009142d60000e0707200e540f101d2203001001180004000504a50501140507007050001404031586607101d02c41d10400001c01c8101c41c45030f245a00e5010800440d444d4984d009400c00c81c00410312000c203a800344c49220514211500740f400a14480c2001e0f640601080c0e545a0500d034503998192440c030300c12110f9038045014841f818040507108d2206200040c1090f1011400c0e0110f51540e00c2c4c6000940d40c0001c8110510500307000d0480544120310040d841e01100d060780c90039015008800c484002e500790040340030003006004440e15941c1040f02c03150807546034100881050000858944203104003400001d4450182c0240812900c0e910003002c410b680e607844c198090100240001e045002d1440102c3d0f000c0711a9000e0720 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 113148246 1250 113146996 113147029
    0xc090612042105030c0a03020310031403090a05040e0c09070c080310050a0f0e06060304020406090c0206010e1e01120c0302090103030503010602100605031c140a1206050a05130b0f 79
    0x140450601802d0200100c40350180504000c0c0400070084005400da007110011009880c3c0180d40c2e0355141e5610285a40d0364000a08850f0100c0d0401154040040949203c0c003044035642c040369507400400c001c0f544202482c0405070082c0f03200b801c0f941340449403940d20460301c0c00c00100d80c0b40b05540b00300c141c3c1d02c01c84210390f412801301340a000314140304103640007030901c20500900041c01c00c0502d12420000901840c0305d504000001400c644881c1c0148000300140e1109025402e103500c0e011303498003403d0048a044261034000034103081100c118000381c0c01d00c0c40088514903420108000d500740502c1c24155400c007581040000140c03078600400340214000d69030a904c80d41000070003801c00700802e601c0003650f828074200303124580c0c02250500d45101c440e501040203008002c0c050b100d003090320400a24500002c54100321140c0c1000f2650a610031155080218589a108001540206015454200c042980b04c01000e203c107030b101c0e0f4a00c3c40300400d4844e20b0403098001907102ea81284205 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 113149496 1250 113148246 113148263
    0xa03050a050c0301020c03160809090f1501021207110402040f030b090f0105010f050f010908030a05090f030703030903020105030a020705030a0f0813080306061b120705060708010308030c09061204 86
    0x14000e2000a111080300c070b50342140203603c0c01d03464210050f52030181c1c074003418900c021800c4540c200843c84c1c0031600b040c1c1c0c014002c0c2500b0718080c0d03a50058035504450034008a580100050103a43c40820078100c903601c2103020340d00740b54640c0c40302c50f0394210b00304505802c680e0070800443d0403038196100500071441a48041184d2800381c0c0c0d40d50130241080028600c0740e0410005001c0d4040d603d002a00b503030410b0b1040c005640820780100c80068440c0d11964032408006009c1034a940d124008201000c6d054a40018040b181c2c03040c540e54501c80c0c480a000101e2120080c001984200000e541101c81d4240c00350606800c0d0b2595030a41c0d00c143d007150007040b00296407100081d0481085a03001c201c12240410400148d140c44401c3c0c880208403a1081500240401c41189245c980620600100d4101c4443d4004000d2182c1c4c1035100c0c90003500d00d0304c100c60000705000e110b00c0100381640e510901c00c1c0d042d5203483c8941703030340f6400140700d569002d40d05000c1d6084a20a48000921850042504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 113150746 1250 113149496 113149513
    0x6040b0a0207091116060f0501080c011b0b0604020c07091e05090312071b050f070303090b0c0c0409082b060504020a02030304021c0215030a06090203040f0303090507050a0305 77
    0x1a10700001c5038840c3c100103040000c040f488100d203c003510f6081008200c40034656800b85402c10007060401440440301d440c1c2030001c1010400000c0c40110221b003078941140d0540d203016922a5503c04032402483d05641d280000c41d41c0c00d05030040c2c9040c5140d0400c0322005070311010a202612b5800c510a644100088a4461f00d0b25039402050b801400e40e8015524080300030700480c0903854024805824044005030007000d100c0d8011140310800d810405594250010780707400d94840c60988026070014061070008280444c0580c00c40d94280052002400c00003c1da01c1403001030226160161010102400161070380020000c06521041542d040d030807a200070f0500a608449054120038001c92043c0b211401c0f0507000001c50380c21940403101e4840c001094038600403606050303100290041c1448081086600350711002e0350007950765500a00c03e1301d4541200908a00003254068442954005c140740400d002e40c1c05840752074000c4040c2c8103450348900c007042c03219000740e10884155215404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 113151996 1250 113150746 113150767
    0x20c060c030c120406020d08040c080703030507020f030c0109031401020706021b1209010905010509120a030f0f030506010903060905070e070c0506010e070507021504050d030302040608070f0206071d06040b 90
    0x260f410f10114010641e040c581401c01c025a60700707481d140d041c18440c40d90f02003010310420050b0040100b100c4800c8488103603c81c50000c1c125004a08103d010302002042000e2034030700031810307020072201a0342e02407980f8503640329040481e05140105502d55400c11800c80442c2c0540003c00c40d000b03d000f010700d40302004e14521072801e0048240c80c8641d4006200c004020307079008904c01c044a03000d1030a207850380a0b0400007080c65241d111910701c9845000401c50405400170f0b01380f62405c405031a60300c0b0362280a141070342500c904482240c0000d101c8001400090407070b03400b4202d454015001c590a20f6110810360840503004c1c0c0741600811800466074007040010010b82d03001d801e5035036a0618600349500060021f01486100034850a50144405074400355442a94002d11005003003413014030143c03c001c3c00075072140c00786000042d46440040c4240e40219400402414181d006103860740c0c1e00901210020500411005160f000b905480940c0e6190000b5001920710000030550710301c031604 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 113153246 1250 113151996 113152003
    0x4050709060f020703050c010f02120327160b030a0212090606041a030a0305090303130303090302040b0301020715240f150c050712020d0803090604150212060d0201020c060c030c 78
    0x340d4104644c03180c0000e2000401c080f41510740d202003828811858402200181e06090901c81189070000c000700c20064015420a406502109a07441814075424481c4c22152100701000500792480201c2c081008821103500045500220400d401824464601d1400590070320640d80c80c0001da010400348105440c1c94444e4900f1007080201c080b4011a01501094840b40f1540d0042c0510001103010241c80d242403045442a104130b030543c5010729200d00d000b51940c40140426801180b4260507032400d410148229058290040e00f00101e10000f259000060441030200e42c10415074241000e850880c40c1a078940170f009928061180213003800c2c500907542881c49100c000b005401a680c002190f40881c1e5507055840300c0c201191050f0f000d0002c40d000c0304043c00014420768001007001500000421502d0041c0d103d11400c4c0c40c60010f141415059014a04207030030b202e035140c404280d45d4034200c05010101c40c81030041d2405190440f0001c0d0f441d0b0049240307a101c1d50400a8400c044540c2030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 113154496 1250 113153246 113153267
    0x30723030901021903020114010602010207110a120b040809060c030910030c0f03200a0f02070605091809010b0411120c03010b0f180604090204080c0d080a120b0405070906 75
    0x541c2080c08801c0000d6981015100c0085103909407020f00007030610079080090281c3d004c09a50807070f940e451400900035806484240d812070441c4041c1034451901078849012664540e004880c2d110342900e5030642e07010081c0045542e4103041081e001d60352211006071900d040218007854170b4003214018004101d001e4041d0100301880c180c56441c04540020544140007290310300090100c40428648003004040c180d401e4a210000c02c0a9030700316486020580c032010355500380c809407580c5807810741702405444921684003030450406c0d01100c03401f40700d066018030150008200341070000e003c5070850749000750458008400155480380480c40c048000d410012034102c1c50324540c50415058041c0c000c141030f10f40007039000a1201800c007580350100e28001c1000301310300d517903507030315040c28000358401d1140c550b1601a01d0748009003864030001108815801000e580d140c040d40c400c0c200ca80600c030280440245e07a071060613100c9a219446803a1040d0403e80701e0126003410b01c1000b6000c080f08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 113155746 1250 113154496 113154563
    0x90109050d030804350a11070f090b031c032405060703030509160f06030e070b070212100603080403020f040b130b0f04090c091803080f0a09050307 65
    0x145156600007584083d5459002c0c0c3c0101d800d080341e440212909415180c001c02440704403841c10507049003030300701c000105030701415038580c00f80c2076001d0354945072035060307a216900e002040504104854082d07500914038189006082c3c0c0c2c200d400c603d03400d10f03044480020000029948204010300c10442004046010000300d0504081500e800c2c0003c0b002c0c820702800500705a1243c000c144014410400c229800908005050a0a8685108808910403482150002418164868030100c40070459105442c0b0340e800182c98400340780c007030200d10202601d010748544580da0550400344803610650018501c1142a10350355131460042001443c0d40d80c84841c0f00710b01d819a00b51080e95079400b005048801058085155100700c07000031140340020b080150403a040610481c100b0610b542c1c0c40f0190745495808000041010224110795a920040240450941008151a03000204c0c105510010044000c00e501e02d056540b04e003903030016001181c01c0e0001d5000340300542440d80848059900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 113156996 1250 113155746 113155759
    0x90109060c08101806180b040b2e0513120201120212181207030c17070308010605031306020703050a090b0306060403030e042a02070b07030e01050c100e0309010905 72
    0x284241c0e081e441c0b0103c1d12440303446180040d51440e0400881e00110001c2041c0c01c0314083e202c0f40d820090f0003400003c07801e41d22a500d1302d50f0202d09803030030f56101c107041d00d0f141d28494503480068100e1003d44001c42e00c204203108081c0451410101c111010304083c2040704d5140c10301d40c40070f00c00500004c407104c500100d41070040c0304070489281d468110550114845000d4032582c003810b1141806e104403030600240c004000103111040c5a04850744100300740c07203441c40c100b64180024602085025030240100020800001003000611460182d90000040200321042c04c101e40d503010200d034010384040b00481c00210781c4c030741529008201e00c03000700392551f103007490342c60003200146845c4518000142848107a0180c0351164946609c0111140b0401d90b860440d0303038240151440103208154110f005214465022039103403190230035681c80303030b07070640b03030f612000d20808015551500b000c00070000c1807041d40c5640c004d80310b481c0142e1844072501c0c400303107a4900b0a84001007142c911034011034084c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 113158246 1250 113156996 113157001
    0x509150a06140105180604091e0204060e01050c0705030a030f11010605061914030a05060a140105030f041b03080309010f061a0304080706050a02180d11060c070b03090109060c08 78
    0x307001a0ba508031001007464000d5a4a03078961080c00110f20520704540c00800201e00030864140c0d5074041001c2c42e060b40c100c142e613051601074080580c8a05d010390000100c0300d20f03881402c2d5000b44c000c0c00b100c251040941307803c20b80340d0b0b0100749021400201034000802c15840c18880c00d40104034410050561002440f4680c2080d0100b00c8034460030400308042c220740452008014070074a4808010113070030707500070343e241403881030032000d060250f4040384144802d0000080036a4840030710030207110b06131101400e60780d07101c1808c85801e1000b03000355100358a1030592501180c1105090014503c01d02c61640c41c0d0424134001030854205032222611f062500d0424002c00c4a20911043c8008082450795540c0d5920701c1d200040f409400c0d0021304030360800f000c0c4005080d803a000781505140040041100341091810404809004880604203820304d00c81c2c2251810000014500e5650b00c0040785c032130a546010406442d4400c0f9002e1400780d41d60828942040414011340700300615600d003400c40d50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 113159496 1250 113158246 113158259
    0xf04080a05010f180309150302121905010e01180902130207030c03022104140a21030f03050f0f0c090a0e040c12051203070201090602071208181005090106030203010509150a06 77
    0x30406004011880ca1701c401f000100d00c0c881c0e0116142086407484500b80b50602805410304000034203444515141400c0002c150701206503582c2c0e04071041051980780c43c0d100c110703a20008021371841607030031442004118241000314001483d0852190343c50910301011418002d0409014641c41a1a400390418002584007140c042d2400e4864580503182d091080400203000120a580401001005040b8440b09824006141071403540030b501c80c407541c0b00c106071084040310303001c40f05000c00d048510302280405000d180740a501400d2004104d20302403544001841e4000103910038000300b801e1200b0801007243c10484c04005002e001402c051018180d80c0309912103002d6400c41503503041c04400601c0840c0300b500f1403441daa4101008650300c80c5c807418449078802108024201003404a00407604050f00380911106c074461b0b030400341c050204840790009c040c14020b40641c0c1750f9900c841e80400980e07000e10900d4042c500d000010800f0214880c2608034412004148000c002d00d00325041051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 113160746 1250 113159496 113159507
    0x90102090d080918010609080105100609060c0c0315020c010b03060c031b040302040c0f02010c020c1309060b03031303020918060403050d020706050c0c010e0a02060d020f04080a05010f1803 83
    0x581d50b22100c010703110152a004500703d001c2c0070203240002400c0c8400010707801d400c0401c240544800b030303000b88500d45e10355031501c0c2003204602c521400030b0300415040000b41c0c41070300a121030038810545015410394a49480f2901c1c03a00c1d0005100d180e50000390074000030024840e0b410202002d50180001e0b1600c2000034155000003418120405080141c4110b106492000c66000d940d000b04104800c080f0390030014140750780c0c41a100c01561a105140b55940c2c000684081e010f8801000300300210010810000908040d9008490698403071840301d889aa050028180c88400708104401c091b29600410a600300003070500c800212800c26000942d5001240c803503401a0141444c543d0303520300c01c20317001c0240f040b410050304141c5040300b8442d0300200705005240c050710900081c010390b1031095119440741c40112000794400c104000603030300105a80c01402ca4801c0303042c40142010b585081c628100450404200c1e0143d40d590f001c026082030038490350850308030704441401414002d5034058103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 113161996 1250 113160746 113160769
    0x6020c06030f0603030c0607020c041a0916031d010b011b0506040b0403140703020a12031118060c3c060f0903220305153d030b04020909010209 63
    0x96030320002c0700103a040d4408000302c0d01c000124500719402c40c035001c40002d4541694144240c0310b5800c011078070341000400003001c15020401048030f43c0301c2d140c012028403446a24075050f400e06440300c2e010140b80380000c0e11001d00c0c080d41070002c555001c00c6e40004002e0980795102c590321506800d07010300810400501241c1c0940d002840c46025121410281e1721030ba4010090b41d0400f400003842d90030194081600020f6a110b0311005900600c0e035070082d401d03600c1000396211712000034003501074182c0e0307055543319400c80061315040c80d1040c1c0d10115070504200ca0f4020380e14449140141c80d107080e20000a01d002e00e001021440115003241c501612010b0103006044200749000c00f085641405004072110041001c01c1c00ca100040c0e0f403032a0141071142d22041d14a030082039041501c5103003410b4a64403c151100991200400a103000500000740c10461861007840750307610090307501e00340c4480d00914000c4940d10380a24062041003000740d402001c5080990040c8000f03006a1140c10003202e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 113163246 1250 113161996 113162011
    0x110406050a0504050604080c18090c0f2107080c03160603020a0306050406140111030304030206270105010f140103060807140f040501060e0a0614040504390906020c0603 74
    0xc1e51814032420448150041c0e4100580c03000300054001280100040d40b01e07000401a140405034440315036001d4504038003110700c0c0f11141c00000c0380072410700e088142c0c1c10350148000e11707903600007060f03c20382c21001202c0c0d00803011030b6201305410301406000b08200391343e20b1011001401c4520360f02a002031900002d1040c14149500800c0104e00d031030280d000900540300c040d00400a580c1d40d505031035040d0390800705c441d010401e580d482c90007122000c011039100d1074060300100503603114006101520110b8201d190884044410454000b45003030003501e00900c00052480407880c1044180d4551108880d25a8140b52401c18104022440807c145c800c580840c0c90300c007403400c22040800c02c1813407001c1d030f1240e101c1c0c0f0b080004207055800bc48503868a00040e41c0041c80d507501d5072000e5401c011040303002e08268409000410007850190001c010000e0612012007424403600b408110030400c4040d80407a1517456038801001e9640600e116000704480e100410458500c0070200303035117100181000c1c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 113164496 1250 113163246 113163257
    0x30301150e2101051605070b0103030c170c0a120302120610090b03040602030f010f030507050607150e0a020301051f03080a020a05030d050a0b011e030b010e0607060f050a110406 78
    0x10300507a50b01100600280c0740340b0810300400c00400645008140072a101c20090000251990445100740e00340c2d0130150340b19001c0002642517440c151074882c03600008480d603111800280d00460106e901414101c94400000c02480c0001c3c900388502a11469601d0101031052108600c04149424180c4d04500d05a4440c01d40c543d001c0412111030a22750003160010740000f0500007081641e50046105240d000c5080711f490340c0b01c10305200c100310f40d84000741103a0311901090207140b03000c000a00c211446042e4500c5000340003030148c0195035000c40b04e21402c0c0c00c880200001d5007000e001d60f9501c1802501d080040c0b4140c2c81080c440880d541c0806440c144012504000d0540200160ba0003240c0100072252240780140c00400078040440e0541c3d59a810304080300c5080d4040d220b4102c0301240d02078400220810700714201c000301481810281001200503640713002d611031800a000341402410045540000c050f503c0d001e80d01e0113055a00034034500035640e0350441030401914166042031404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 113165746 1250 113164496 113164517
    0x30f0207031d060d11040e0a1e2d024305150f01181107080c0705040614010201051008030f0706060f1205010b0316150207090c08011703030115 63
    0x490001d001c0c503901c1482c060320f01540600480045d0010f881101c040c01001081565840c8017101030750747c1030100100c0701e580039101592494003a0029212190760b00c6002c0300b0800b070300119040208034590705170701c51507000818640a003165000312160311086005e00d4940e0207114000381c902c14180c16060460300880c40d1a0041001c18042621408501c110142c070a043c41ca1680000c1c510a1241d1000400710846038510100a4020051010001c424007030402d02c1c0342d121002c1c258040180030595024000001c03807503995034811000600140086100074070151800a42115405041941d44030110b070f42c2041352900000881d4009050300311a20740f10307100791400d18003804168001c0102401c146401182842001c10000c0e0498000c3c002844410041000c2c19101e1040b03c0d41c01440e841030034420300444070840986100c10705c003032040798611941e405201c4211001c103801e400002e03c0840c0100141611010106100681e540c007031451949454240c0782800c0d072440000b8284900d5824 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 113166996 1250 113165746 113165749
    0x18030306010f050c03180307080105071407060b040e030301060306080304050a03030e010c0b0f040611120a02090d020315041406071d0f0d050f12091c0204060302150a030f0207031d 79
    0x503601c91307040c001c040341c0c1ca03030280300c0b0070001500d81005428000d100b20000010340c1d4405006080c0200d419454401d5000c40043c8610384550041605646a1391038010101c4c40d61114410721000700f030740300061526541044001000d94481c1d81c03011102e54070a000c28011070b0b03036448612007141d9041c1008040094070b500140c80c8040200c20141c01007a000080000001c2d02014a0784240c0c403880081020300e01c954140201e40c080c02c41d0441c0307010440d0380050750f030f040fa50b0300800312210300400001c0b03208020360002c0d180160080509525039032241c144410050210b0160090303040c2c0402810180c604520010501000f109400301c0011004101ea01203844109411006104c080d1422840640c541001551280c40c41071102da144280c07094215440d0080b0f0a696a1410041a04007030b094812134905e0410039821003a6405983c5950000050b41d5100c41d9030755101d1481055900c1c0c1c0d82061025045844010551000340d00410900e00041d0388482811010000c0ca00d000c0503c200c00d10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 113168246 1250 113166996 113167007
    0x1d01140703110303010303080118020c0d2010020405040c030501080a030c0c0b0408060f060103060602070e0a0b0303071406070305130f0314031801060807051008090316110918030306010f 82
    0xb1950740e09404000004400e0590041055040c0d07098003004804080c1a10700150807407040d5085031845400036200c64900300e101d01c256401e800c9000c6c08220194005110550801504404500b090755002504204905040c000d1006440d51030500700308a614142c1c0254841e19418001005c10600c0701007642041000c4030080c0c00740c003c4090554946407207070f551956480040e40e2084020f180f4400007456503210340101d43c19240c86a02034044e0310302c2c3c0307090003079a4000074228102194684580001546040001d0003000e400343d40e10304840c6007104083d9003000d00c0038119004042c02c010802c600103140c03c0383c03103150750740c0034140d002884c00a08045608203e1100c0c0b0194500f00007050005102c400c000c00810ad2404a0080022540c2e03070302c625550326075a00c141e13600807200c400703030100c2107018009035a400705002090300d00e05600d5a644280200000b14121482d0303030081035040c19801d00c0f90b00d40d58461501185048118800c0c02c0e80360766400020303d10381c1001100603280e13925070301c602c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 113169496 1250 113168246 113168267
    0x60a15081b030406050105120a02220e12032401050a1b0c090509010605091b0306030a05060f0a0501060201090302070308090a0509160f0c03080a0506010e060c06071d01140703 77
    0x110001c0e469080510301103002d083e0a104180c8107002e00041050116030200e11046216401040181190b5007100400784800c14000810661396480d0750781100d582041c456500e5190780980450380d2407800c802c181c5546880c4802404901c2149a150310840c0d0b040342c21544c1c2800c03942804940ca0f0101d0340d105000c14145a8010704031000c1e40b00020300d10304031b50000c900440c40d40d0000c1c41025140c606208000f0b10440c0e507141150310000f56001c001d0180c4005540141015040d01c031203003826280c441c9400000e949208541c0144401c1142c1845c1074402d50f405003c00b0b10081c441100c164030025540c0030103000107842c440c1d00040b011a1607844002c2e400c0207203005000d950b100c4c60501200c04901d080c500d00840490811003001d000c49d4880d40b004030340e855154031303a03000503250019020021700c0c004040c0c40c1440600f03d290f00b0260382d004090b0246541503030040c9010701e080b80c40100300002c204203511601d03092020340c1c2c003182c2e00520003100e0100c458888544400550408036034202c1c10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 113170746 1250 113169496 113169541
    0x80f0610030305280e0102010f020901020c0603090304080a1b05040c12050907051302090405011514030402060702090a0911030303010513020c2104030314250317070201090209060a1508 81
    0xc0d60000780c040c031740129201c086408243c008014420080c040401070703120345020640140c02ca407555034900d140c0305029541115103c0e040b81e05154841a90703070300d8880780c0c01302603481ea510940c00c400e400384020780c0e49002c1d11003a2818400dc0701800320241c0b5842d4107003095581591a1000990510704c204420341c02460000c0c4413220500114070031000a60001c0d02150156003008004211103800c8030031049243c8c4a552810810388524001000f07070340014104903403080e4200207510250b550084501d0149402190008906e60740e8900300728102481503000d4040d030803c1c00100b15070342d82c469440e00000f00078a0003594910714481c409080c030716201b0310010f084003a440e101c20001668030107801501e209465002c9182c0080b01010b5150103440200700600d12502000030040307c0318144046998468140f018000d060b0f1042910707220011141e82c00140e40d07910050341545081c0c411107030131410035124040e140d03080002200b4a00b07a80c2600c0010300c40110040760307000c906054568a203050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 113171996 1250 113170746 113170807
    0x5030a0b0d17070213060b091017270105010806161407050105070f0810051c1a100905040206120907030609050d11160311040f09050106080f0610030305 67
    0x30000d0402c0c0c5400c032a0040e401407085003108401c1100d60b108500aa8001d00c401300d081480710f6040121000d0f80b10045403c020042204a465080008a003401411058906492240c6034691202a01024044034000e030f0b0410300100f02c2e610000ca002908001c00c8854081030707615001050b24810641c040420783c007440000c505040c414190b12681c014031255a0701e640c0003a000e14111004441651818039042e80c2c44020001480d00030412012144903644d44542e9482d6521140401c0e03500318514010440120200188102d9095401d406040500c0b01049103003031030f17001700300c40340509072080c0180002e01d800304890007002c0203c01c00459112000703200c208450700d81251541c1e41c503010b50010581088030070704000008201085418035002d00c0000007841d40e21403841d505a560241a0030a0b52140c500b4500c04103170282e0003110b4091000400d5440c94451002e2401c04a1301d8505081e800100c10300c800e004059403801d04880d01403400da500c500780b504011203201d070f05e00000f201024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 113173246 1250 113171996 113172023
    0x307051302030423031204171908010609120b0a060806130b01172d151506040305060a0905030f0309010c020d020313170c0301050106051e090105030a0b0d 68
    0x38040d8000310711a0b44140360022010350150300104102c41090541c1034280c01c2803013000c2c03071034408404182e4001e0003013005588100321070806100d180d00584a007249a02c0e41c01c0605015a0410300305401032441d4980042907a08d0321103000c040300040c0000a03c41340c0300c0030102c0c4d00c6405a0f0400d07000790100500340c42e07003030910315008480c1181104003100c003035401100003d120b400441081400c0c2d0b9a502c0580484001001c00181d00d0108016866441701c520080e441c49240401c1400c112035000805140141000c140702c142d43e0030f00c0d031143d03071041d10100001c5c0000391010845503001403105101040c0001949081400c40c066142000421417012080014182c8150407081000d14541c0079500c071070003041400ca86901c85c2003540d0000716040c00080001010b41c000364421304a4001c01d58020081290020f820740c0ca081c3e018034009280032032003000c84c483e0301950403144c0d60303d140d0040c90480f50b180041c1007400014284003400ba513903042421641c03102e00110307030700944c0101040c9249 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 113174496 1250 113173246 113173279
    0xc02040e070f0915051305040c170f07080c0f09070e06030a0209120105060f120313030503121f0302010309080c01060605041406040e040807030c0c080106061115010501030b030705 79
    0xc8503602c03a4045150030b1804c0c8407401d0004820740c100350384c0701030030140d01103810305407044c003504000e40201d40c03a40c500320300014000c015a041127038041e0800c014180b0b441c654030030103281402d59084083c89800c0340d02e114600e40d503401070390300351401d00741d810b00004da5601c0d070b00381ca805078030364041500044004104000100c5580c021b0094540c22220340901c64030700503200f402c8490484556410201c4000d000400b40340840d043c000110414080b2031901000e8550f4019107405544122501c1d400032861106e00a80c02c0e0f000b980c40964801e090341165848151a42c06400354440079050565a40443e41030100010449070008a2403009200035a0f85510040c242c1d40584281014a10249507140c1c0360302d0102c1c2100c080368640d40114050303803140d843d0103285601081c002c07000d208a0400c043c0010340d0b6145140c004003184400094014945a80034144495000c4005ca450b041280030840b0044c0140500d419a0390030300e00060302560003030209160418030740205a0149601c200101503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 113175746 1250 113174496 113174519
    0x3260703020a030f0503071d04060503010e0105090f06070f03021b1b01121404060b0f090901090c0902070b150102070504060b0d060504050f01060c0606120f120513060c02040e07 78
    0x105407080d030300c0a0300c1134110f0400b245c031800251a500006803900c009500c0200660552852400c4000c2c400144141d49030006030031100030181c0e014099445408124641a0500c042c080510300c04025203840c0c68050b100070074844050240009142c3e000c104050f200d8040481e07550000c1c007030300c1160b00c180050006107c2e48a164a00140003d068680c0f9529a481502501c0e4400401f034140f40508c0e112540d0b004007400c4a845480d13040f03600e62000040036500d048a4502640c6458000140b0b00c6582c1860944164103401c80d2400d503004001080024880018941d0b00020010040100307280010040741021042d6018a034000d040200100b0420005002003c10005c001c00400510390340d0710500060341e030704546207509203405000400444d4010748049000a00c91400014256198000c030540c1030400802510625458840d107002c0007690501600d10100c5804d1181c24078003440100c0c02c06400c140152350401c20403841c3d45085440c4c5420544c00105110b094a4900d503c4000c100784 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 113176996 1250 113175746 113175763
    0x7030206090d050412140a020913060c0806010c020f0307030b1501110c0904030f05040b0a0c110d170901050c010c03050603071502030f03061f052703070326070302 72
    0x1400d0140b1541c03407041c1402103088074211140c0c158000c21100181d11071040c2d405218036594041d009042d919801640c030420145e110394400c0003d05078440e1282003142c1211640b203013103020700a014062001c542c0e085244040c010354110398881e054180d880c0442e041c80312542c00200080c4061050098032003000108211600e000c2e615800f4511181c400190354225901080d40c0240041012402180c881c9800c00355040320b40c101a480c10381d480e0540e5825500078203020000488406038041004000901c50414036000c0b511200113400640b03800306103d4244451488040c40003400d101c8a0740180c0580300450074800003001074401e5400003601030300d012030b5245d10900a501c40070409134030b9200b0850800a042c1c2c0194180580310b0040c0b800c5a1014180355030211522400c05061048403080b076011841d00d640c0c00792904207401c404043c0503012a9a542442854502e58803251400680c100c101d039000311a115908103a000c40c441002540c0850b254400c000041540c24150000303160301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 113178246 1250 113176996 113177011
    0x3080a09020105090d2303191407050d09050f041401060509040b12210a02030307080601050706090c0608010803070807060906140405030403031403150d050102190801030501060f03020108042607030206 88
    0x2c50090a0000d007071f107030302c01d01c940030064015007503055228a01c41e4002d03100070b44000d0307290b61408440351246460a00d500c0013070800688000e00c00c2c0702c0c03420314141c241c0420304195010301c040d0b02400c26404038007a050043c0002c0042c08240d481e00c5507210740101101e0308000e40712000da9400c0c540310680310000305445181d0004030714910244083e0000c01c40350b0000c01035020b1425901c0380e00702180c54003000350030740c0c0c100036041c011800410194843c1e4030b200303449510841681e6192600180103050142d010040540040c040c0c6404907400030300300c540040c0d00c81c4001032aa42145071400040080704480540ca403262010807040120000c0200142c900031f03140c45080c403030364506480c154441100c1c0c500550041d10409802400c00000b1000380c00d202d0400503041c010701590040420511451082c001038140c0010002c2c071100307125000242c80015800881d80b810f640003c0c00c1c2c1e240c040c0000741103c0c0300c8544003030030480d0880100c0312240c81444940c0e4504450800a64640381684e800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 113179496 1250 113178246 113178293
    0x503010c05070302061f0504050f09070501051e0304081605030304030e0d020a1509090c18050303030c12100905270d120c05120c0a180303080a09020105090d 69
    0x2031081501403400d4414650b410b44c01042680e40300d0103010302c0c5009a240e413014440c1c1005010800c1d54070390043c42c0c803800c00c41b6a504070381d241c00018a454401e01c3d0307100701c0c107001c403c109020400d54240c0c000b50368090100100ca80d04c1d12035140c01d00d21881115a00002180c00c1c03405241008808001940030b1802507440c0b134803d01140003040341b205c030303103200003544803141e81c00070400c140000d07108141820050400a80203a52060040d00fa5211088110009a9002d0002c84152035060f8604050320080c1c0080d41985814080784031648542030b42c085441e030f90500010f003001c154818800c05814031010602060030841503032410407180c3d10020a446c0d02884134521072440004004a00d006a43d4400b0004103040c9070100003410f4484803501000020000080490305030810f43c0d00030700d01c403110030380da13500b8031400202004000c0000c0d00d0300460354102040807030b52218030682c2007400304c1e0700000c11143ca440141c401e0300c19426403d4000822404c1c0109100d00c03460088040604003122 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 113180746 1250 113179496 113179511
    0xa060305010515181527100302040807170f07080109110904050c010e061b060103060c09080c04020a030e01050a091b0815060d1407080c090606070b04030302041d01050301 75
    0x401025026500b005224035800030b4185009213000c84074000703040826100b061900f4181d03986c020300e0205055880600d40043c1e120304d2190300380f009840c07880c038a80345000c60501d414400c610b9105c03092882031149035503074030701c05045508061143c540501d2989046601c0c0d19074410b1041d010b81109141590802c5480c0303182240c41c14400c23400351059078003001914040408000541d1f0b459460102142c11080c01d100c0824160702c0500312041c43c0d032400e001045a0740c998078182c01a10051000c1d01c3c01c12a40030b0b000c1003100b500040240d01413030100c9001d41c513034404d16000c600600315140190798543c00d0105020020340241c2c402400c0324001d60f6202c0ca5649000030303141c0c24070403604c11081c1c540d20241d00e10340d541c0c1c024401e050b08803000500c5d200b000c0313201c0e0304c8888040e00c8113000d095094001243c2045200410001404203960581e9415054545040081c4ca00d01030880301174001c080d644002404c243c0f20342d04903030250201e408400f54250802032000640b0109000b5540030350700c1c2512 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 113181996 1250 113180746 113180779
    0x8060f01080c01090b0a030f0b130b030f0c030a12171302040e19080d02090909060a0b010315030213060504060603060503010524060c03040b0a03021206090403020601060f0203090a0603050105 84
    0x21300e5010b50300c003683d800b403414403408001c500410b41c001541a0050762240480c05035903450300c0180c4103042c100000700d5151112001c150424107a030300030f150076500c0300481c5981c0351400720b03100c00001d80041000822504d403440503245400f604100605000e8030000b004651501789081c0072101e4002d0705c0800a0603412600260b44810400c0101e031342009401220000500540007894111f20300503000d03081048980210b03510050a558903940c640010042108548680c49003c4e00e1a809290a201420440f03034208080300300e50001034004e8108003158a40c007501900901f0040030044d0040194940e02c8000500a081c2e40c050341d8032950070076000c0385458482469207004140942c0001c2000381c114010821240d03c545402d40307542c0401c0c400040c4e003880e50000360401d0034841e10003607920440b640c101445504000c00d1144190803070014000031a40c0092040d05603046070038580c41140d0f200609918600541c80c0351548070041c0700e008138405505800c140c0c122002500c20b024010913050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 113183246 1250 113181996 113182007
    0xd0609230702030f180d03090501080c19050711090705130e061c0311030a030b0406061134080f0105060307060f03050c041d0601080a0c09030204090c08060f01080c01 73
    0x200c001006a00c1400010307802d940380c00081010050700704a140c0007044c210007194840c21b0104069002c241500c4c003c00c45560040300440d8010f40e079954061a184120140040004540014904000c0c010611004001000e80d4102c135002008142e080715151003030005015502105c0b15840ca80030313042e0002031480140c402540140002404819940b0b85a0b0185070a4451008190100032940d00c414400039800e0000701700054481d6404140140600300b44415115558050020400070316071000d6100c5021a0960081c1c4c459002c0407403031241d240040501603800d084071111681d41413000a10381400207500c80740381f0000130080c8210307611780b002c140d2207a645114003004101e1112007485600c0c46507200961104802d0020760420340c50382e208113070743e03190342046d001c00c01d20744810302900b580c0250307559600c402020024064141c0400b00141144014840280910f0700e40031030404021b0224040805070130b1000484080c0e1174203140f030344d040250a100d104a24010200c0f104140c1d407290 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 113184496 1250 113183246 113183251
    0x90e010504140d0e0f03120d0608070b0304030f0305060303040f061110140f07120c0e03011b0507290408130602030702091611030c03041e1d0406020d060923 69
    0xa8484c5140e0070380380014403116080d40d4007419403501a110010f0780003d000400740c2440302c0f00f0503001400c541091085880c0a01a03005000114028010403000035031180108a800d00305103408a8540c45000100340b5600840d0001046140d404a0105042c0e5211000c0d103001034001d012a015504561116421101c0d85da10b8000c02e008a40b000031915a4880380280e005039841c913081024036096035002040304d2542081400084598200c207501e480c0034041e0380200b00f60070303c8000402c000c034075016100380b00b1060000c0103085904081403074100340b0102e44030394090080380f000c82403400d4a044405640029891381822166680c085035030b500c00015105a15800382a02c1950f888001c18103640302201600d01d000c2022200700668050390910282049484420041d03880754100360740280c1c00200340403444c01d15002c8900c20465601d240000080d80c044441a0100c15147c42c14034402a108076000c40c1d50503030902400140041d2590300c4411003030b040c0310755030310744ca00b00c80103da0420005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 113185746 1250 113184496 113184523
    0x8100b0a120305030121051504060c03060608060409080c100504020321070303050a0b0a0602071d1b0c120c0601031a090715111204090606050412060506010504090e01050414 76
    0x38070041c000c0b0400030128180c203296015101b1081e070790b00d0780c0d075518104008410b002e0406a080501003000064011600e01000c40d090030300c41103092820041c031444009004500c601c0c1c452007210f0074070007503504503418900c1e00e005407940010402d9166029000540d8224040d00c01c01c030842c04901030404046001116070708a03285004043c1d10100c010380030140400d82100e541e2041c5071004d0791255500002428560040d001007444c2c10024008030b010095030308104000340040001102c060a4040c5103503030340307840840d280d80000c40140c1c54240b10003d990143e24000400721021032000810904aa1140d1881000d80071810328100d19468160b900540343e40c001ca81c00d1200f05603544007414040c183d440c0154180c42d0b0020694985412a1502080e03041c00240a011900e424058076000c0e01c1c4605005203040c0c42e00c050390140e480f0942d4003a007800e681c1c50116032a07a10450481e00100031000013801071210041c0030f40d000f03110075202142d0000450028407003503070703010605100c1d0300e14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 113186996 1250 113185746 113185757
    0xe040803010603020f0408030307020a02031b0d0807060e0d05130605091c061808120705070206030c030601030f06090f29010c0503070c030c030507080a11041508100b0a1203 76
    0x2e041000d40107500702c4640f4018421091102003200782c010005144035026030307070007814174840500501d41015004224048406046600d42001e82c55070401452803950295070709640b0541130030706800170300720810840d103240207040007412201e40c050b014018040c0000503a00b00c00d41e54180a0b030b628803840f03c0709500041d20900801080401c11148007255010303005c08220b0982e407416030b0082c80c49004040b640d0201c04940c0070403054284030480d9000b086400d11030b180c959290002242c600004000c40800c0c9400400600c0992085e0070088070900c2802050110544800240010f4800c5081c41c0040b40d1501902100e040c440707084071003480210212003101d02d14003c004507140d090085003520a032104000c01800030b5a40e01c1d1400040d1b0195051044c12330a61800c40d00b402169031100d5100c0c0d002c800c0d580c010070070003442040c1090040f240011383c03540c0e00d54000b906141396070080b28240213000c0700302c4554030701d90081062a20101c650307081c0652100b844000d50349007a000580001c6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 113188246 1250 113186996 113186999
    0x1707050d11040f0f02130b03130b070c0206070606031b15030e03040f080c01081e01150c0f060f0f1b030b1309030509010806030c0108070f1205090f070e04080301 71
    0x315801c0807610444809000481d80d5150a40024107980080c0301c40c0c000d5542c00141c0030f6140c00315454184c05070000c484d00c0342c42c50601041100c5410f041c404051310082603d0007054100d80038005480e1695809072030a9141c580c14181a170081403280b0042d10f0a010311000c2004842041c6d185000b584d4280c40340f082d15104402044000f0071540280d8a01d5100c00c10010601c203110800060042806a00822038400080001003a100014000c0324480304010b4422080020b1103034800e041d126041210b9204180c144000c6500c52039000f0003800002c2091680e6091200c660410290f42c04100740500850070400000412540b00c2800d0b240c15501c0218528007042c0310790002c402800e0020481f42d000b40b94840f9800c104c80c6288402c9010503800100d203080c075604004800d0f84204210080c094242c112000607024a4008004800300004100e00544480c0074030030116126580035010452840c01100e45c541d50941fa6405642901c52385038005140d07040204a10b07c29a8440340650459 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 113189496 1250 113188246 113188253
    0x120203060c0a0302120103050c040606020a110d0602070206130f050a0b030f070c120e0a0501030501030803060904021903140f010623030102040e04050a030e0603070504060c05030915041707050d 85
    0xb500140c1004040680030090b010301c1060307820f5064041d500800241c004000d00c003003004101d03401507202e002035400111204003c10781e0285690300020b0243ca9280840e48686803d00c000e104e8000c0080d0f0102001c0307000300341403090382e40300d0007510711150780c0307419041e00e4404000b1050000d100d0040280403c000290500d80065041c40d0004d2050070200a06c0b0085d136078034102d11440d119074800040c0c0346a9502518600203030707401d006150a08003080554155116814544401460240681d0b4000c002c2030446d242c4102d02c03518012554001c0101d10744170301c4c0c814488900c81102c04011f11584120350540d010620a01c0100c9a20f2010420110715160702c61501c01c2d4240203055055501f071000280d221648a04a8801d47c843c4010788404070542c074000d00300300c0b2503001640c0540814420048400d4110080360309136074280c240300407c41020320b040f901d0340c418413000c40d4000400b140c00c070070600c0101002e0025104644a0320440174840e1030305650703410491241580c030002400081020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 113190746 1250 113189496 113189521
    0x31409090f06210a15110301060c2f01030209220e011b0f0c050f0a0320010b01080106050d0b040c030914030a08130212070b0405040b010905060421050d0804030912020306 75
    0x203580151710218121900c001302211a402c00d920030400b0030321007814003040001000041d2409a404c9904400c60140c0091034141c08041001c035a0500d03a000401b0304d030958428440810b80d141a17010101c0148200e00d00001901105c1e8209129601f040c0c03181c030301040d0658112f01c0c05201d50392211a039000b000e404035000045001d00740d401e03004504080466240078480742c400c89000e512480c20081c0300520001d40442c0c000700c06034181e45440d01c1641035030303804502c080c1101c0d11450040d031141511351398940100100380f29164410301d00310503c4001e40d01038100050fa14094540c41da1910f40304607041d80c40b48a031090b00030020300c0034000106104d0441691032700fa140003800b00c007200e031035810105140050a8105500300140400c0800030707841d083c013424403501d20a00c0d00748522450400841c1c0c09004070301644d0b108600d810070f5000291080709180c0016a0040103c0d10107046c0b99070064030155050b242170b40059120800455400009001e0064265024006103600d5595000030b60381c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 113191996 1250 113190746 113190773
    0x10813020f0d0b070e010905090717071b0b011505070c031709030f010506190f0e0a090c030b0a0615021e240105040e060c0304031409090f06210a 64
    0x41c00840e1241c0e10b0301043c04000c0c114410360941d1180042d00550b00c1c005004501250701051090718140c4c01c010a0b00c0d80481c07075403003221900c01014843d03180c1d040c007554070404150004e41d6103920070101101748019021418100c50600c1e552944102c0c801e401141c1a00c183e0f0b070007611f400340110b42000010b501d45840074101700703404141418860400b001a0821002c01e28203940d6a4489081c4030761450850110542d2036000c0c5010a9828944100c290304004d0390f2081104c030310701d4540000c0300040305401082c04182c1c0442c07034800c05a200d142441103164250340440e15280382c18000b141c504580802d00321184000d4004242400288103030f003003044c4005100c60325602420720400007180c1c9a10310b150125100729040505981030005000446041c04a000102e91220003485443e22074001165001501460000c1c0d040c1d04071190703004c0074485d80e10002d402200110402ca09809280e4100740604801c545a500b81c000304200da0802c80c001d42034400164005a59030000522541141c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 113193246 1250 113191996 113191999
    0x10081603050907060f0c02040e03030702010506040b030c120c0a1e05010504061e09090203190f02040f030215040b0307030c020d08040203060c1312050a140609060a05070314090c01030b010813020f 86
    0x700d1000651f800f08085c1c0d0300040c001f041d550b1000c400d00146039020b0007420b03446041030701c04000180e00070000035640c0411924260181e051540c0c0817616450038000c410201e200502070580c1903030359099030b003488000c07000c1c008410354006c100030a035588180212800c80d9010358800640030b080702400b040381007144818034248103c03888005000d490b02c4c0091441795821806010a18405c041b002040d10b00724440c240140d441000140011245608030006594040d02c0140e42e1800ba11000d10003442a600070103000000801003100315a4541c102c0440480700340d00340c9500810f01d98007610b00c081d041e14003d5068108000061b0100ca00c0d10251101903500c2400410042e076a500c44110340c00d03042c0b8181c500f60000306084d020301807000314904000c00d51000a10340b600e4032282c41d075151040034000e10095501c49020030180ca12075049141a44011007540100e410400026562840c00c00b01e25030109051007028007a960013040b20078810b115502103540121425800c100c40c2d2503100c041d06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 113194496 1250 113193246 113193257
    0xe0307030b091f293109060c090602010507080106050d0b1e09160c0f060204081c0305010f121e0f08070b06040203010302010507020d060b10081603050907060f 70
    0x1e042d40ba0800c3c14540c01c48035111000203400a03921050010b088941d450400c000c0740b1042125003d0b00c0e4680100c3e0a503403190b03811300300520400d00c0203019844442005105c81d0070300d0380d94018444940c1c4a01c00c0142c1c1911400007080d66420140d003650f508a40007000b04600d07600401941d8018030040c5824901c034500051202c1240c4001303140d11000055070000c0350780d1079102c00410300f4107002c40d981005400051017044640124018610b02c02c17080010b02000145400500f04002034055501034262441601d00300d00f200040c00e03140d5862201d01c500000d080000014113160424154020740790120b81c2c400345054a03441702903081c01500c40d540100d0607203888100108805103007203482d0b180314010143d500c0129041c14542c110b40903244030300c518410001000182e80140451300c00543c1921700c14030000c000c0c1403801c01000950318458100e031080c5181c00506503c0305070366101d007403042c54040a210402c0411000ca0300300301c4d1007a115503c581d0040c0f1102e4011641503040e0441458907 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 113195746 1250 113194496 113194513
    0x100c11061603090807060528050f0a12050a1a0f06040f0b030114011704031b0519020103060909020609060c0f1b0310110409110415020a030206070e0307030b09 70
    0x1c1480051455109400240d51080e06005a041c14414074008006501e0f0440c01c007100101082e00c4142d000c07015059079481031012000b21405102070b40d01100c5c9010001d0789805680d0310281c0081107068050146501e420006600e414a5208280101c4454a0382d415140c10036801c0c46021180e4001060380f12009000c00201c1c265002e06000250001400c0d45480c0d5140c04005c080d82086044002d042c02a880314154089103000d1280340d0250b00b40c0780c4298440c00350b0283e050030a4001801411602603600801018000e00c600503075080e100781d81c100442e690340c0c01c50004403002410007c0d40024100410451894a880604110030302e01d02035612101d14419124540303000020024040c50850b04100c04500c2e00740022450b0290080b414003100c8007002c4000010720990090701d40c00d5980e03944042c104501d00003602e011713060800f6191200c2684e454065603440000c5021001449850300140c0202d120340811591201d02400074008141150303150242482c00906a200600c07c482c0c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 113196996 1250 113195746 113195767
    0x20112020301080a05150103050325171305030f030f091c050a0303110c061801150b03040b100b07020108150904060e010f060f170a140c030705100c1106 67
    0x81d8000c081c018010120b54a4502c0e1032410a561420316136030104a0100400200d03c0200031034850344034401030f030190040c04c1600f085d2628907942c0060900400c12140d890a80c14110007042c80700940c0d0001c0e00640d0359181017540e280040d0101c000b40ba001444207280c6006240054074051000030002690f1024121600b03d0030b041c4501d0646040d03200c544854141070f01032203980701c04544100000d1902c1e92604409a0f1000b000e003459200031460340100d03100b40c10039400705a9100300d500c80c0300c4810707941c1c00b55048907410903181641e040c44c541d4003046030001200200c80c00c640c6a0080070b404d03c0c07925001900d0b40a001407062114071502c03031088006649158805100c1c0b132140b50001000200801e24a007190422820011b840346408014081d03190402c40c0403003110440010f440c0940da003284010b007018040c400007000d0305d040d00658019114041040610100c05174100c80781d5650b980c04200d40070028002c1100030a8240b901d0102088881c516500040e9024101e246401c5940c00d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 113198246 1250 113196996 113197001
    0x17040f0f030c060b010e010c031110020c0703020a05010e090117070f03120207080606010203120901020c070609030b060f06040b0d0e030d062105030f030702070b0d1431020112 77
    0x60114001050102d100b0104001807141d04001d20f402c1c40e0140c600561280013030705840d0785010103014064003800c00404d95104010f01210410101025910345441e100100c1d0384040070b005c02c0b07100e5000c10b40c003c983c55118074620700010600a00da074006910b406450824005503011549050103420350116804010f500050001c612800c80c0040c0442e6080000b4203010b0650440c2110760841414018ad980c0e002094402500c0000fa01100c00e0f12182c02580c02441504490f800b14041c0c548001949900003030340e4800c4030700850f1807030386581d00d00f82001410f591444401ea0b101005010501000b5081c0010705111450050001111902ca12324103107190018036001c0d03904d030745840040c491880001c042d080c40c90700c90200c03000c1d041016960a40c6034040d400c040113411341c0210001c0c008034420840600103114081c4540c0e0340d0583c0003007001c09800d035420760080c010001000f04030300306403080c1d400200340c0f00d041040500b8240c4e83d0851309202d005401c282d041010080c02c081d00043d81c0d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 113199496 1250 113198246 113198273
    0x2061309050a060501021e1606080106020607030506030604030c1529030601121416060504030b01060503151c02090115031808030105010f050f0d050a0f020a17040f 72
    0x998020006103840d8184040e208000c10020071030f0b0070302c1400c004070398000405800c2c00c2044130041c460007203448140d91030304041c03141c10044400004000a140c0390070034011030586200341d003554025980c20000394103680d001d58041e50117034441070019011034459212496494410401505441c107440b1450040e01c1c054204011840800e0f007081c02c1042039040302036441c29094014041d95807500000cbca40c82081141c02030840480c0d03649400c00c040e0280260345a034070840b9801702c100c580b504401072594015002c2110350318803281c000720381e40d0302403c10b4900c242c519010414200d0b49100621000d01c403407402a45845d803031038051500595605503920b0182ca44c43c1041400141000300040680390b00303014a0320206c08a80303d21010990301030072030741950002c0c2400e000d149040182141e6500c590180120414004281e60071009000d4000901501c0909414040c04d10729100c801c04900c154041440070603a0a401e80c0415200460320300d0340103004440e8100e0740401d64450f0940100c11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 113200746 1250 113199496 113199517
    0x10e040227100603060803070b0c19080405100506060306130608010908190509060d02160206030c18030c03030711040921030c0801030c06030e120c160b21040501090206 74
    0x1c1c40810900b4050981c00c407000740b80798078091001174600800e8580300d108140002c0c00c00340004000400d60120402124030104581d0380203600700403014030048c00c0c04400d8071704076010300a00a07441c410841600030280105401404149141c07540c90800c00380945000803400825115400000c21601c01e104829400d402a000180d60f00500b00000c2a180c10380e00d2440c09101050140d44138079202c4800ba500c030302070f40d1800180c1d40c51495804008102421400030340c000400010451104c1402c800360010039010103800209040303040070103445804444146415900900221002c101148001400d24902901c005060600e6483d0b40c440c0700c0403c2c0c0c0c06000421000850100540c0c1440380001e5a0000d16050007194150303034881c00421147d2041004044c1c03542c0790b8550410b030901c6510280d0f461111880d5030f500f040c1d40015181e000c4201000f8501141240016074010058202c8403c030f125031114505a04600340c3ca00d11403070000c3c20503549590389941c2c840042c0c80c1e0070000c0c00a03211 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 113201996 1250 113200746 113200819
    0x512180708070806010e0108191a070903050c03060708070c110604030f0312020702060415031404050d0e0d0b01090c090305060a0605041d1b0d060504150507020f06010e0402 76
    0x10054044e2808106906c1158062055401000708150210300018030002811240f0f501da12a4103103130550740c410305480c100900155050108441c1c10440c4081128400c105480694140d1020546ca8040c01c46044000c220b1100004804903c01e0040c807a0070303071060b0446070741c2802070008a9800c0d0010f800480788140d040c1200c0c028103070881301c058451131300132800354039011107640418402c3c040da20442050103c01d41d1120603060080e0403861804103a8816100301e03240a00703006a0b41c00500f108038001c03a003844081324107424080350b0340d0714032703a00030354950501d910b0034401c44000c062500c00c14041011061000c1300088061004a002d030b040104081440c81c00c0804100c115502c9002c4a41b00c40d01c0c00d000405156400304000c22500100050724202100c504082001507051440c01040c1c50316107006c1100b0000c0600c8107200d1448420020442075072021403d90341c4c2c00c05242450101c1d40480e004000203042c8010403503101e480078110348101109800103034144020b52814115804 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 113203246 1250 113201996 113201999
    0x32001060810050f1003050703031805030a05070905010f0b040b0705030f13030b0708040b1501050c07030c031b03021c0501150305010b010e101b0f0c030b0a0b030607051218070807 79
    0x1e200810b81d6804c0702c50780800c00305c05461582e0b21030303407100d1504c4018203200e80100f00741074868414050200410780a01503850130034252170800e4a03882c0340e000b4544d103070b8942000411184c0004242100f902c00d0020850315107810400c45031055088802c00f1103a91104000d81c60200300c4550161010071801c071030f2040c0080c10761a1058900307000908580400403004100004070354403414058000e1640d0b900d40c0d01d15800300004854a1007031a1001e200362042c1c0100104211310580c600048078015031070941154020082451040e43d10700c07000e54082100c1403650a810650801d0401c005e00c104000076419030401c00410f52a03860740e000352441e07591003008005a580111a0880b02ca004a9505240207600c07003001d48070111102458044601d5028280f0405c129080c2c2007542d1608140c900c1049603803468011300342441154a0000d0500f8580d190720f2a05002801c107000b50b0b001e44401d814800401202040e01c03400a080c00601a8080c400842d9600184840070203444442c011b040b03400d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 113204496 1250 113203246 113203261
    0x30102121e0c030c0307020715020d030605120c1302090a0923072f061f0902211e040b18071a0a0216080610080102030403200106081005 60
    0x4910441d103682181c42030500b00000160007804507688408401080c40e280c0d160284d08900d0408a41c001c0000700300c0f2040c640c130030b064000408407100c0080341c1c0c1c140911a1180d040c0803070512480b40103180d81c2d20041240d00d2900c1d000892007000b0400d04001810030100000007070000003240d111002d02ca585550301142c00018014001c600010031150030f1440c185007034000c10684c1810410030a030090310415000c080340f18040052001c4540301100c1c21800c0004142000c07050041300c01400c0c071242c180c00182e0307030a2802600c844140fa05404c900ca204241c01c0c522003900002c0c80603021141c016249032845402003000c5000750f029201c1c1459926000072212249210103800b0746190f0b0040b0030400a0340401c5d11a5010254885190f5844881d00340007a807a0900034075500c01c4410000101181c440c0c00014082d200d034420005000d00a030351000018200d110983d0094005241a48a4100c1103c1c00200ca80580d035003400001d0001e82d290045030522408415010b0019107071000d000da40d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 113205746 1250 113204496 113204521
    0x4080c0601030804090b0301150e060d1a0601110d02060a180f05060105010806061213060b090a05060901170607080601120c020c090105040e0304140102070306091b0f050a030303020f04030203010212 87
    0x92001d4000300308004a41c0c444145007a0203100d4244ad15070b00000240c42901c0781340c020112203602450304c5c4010076502c140c40314484002c54203107001900c0c942541c1c0f0031007800a1784850400580e0040c0c0002d40316501c261000c3c00303e100007002501d6249002400160690386815000740c000c1000c2c02c0c107541408001025a01c01501046c0300d8502403201c4c3d07510500c20400e017604801080210400051145080c0c0040c000002c886a03028001074100980340e0616040a0701c00c83d1b003102c8000c00380e030301c03191344296174001c083c0c00d03a95030b52012002400c05402003a1003070b08410141000110004255413500941d4191680c80006800426040741e01d1f04001c581140500000c841c24003542d034680005542c0c80c004d45c0701304100350414410785800c5900038085040610f41280080c016480d040c2004000000c031403403400320000c80b4240019280c44101740600070f4403070003403281d42c00714030f95101140650017200c01c00030b03029010000000143c2d001d1009080c15039410b82040400d11742035107803c64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 113206996 1250 113205746 113205761
    0x406050c16050a090906060e10060201050705280c0b011403100b0105030c030a1415010f0e01020706140c01050a09120302070c0501030222030303240509010e04080c060103080409 78
    0xc62040320092019949180c0f4440c261000c044002a95502ca42080c2c40507020942c80b508810b61440113200d08070105aa4480c107079030709034000340100d031242d1408403014802d245d80e941d00c1c111360f1100c03140c00401620728201ca520303a61400004c40880d61302d400380c40320000c0c3e000d01e2000302da0160500721801d007804005910a102d50301000000c0c2c03c080040c10b02e210040460384804400400100c07000025480140039000d243c040c00c441d482d00011010b80c1050412455001c200c41a09801105105145c500803401060303002d810701c3d510b08002500c40600500003034460352030030700007007100314024800c5910034001510049091001420514203c088008070401010700400988000c00c0c92801b00780c088071b9080c0381c0142e0b61001c2e1007201d5100141c00300f900700ca041030690004241903041d0001e040401d0860205181c654217403045240058007846160341101c0300100401c925540428050382c010f0107426a60319005120040604240003600f04032030f01c0101140030b100c2c212443c0705018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 113208246 1250 113206996 113207023
    0x9070210060e01081c1806020313240e030f030c01090c050108040506060f010309080304030903021203070203150c1e0a1713020d080c1504020f01030603080a0507050a080406050c 78
    0x10615410f044c00c1c56201d81a204800c00d202403c6400b1604503442500321034018501d05400908141e107a42c0025100d6100460f00443c1c3e1000310000700c1c281d400348205150010010142c1400358246c50720940f202c00c01d200345590700d8080c001500d58001028001048c03d51403200000565100524203010340d03004a400c150b0420207401c040000192000503059008602195212854014000101c01a00b80719000901400300402071104140e00f0155150903a0310880b00c0450050310f90000685d640120310000c0e62607402464203240891280340c005401c0215010030624021800400700c9070081c42e0440000728620001300c0180340c2d0340c000c450503585100c0c1480e0050f241000c003254229218200d4019101f0341c0108800010009a0003c480e00e00c1818001e4528420403d141e140c1c0d07011045505034041c5403042500b41103584248030308003d4942c400ca9181c20714014582c00c8a00d90007280f400c5856214a22420010071042c0020f4070080400b40c1d03c0700c0d40c41c51503171080380c1400389204080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 113209496 1250 113208246 113208269
    0x4020f09100507051e1207050d020105011a090105070602070c0b0c06130f0219090501091d030f0301030b090c0904060b0f0102010c140a090e0103030e1009052d0907021006 75
    0x10028201051707072050140d1410306912100c148804090801c1801685002c200d90b000030360340c08000f000701b0400c0c40e40f8201e03002000580e9035511903d11421201418000c504401c210040d81580900081e1045a00405005050007010f54a46d400c1e41c800342c01850181c040401c2c4c80c042550100320f46584100c203100e01d100c1e620410303500c0c1032800d9002c5000030300c224869001c0c50780701c030791044c0b049004044110302844996500e01d11440248071910320681c2d5050300040015418600008580005045c44112855030b031a58071250b00e5003002402d0000a40600342080d00142c0c2d83c0c0c02400c0c0039501461000800800000810001e60a07555031306041d079050020040000c0c1c2c000100481d01079200c03d0031581c901c0d4803c01100c00384455040205086c0c07000c00044245640100791a02041c810341c0e1604519243c00000c1d203a584161280c144e010103404085845240c9500b00340240d41880c00c4410068a2020006030300403030203c85410043c1c1c054120a036544041e8090b000042c441032255 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 113210746 1250 113209496 113209507
    0x605032403100531021011060f100e01150c0309030b090304090e0a020a060f030f050c091005041a090109030503071a0106170a09050c130207030f030c05190e04020f091005 75
    0x5000d4980349041c4c010384039000201603003201e1401408581d54034a00300c020380d051464803400c0300801c68000c2d41d442011101e841404201c2800c142c0c0b00d503058621521015410001d629011035841d034400e4022802c000943e40b0020024110048160140b8500d0000d9a211428800300c0d50803a2150100c0c0d081540c024007080000da100c03038400400740c03076061034030240117055418113502920480c3c18000c06c140c5032008018103440c010014200715981162400d03150762503654126264065401034003850f5280080341e6282828400007029016810704000500d90740c1c076141d0038119003000c2000d64580220300961038605500d0070400d4050500c600b032007036642c3e50400c40d4488010004014000041d42e8004840a0000070003403a5200340c1d0080c40d107001103558903100000307500030142c1100400e00c3c1a58010340c0e68028040e81d1960355081d9902030074110380010000101c402a4070510a000d010150210140c90360b00090031a01d401035078180d5119404400e014044062003c12410000300703100c0f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 113211996 1250 113210746 113210821
    0x3030e1009051c020406120602091314010b0702240c0d020111160204060512100507170a09110a062c01090e04080c030307080402040b0a06050324031005 67
    0x340d000020b000428150000c00f0b600c0454000c10079034002661802c0c0341103541040241d5a0001c104400050303030b0350009040464103242c191054164240d036803503520401401200a038101800d241800100040344a40311071204111901c0e10000303900740c1180c0040c0d040e4000204119800d40e5154510080103805648070f815012406460607a03200001079020500130766890340c0040018001c010301210340000c3c08070006070380320030b2800445482c07800c01c40002c007601d0146170304410001103040241407503501d00344120b0040460b813504881c106145545c140307407511041501b0b400307030032039466a440d5056410200c20701d0180e11a014408046c002e40704048030707680514810308458485010700c01c10303150b034606075016000d44100d1810910000c810060041d61000d060380c0118002e444c2004015070343e4007480701e9003149002d0403000c1002040410103000c59000794282a030f10840142803101c020700006410180030445441d44552100184000c4c0080403d10512034407007801604c81c41fa11000c17 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 113213246 1250 113211996 113212009
    0x1116030809060a030204050a080a0c1d07050703030222060314160c020109031209090e0321100e0a050703050903031b090a031a04050d0e0a0504180c03030e100905 71
    0x100756018a101103119081540a60190303800f500000b0b251403d184c5c0c54038a00c42c0e5402e4840810380355015050b0000030850030403c10007031501002030640d601566100401d0b9819482400100c00b050740c04c110040305200c10a8190360030410a003c1d01d0442450603e000b4161224007039214000c0d2100030034003080b501981c4080d20000a24104640011500d00050319265100d90010340074102030340038000354580c021014419101910307010041c18950300401d0342c1e40e010700c1821100c0d401d8454202c0f21808904640a9804820224092045d075100e100400c04550142d40c60940d2a485209014030307540c15004659020b0b61041c0114150b28044101144071040590140c2010200040d008215110004040c1c05190008040d0b900c06805d1507101c81c429008880076a00c41c0a000241c00c0c0142c80390300c4060750b401000341504060b900345001c02004065000d130040c8010780614204c0000b0b048030600c04020350185c0c85115035404001d00780b10b83d03801000504010000d00300002d124940e00c01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 113214496 1250 113213246 113213257
    0x402040c05160f02190806040309090207030f030b03100e0609061608040f0303060b0c03091003021305090c0705161502070b0a0e2101061a0705150903120711160308 72
    0x407080c03c141c20b200c2c008a1610f0903034500b520900c2c1c040001c08076070203900051080c01a8881c2c2c0e10b1480b860340d9240300c41e0890286420050000b82d118013410601807207a007017034034031000003819506904d501c84065011600c000203c1c04058009a007040f07042541404510750149180001d298080c5189400916800c4020402030610b0095001d510a140c800e5000070b019080010000340d44071001c40c10b090b81d0350803100c0c01354440e644070030903552464480e00903190064050181700850a0900040280c2080700425481c20381c90b0a10110380031900400c0440c1c0c04003d06a070311280b45050000503290815042030381402d56101d0207040205040c05030440c1c0b0749008038607148016241040000700751b54820318001d200d184441c4600901c1e54010b5100c6011140030f41c401110640c602903820303120307025400024225400002d001d40c030200611007a660310bc10b0040a40349000c0703a102400c00e4800042d14072200081e1507403140d815a00c0c00b08001c0c3c094002c1c42280720141450740c2d40700f0312180b040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 113215746 1250 113214496 113214503
    0x203030403120e010603030503091014270304060e090106080405060703090f05101b14070b04020126041a15040b0f040e0c0a050111060703051801140402040c0516 71
    0x4952401c1c2c504203510440d404921200244041581c0f802d0040c0079800c1521488042d0040c00441207800c40b5034800d0603421149035018202564a0040321020400088008025101c1d0f800d90070441c0e1400740300a00c082c000f5071b100e040401341036205000603414140c002c0c9052040c880d0612002c01c1c000601035622407071601c1d01288146452400c686001c2e03008000910030311855100c00c0611810b900301c0b030800c03600440d10000f05102210200d4031242d421030b02803031580f000c02089012565114034240c2c018010306054050360741070b0000c40841c01007510740e01580c8058074184810004400140f0f00071440004101405003003607000080d0144e8814807091203140c0d19285d170f8806884a04401c5c0914200800801000d400c41ca58030342c0398090300103440d01c60640d50001050560088260007110344d5540d0003028690b072500c50641c024034000d00345041044201403511602c640901603100f0400704513208609a0801e4411310080d0b6031410541ca040c02418040c04140c80903881d0f03a01e004640 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 113216996 1250 113215746 113215757
    0xa0204020304081c050a0b040c0915091806051f0e040b150703030605040b0d031d030a0f1b061d0114120405060106020d14030c0c0c0907020d0801090209010203030403 73
    0x115460500383c588103416010100e580c1020404804000d13591181d4800c246c0340c2d206200c02c50000003044201d510780c6007a003011518118060109160b4902d44d101200f0103806d00454091310340207951414480c1540506040e80c558800b4010f50800c1019a0f9014524140000358501c80a00c05000d00107081c174454001c655620b2201e08a03690000800c1380d541210f92201c0d0741d941207081c028040c0c0098041c15020340c0c103102e011481420802a5129495099a10140050443c200380780020382c00300000ca0340340c131030b0720211404590409440e0300c507030313103c0d002d80d09045407101d041c00e903484996801032041c8461322100d40e190b008100c024840d6004240303050a04d4101081d900b01c078500400c0d0404000c004002e0400040280002d10a41601c0740b6400f2100d9450580000303d429010008003101a01d005201241f2004116809042508010800d44056080084c04078044241c119080001030340b00018944086400254442c0503043e00f500075481c0903000c400103942da11004c2d2005007040b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 113218246 1250 113216996 113217001
    0x2090f040e281109060d0b100b0f12060906012109060609020a14070c1203020f120301050f030a020303070201140f030702011b1707050903030408030c070807170a02040203 75
    0x2006200c00502c030300c149808111074500c400140e2108606011003124205540c0014501c44d00c2d2000c5030501c40c942c003c0845940300b000b642d40042040002e8a520004041804c0200d0b03111600c5020b0294025901d5403583c0f02c0226400750300ca4000090a898041c40c500002d02c011643c1c0016515500e045250300748400c201c5410704d04005145011000d80a01d10348500420703109d88540040410650a5603003100100e140e44a940592091600c01802c60740f10751401c0022034500811012450f02a0060f98104c494114215046c601d9140300070481f400e0000042c8005d140602408200003000c0d4014507601900d035010030741d68418044041e0511602d1001100c00c2c118100803110195203404034192a41480d8070040c1c00391101180034100c61080790000002e00d841812805060310120078006096251404151200e5101006603501400100008603d0000c104020510080d4440040a070903290546050410f100c94210061a9020000049807070300009000c0c03c466404460060303598 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 113219496 1250 113218246 113218271
    0x30f08102d0305010209030105010b1305131407030b011107230a0506040303180e0f06040c1107170d180b13030b010b0706050c0309070b03060a0306110a1202090f04 72
    0x44504201c1241e146031400040100701040d005000048001d0f0024400ba0762a00302e40000c2d40248042030342002850742040203245000d00c12a0900ba03820080002c10200791810940444011902000821b494205800555901c0008800d9100b41c4d10007419410b424418041c2000c1c21040010704407040c805000d03c07151b40c500c004000189002070200390380e240c2e42c2c41c02800c602403c950500c4c28041183d00014099490b241c004c0c0700d400000300e1064240d82c0c55080000510700207646404020302e04856040201e010481c42c005400d808801c04541d003801481d440c6071031003000f214410032024482c2c58001001c0e451190381a10001401c02e034581000308201000c4903151707400508400c216100004005107080c0c01044101e0240703009000e01d07036a1080560440c88281e822000c141c1c45401c0810407000110055508120f004000e10b000303940d6a2107a000f07540d400c0f10229543c40c0c0c0060b00d9040c5603005080c900b200b10703402c60294240562000000d0030b1100c00800140100d48914041403503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 113220746 1250 113219496 113219549
    0x9040b03070314060a02090109030b1005130f0b06090a0608041403030a05010608090a02010f0c02060c010c050c0f06070e0108040201030e0115050315090703030c080d060b07030f0810 80
    0x29140260440385010303079a043c01004860545101c4a142c0034000114885484d14001c50301c1a002c10384410304410f1075551106990b800081104a1074081c815012800b9611449043c4002c0c400c4000410710712645519001160380540711544550004c200015403030301c480f0b0701d103001c40303c0d242000b401a81e03441c1072000040c201602c400313006010010400c180d12140b6403040b03050b0b40d1643d40d0300d83d560341d5035181039560748074829019000c607100c1004441e015200c1e007608071034240302500c0142051000c007840da00f5503840350a00f038007040300400d4a41c08101c04000a400c900202c900818550400340c1c8050100300c0d101c25014100890040024196406a00802203000d4014020403081d8000300410940304120b0080601c0b078080c1d1940130701000c03102010380b80505d074501e0141901c80c5c90340d81c040d02c2014501204803005c1d0402d006030108c03805e16102c3c50009081c4101e005a40d81001d2500900c10304100061074280245175060050407180305440d04103450002106029842d4000c000008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 113221996 1250 113220746 113220761
    0x6040f0215041a0a17040b0a1107061d010c050f03060418080315100207030503030a020a03150f18091203050a1b0c0c14060703030f0b06040909020f0303040b0f0904 72
    0x10343c01d412941d00c3c014075030020081c10004442e64400321001d083d404420350221003034501074282004039010940340c1c1800d80c0f0902c103018107071080602d08207031682c031b007025115040301d041940c204c11019030001d84005c0c061040505810324041c2d14102d210344500c105130001408441c041c50350342e01c907003407406ca80010a060050700b00802c03545920340201d4050210320b40c1c202c02d0f0301841001c0d14001c56540001054000e881d07002c4c01544c10b59450030b140e40c000b03400c003080c1e01c0c04154882d4402200718042103031501c06003017200c0075150114101603c016900a03000240b04c0c150b450f0000140208032a108001c031583d5851134007054588a8010b04030180805411851451112107441004680c0182155200f503104210b2554055620703d402186001040ba440307401c0381c000c00603400002e100398000c40c00e21081400000d40040b2640c04200c0540007134000803c216034644e210015854054041200103008800852419080c200e460b803107800f500c030078028603103000b1551035841d6030b81d50003900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 113223246 1250 113221996 113222009
    0x1d1506030619020f1e0a02120306030703030c020d0c0e10120b010b0d140a02040518090a0305070309080105010605030a0f0623060903010911100905010503070f110709020904060806040f021504 84
    0x2421140002d1030313410351ba40424130050142c85040d419001c0c038540c01c02601d03c103880080180c00c07190310711780f02070343c2105450300200d03440740e404070448000601c0303030700d60801401079070030b00000c1c900e448200446040a20307009100102d06a0001d0300c002a403021a00f4150b80c660141a612170440c00e0b90403014000070401e401d016500706041190459a42d405401100d5084415881070307005e1401c61030f001c0d2001d03222440146c02c03880c045004240194000c00d2418443c0c508900300d1541c0d100d2540c21600d003031304010300184000060006042503401003002980c102c032410000b5510304180c026011044400c034200d404c18240010201d0380c5d075041980e0030701001500911062204d460140390440c0c610000c94881d48212019020041c49180050207031a01a101c2d2407440c1c0307c5548c1a07030200015441142004031403422215200c005202c9100284030350403015880d401003904100a4030039607003007003409500a104200100b02c0b103006004003183c0565040c1400540d01c1c0c100400340c8595007058 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 113224496 1250 113223246 113223277
    0xc010209101d010302131505070506070206151009090b120316020a360615090305010615081302150403030c0203120306130c02011d1506030619020f 65
    0x900d400c1a00894440c04000e030540062078070b040150101d0180380050f8100b465401c1c1309000e030748510264a001c0031041c0c2044c6052803d81e584480c6043d000329092401a04450184003c58400b5100c049601c641110f8450300d4100c5a0b10080a0042c0c42c403488070015280c0130050450780380e43e51000f41c1c0c2403014055a5030342240401d21a11600c1812040740a130701740620000c1c41c0c140204400c00105070300b4400d80301115040040c1c020150144080079044d960310380c03000805c409003071465030000219482e100c2e985c41ca0760400034219903940d0300c25041c00c5120100d0f451410ba0111495070300081c0340040b410f0442c07403400032514241c540e403a80c000b4040d001a002c0309064101145005692089040729000e45441550040c68002900c0c0c19030040a0306014103038200081e0403c1c10764806034800040c00086441202c1c01c2e40c079000c550003405420003581f03640007143c8680e1055110b0003c0e0300030f041a00b44a00c032848182200c1c4508405160701050034103e503005017085452495003090176 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 113225746 1250 113224496 113224519
    0x90b13150f0e0d020106050307030b1504060e061302090109050904050114010b0c070b190c1a0a020a031a0603070507081e0a020105060a0b041202030a06050c0316050408120c010209 79
    0x40320000c00341c0d82002c411501c81e01400070031140c4140920015110090081c0c18801d01c2c0d41c0d16644400005011508035000710101091152a0f900c5114006e01e8410305600340f60500320180695580025504108240100003e01413070360031003a002c080303520603204c0c1300399651242001401802c144031602c0c1c1280d103d01c00041c0211035180640010341d500030584800d00d40e1021518100d109407045c00e500c81d20320301c1e101c408090081100458030380c0241844605210b10740418034201c1401c54555103259408104040540d0703161080381c50b42000032580c203c0d04081140051094017000304000e080203400100c4a0800000b40d0540311070b04180f15114601110399200038a040d001031004400661900c0005640da1a0106080d0111003403500114601401c20144921340c0340480e1060360140f1454865000081c0d5a114080c81488007240407a26411310898441c1f14180c03070b0340c80b803040100500080c810210045030306d011032816901080c4d542c034408005107000e030094924440e1321803c01440b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 113226996 1250 113225746 113225771
    0xe0112050a0c080c090f0103050d050702060c2d03180d0813060807030e0115210c090b090106140f03070e220605040603030c080702060405060c0c0a09090b1315 70
    0x1203130110350358102d90000080d50307060340c40c094078030b42440098020b91041d507554004500400042108900240039146040e8a1b64103442c40c203860076420f44401c0f0074508030905282050300f03200404003040c2019502e8130b42c0306100925071800041205116121142ca2a410440c0400859080184034601c40300b103aa55000081e065a00131580f6402181c1010582c9031819130602c84d0030040074004030030043c3c0300c3c2843c2013080c002092440c2c01d146407030203c00701c0020610b0071529100030401030f0404991461600b05000e41010107a2094040c08503501054590a4648003590203050a040503191255180c42d030486005a410110302c2c0c00061a800c100c1d4142011300712060700700940318080c084540d440050008407401c2e480301900123030305090520b00080c000e0004004407400200b040b42069100d10000c4d0440e4080304890003980d01c0840215060305003405104010101880c0030401c06215860b0a00d4169000b4a4a00d0704044490b42000304103642c0005146010350450804ca0001100d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 113228246 1250 113226996 113227003
    0xa02070f0507080105070e0d0b06012025060203070f020d08120402090f07020d081009020406110d050a051b011b02070801050105060c150c09060a08040303150e0112050a0c08 76
    0x4143c40307075007008002089203020740b0002d400e192000e00080c107129061f480c0e0319403000740644818100304504030181d1050120344c0e82c4000c40f0f5040c070302030624140b6208071800380e0b420040b000003220240c01c404005c000e4011040e0303450a9000100c0e4102c185e0b6030320004000100403000145206000309400a510307222407441880345100386c070040c41503140d01002145801048440c01c0041c2d00c41d5051280541c4510340860b0003405548141680940742d00340d500507a0040d4200800007660f1000b21501e10b001000104481c1005091692510405590003000b6103d50000c4000040082e072000540d194254801c0d01001031401411041e0444c1600003034451880780320782c15566003801c001051030314003402110350a44a00b0010071a0080c0b010458142c508002c085291310030052020030303100d49624004001a070402d9803103003100d1405190140460300a1100112407031440c4070107020140802c1d4190341941c00c4407840d00c941c1d10341031070918030b00481075a00500850700b01c000003541e5280003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 113229496 1250 113228246 113228249
    0x1803071e061d13051801090c060f030e0a11030d0503060607081b0105010605041706010b0a0323010b0a08070c0f1410060b1206030d050403120e0918060a0b0105040e0a02070f0507 78
    0x5c0301c21403a800b050040700d081c1c3d22034040c054418150840200206802285c50309940c0b140d6050201d0440058418103007403081c88101903400d0340390301c1c6081c185840d0522000704040d981d07040036811400c000000ca20381d4003c1041c000e00d09400050000441c0c0803941180c0b45040704140244250742c1c4401c0002c085d60850301c40d240801030b00741c41c000301c55500030a020b41600c0405400605010703d542c02140a0004089841081d050032800f85e2206803d05041034040e1202125150380e40244c2c2c00003e20f00e110041400e0200b1002c002c08600195082034561411034006000444168801c0249403c20400180e4007010034a48040044c0416001c0040e00940000d030301407a250390340d8a0141501c41d4440c0030302c6000a14100020b00c0000c0c1d907045c24a0340300d082450310035603803074400d00890f40c0060180c2c2e491401461039100c48510f800108101a80038200030300038840181543e001070014020b80c098100000c040070002114440a44d043d40d40e019007144181d2268400b41c10b00c2c0340c803116107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 113230746 1250 113229496 113229511
    0x81b1903110c010507080f09060d0b0102060a050702030d11041806080d0309081c06030b090a0209060303040f03030819060608010305070f03020a050d0f0204021803071e061d1305 78
    0x141c00540d4914072010072100030000c011303110249005240d907614000f03584204080452480113120a07411520b8403000303050b00d910700d00b10009484401c10006840c10340c0040c02030411504000400c40302d00c1d40842034031101c4445101c08242140351403201300450041e47c0042440c803000c500d80814410094100310215403122064541c52045082c1c120700b0355000c8000982262030400509a1024891803c10b080d880c148000082e06900c1e40c1c0da03801099401e840b03d10a40c0c2c4584424002e40c506050a207030402c004800844c0703070514040444106840c10702c4090144400d070000150f2841d40e2684890700d4540030441005455111a00603045100c00c0c001a1564403a504001c5404442c0d11011400c3e0b071f800506442d107041c80c18040118520403000c0442c2c00b80200c10260340103840d540054046c48103c910b42018000c2603505140c607200701341e0f0105514101c0042003a40100d400a94041510018074111174001c04200b504404114114070391034002845417140d104010107a070005004028 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 113231996 1250 113230746 113230757
    0x30d0c031206050102031b010609050c031501080411010c140304030f0c060203130909030c0c0e06011209020a17030f03010b0306040608010b1302090a0b030a090203010b030303070804081b1903 84
    0xe405000000b110143d00030180540d100b0408621000d04003620040c402041c02e00214100d83c940d410354041d100c0a580304810500c0c040b09001810352a0200000044c10a18040540f0318050700d4610001030880c14060501040480c0340003400f1070401c00042c5030f801c1c1c1040703030303a5030b0340c0c9140042c9071405018041d1004000d00c040030500c0d40c400710803107030022005154200c400b4281a01c0100801d103448040b024008113042c0040010f1422001c03600030706036000e07030881c181350441c005416461a07800200b499480d103440c00b00182c0d0baa41c03109060319801e280045148020a00e003a10314400d1142007280c294010000180382c2408500640c401c81c81a1800d0001680e00e0075103900303940e040410141d2090940312400610f0000c0c0c2d0141910420042061216903039816440078540d000b5201c4034141925648040c00354102401510002c0d0800e030015031540c501584000d0094401510041800c80c00280080c410f01c858500300b802030710510141d6030345403021a07401000050120040340401c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 113233246 1250 113231996 113232017
    0x70501091212030e010c020d020d020118111809060a0c080903031b040b0c0610050a03020a06050a1e020c01080c0301060f03090503071b0f05100f0c020f030d0c03 71
    0x148184030032021152826040d401640300350ba141184071090910100030181d50700c645100c0c100013401900c001d0401a0013074403825405040c02030806540055040a6a0504100550b1030480c4500b41381400d402c51540d0b00c50003010340001d4440015000c0ca84001c440c210705010061034082909130040c940090100b143d4542c417442500c05d0441100c160713001350801e0000501c03071083d40c9030950440410b00003e80c507154546108250799009112100225886601080854010100e00a000c0d180844132800d10740c0c60f40e40081d600c1000750103504204000450b410308002d01032020080d00410040f66890341038004d2400940d9008c076481043d000840202c00b04111300c0c45182140d051b04c032140c1d00c092103100041002c0e0060015000112a0f5210800c13400c00801c440e5049031000c02c441e00d0285141a29200c0781550003c51138004c284200c0100c2ca5940c0f03640d0700710280c2c45840c48141000030320307030345507000091403007003450380c4140c0501440c0c4035601655841400c042d400351094842d42c5102 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 113234496 1250 113233246 113233249
    0x70317120c1b1f050604110309070e0c0f1e2505011404120309031e02010b131b2703141221130c0905100501081003060e0a02030615030705 61
    0x1d00941001221510141111000300003a40e00005d9200002800100d00b43c03440f41c003c50070a03481100c0c45800741e00190702c2480480c042c62603840d04510107200d60760a04503110406030140c4a00464551010384000409190030b6aa1090b1100088090205104241700c1c04444126183c00d40c4211000d510340340c3c0000f061405c0e00c080a010320342100d4102080403000c001507000741014617054060113402d01c4414002d10042140d800d803051141c3c00400c4140c1960148004848140701803c0c0441c281450512840003031043c6001c0840303146010b4100054280c05801500c0b10005c0174150031a04600c0401805201e0201500c072550a40481f020741e000304068070310034000d10b10320719000840306224842110180d0325440d04280100d107208403502d02ca3b034074000820960b41c00800003a0310f80d8200701c902e05280085c1c4004040a0a00c44091701e4002e0f48007101c195a030100620f95540e508410207442c1c000c20102101c168045c0844426003810352288107400c0d00c0303030203144c030920a88202245a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 113235746 1250 113234496 113234503
    0xb0601080f0a0f020f0f0a110303040b0a15080d08090d03060509060d020103110a0f0905060c030a0807020c03070306090b01050d050a11031c05030a110a02070317120c1b 74
    0x11901c080c40e0011940750b0014031400782c0030b16241c14901c55001d008840c0c0354144030000345140040c50820329030300d000b4030030054400d10840e900400d4580090040001103002a00711a600c00045800001c1070304010303908140e000003a4000c2855489403407030080310150010445070080010004032040c25500745000c600765242030044c00d800100c610301080203030400703440b050034140c414100451700703840b030401b030b4219508480d110000280d0300c00120000a508032188030064034054517414a000451b1000d1581c1e4800c845c10b80c4100891580001e01951007845411140034008041d140d40340d551b03042c9031b0301518020400390390082c214000000c0602c1d04502041565900c10050040c07610103031170341415030700780c1c84800d501401015040070351702400e92104c407003001c03641e01c41a8890030171022050441e41c0064241800010410003001d003e500000c0c01d00031a1b80c03107a039900801c2c0310544410b038240100480c201106044c1c20501400c0c40500002c0c0002c9400e006166105090480c0c1203542d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 113236996 1250 113235746 113235751
    0x6040b0303070209090703080c070306110a05070b06010e04050a0b090a020a0e1c06020301030b0406150602060c0a170a0207170315010c0f050a150605040e10020c0712050a0b060108 79
    0x9140d801000410014100159005d5008100e4819100340c00e581e52074020255005492842c840d03000540b040c0100081031103046001414190030500740a00840007501303c0c41845406408480e517000010001e82c82421070300890380c1c000d4010f0100d8146582d080000e01040c0701c03240c4c8115040300001d894102a0b100b5584900d80568803c1d01c44819081882100048482e4000d614440007001c030000c20071500007140214031402c0e4042280c9407070306143c800c94880070b00403e40020207040030000268006803007a0445440f075127580d59041d8151080d24100b40050461f030203081c8000402c0206482c0360b01404502d401000907420070f400c00b111a10181c80220350138850540143e1008a0b15403150f40b032031102c0352103020f810520911986030709141400002045a0f6050740c080c00b46401c2209009041c01020300340d0381446641998125a6292003282040328051035000c10001c00302d03401040030600414603003020607020700e070303500748180c489a01d68001d45080340120007041c115445850b20a1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 113238246 1250 113236996 113236999
    0x606080f0309030706270e16080f16020c0a09060e060306010b0a12060305010e0c040b030f0705040b031606020d032027130209030c010203040509040303051e070503040b06040b 77
    0x20150506901b600c8509041c40007a011031045001494019180e17043c40000d0884000802ca5614089554a20400751440031608002a5109000d8055600410309400c13440302401c070790072640c0188003285028915007000741d2000140400044030781e81507100c10151542611000c01c0ba42d2284241035884c8401e110316a1441000c201c2e40f04001e10444042500e0081e1b81c1300496642d559031a243d095800e8a156401681c2001c80c03030708154a41480380b20081c1d40144c0107080d0707820410f03c495403079108502c2454091900c032000103013181d03004c1c82696081040c40d20503070512074031550020740d528440d94015010a01c1c207808100ca10911300c120803031403070a01150b5860000ca005e8900403d0071007881c075190400346025580260340d64000c0f1440070100325074005032103411a20030036280c911603d602d0750554200f0001480283c07981140d660340960036003404520f50715110031982c0c0500042110005411600c41404001a4410003d40c02180900c04005840d150b000c10801103882445085 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 113239496 1250 113238246 113238253
    0x3090604060c020703170a0315080709110f030112031107031e03020703050f0d023f09060301060e09090d050a0c0c05060309010b0907030506010504140f04090606080f030903 76
    0x250004505811103802c4070341c01d00c161804a5580d50703a4040303c1c41000039a80d0607040120b00c44c21b1803541482803c08222540450403019491314421548407001805449480c544640f4003040b01d440e014100c0725080310721a031180d0faa60b910881b500f21051000b00840008007030211710090f1003c00103c42090f02d070001843e1280720340341c00c0044008904160b0440540c0110140040410320510002c4440a00d02002c0c2c20748010104000381041c840302d0301507844031038000021510417196110b642080724802c29901060000c01c2d484007040c02405080d6500003400000451001c0d846501a445680159090052515444c030016294106440300d103000920901c08450454031600070550101d020300300f11096907071100085034540d801191484903588d143e900081007428600306c4242d00144600d02000745060040000b42a40320718032039a00385000d45a504290b039900e40030f587d8008000140100282c80c241d1030035801601d06482140368078080c42c1010303494407030080121180100014042d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 113240746 1250 113239496 113239501
    0xb0f03010501080a0f0507030501150c08040e0702120705070317160b10050301140108060c03090c130b0301020d0504020a08011e0c09120b010305010c090303020d0f0302160f11030102030906 83
    0x44a080300004e00c030040183e2580000b0340e41c50824071035140034005541e0701181070360406d4900301003211a40004401c01c20b2141500012607400c4e4143c4040d03a00c0300c850801c0a88030301d50100d1501c102840c001820960015005082004c00503205003100d118105110381200e560920001d80d014a6100882c01d101a5284c000090035112445074441c0e051040f820149440d500400e08582c0e075079903469210380c1d0710310051064070310800403e540900c9404c9007174954604000300d151101d12040c1a2805109801d0a5040d5080035800c0803d40d16000b40007151110401c844a9002d840265800d81c01500401c001107031035030707060003100070052071751080c1407d08142080320310092804480c1d0000300400c8050107d10f022050302581c94450085d61144076650450401c1400c4950340d020440a11105a0042002a0300400d0301001c0c0345a5003400411850075075000d401a00c90400d2006614a030a03902408021b045800c0c404068040e02d00ca018a2f1140802e040c200d11081e0b50305102c40c1d102400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 113241996 1250 113240746 113240749
    0x307030504021c240b0a0b090303040b0f0702010f050c0c011214190501120b0f04050c13060305010e031303080307110111030a23150f0a0e010e010b0f030105 69
    0x4103401038400307803556140f907901800d42064090504401c46041000d03410107505407000040b00b012840300140100400d12030403002404000300e034880d20382c21650110306841c143ea01402550000c01546034890354605030340c0703080006503200c02c4049012820300030040761803074854015034440f95208401461003480344401564500b00e00c0b00840c042c00d4850322850307081030761500341501840c482015560040d4010b40f2180c1614816000805580c2c00f000f0f5802c0411521055160401e06000300284540c495003441401e0000660066400101985036121480165070040044900800003008506100c25000380c882c800c60b0429070074000a00000d0010a40c030800560f0803020700c1c20961418050070107400c0c01d40d070080b208280b4804c0c02104000d0300306458014000200000508811000e014500b2104440d0015000360810650304000000c9919000e80c11048224010706e000140c9669010070700140009001c0d04821121510001a0904103d015240d160710003a0000b800c40c0e08100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 113243246 1250 113241996 113242001
    0x1060303200a11151905040e3405070b04050c0a0e090c10120606031a04090201121505060f0304060e0a1104150b1309060b0a02100504050f060a0506030d03090305030703 74
    0x190304c004a09010402482c1c2420030b20f83c5c03244d051109469954031545440c0c40b032403010307000410540d04460780c40c46102042078140c100c15180ca0201c5001c403101201040308417458020000010480c00201c414401400f00c0000c000c01000702c200c0d090a601a16280e04041c402c40c1520030320403980c02100245910b02c0c080f0f00c6034a0000340c503d042103103051411f01c400c0955285502000100f0383c1da883d0341c000d1014000c07890480481c00c2d507050000c0c02e01540002d110450b02d05200a141c0e5980d1095400001c081d41d0300001054014540c076225a0000d15040860307000751012183c9501c0c2c1140c884640d000880c01030b001f10340088554401507013000030310000d40303490340c2e44062404d4900d00100d43c074009203001d000ea03c0c00f040032414004e424990904119201d80c0c0004140c180188000e070f45a90780001d401c0405480b00c6008662a00c1da803418500c1c26a608104403040d00400c001c120006546d40d0003a440344400300e040300d031400e1229030309401310303005110040c0000318100009030300369001c1e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 113244496 1250 113243246 113243269
    0x6070e03151e0f061009030201020a020f13020403061401050102070b0a110304050901060c02040b0603060a030f05070504020c0d02070f0b071202120408030703120e0a0b0a0e01060303200a11 83
    0x1400103802c00c0d0301c121582a00382c00708543c16207041c50b20b81c0038084035080442165030380c128541400c9840506680000c4d65038081e400d4001d1140540e40c05040d00c0c1e0719035000c400e0302c10591100942d1039030f42364030702000a415480150341e050001000002820340c4000b40c2d440c01c039001d4a00a038940348207010120b03036401d0720044601341c0b44020040000c00d600d4801c0310318028695039603040d02d07111461040000761030085440c0c1d8400c820078410304c0255030320000c068007100e0303001160103505045441d201b810400079512042e40144003003000142d015020410b480e9140407079080d1845d250721004a40710890190003a030031251020300c00c3c800065407180803080e00056a0044442c00f6016041e80d8060b0b52098208801ea50004220741c6c08041e0800c000e12661807000c0420301200da12200c4c0ea81e03803000b1658002c0c000228600200d14000040d03448143e0a4100f00028040262242006030032014035080300c4031000321099a42c40c06150100d10b20a01c6684424103403081e1a900303042080d0640b0b072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 113245746 1250 113244496 113244511
    0x3040807020316030204051b04090f1b031d031806030702010e070b0c0d0c0203100c0c1505060901090b010f08060a0b040f2c010317121806070e0315 65
    0xc000c0c480142e070301004849040340300b001e00e03501c2c0365003948148019110b01521855080c0c410700180c080903104034081d03500340c8500d42000100d00c121101c050340500380d59626048200741051080c20700c07075455040070340242e020021600100100c85c20300d503524454a0701d5582c04007240c4015000a1420400840e04008288004138410343d05090550605c95140d010403200c0c2000031710985d0301315080c40705480f1b90865081602c08030007140c010a45951141c3c07002405103540d04c02e00004640100e0340e01d5000358000c030440d04003a41c2e200c2c0b0131004020559040380b04403503100000a80d0300c254021292001d00c181e4032444000b00400b02665000e40103001203074488160440803e841d000b10000c1d000400260548910b401c1c84c11144d01a05040c28000f020242100f0003900c400000d29040c10341100d501035070489a0071032080c02c401d094020041d03459000e9418900340700c80c02c91040b2002d000b95400000b611125110f640c001d45841c0031040b00150503800c00c1d0880e0038051051540c141d4001c16 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 113246996 1250 113245746 113245763
    0x2030f0f07080c030c062202010203030a0c030e061003020306010905040206180103110c060103020406080705010518150d09030e010306140d050319081603062301120203090312090c0a0303050304 85
    0xc10402941540c0081d4803e0405c1e40c45801002001c1841c8900040d100f00c64050182c6401d1140d00000d440e0b00c4000c1000c49000e441d0501800010300c00c0c0e000514416210045d20858203000100c00c9803043c0342d1205901c00d1040100100f545080c5210b11401540c0c024010352030005900300484483c440821841d05141c1c0c0c03440c8109280000d103000740400c0d82d0704400b03807030158150700c10042103840b40d03000b808030343e0700810081c05542d070081d0031a80b0f10ba401401102520411000140182c4401e0400211205001c80d94204100e03440e081030342018840d854290160b9007820044045881b588101031001c0a0b4122841d42410462002100c550040b401d4030b180c04d1100c0001e08800e82c189140c2e00001d1703400d804100d00401c0ca244002e4403080d20746018000b092500305103070b04450382c1142c001d110004e80c1a4501941c1e006800603903000c4840d0400755201c2c0f401c518123903103d0700042a1a100c0006000c0001c3c41c940002c141e00d09024002050180c8460540c0c84c03c0707a8a4000600844a409 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 113248246 1250 113246996 113247007
    0x30c2203020301060611010e0606060f070f12050a02010b0102010c1d010c140f150708010306050910090803061e03070306020703122c010e0d08070311030c031602030f0f0708 76
    0x80b0280901000b034100b5854040b000d1590000060869a40b5807100340160002170500115669910880c0d81042c054001c2030345628081c2001618241c0c0198010005a02c5848042c002a0000080c10301ca010640081100178400c80040e42610200c1000e103000400004480d4445600c004414001100c185080039020480b41d881c000c0590a04180d10380c550300a22203004401410000c40c006d0a40c4001e1076001c43c10105405804903106020060400c3c0e00d5400207542400c08012106003003030100400d0120340000d08140c03415520503948a070049087d82e80c05000c240c9030819004160300050001d200043c99500e40000940084004808215407a8214007003902103000e2194140a40785040b68480035a034080e0801c0b10044130407800c1a414140c030b41615280c01300b80d0454400c15800c050310240d40d908811402003252120701091030f9000300c14440c0c180980d001851107006440c0d0488900b52084600b680e9a00070418030f000304000420904036241581800303481d196207e001000d0400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 113249496 1250 113248246 113248249
    0x30e160501140904240b040b030a0c05091c170c060f07030e030d050702010c08190b031002070501060e0702030310060507030302090406030f02090a050c070308090a0212150a02030c220302 82
    0x4507001000104800c5840d101001715280c2c801400c0010010603401c50b281a141030b41480c42400002c02c00800256170391555084940207108964400d20300600c0d01002d24100210300b00b1200f000b10003500c41000a852051007147c0d60b8040b240d8000807500186565910340c1075041d8400d40080250041544541281044401c20409400c0d03042115201040c145801c0c1c0d0001c0c21a644000c04504021003074052240100b907a2804021a00c4040c03c04a80b49400c10082850304078402d5070b0100d90f520009007401486819401b107000d075190a21000d4041e255101c0481e580e00050f908521614490b081c1040010300400c001c1100600c039050141c289070710000010211442c07a0b10664100c403820f50303003104500d000d900b0b550f8014444001040705041c65001981c05000d040700080601c101c1202140712260200186450f4950050407020540c48180070251144030404800d451440321001042400c03403123009492160003807101c1d80d070901509542100800341e1460404180081402020025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 113250746 1250 113249496 113249501
    0x7080307080307120519050a09140708010e0c21070b0310060206060a0b03060609060d0504051c08040b0402130f1b021e1005040c08030a02010903030e160501140904 72
    0x114040d090542c2c4910380510050f000c0200c100d100b1002915000410a180e048046916000244004009a685ea40c0c410a0b002003004841c0600140c010800380c4d548503200061041c02e9808260092040490287d0395541e503a1350a00c00e0f590100710405540c0310003c0d41c00c1555000942c600031034240b1540e4280515140e84203645a20042076050b4040c00203c1d0100107150700040c003a03408101151030000011035501001e0840707489030318001401d00c802c0e61a9010b9074125a900301e000c005a040034036000d60f9400152014043ca10041030b14168180e00590060307110300e03003000c00085c0c25503480d42004803240c1d0a2b18001c0c0c605a880fa07912940c0700d010710800c207450048682040c1641080d40c0060718001c2e882d1901020355101c00090000b0303000c04941103c025081c1d91000c226030b00c50385000e8203507410725040001584400304401800ca41d0540101d40200d0084e10104100e0038103038010345d2a070201e6554000405000142080f0702e51141012103550420b044800f4100b45160000806 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 113251996 1250 113250746 113250757
    0x3040f0f03050403020114030f0a0e250503010506150403080904110a0207180608071a0705030a0f17010521010e120301050306070503010e070507032313090c05160203070803 76
    0x500103d0140704558218012985a0b070840450b503043d407a000400f0895501c0051200d072009440303041c0b4011103641000800c4103400440079401e031454007503200400042d5540304040c8258240004503001d0b04101d86403a598004203040b10345041c2c25038a44100b02e0740844100e0b6041541da00d04a2007070004580036000482c495400340ca0040d141c0003190000b44014402c90b4980b070f203803030410801c070000015480103c034076126104802e40d000f00c000010360300a500024210b03004c000349001c1d40503400000300c8440b940c01d444089041d210108908502d19003402071903000483c2510b07a8483e8840a41e40c45541c90303c00c000802c0901e51001d489041484007202688945004001880507182c10300103260701030b85504e415070039580742c0328805201e4080505180709114001030354500303052051071003001c8140c000740340810700e8018919622a07580710011031a0000350502000c00e80c103c250103000030001044c1d860074200003190a41d64800c3c244210201d9051040e204002010b003c14405040b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 113253246 1250 113251996 113252003
    0x80702120c15070809030d0b060903060108150106090509041b030c060c0201080a05070915030f021303060f050c1803070e041110080106020a03050c100e160803030609010b03040f0f 79
    0x20340a000c2c1148011100c01c06442001400155001c00409020000940d00750400609010441d0f0300c1202c08a401881200c40c4c00d41c01d40180c20011808d02030000b500314100c0e040815204060383e890704202c0300c0c3c010303501900d5031001405e00460301090b09003503030810700d110400c1d000780803550744d90b80c1c011f000c0c440303500c400c006c902010646415980c110340c805600490004061001c2d16001000a00c011081e01581c100203240685c501c4810b4440e40c050692038814080031940d40001406000a014252008981b110b003000da07801d80600c0c2500556000d00c05000605003000400e80f48940c480800d0610f186e05031144940028a428803240c09602442c00b4401c03444694444070309002106101c0c103260014824a0b50042004a5000603202030a980501d0056107c680d40000c0b03a0a29050802c0d80051a040100b0002140741c041800340340448807541480c00b05940f003079030320f450380001c41e5201d5108009034010002280030760000d41d1300500ca1901d29500204a03605d064880c20f01c040b003507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 113254496 1250 113253246 113253253
    0x50c13060306051003090807021c05153310050d06090b040e0d0f0c060207050d080105090106030605030c0d060204030203030f090a050607080a110c030d0203032e0303080702120c 78
    0xc10072420804420800d1611603d01400b10151b1501d50381440d00c02e000e0002d000c2d024580c41c030100d41102401e0801003a130300c142503801c000e000e000c0712020408265040043d42c058089510085a06501800d0300c8004044c85020260765050800c000011025050418807100300009a0114890701c07542004d4a0003000c0002d031a4070000520044604134410f400180c0c0c0440c1c07607070b2a181e4101146554000641c0f42c24140c2c104d9070710300600039000703118000308a40710700201100b402c1d8000c0006816250182c0c0c030f402c00b40c4e90303c960072000c0d2805403051f260160412047c1460030b0900d00e42e0b030890b250083c2c10240c83c096407175001c249550b020900d03840e20907001240b107038801c0c94540d5031f2200418044403694205040c64503445001d01c601e08004040c40000e00b40c01c1c1205005008078921554010151444c15000c10406901c1b40d01c01c443c4141d103c4855203120440c0390403a0030304041c84004a02220f015400c55600390340043c0e0150031141540306104c000034940e01260f000f03004c03210340980613 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 113255746 1250 113254496 113254499
    0x40207050303100f0513051003140a03110610050d02032e0e03071e05070b04090207021f020d140f04030c14090403210e15220b0703050c13060306 64
    0x82c0c80c260a03250000341c44001308210030000341c0d4981580c2041aa0075080004060321010070082d16240f030b5a2004001032580403d8041c0d182c2c01181d40c2003194001d481d003110881c481100305865038400c841f00001b0068007241880207060141e000c0c110284080c003103035003002a495400588a03a00c2850742e0300c10109048603481640180110304a0056950065040410035580e000012142142c0c2c04090807400c4642028003e0401c0260003c04080c588107a603940c039001031801a600c101d105030b010b02c00196940e0340040481c1c0100081d00c055a01900e40c0c3d46850508031150241c1e40f1200f0540301d800c2c0000c455248000000700b0042d4820f6815803802c42c030b000b5507c06418080008948102c24800800020039003220b29a03240d48100064541140c280e210700d82d0080c02c1c4101c00000c1c52049074070301c400d441c8210f9603e43c00340000300c20881800c2c1c49031819880070800f940000f00400c0425021911450094010710380090307004a0721820120309105082034404980d1180340003a840710300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 113256996 1250 113255746 113255761
    0x3030d230a0618060312030504060216060f0e03121f080607020c0406090b01020709020d02040b03150f060c12030604180c0e062b1b030809041116030f0e040207050303 73
    0x111076040c2c505481401441c0c550b499446d000c0103048140018103440700009420000660b046840b022b402c400e2190440840b82090350081000e4103541710103a2410105041061000060320225041c002c2240040c0d6030b00c0360000400f0320f50041c40041820801c40205500b402440098840c910560080031209014010031003941d40743c0c0d0280368403e2070490306c1c0285990100e030040540d01d81c1c000c00b40c1c0c0d981c0406071140081c403e5038809050321710080248590382c1d19a442c0d0b0720960070120388a01c2e042000104000613445004e42510040d4400d020a2840c1b145040c080c503441704000b000001d010095a900075200c10040804544050641c8801d000070139001312301641103032041d1280e001d89001991200e00152071003014041c04090450b0900c1040000a01f609091b17901c84543c04403965680b81c0070650780c0240d46013038810707070600205000b0b00010300140d4221103a200000c001f141c40303075181526181c1661810904124151010940301c0d20740d40020310700d444c070a800443d0f0340d140a08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 113258246 1250 113256996 113257019
    0xa0e12060f0601050702100804052d010c020303010b03220605010914070908070b030a0b0303190207050303070308060d0302010e16060305010803070201021203091f05160c0203030d230a06 82
    0x300b0715070500c0340602101c409a01d8080345c5d154802c0d034504240c1d155031581d08100c1e14141c00e8021104441c20a03200101403404040154115032506c040240400c004100003aa100e000900502e6004401400040e08524181420040070141c81c2c010314822010313030700d0f21030035550f00740c100210f559103450700321101007030311a2103a600000d00d1034000c20f544d00b040e02c06a00c60300d5920520442610200c0400c0e40740c862903100c90b01d60f41000301141e5403164002200313048084140c00e200050301030540c0000351824088101e90315650b041e902d4040c0360f5a0a4100407424144010503421507503100a090915135040100303000070107070342420161140c9414001815600143c1107507410b504144091401030b600002c0c5150305442112605440c1d680d903404503440c060402594203c003070703411070004c45d44035619484940200200d490392642840404c005445046020000a4050703004021610b4020210b51000580c458401e8240003040080c0c1030f03c0383c0d1540c040d6500d01010ba0344240070405203800030f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 113259496 1250 113258246 113258251
    0x50709030b0618011802090a1401110318060c0c030106061d03032a2103071e0f120b04050405031201082a120d02070f061d060a0e12060f 60
    0x1c035200421076146038150310f030320b00041c0318403004c15520025103203050786543c050710403c1d600940303098080307541e95600c4031200038180546400304a08004110140c80d01004441012200c01031749100e280c9501c052000303650110007001c000e40120610328031a0354003030103190002d003141d40d140018442d000d00c0e0403604080440312140709038010880d000d000c180c0001100d4010903c903a0b1803140218614106003008035240a400b180803a02c1c0105c0e003d43c9081010f58043c507030300d55a200f00d07400a42c3c0704201c0c001340501c00d1404500c1880c000403c00d407296101100c0040c0070800030038150035100204080d01c00644081358181c1011a00c801c0b20041701c05c1d07083c0144415001402140380050000d522406844e6803040d40181d20702220b030568890705d007010ba01280c0703101288c803200c00e1448000e4603984075000b400d0351745280801c0080c400e071065102d9000d85c112190002955081d00007005015400100706005002010410034004c0e6100201545040203003000b82c1000c0c41c02040e01e00641c01d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 113260746 1250 113259496 113259499
    0x30306090c02071206020c0d0203070b010603061413021b0f010b0108010b120a14040302010e0d0f020d0e03010e0d1805041b050a1116051809030909070909050709030b06 74
    0x180202021010b82c0082d20310304544054400c510660440d040c00006071040103201d6034644941c06481a08550020007002d00502400d010361481c0d80310803040341500c0e038504c5450b00b4888400341c40842031030f049c03e510b07100284e1604018074050256200c1c0d0800814282c404000c1c0d00a40380c0c41242c03a40a0158596405007460100095810305146c1d035002c1c001d03020550320090b064000200d16280540c007070300c0c02006007034080d40f00f46060314001b4083c0040561010050080b524000c044600030601041c0c9e14040341c001e4540700181100c00c0b607400a00026441d415921340c046402c0ca584140400e0341c40c80601d0ba03491a29800b44917840c10240c0444c0d020030700540c605039105440250728030341c1c4803a41441d840e256907582d510481c11140750040d032076280b480d80110031410303801d01c42409200c82110400e489664110b402d03a0b8101031020300031681060030740c02c104500e036402d02d01299440d41c80759641c20035107141902c0706035a00c11107108079450f40100b403d001091080c080040c00a40c2d12100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 113261996 1250 113260746 113260751
    0x501121406061518031506030d0e0112020702190602030c07170c010c050c090c09010e0105090303070f080408030309031c0b0a0e07090b0f07020429010f0302040314060403030609 78
    0x400c1c40200b10020f036006003010081c41d01003005038501d1001d00c500e8000000003421505185002a0f864079060741c16541035200c0c0c460301c101400300d2405101182002e0700140c46044004c1104c0310313807130040c8d804014100e80c000c907000100722341d51920010320b00180800f6030080d910b624540d440036207000b0254111702d41f04070080030010030051000412044050080c030301900502c92501d13106191400003041c4540c45900b40040000c10b0141001400030744100340d03511a4004c0713662006450b28400e2005041d00b5404c20001a008038501a801c908172034400e0310600e02d030980d940c190750300319001a9805a03094000041c1041d6101e800c0c070309500300e41c00380881006a20340c0e540c001501c14189100750240904801c00054403140101e4001004010182030a540c03070801c00d0700e003c901e500c5104100d11662a10401100b4992145072205a44086080c2c072407042003185c006503a0050312500c1c1208168081002000080c00882040304140c0e10100401e950b0a00c1d2502909486260708029145803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 113263246 1250 113261996 113262001
    0x405010f150507030e040903030e0606220b01020f03270609011e050c0f010609060b0c060c0322030305091e03220902070b0106110703080901110708010501121406 71
    0x14458110454040d22030802d10354505081c5010ba0301c241507080855072280c44d00040406040d010f42020ba0300c2c0384003000b41c8003140e0f00c1d8000c00c10f007160600c1c83c4801021899882d40311408090340400b460f040140100d50201ca5a40f040d03510b50741c00142d043d06a004000001040180343d01e544040007482220401d08220601c00024a4254010400e4079401c1c1447c00442140e07000c1d600701c9045103440343c1640c001d5014004000d0103046035105000d80f0514003e40002c204160b50251011108a40050034a58403894802845c80c1c0010b49000790307880030040e0181d80980c0321170110399000c0c0320361030204491400b0040c4a003010010640391441e00d440341c01c0740403d140702108482c0c2003001c50b00d2840c800d182d44040c0781c50b002d41030f811103240540300040020500c0701c01000c840c100c855560741c6a4501a51005003515460b440c840142852814400358030ba660042c3c60705592003141038100e07058a44e4030402203094840c01ea0024014174a80186803003400080168034640da00c1560007000c450 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 113264496 1250 113263246 113263259
    0x120301140103050a09050726010219050d0f02030a0e0c030a050303070309150c0819061805130213020a031109090112050a0c0609090b010206071d041503060b0405010f 73
    0x2000c040390040e0425688a0001d81c045903039a01a000c8940c02000311014281c0790f0601882c003886407248803201e4885c0d89000410081e0500131a000401c1002400300240042c44090b121a00406520f440c2c2e50380f580c20f07880c601c0881d48050352003005501c0012605403038502ca50ba041048124025000b0341024099402240c000800c4079001341d414035000440f00d0083c03d00300c803202c0240c8088202e2608000c0c0b40104035038080ca0103401a8809604d200e10987c41544c0c0c407044400600c20501140ca15040242c1c03484083c0d442941d000c245501c07041d028200c1640014000201d05101a05a590104400160750750500c600451810b80c10001c03842d0403203020000b40000d4051140c8251440142d0014003080350911203402c0440e80b1800300c0c00c01e0f988078036002e800c1d045640119003500745029442d1030700b58400184140102050340b5540c2c050198000c2c0880305501100406402a8881d80c80c503c07003401100e042c00046004080002c0e407621828100000d4410603030142012a46035942070064 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 113265746 1250 113264496 113264519
    0x7020c0a0506070309170703050a060c080f04030c06050c090324010b0c0c130b1906020d0503041208180d020a1109071b0c050405090303070f050c0304060c05010f1508120301 76
    0x165051100c1600d6446c0000100c40c1c503205550b04020304030b015400c0300d88100a0aa0007001e105022629603000c40c0c1d540484403070b4001400c44024000807500c00c0031202080040e8811a0012880000d186c84c201001020a182a070080500f03000207030060710702c0c40407064101580307000d440c1111485203800e4988020a5544150603900c41c4522440d511000f80c040d419800304000520140c807890090b03104611100c0c03940306601c034810260113410350a0f1559885001103901c210741c1702d5081c0f00c400007101021182c1c084020841c944424019620048840003000301c501510b8050f03004000362000c52038211426030385400124081e681c0d45050046454000c00e01c01c003080ea0301d8103201c0400031541040100290700f5441139070024608014442544404802144192401e460314041c103580e800003100e8601c42d080070a142500280300500c0450b21508000418500420010030b00c0d4614598100845481052400c0403100c00001003101940a016101000e9207491505065600d40270040c1070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 113266996 1250 113265746 113265749
    0x30f1a0c0d05100e01030803070e04150909020a0b0423060c0c01080408120406060305010509060103031d040e0f010204150f05090d051009060f0e0106120204051b0307020c0a0506070309 81
    0x640d5500c980c00038265580d6007a207640241301c0c80d0400103c65941e41001e0b2116442034512600090750141d44c6031079400d03e401142c007030076050150101a5454042160014042c0120490b44108281d00004105110394042c001900138915503c45482e45402c1c5090304c141460000e030300501007441318030480040400c2d10303a020642800c042d401550303289040710740340c4100007014442400d09402e100034480d0360750101080d60700c604000c00203601c2e5881003e41d0345070240310040021b0301d2400b4049c0030400e80c40c26501501ca02400100b10700217099449030420940980031075441c0e40c00302d0100100c1ca110480c0520605050600d0710180850303a200401612603144020700a00d014410b003c2000010080c2c201c440c4d50401d802c0103190014500000030301b0b107002651054600703010b03180c10203e8044c4109000c540c42c01030b260318003410316030921016100040c0700d42d92000c0750b1003203844061010700055104100d0742d4050719501000380104218582c0d00e40009000d40806c3c45480006034121a0000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 113268246 1250 113266996 113267017
    0x120f011805070b0307021608060406060506070b150301090510050601270506070f12020703030801090c0206060f120d11070b090303090f04060906030c050a0e220c0b0301030f1a0c 78
    0x160b881d030b0b60702d07406d038076011030003401c0c031a10b1884c450f0005003010045145401035100b80700c01d200302a512010800b00c0d0081c00c402030b0611003a200404c0a9541650588200704800f400110706080c49850701401c003e0700d0702100240e640c42d40200403040d1b9001c2c0f0386c0d03d010b42c252200f161911003484a610742c81ca000b0300a444c000c0d50001340742c10601070604006c944041c2d00c01c0070f85001510f1303035000946030380071441708a001c21140b00021a14800f0350196000744046c46c0c0c018003241c0e884204000c40d54140600c1d4075000751074240207000e4044188800445044141c6843d40400b604c0144989044542c1e44500d0030310320203103c007003103d64010003104c4640200b221014180c0100720009001130013070740d000c1c0c150146007010020412203107564260458030308580004042da80c982000c245040111102d06507802c1d44815403070302c070500720040344003c0d0081681c0c414003500e94020780c006500a030800c1c0e4100b0600c0c005182000300400900400c441c810900014608001100344143d014900c00e60 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 113269496 1250 113268246 113268269
    0xb01060c110904080901030c0509030309010305180708070e060f15030709080d0e030c1203090909120307111c020309010c031e0c0218041709060702120f01180507 71
    0x40003404400e0741444a0848018110003041c107181c603041c0045e92244807070501080c104003026081724004c00c243da50724000a005580340c40c0103500110010172000f45514403100c5103c41580380e1103020401c41d0090709180700148006400c000d042030a40c640107208620920442d10090310545403010f40100195040344215200d468090080e1810000d0350040c803080e00ca064003010400b9030018920391458400d9003650341c007031844010300c10070500f4851262016801001524010b040100605500c03201001c195101d61403c2380307010115a000b500c0090004000600389040703142c06204403005001004000754100c020114081e40302e000e0301d80300e241405140342c0505c051502a0340755010181100401d40d01c0c0d800e600802a214003140d86040c0d000b403010207818030300721a1500d80c10740641d4020100280b042203041101803903501c1646010b41100381400502d0058940c0c1ca0040c56584284010708618081c035002c481c03c40da40d40d50440c0c2d0400300c0503120b00100d080454080305030344045840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 113270746 1250 113269496 113269517
    0x8040630020c0f061f050114090904030912030906090b130314010f051e0106090602060114011731030c06150305031201030b070c0809010309050c040e01020c0114040b0106 75
    0x4907080240c1d400a0f0450741c09120308124a003407450084000c0302c0344a000300c05a440e212001100d8080c050800340c017070f41c1c50800645410340741c451142c1d58041e03ca4031b818102c1544071902411416070000702100861100c0b8810300480e904480141c01400035100600e041c41c0c2900c000010340d242c1c070b110251100c1c0c0c0f4101e11500040080d0881070403840004030500c0141026003510010340d11140c910b4901c00608400410280d02c101d600302c04564441c1e004020790303403d11048147d100380c0003180c6418091807000c0c45e8600f000c0c5d201d0300b510400321059002082d408050030076250f046002c81e10000c0d00011498080029084509003075020b412900c00500f043d518103100c0b07486c030055000682244804070b001442c41c9883c032101816684039000007801b03611102401e4808003003114008258100034042c45e00f41c0d5100e6031111800703e014404880c81843c0c40e40100c0d00715a500031100d0866500001c110074403060034050030490f61045019881240b810303448035480f01030103008000401c1401e649 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 113271996 1250 113270746 113270767
    0x10020a120504120b01080d050301060f08090a1703041a060d140106080a12030f0504030e040e01060f0b0c060618160504030516150206061302090a030804030804063002 73
    0x782c80c054500c3c96018200000f09080c2000c91020902c2100214400ea16062114611070000e880c103d88280e141e58100341d10034142a80c800f0700041c480301003840340b14448408500240c030f078800c20100700042d0310380d24242070802c2601003480f04100b150f9600c1d82d000748101c50f290800b00c1081980c100c0240003115517001111400360403280c1c4000c08600c140c3c00f01005001d00820034a1446072a0b0f01e00f04090082846104140c640884019000c22a201c9500345a400e280c2c00010a08801100008416403a4008da040088058001440f884400308681502040400103940c20013411521501d0480d20b03454010326921005144c02d103000c8404405103010340c0143d0a64024550100c16207910701a0405507050284852261864031000e4454910409002041d0709000308000350481060b541600203d101035031003642030315000654268004041071005015001451107600400d5840b0711300440113100c000383c0702000300407031a03011b407000c0c0700c16148006500040741c021000da01d4420081 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 113273246 1250 113271996 113272007
    0x41e0905160303020304060810080a03141e0307020d02070b0d0c021c0309020a06030e12091504030f06050619050405070e04020d06050108070302070f020f0a0b0f0a03050610020a12 79
    0xe07008110540e25480c080101038010000c0c00541d141d517550448980d0304c440300740c00c0d40c117824815400250080072580c0c011a12a0401d2086612a002840c1c80c1a9408081c0c43d02e0000b01d507a0049030540100c00d2062983e814044480d104103244010300095080c100d021095206d610301a100280c0c0d509610141d160003031054607000040f20018a00049080101401500405ca0b040b8819100c584011640901a206482c1a85040c0300280160051039001c000240d021001d03a42c0d100c0c0400d25101c25180101008002a501c60400c00c0810007161a01500b03903a0080d0a441c030410380303101c03108448c003a00006c10040343c42c2210081002c1c0c841c0c02007a41e2825401205540041c0002a80446d00c042034100a0860302d00f81d950071207558885104804034050340c117000700615100300d100d1001d4a801d004503194044010800081c1c15950000d50305994841070f0740313211140000c1713102010b841e054030030640c0c802401c0c2c80c0031100c5901600c0007515500352140042c503200002d01d10010303851140d07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 113274496 1250 113273246 113273263
    0x1106010e060d080301060201020403030f05040e1807080f0a0b061f0f0314010b07050c010e01120207060b0405040b090601050f18090a06021602040510030f020907051303110906041e0905 81
    0xa48090740c4e07540c440100a01070b6000740015008900508480c1d03401900c240b080b10100e41005004100c1920380c02c1d001c0807640030b0141141954400c0080c08110700500307108000090200c60700800312a1201e1034084008000104600e00c2042d4038585030b06010f0500e4101d6034071130341c0d61406092a803004c4034141c0081801240248074041100c0010842540c0a4010510203000f00d0071122042e60752801101c07140c0c00301200d2400211030310000413400c95286c0241101d03d01c2b412022030190b0105000c9002c5941c11101070700c1c030004240c1408807400040c04014050300c4244c5410401903c03140210302c144201800240110603002c0c001003014105002d1030761071a0740840301b555107409032080318182c40e080348001c0c0c0c030132442c21001c101c0803904461501c0c2125441400da000c0f04020307808000003034038002c243c4814020300b00f10600a48420301c182c413001d5407144080d0300c00d902940b420700140580003001d00e400f9500d003214400c415105944140d1400c2100d180120781460b01c5e240c0340d030a09005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 113275746 1250 113274496 113274503
    0x17031806070f3f091802040e072102030402030309132406020705030a050a0303050601020a08030f0f06040c081501050903030309031806130302040c090b1b010c1106010e060d 76
    0x70003c0d49981400e0706a1850f440c407a0040101400e1401042c1074030411901c0c10300d040101307a240d00c3c100150300410301d0030301d081e003074202006007026a41c0382c002c44000c03800c4800030f00044541c00c8600a0021045118051040741c01c0c045056141c02d5020039901c1c8121000c0d2440f40d025880607226014083d0440860301034400030b214a04c48698002844200c10b90266001500485402142500700012001c4c5140c0d0000c00174502c80c4480e4801740c0c01820064981c1d411401a5104680842c0c440030055009001c0c010725002700b4541120940003888028180d948514144603240c250503074085c0800d6040081d11b00b0640b003d1301d86000503200f03486005107168040c00044200056140044088e00802d860b00300082d000103102800c00013584142d10b0a400c65842c625810b0000d42466840050300345103e06040340c0759503c801101c0069006581786482c100408040910680801e0054a450b02c0641c03c01d8480b280c589011a0b860345814040d40350403403110300000e66a40d0700c2c01c80410001da00b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 113276996 1250 113275746 113275763
    0x2061812010506040c020f10090c0e0103030f08070311180a090c05090418031e0c0804120302150105100509060708030f0f1e01090203040f0c06050417031806070f 71
    0xd1054080d010b00001c8035602e20030352914050202d102d002165108203040008050000c500c0300051110040091607401e481c000c071041004180b0b01c0c0c540030070364041d6001c3d4403080e441d6043c3c0c1000502034000103000e034082500b00703182c00c1201324080058562512106082c1032861031034a0120381c194075140e02942c011030400107254103568100340248001a82540c00f0b104011001c080a0000f0780040c800400182d40c15619011620f4002000481c0c0c0781c0a141040c12008c0540300c4010030340094000014a5030070380d00d51301c01c043d010402140100c28604840c021585481e0001b0724030341002c08034505100740042c44001941c2c0301d01c11a55401d521441c803503100d0901107000b06007000f04075450140d958140001c01d0741004280c000e4640c0c1c41c10280783d400d035a030801920002131340002e04222a8061103203150307000038800381a0714000d4540c90340c80301c1d102d03498040946d0400c000d45180d025641c1042000ca280070401d03400c604904042510150354030b03070076494904c50303d100d1580c0146c45401d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 113278246 1250 113276996 113277019
    0x31602130b1c0c08030c0c060307030905060c0a1805010f0c02010e0a0905010f120c05040b18040303020a120b1818010603061406030c0d14010905150402150313020618 73
    0x71075030121162501c2c000d2501c3c00440752200c1455982e84034441c0c80c807040b680400c0d0181068074201005507481011807030082480081aa520752520109868810340d640f404900e52900c030754001c0c0254009442181e00c14107480ca40000641038101c8165440100442c800a500559002c0c078107810310804060481c17a14146d4a14820006140c00e01070544800155040006e21a000e40d80c0c040049411400303108607589802c04220040540580040d04408281204900e0307205501456201d94000e480141e5251a15040200010008100001e1541c075107080811952a10240300340410340002d00c400d215210031411130b515555050440e000e030341c01d00c03001204006586e081064000251070241da03081d11038404040d103880e1600c04642c6c2042c0400d24080106450906c4810311590880002450348801c1c0c540a050190690b031361040481c031780342444110304040458440b03c0c42501500c40c1107080246802c09894001c03080a4403070300001c2806000a908030510031500c920080100d441e41 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 113279496 1250 113278246 113278279
    0x50f15130c032d050c03070503061c050a0605250c06020d0b0303040b09040f090827030d0e0a050603070f0c0204020d0e0606040509030f090103020d0f0c1205010602031602130b 77
    0x800349400400f0507a04001c041036080141e07006980c00b07050b140c0c0310709003103a60b40014020420030340440b11010b23230110914400803980a02507045aa4010040800c1e1840c1c41c81501c9081071002a00c403596800e018100940c0c0313540480c0d50149250310140c0941d071030300c078200c011000e00500006030703602d80030008002440c10f403248020540c29505480510607080d040001c03000700c40c110035002c4c1a250b030402440d4040d102080403500042007000320501076940150100317240c200481c03032810108040810b0302c030b80361170210f5018000703160440d0b50728038619103a1401003103804844481d000b84805007501c5021507035150190307042d50071007070310070084821885a4140c0d02c2d501551868012480c20000c2410b0300c42c00f00071151012481c100c01380c54201013000440007035001100e40490a0358070600a994021640034201e038070799195880304a620700c580ca40e030f000c45106a1141c800d540c0200810000c0d61007100c03018404035011a01c0201c0920041000000342401400050b03008144084500e5131 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 113280746 1250 113279496 113279561
    0x1407020d0206031602010b0402070c0b070609200301050c0f07120504270b030109020105030c1e210702030a0801150c060e0f0c0a0506030f1305030d050f15130c03 71
    0x135500c907900034046400c3c51000e0000301d200302e00000e021940d170408280480d80c00e00740100390080c03241000003103600694030703000d02818910081038000d02021819008618003409003e4200400f159100d02c1c022030764181100521401400a000e00c99070030784480000c2c01041950300503d188451030304040b504140041001c6921001034000620344086a80c0d20f00b0305104401a20707a042c6c58a030b00c0c603100e0100401c40ca0304a00035080d540d400c600440040210240007034015105880c001035048090b800380d2080009008084008560050117412890340c1c1c041c144c241100c1c0c4500d201551010351309003c495018050300060710792410100c400181e0f4100160410080c690302c41501c2516034040c0030400c0c64602072040701d45c400d1003800464281f240c1c1c807060f150000046d082004070450306030b82d003c0c110342108402c2007240342d9a000b0048850801d04c01e031a40b00011059082050900c1c0e4002011208003c1030320b14030307550310136507180018000c0d0310141100d02c2c150804854025004440f14a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 113281996 1250 113280746 113280781
    0x70308010e040c030311120f09030d210203040218070918060b0d0f092103060e040f0f0501061a04080d11100218040c0503160f1407020d020603 63
    0x55458400000c0d2114007088090040364400010351149140d510202d46811068107a084140114849221103c1503030005200207100d250b9490386542c05402018180428139102c01c0510000620b01c510381b201000c40008180340f50040103072603407140e0000c81c0c401030100c41c006808014030b4080c40307580c94105442600b1541c0402203c841d031500f4410034001d442007840b6410101005120310702d058202c6400c00c51a02d050400c0005506540780c413100c0c0c2c030444c5800c449440360128241c5880c0660b060154101408540860462608003540d60038101381d1040400750a001110602008020084d08403000911070310070000e0782100b43c0c0c0c089400a42c07040c0f00d60202d510465414480c2c40d80514422040d00e00420040c10740c184003ca5100d000e0750240d0540f04803482a80b03c0700c0360b15519031061f0402c440c00b6503125a240d16010103c0c102100c070088805050204544800c501558070000002c1090713810f40d400c031385815403031011a00d141c0940760000e50002000c0308204060310814180311 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 113283246 1250 113281996 113282003
    0xf0e060f011b020d02030c0a0b04231f0e10030c120513020d0c1505040501020c0d1106070c03020301060303020f0715050304020603091006080106050f2d0307150507 72
    0x16003540c80880103445008079500b5990040404112820141c9401e80843c8041c034005001e566800210074001640413040360803198144101050034007044420381045480039011041c422000c900340340014501c8103004100c1c00008805c01c514482003403196040504014000c2c01445801e2006076029018001e10f01ca880f001444544603d1552a240d014041c0280034441c1c0d00903112030035409024424100d0b400682d0200d085000c000741c40610140f5002c80c0c2c142e40d81d40c1c2c40d222818031300024182045034204a106088404010012520120b22140304242c00c55200380da4414038900b10303815861961003e5815464048008189a0003058210200b92050180e64285071111440c0c1800f00c0e00c03443ca640001e03400e00c0060014101100190b8101c440242210030709141c041e6403800f80d803030b42e4010000e80e0b51140020082420000903500d1080c0c01203a141054400e25040c0440c00303030084500c44041c54206030031007142c3d1010300140d80070307201110f4014294002d07043c010b05190b22050088 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 113284496 1250 113283246 113283259
    0x3060209030d18061412010806040b06240a03060503070b03010603060b0a080106050703050d05090f0f0102040803030604022809030b070f02060708060a0807030302160503010c1b0302070f0e06 84
    0x1960414070440f1032282c00700c4003003c490003003403e000c011070b07441110a4003440c1c070190411650b8584560285014003d0404000a00d2240340620701405e10000c00b41c240d0303010304040100500001411110480e8520900100ca0789548025404130042c00300c9a12032601130242250104d14040e5031002181a180d040d2818440b040d600c45561805114801045c000254003000520016100314020a04c25010340752182c00d01000d50740f4002204c9041d2103540a80c0e00c0a003d41164200900c1800d072124141c04c000c43c2030500d40000301347c4907c0018812440b996000610303085500d00183c007043e00104d0040b440d00d140c08040400750070420507001c1580d40440000005295910804c1302988a100c2c0781e0241031a601e0b043d40a9070001c0c0c000e440311760b01c4041c044c0041060201040080300a40c0a9802001c0e00d000f91650760350001c2d090b82005000342d0501441184c465007041002c07104580a0f1140314400c403050904a0801c001c5400c05450500c10b00000140035440d105028000c1d08100c1e4071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 113285746 1250 113284496 113284513
    0x60102070b2217061f03080301080109120e01020a1e05010203070206220c091805030f071a060a0e070e06030a0f0c030506130e0703060f05040302071203090b0309010e070306020903 79
    0x40310b002c1c07214021106004d42c801400508000b0b040904012480640442da100c0b1917180c1c1da0b1060542c00036000f91003145c0d50348291505010b070244d110b0070b0305c20300d0703041c00240c0880c810300003034891481a5026240380488a05144080103500042003240c3d0004000c54076800c0c080700c0251200c0c1c058680c468806040b13000545940e0801031000800b5901c0b00384000000e1500c070025024024400342510081c000e41142001b140c000c0c0024500c428401901d03658030300c4103103050003502c18101782c54141a500c9030100700c40c40d190184244107035001015241965aa0b10100b00c6840803807080781d54018001000340b01000d41260480a01e081c10b020050204a10019040b0101c0b001140e040d075104050318101d610908560b0b0101c0d0b05451410103a403502903da860318000d490302443e960010390b98480800080c15130503c00480a80b82903107414100752000e0314010700c140101d014140c0c1120000001c200c940f1401d42c0180040303d4402e080e40c01c039542e40d0802400a4112500070b600a0017032500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 113286996 1250 113285746 113285759
    0x1202130302032e091a0703150902031302010e031006030b06042406050d060b2d030f041b03050604060c030605040605011209051501030b0702010c14090405060102070b22 74
    0x81080030b010188110b502103420101c0000303064a80e1080d00c060ba4404044100b03001c1c806071840c4103011903200032400302482c000082184142703522208030b00b0310600c14410f03000101134940c51580e80901c0c041440804800c00030781010110303501600054034043c8000100010400c403d480b0780700c2110b0802450f40d04803000008d411785047d041001c1260000240804d078051006401804001030002502684030861750505500612942d01c1c1c00c10b0042015500c4c0040c002091144189104070600398241200f80110030300c0c0103440100300401d40c41c00c0900c07148003040781100440d0010300311842800c15060010081c036003441034800107402c2c54400314550611b030107030a04494060355a030610559940d40e4100920660b18215010300a00b1203003640580080c0c2d00304c0c069401402c04c0c40c40b40c18001c0c1c000c0d0845004124410900040a092a034101011016204554002e440101d031301d43d0f84c04c2c0100e0030100c141d007282c4000380021601142001503103038801c02c400040300072154140c0d15440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 113288246 1250 113286996 113287033
    0x4020304051905101811030a020307030f1a1602070504050606070204020c07080109030f020105010918020f1f0c0302060c040e011e12030305090c040603020f010f120213030203 77
    0x4801404a500c203005030340001ca08528020b11090054080e50700c10060751080405850076400c1e03044010f14a12400d1050040d038684620000302c0071801040c41c4a05640440c1d1039003801e00c000340c1b20218488010741884050424440f00d074041d81c40a500c145861000c020140c00444407041c014462001c0c042001c0c01c3c00c1c8201c86c0543d500a20b00360600b092a401c01019503c1411084914012440d001401c64024041d4981e483d210f41c42d42d0840345c040e840000d0840e40140d01080e02c40c2c0c01d286201c4c0d0010b98100d005981c240d016184200c0d040c40c03202c04107440302c080080804040c2d82240080f02e0f959804400e0f229554400c1e802e4030615254120004e07118000d9025000300c0c95158001084400c884480da610311801c451204489240d45a003041d003403011205064021075140e50400c0380e100803d010001030000100d030108013060843c0c000c59001c1c41e10603512814400942040075146014181f021016000c4003420b540c2c1d42e4880004106c22040ca10040340a445100d008510250006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 113289496 1250 113288246 113288251
    0x5030a0609110d051006200102130e012301092117030a06080703050303060d05150c0403030e010305040f060209061e0c06061008220b0f0124091e0b0703030605030c040203 75
    0x9035540741c0d900d501f8044184141c02d003090340040540d0b0030400341c05c5075460304044c503008002800c02c011003503240520401c0300300e50039004a03842e4a01d910000050b6a046517002068441200a02580603038541a410258040c00340141115000c0c4164100b501017540c01548603a000300000d100c42c0c2e0b9680b004503950003079400300618541081c00010140d040140072052428064011035103d800305200080c007020042e04e03210f03000707a00001e040c030a143e0440e040c0400300d08280780c1000710f4605a00d0b0605052506180101015000584c14000ba40d409098402000307001070074090011082a20341810303440300c50001c4d0300340500ca001030340741e1030550903412030000941c079124070642d500c40403c507040405804030302481000508040c0032030300005280c1c0c41200c41c0000d010055042044254400c0c11203602d00707180d10300450304000750a920900c680c003111514401141103428440083c43e0143d030036005405200b0b40410558140750b8103400800c2140d1043c1d058070105440142480280e1104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 113290746 1250 113289496 113289509
    0x10030c0506090a0b0c032502101409010c030908010213030501050c070c0e040203031219150602032502030109030f0e01180b0d0b030601080f0c03010c020d05030a0609110d0510 77
    0x40f031410468121540018010a1014001d484c903059940031440d02c021180c2c2000f84d220b9010f546240304608124040220010850500480005100c219a00301d48247c00105d410860040d0b40d4508150042a059000d418500001d64458003884824200141c0b43c0c803080c0c038550f003080e000c500c04d484506c08841c40c7d150030000200d0b09078103011000202d1000640f0490301448100142c0401d00b84120311540150489400c0011804450740e105041d1b0f202083c51031881440000100081c030f4001040310110080c440020305034a41c1700d50181c5500c40c0306400039403d5400d20341170b602015809500e501d44205507455280e031403860100112031055502d54a000a407035280380501400c1548c402401403034402c0e039400714031070f03130103002003828148280d029200c5603000c0c01850f1a112401d01690401300c0040d0001c000b090b1600c40000c3d40c0d58030b2a00c14006114001010804a1105800c58005016000428444200036880c042003592081c618400001d180c00c01080b1f440c0320700b01e0902c0031602d6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 113291996 1250 113290746 113290759
    0x15090302010c05070806010e0402040e010b0303160c18021e1c11070606030b091b06120705040b0708030114010c030e0103020a1704080306040b0a030c031106040b0310030c050609 78
    0x5660054a002d40301030700c107803201d106214000801420400c20580079081c211a98a00c82c24148140010b890460403101c8450f414266104816100081904c20589002c200e03580b280d18241080221806141c0002e540000c40b07602034000c20b14550010f1000d40100810069454451013502e1194011048000105046880c48030154680c07a08150520302c0d00d139034000c0c0392207150307500c800403141c1541c01281c10007134681c20000c41d08002d005090b0181290002d00c680d050359500015032074883c1c0010204144512800316020074428016500901100c030070781e070754a203424100120183c00c09d1140c020000200036124a07254401c1d4514000c4aa064480410f0350302000c4c01500a9009665900d01f0080030000b4000b0241ca200205800386001c0c130172300703941d0b810001c0500041c0c0c1d80b100e28050017802a45010800114081d5041d821203400c4440c030380c04800e180d00059007510495112444a05006c01404082500c8000401c1181d200d102941810356460b42032000178001d69042c1130788000b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 113293246 1250 113291996 113291999
    0x90b0f010c0c0501081b072303121f08060907050415060c140c060d020c0601090e031902010b040e010e0d230903070f121b12141501080d03061509 64
    0x50049a070380d500403040c01e4130031446900809928070306402c0440f05a03010600c200e423645006040c8480e01c5020181100914941003040030700c203019000250441c0740d0b03000480c054500c09000044140c02402d802005c2d5001c904000e52041c0c0d607a00c00b801118440c0f46015a141c9500503c480c84000f00d450300c3d115225810b980b52184030010140c20a01d4900c2c0c007807050110482e03610743d401001c101036280001600c03000300000b00e515017075058101454542c901040750203140800020b840107514240703806882d0000141c8200d02422110440356006800e01a84021012041d0001d00102d9101d80c111541d100411800b1142c000007142940700d8000098080207034407500310f0044c503501501500310b50034940c1e2211014500f1b201c985c0034210740e1842c00111010045508400c075805004640004042403c00c1d02100311240e03107042c0200001541079000e2041001441a010003000811003074a00e50382d1120030340d4460050f01201c1000074580301007c0f43ca034506c1d43d104250445150344200e03489 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 113294496 1250 113293246 113293249
    0x110c0303090f130b06030a06090e0706091a120c0307020607141803150408120c12070c1103100b18041109040f080d1d0609060f060d060204090b0f010c0c05 68
    0x1001c0d03c048040f600d8484010070520b0721380400441c020324030352200182d03291515000d0011a5056a950255904406001c200c002c0c1e00c05802c1050302c6984445451389800c0180c20055481044081d48843c000003041044c44c07500e840c042c40c0b0568594081e02d00a684284044512070008011700c1c002e071605100284200b0501d00c9907840d98030000d4111008130394980c0f449000080c0481d01207403078503800105100d200243c1ca0350190444100b542c41c0f400c1c4403100c1188003c3c50741c0240100208500110100d0500c64180300701c3c8000c10024007036642e0900007070b02040180c941e0100c030700e0095924140b02c07452200d84a807a01d10481d005420311001e00300100811090701d80c0548140c170080c020200301804100c0210081180340703c1c20100207a0f240104c010f443d1074003007580c5602d04642080f001c01024030004500030703a200e00d084205011603500d040005541c0280e0800c0039000c10300c0402c001c1040035043d44428070045040360100101d0f10749200448418100080c001d0040c01d00c00c40c1040075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 113295746 1250 113294496 113294509
    0x306150503210a0c0b1003020102010b011803110109090c09081902060708070302030c10050708010e01060f080405011506050301030b0c0708120405030d140708180c0105090f0301060303110c0303090f 87
    0x4a105130320b0401d066807520748441c1800c1000f40c0c0d0004001e00d480d03608000315070702441401000b070028206a0350105441c0002c81e403a40044c0300141c11900741902d42d0104e41e115601120162101c4031007000482d418010050074590325000b119600d00c942290042010300d2414100c030f0b0651300070903051404050741e407107405580021030101d0540c4000d211340c41d405001440340301840d20a84100240c18a05500000e200c094103074400b015003804003005006d100c1d44030f590300c030741404a030030464025121441c0080c01010848401d2211300000307100800e07610307031200086040341c0c09102e44420b580c50b0402034401ca40303d102e10040000318100101400080d5500d03015074054015002c0c4c070f0030071101d0300040e2300f0740703420610120300b0f040d000c0200000160000c01d0180c118014032903504050111213051b50340c46685407800c43c144080421004050b684640f000700808401400070700c44182e076031501810309000b007110a6443d004500c1442d08504001041d200034003002400340942c0c8000c1070504c1007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 113296996 1250 113295746 113295757
    0x405040207060603080313050c010305040b0627010f08010e0d020c010c0804080a0b04061a01140903120c210a0203120618180c0109080d051c0501030615050321 70
    0x82c010303101c41c0000041240309015600c11074046000d041c3c0081580340141c02c0045001c0528141172505060101040024501c00e6020320f090f541e031032030000080106c1e00c0d814042d4218251040003d0f00110b02d400c40b091202044a007100000e101441c1c0306401c154494a0302d8130101c0069000301ea2541c01584542141114140111000d40c501504d4032003030340c1400402c00c1c2c280c1d2900d88510a010810400d48920003c000901c182e82024501420000b810165900c208910809001c9200388143c1d4050200c90030004c001c0b5001c9946035601d8000c0c40d01c0380110030503521007800000d40c40148031440d400301c4102d40190340c041c40c43d107403440303034013041c8040c0c00381140e80c000c400201c44591b55002d50a22a008180b00724894280345004c80d112171804e0703048480e1504000c80402d0820150780002003030f01d00729815041c10740d1582c81c81c60030580d9058440391101402428180000300340042130b03200403808122a90ba080d40e00380c46d0410705a41c3d000c040f82d0808010746030302e103c0040d040004090700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 113298246 1250 113296996 113297003
    0xb0307080a0b0705031009060b120a0b03060f1e0115090b04030c05090a09051b09090d0909090206120106210c0c02011110090303020d050a090210081e01061206060e060405040207 78
    0x14419034070307000440211180d64000074460315001a88400c0707051406951903014bd0000740a20945d44600c010a441c4ca10140c0604040b031602030100f440c40705105a1740c0d684081c080104030301981d5522006403500240c0003610003107070b2214000716880d2801c0d401c03241500e07003095550f1441482c04040c40603810001382020f01e0903660310300400000d041400081210501285000a13000c52031041000b0290b0182040f034607503100601c0c90a100d604801488102d40803560001040030301800030a00c98400c183d1509030021040c400030900907005100780311250120989040d0001c040107584c01201d100c5628031010686050201e00150320950035403103250311103007d64020304201e800c1c40081c1c543c2008200c002c6900450403c11040c082d02c0b809174008891700e020300441c500c0342c011404200c0200380301020047c841000031400e02e2400c50b00f40b08010810400d00180da5103100052072406c12941c815001800c0150000d145c03440f500e00110400001080030703252030b15101c2044029401a0001c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 113299496 1250 113298246 113298271
    0x2301050a051f1b0b0411040e01060815060a03050307031d030d1407061407090302031603030c0821040f0302010509060103020906061803030406030204171203010504020304110409060b0307080a0b070503 88
    0x43c00180150086409079100c0c0b0040710f20354496204100c20f582210f48550030581c9094403c0100450008e1030100107442019a0011500d0f50000300d880180035400141a03884005200300c109580860b080900001600940204118003800c0548a074140903605001a8852214174280003080b001050307010301c034036000035280b426030300a23009240c1c049401341302049521004000b036003030034003410640a080c5101c4403403050440c0c5d07024140e03452250340501051030124204002c0c0032a10f400c2c10051009003452401803034546072480f03c111885808400650802c004245894070000c2d02e0703816a507000780100b003507035180c00502680f0b401c805521080c1680309501d10605840500c0140003412070b40c0e401590351824409800b000000a0b46134482503445030144281104941e01a83c0c15900101d80141c1e907a26282007500701c6034400076103e82d006290406c10400c11800b42d001142454050f0f04ae40e00441d601e5801a1311703400510000b81081421000040c02d1510a80c000d55110f01e40c80c40c1c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 113300746 1250 113299496 113299547
    0x270c0612021b0c01120b151809070201050709080a08041406160803041502190807020304030b181608060412120213140303070203100f090c090203040302070b04060f0c03032301050a051f 81
    0x20b00700080c00d80d052b00150350759400b40310070181d0000c00b560107002200c0003007174075513515502d00080c0e128502c1208001e002940d0455500c0d5a00300480c4c15001c0240031600c94030086003400350455100b69007c80b24000e800c82c205070002554002d0740e003a640c143c603201c80c1c103200088043c0d9051100801010442c0001c000101c0060417080d50346c1c0c0070305000c00444521001c0110620702c0d020030941c1c161407070b8003800001c02c4228070021b00181d01ca0703846884403038107039500c0714180c030407000c0d1040042d001e50001c40c45c103003800010300803081150b0400c3d00c26910b1828030003c0c036440e40700d580d030003070f41581000f40c4020200c6110340040c1c00b01070500700001120b0009440e0b02111500581180c002c40703030000b0604c028554100010f0000e020212001b40c0380c189043c5001d420142a002c4400c14070140282560078140260b20649071034910b10711564603501e10003030700d1507410024051544100c010003004a1300f07007000450036205103c200c4071096030081642094801b41002c0c0c80080d01809204071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 113301996 1250 113300746 113300749
    0x50603060108060604080d02030304060b0a031205071b08010b1003020307050a1404090e0d020c03070506121b1602090a180f06060b0d270c0612021b0c01120b1518 71
    0x41c582d1f00d08030351b90107141c032810189071403404e40301d0110a5a10500e20250140003040060707000099182d49800d156658003400c0c034003c114010540f240740d00440d00490001200b20041d0080440a10100c030907100d4100c0082c1c0503412070109507411000a2814440110250b01805000b108074112524103410715a50b07600342c034281c8100c82480001ea411000c0d9644031103404115203150600d04a0203007840b05d0401004c10207501800c3ca030500c000c2e410201060400a014142a800e05082019666208071407130484c144c44c506503008034012104000003482c440141e1061805600526403601d40d8640e554540044518000400b80e030030540d1140d0003e400c00c0110000c00c0000204100400d06a0080310b03481906000c030b611544d00d9441003540c410015404900100941e20182444811003600240070002800352410304890f01451a02498050b503000980c40c92106017640d4142055580d000c0501c15590500d02c2c041c2c028021242201c072a0990714080c01100d00c1600d95030316011311800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 113303246 1250 113301996 113302003
    0x50705190b22080604110108060f0a0311130209030303070302090303040e040605040b090a12050a020f1009211d15030412020706050702010e0409030e030313140a05060306010806060408 81
    0x4114580c2040e08020806000b80c00c207400000c2c001400508454500344d219889614810b04144d070422007002300088540e610400005402c0c1c1d405000c03018829242d107046900c07401d1800038107108400f0400740295550150080300c0b00c1071009070245043d52520103094010307400113a646035050005000114080a9070f05401e4460b501494000c201ea09280c00e200c3c4000030003510349042c5400543d2010302155010486030742ca1140d42c50000d50300c617a160b83c00c82c1409020020184203020700e1100009030202d5802699103e40074444201c000d181300f501940b0a03104c030f042c410740803882503803407007162140c2c0ca140040c5501015001c4420700c01940f841034915401210116490a81442071020090f030401c40da40140a441c1080c52074042c0903000680b8480041000381c0c4603d8a510301c5201b058031606408091050140449407904840348840d21611001c0c0140404403100c1c6010007501e02c2c26100000466801500c66880c41d11007c0c0115040807000380392680000e07080200041a02040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 113304496 1250 113303246 113303257
    0x1030905100b0406122406090e150601030504020a151e120b10090b03090f01090308010303021212180109021207090f02040305030a050a03112b0504050705190b 70
    0x700350024420360590108001c403041900814140c44c1c01001103400915016580d05941c4065201d081100090350218030143c00590000d4032464200b00312a0800200041e8911214645001c0e4003410340d14140110100c5000300c802039807184100104100c1c80682641400342140145022100d403210700300d0136034507281001c00b514001f5442c0c40000140902c544200b200da00070817650014800c66100b002441c0c101d0a010304d4038a000000b000c603a400000b0040c40d04200c0c40e0100a01c590501400d0190180000b44420b40250140400d51120480c904088440c0d8030000b0034407078101d803100300261701003404038604001c0540d40c0759a0f090150b960a01482c054942c003a00900400b030400590909a459a00b641c204071401408140300290010040c0d58200886150554507111414400c030080d01c501e07190310000d88400188aa40c07203101d100d204e18240105603001140b410014060002c8400443d0050a1600400c0c010b01180c60300f004090030150f54041c1141c540303500c2e100c001c25541c0c0030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 113305746 1250 113304496 113304523
    0x50f0403020f060c1c02071b05090108010501082802030f061b030105060f03090703080c0607090b161205070c0e0105030d1103030402040207080d0903080a050604180206070201030905 80
    0x11402000105581000400e0704441a100030f0074031400c044401c184140189a50312050f81c802c4015a43e802900380d056400441e000740f203000c12240e9040544410325654024980580400c07030021894041c14013440b4102d451680042801c410182c022030b43c8819141c120302c203140388044010015175001c04c551140d001d042c10241259042000c1c40d85002c0e1000368081d0a030320400c0c40100280c0c0d56040513a5011860030a5a41d0b07280d079000003003801d101180d00700400d03800d804100707807210000c00a0b1803441000180c03544888982c441580710300e00d000b040c030500555104081d1080c0007580c0c00e20300a41c110840d00b05581401e420b50341c1c500d0131125a401003000989403e0040240e45420809044c0c200014240600020098003a0b1900d0303101c010b1010b40201d40001d101020805010110742101c52010340030040701400d840c00a0500c8001e6441d41c4041c0d0038074020030214031303140c4116400010121100010040c0c181e080c06902e4010520690505d03070348020310740c0441c2d824070400c40000c12 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 113306996 1250 113305746 113305771
    0xb03030a080a0b0f0306180f030703021005010b04031e020301020903010e030c0606090712020f190221031e04020d06020301120c15090b0304020a0f1508150f1507020405 74
    0x2085024a802ca0f4241e558861042101002c81c01039071701c01262007034000b00150303600d100c140400482545070404c60b01d0144807a200c00035504003403550101d201c0810205801c41401203036a50f414240032400f0710300003c4d060000c2159180440a46c0001c544c00d12440500054241154080001c0c2107810341620210503420010f030500091506100c41c41e4001d404880c1002c00d800e0100d4014924148070501e10307542e6070f0009860080c040c06c2d4060303880c0f400842d100c0c0000c0c4940644025100c84248003489079480c41c1000c20040e01d440c1d01d00b035921860b054a942c2e07041c403240c4405540d100380003a100341d0304440840350a0001c01c6440c0010b5001c1c00e848265260404c05c140b520103040c006641c0841e100100c0d44840c01d002c5540724008800300c6100a9400f501c036211800040d080554950001c000340c4900c500000e20b1105802d84581c0200355a26003400d26507803100b10b0b40c05d031410b101c0310035030002c00c03030810f40718078a0482e184030a03071007203100c03070300c2c01c0c600c15601090454005a640184003070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 113308246 1250 113306996 113307001
    0x110a260a060e180c0105030a06050a03030f0810051e0114030405010203060109060815091509090c010221030a1104080312010e160e060343050a020c0f040b03030a08 72
    0x60400c200700b5000071424040000d005072030050a034480c0013808682c0d04214000010038a14041a01300d800523010080c03400c030742592b4914014012443c650b000c60081841600014680d1595209600c11904050040302c5c402d41804054603440c107900c12014184008840d5210100c20340a020b540300d00c1c80b8200041c0c1d41c2c1809030015100301c6007035000e0000c000312141000950f01c00c5049506801100341c40300d1030b40d521403072203401c10003015400b815003002c000302c2040020500080c00070b007000070030703001e0310400c01599020004842d00e051190302109810004503a030b80030a5440510700b80d240e00700803424261903118840c00c2d58808880c3c5081100d00d40010702084a2114145400049500802100210b05000580410f07a0362640922442d00400060344150364101c0c4024000246140c001200c001d0100d2407484030900301700072122001d41041289640e024100f01c82603000660000c12003590010108002903903080c0c8a1a0010b481750080041514100050503506030541c03240041403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 113309352 1106 113308246 113308259
    0x103030e040c03020f160c0f0302012703050304090501050a09060e0703050c0c150103050c010c171e0406170a061202011b0b0708010f09110a260a06 65
    0x8a0008061b00e421072620b0700e01c00340034800d05580c90794a80306c845419800c80d090000902103050086440302c2540101d11646800034010416000c05451360f07500340c1107400076403001c0d59681c0c80d040107008034031b070009030140038124400c401c000d024900302d02c1545103040500880189580c41001c9080380c0c2c40c2004462a0095010031602c03c540028001008039009102c252018001c61041c84019842110220201904500307101606200c000300c04801d81d10689202522042958070318120b0407519000e480107004580718010100e21440c0b29590f2001c00810002e210ae28291b01071100b558581e030304440250302841c0601601c040400d038070040d01204a0f002d045150006d04005070346034420300642c181c8d0400040d01c0030840e6904000025248511800c054114043c0490b01c0b030140b098205107040c046105820804222444540c00503100a485027104540c5800052124 = true := by decide +kernel

theorem cover : BRFrame.Cov 113129496 113309352 := by
  have h0 := BRFrame.cov_init 113129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 113129496 ≤ n) (h2 : n < 113309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
