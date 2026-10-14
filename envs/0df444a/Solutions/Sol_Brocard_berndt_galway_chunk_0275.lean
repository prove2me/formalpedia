-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0275
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:54:02.961605+00:00
-- url     : https://prove2.me/submissions/b04989dd-3281-43a6-ba4f-fbbcd8aa23ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 49280579 ≤ n < 49460435 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 49281829 1250 49280579 49280597
    0x403030f05010b030103060507020d0f0c031b0303020903070b0c0613060b090106180e041a0c040902070623090d0f020f010603060501140109030c05060313120c0201081f0e07 76
    0x10040880700c0a82004080300310000040c020b004081c090316420050a01c02000e200e140000c0061000d4612090b510070800c01c2401039080c98441c14109124517a014143c19503540d140c64090000d41c410610b103030003400391502c001000150305082d50180f034200809011a603841d00b850308410f20048404a412035507c840c1d0300030948a240000d4060160354544502c407400151030030001a0159100381a01000b21003000000340e1040045080b00d1b100e1307a425641074484034003090302405150052010188086120424400c0b60781080d07032000403644038007a825503001c0004084207002c0700d070350003d580b00c03160b1030407001c0c410422109c49132a1403056070500143d802c1c4103420354007181c0c000e0b01c3c5c0c5600d590062120b0b0040c20000134146d6000d00f010100c6510350394400049004902c1058440c44003c40052800c0052542d4041c06640c0003445d00141c445840303024010030103101c0241d00080410300003540e01941407004001c2050703030744603800380e00c0c0c5001c0340b035805220010218000c10803901 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 49283079 1250 49281829 49281851
    0xd020d06080a0b0403030b040c23041701060509070c0803060f040b1504031b030b0f0a0912080a06230402030a0b090106020703140607050a0302071b060309140309060a08040303 77
    0x31020b00580c52251010070320909045c1401800da5502200c114455881e0220301701045030040032800e90100710f00324074100c0c0b03091444d40300ca2030b004070340c0320540f031401d40e039480b0040440650114095400868014005442c1d0324001c41d038068050b0401000041c080012421510748082000000724000344042604180040850848500ca8501d03403a1850045420710401850040b08415420400d41c51981d80d0b196403603400f400b81c8080d04980c1703c00c03032040201c2d07517502c032036041400d50030340141e82d521100d581ea100003844100d08a07984072182d40f071710340042012004620308035516680d401400350549490800c0000035440503221031045079403611410415201d07010711900074082a0082c1034000c0c61812704d14250030b8003074074084880e00030307a04101200c1e0b00501076071036240480c6070061302e585e101c4c90500341500c81d070081d00d4012112044002191985600100f004520541981c8070107103d20361081d13a07034042c540119a00c00002d100e8945038901c58501c40343d02c90f000381790114082040e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 49284329 1250 49283079 49283083
    0x3030c09140607060902100e04061a090603090a05060c0a020d080105060406030b0102160b030405060106050f070609081e0310090204030f1e08041d070c030c12090b04120c0b0307050d020d0608 84
    0x805d1010046003000c4030319448c41c80c0c207104200041004440d980f03100308016100d12500e1040a0b58944a5100807000c5005e62004001100c40107038810203e5001303080106202143c1e4009000c10b5005101c0c005008513510312800b0443c1c100d5001500045c10541000c0003900a400c031803c2d5281103108640c1c451480307000d40d201400046c85000300e807a5581c107081c02c1540c145001600500240300f0200510142c2c003039408120395007150012000600c120640c41c0251191260128400e405510640c054000b8480000214015200c0142c10000540e54002c01002d0340200e110140000c4a40040745002c103108000c034403041c03a904407004a1800c0195240d030716a40107500a01c1100b0035200c01c03c605040395140b042c2e0000d003a401c000d81d9200c4143d400070242e90b0b071002c0080c021803a000042d2401c80c0980c80c0e20020b00051703600d8a8035a9203428450380300c080c110350140c0c1c1c00340e002071000401c040c0481c1200d02521381c0d0360740c00341381c4000100018003a5001c00c040b41d0019075070b0103002605c8442 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 49285579 1250 49284329 49284349
    0x2031c0e0c03060c0f0912030a030507020c100c06050601030617070501080601050313020d050c03010204030b0f0a020a05040b09030a0c03030c112d0a150c03030c09140607060902 78
    0xa598006128101011400d180c0126409181c0c0298030200c244008281504107917085200c008503059a24460180814004c0c030340b42d03140e14424400419888461505074014602c00c507119403c450000140d81e0410280130344a00b10040490103108a284c0031070200d40115600c804181000309500ea03841e00d0b02c0d0780f0801c900725a8080c3e90828202400290b030b0290303181d5040403091901c9800c600345140190000240020024400c0d481c0c140e2100405c4402e00102d6450900100215200c5a503801c0060300c070101242e101c9203d4566500041d01d400042c402c2c2d0f800601266100c60505003421501c001550100c40c0e4103074180b15000c801c800240c01394095101030340c841e54580d405441c55161095007004914103040c4140405079240f4050701c0c139003261401d0705c0c13010040e11350710080c90400b01d928040640c00541600340c4604114200541064660041e02e100e030381c0420145a040c6c0f001c4802c54120b0082d02d6803180f807148005464586070f0054115680115800900c165840d4002100d26403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 49286829 1250 49285579 49285627
    0x60325020f0f0606060a0c0f0204050c0d0b03010e03120403110a150f0b0105161113020309120705070314030d0c1808010b060301090905030f030103030309020f040b030a120203 77
    0x4440e04401e00104410310580ca00c051000c1c004000380d05284002400c0d034000d0024520404c0034a0303081c1800c1c04410041c43d541583c015004220500f0040034108080c1c1c0580c1c14070700f0603070a280c00b80b501c0b0300301440b804109200c1d03000514103114007210304000103100607000390200000001c2c0042e00213070501492290622442411740740080d860a26400d40b0344010680a1080c6040030124881c0d0300b100888402154944181035030101d240f8041d04019064050103070010012401c0514a051070b60046010b031b0b8550046811240e0003e04102c014801c00b180103205400c42c11040000603111030f21400701900c2101682d0a2044005000c000c0360380c01c841c1c4200141080042040204079110603101800401000344070354011980420003c0c0b00621486003095500c0304008280001030007a03540c0d500121461b030b5640d503528100100607040e4008164490011011303130b405680b402d4031550303001d48000b03000b40a00303280d1034640f0740090740c14a41501c150b020401c007011901e1603c0c030a440000c0703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 49288079 1250 49286829 49286833
    0x170a1202010212071106010303030b04020d0905030a0201180c03020603131202010501050f1009180b0618040f0207030c060b010504091d07140303041715041103010f1a06032502 77
    0x50b20309050003c42c00e00250418040c0040006031032020003000c00c00c5415290181408181003039010080703070003807180344078003450300c2d01d024840c104020012004141c209c415900074002440c20054075411800c011070000c0401ca000b290420050800001941e803198100000244000c455200c24000c09001d01000c0c1c0140d65900040c0414501024075842c408000c1e141e0b0181c0004060b0068160000c42c0118448441c40c9490f0010b98481a001141e50103009001161a00060303100e03c2c0e12402c241c103816200700e04140100d140701002d8425140100c0c0c00d9522024286680c1d2220f100601c051021076040180410011943c40d0301c5004103140640c103c3c0c40004500a03c40c0031a0402c00340340c000d804116480000c4008540d000801c3d43d055818800e841007280e02049410791a010100c1e8000c0384580e000010001440301100b03101450041c01c0d0003e020b428480c80703e41046070180520000210000ca41c000c1443c2010409150b00044007406040000311041440d00c503603032104103400c010303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 49289329 1250 49288079 49288087
    0x80109060c020d0c030305040c0b0a09060f05070305070f0303061505070b0903030907061818050103110d050d0c020d08030a240b0901050a031b0e0a06051201170a12020102 75
    0x100051103030755030607902403000d001464280040103190100e000b40103002c2540b00c80101d0140200003201c134004040b003054044d550010702001510309403c0e81325420210301040282c8002c107005000301c40701c09915644062418503d0351720024410f586050079001c143d910000801c0d500d02c9240444082501500c50b41c2d20f9040034904001c02040c000c00340d0303c81d5041070090100c1200001007013000d840b80d60400181e0032081d442c00b11854401c540c4800105820300300030400c4840d00e9400a410703a4010400001030300b00381d4003480a043c0507044002c000c1e03804004c640340040c4c400c00d04200003030306c0182640342e601d5558444c0c001981050b1a20101c2942e960b5000080300d601c0e4107407103034040007604070442c040d14100445040d07004007004c0b641031244c001102c1c2440344c030940c85100100e61507030181c00c80d88100d960003000711254a00d1315010340310040010882c0d5029030241d600302c0c14106810156031382084450711140900060821319072203014201070015210746132000c0241d030f4507800180c41d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 49290579 1250 49289329 49289333
    0x4031e021e01021909081c0507060501061d0121020d060f0b03070806030f1f0f05090c0907020c030c240301060507060b09040506040b10050d05060906070306050a030308040c0e01080109 81
    0x114401415001c0244441d100c01044100001f007451940b8503e0080b0381003030307241705200c203407141d100c1c455001b84278034500400400c100341c102c0f1040794903125007030b8403400000c002c40c0151740c1d4500c2902c442141004462141e0700d03407680e40d00207100514000e500480c01a680e107540d03880001c0300b50001401c1e0130012040082d00f42c3e00c030f142e00b984280210300400b504144000010789884185030b000c2e16080807044000e0340b5000b241c1159014000d00c050420092400300c5c00c00e9100d084642c0c00324880d1a800000c40c0e845480000d085940400003405030a013903107401c040141010300076025010f0f08501d10500c4200a043c1d0002c4e5000340381d00e40f541560340c601e600d414811101035005282c0300b0001c100600000c5840001c038183c0c0268071520801c43d5407181e41c20300300d060721168400341d40b151161010008010002c0390b01c3c0e019a05010454041e03480e060829015910309004403030300b1102f954020408244250b131000d4000d0701488088180c3d585800660030b100000360442421691a82d28a0782 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 49291829 1250 49290579 49290607
    0xf02100203160c0905070f080a02092103030601020d050309070621060b03010311031911030f030307021b03060108120d020c03040306020702091501050d090606080307050606030d050304031e021e0102 87
    0x6c0d02c104186403034000c2d1143c1c0c00c4042c20920b005083c00503101c1c0e021401c0c40d12511082ca2023061034210032300701c0b0451031079002e2a6903130390f2003144d1850050080b84c0000c3d507203501560999004000000c00760580c42e00b010b00c02c85800e00126030014200c4442c1c00004200c800502c01c0b880900100c0e0810766480d130543c241007070000000420310b03001340d000118914400034540001f50b041544440080400e105c0c0e00c00007031800100040c1420306000c00420300c0b0301c0c40c1d000100c06151300314518010946051540030503480325424483c2010907009554625900e00b17404004000102c05180010300b4458110303245490b40e0000c3d00b040b02d840d03900041c0078040d032405518503030f0f03c03492403006075500c0041e01000801078040c0303200020410f81c07110301442c10080581c10440260032144100d0b51902c980b410880e685000030340d601c90007406040c002d61100f52251003142e1240340c054440030482c5441c0140c812414076401c03003a90850264010950a00301c8920311202c511a407440003685818075010307020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 49293079 1250 49291829 49291831
    0xf140702060c03090d080705090a0807050a080c030d05030915090703021305060307050f0607080d1d030403080f09011b0b0718120f020f061204030212070f02100203160c0905 76
    0x1840b070380c240104020f04600265581880c1240d00d8100f030f01d91640403065070a03014100e185648406000004130792004002140d00444008481c02c0701c0b810b035503120440d1280220b080da0394150300003905400c202c0740601c1c000d54200d40d100d0304481b00d007070840c01c02c41c0e0190402d89840b410358102e24010025443c3c00180e52140e04041c1300c00700814108440000d81d46c02a030b200c0c9600030700d500b00d032503640355807450191032515401c41882c550728496402641d00078015a103117809642800c0044040949000060700c090302c0d40908a2480d01c0c80c0e03036010000e10f402800d501030411490048420000e80711043c0d400000d803064600f2501403d00070360103090080140b0075803160007403040e03040082c0019226a07191403a0003880c0901c5500260001c10060048101040d410820000c1c48200910032242240e1250f4001d0f800d8901c040743d0099820340601c1840700241070001151042409450060428689000c0302d0040300e20b401c01c3c00000208182c0f07510815201009601d400708904600e41c0226 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 49294329 1250 49293079 49293091
    0x20a030c03051501110f030d0e1605010903200d05030a0e03010b01020d080a0f021306090801090201120e01060e150f03030403080f0c01060b0f0c010b0d02030c01030903030f14070206 80
    0x14801d510303100001a103621100f45011381040031034001445207100c00d001444800041405581da20501462900040c1c503680701c1e042058401c01550581c141006180002628416940d8901061940e1500b083c03c4400540c0041c115060103e02a11a40c0700d581850011340b1481c007441d1114024072000c1d01401c8000710950180c3d040c01ca08900036a408501c03095a900c0324103001c80380741c0321018060020191243c0c00c1a0742c078400035a03800b0800408441500b1034960b90344203110305071151a580e0130f03940c030514000c2c00f01d960281742031303035080307568001100300c45011000151f456030b00c81000e200c6d0041550f00842d1418070041a02050410300c030840c000ca40140d005600e02480c5036a50444c511507540e0b403050600012a495115440c20f4011100614070a40e2a644409038880c62160035804140c0080417903190032304030101400d0030880721000540003806409110112001980600442c0c10114205551a1940c4403003d03042d00c90a80c3c4c404009094200d14074014601a01e420300192a03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 49295579 1250 49294329 49294331
    0xe030106050108061e030109080903070807061d06090306150f030703120e0a0b040303090f0909020109050603070c0c090b011106040506060d320c0105070312020901090f0801020a030c03 81
    0x14481c59811000003a0041c1050b00d4075031000d481740081c0011440104800d0781e041d400c1480c0101072007900f1010300609102102901c1582d0390300c43e00180d59a0984c440d80011584421014a060710540600409400e0160001c1e2811642100090400740d00315825a0510340600c1b400e429410001da100d44110b030150300030700303070780c0c2c150703140c41c04102000485401007005103a40b03070744a5102c24543c03000404074a600d05444686903e409081c001803801213500c4c0c901d019800050b51030b2280540b440340364040c0c40d880006410541030015a40c0000d10720710078031924820768000950030400306401410032040020721611400001404864503240003119079001e003007400b010407404a0080e42203030007210030000500e00c61a001a0096100c86480c0545811085422040b0740140b01c21010342d2152003502e003141c9000300151490f0281c881c01070001021848a162540050390081c19031300d80c1414985074070380d9100d07445102c00b03d240c2c1040c07c00d65008200911081e03014015100c041ca441d0070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 49296829 1250 49295579 49295591
    0x30603060c030617121b010207020306090c010f09030f0b0a1805210a05180102011409010504030306151d1309080406030b04020403080711190f050a0e010305060f0c0d06030b0105010e0301 82
    0x2c843c031050040300780ca8080080c0040500103511b90075811900403550182c16950f03039242c1000000d480c1e0007420291408500000d0100340c95910400c85442500e90110454000103a9621007550000000f8981c5a000d0303903c0c0141407900229215441d003491080c030023000340340700b00801e51425540c41c0e0314070380d80c884003801180c441c2500031043c1e600c49032110198180c140601c1004074050f22080040c8100220803405000221130107421840c0b10b64040d85080c480e182d66000340014044603080c40f080003454024031084001041c071208071958030000c106ca024400c00b00c408000b1180581d10459169a00207010080c007501030081c01c2544408950071418145141c131285000d1064140080c130341c84001d140c260351035441440c60402c1e1b00001030000c08040e1240485922980c49000d9648204409440081c0071041c46284074140c96021000e131541b91100c00168041c000c014101500701e030000c0c4110000b00d03d451003048010740c001c1000c0302003945060000340803000016100340c02031741040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 49298079 1250 49296829 49296853
    0x1b15030606091516150e070e070e0411040e040b070503010807051005070c030b060a050415090903091509050406090c170a060e040b0a050601020a0b0c0a030603060c030617 75
    0x2a06490315040140c400214080003041110741620451000403503103440800e01005001c0d030028803810003400100200a01c2200007035555451f2400d100d62040400110002034103540b02d615101500280a071001c1040031926042054a4000781c118014400c0214104018000a0100d154008146080051441d41049a81601e4801e0390042d10301031001262443e149600c6030b800c40344003640002d166076070035450b844c001d035030a0000d840083c401e40000c500030885241600c01c1b6115013078083ea5440a0320324246c0f02c84083e2450000c00d03024042c80440028002c47e004100b403080e20019511400c5440c00c0a08200c11a03005400440459260140b01040c55401c11180300325160400c1d40c1d01c400d030341c5040390000a400c054101400c030b01c1d41c140c140001c010b001c00c04ca9015030800141400700380c0e180300c01280d07102c9560318090000680100440c072000541001000883c0036440c0104190361252240d03c150b034807030b819142c0006d80e46c01081003c01d1584940286a13030b580d03005008004902 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 49299329 1250 49298079 49298089
    0x10b0a0312050711040e07060311040506090f0105090d0501020408060c210c0d0e10050703020f04091e02040321030606090e100815040311150103030309141b150306 72
    0x803007010802d0010004844007400074000c00d43e507031420020814440020074014880e1140094410b81010034244140340000c02c3c0d100301a20184d50020300202c0c1014000c1c4104000702400d044000d052003000c1220b00d076151141055814130328010000503a03218600001e0503d4880024043e224140c07090002c40c042c110340d20140c007520441c0c2c224600054030b441c202101340344110301c8510810703450400004504d04002c10602071070b03500f0f28010461945c0d2040142e040c1c0c454102039001404081001740203002c0640d012412040d00004540c3c000d012501c0040102d81c0950400d84040814101e1409803162908628014910354501030000610b4140080c20f000780c18024038101102c04c00c0080c117041d0303031060300000400041049544c0c604240a00052010f0b099605500003950b805880c100890001039500c001030a41300005040c0c3c0c6561811802422101400c6503511400da6007a21000000c024a556003401d014466602c05a207008102140041000081c2e0788641401003002c295a2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 49300579 1250 49299329 49299353
    0x412391508010b090d021203030703060602070506030c040608070c02040203040c140f06090f0f0d14120406050304110627030f0105060d0b0c040b04060f0909092406080604060509010b0a03 82
    0x161454400d1070780a01c0002c1f8101c1229030302c01e00d0f07440040200070300c40764141c000104890643e0261006c050f00d640601c8040c0c801160300c0d100e866801c00041015034401d401c8968050000d02d098201c0321031607400102640e0098605a502946119050200081e003100b2420105800c0718500e40022242000c20038074000d0002c00f41c42403600c50a809656225a20f490b015148014940c0501c00c0d100d00e004942035940b921030003054422489400314005402e4202c038151105610b54505507582d030394030361124808060f840c3d03410010031f00c40090010312100b41854412031082d44801785080321003d1515101003980a140b0030b07810181031040355142c040c1100c15598202405012955030703040d081c0c600e0710460b40328021401000500290480d4003900200c640c1ca000d9175044542543d1302440c41c144d804000c009881d40c2c02801001140d015014030a40f401e180e0724001142e92544c40c2e00b103d00b040d00c1103409031b5019403a0800c003c042507082c403401c2240d110441e040856242191600c0c27080040c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 49301829 1250 49300579 49300597
    0x905070804020405070c050a08040e0c040b07060c051b07060212070b010b0307031509090b070801230f060c030403300c0507050d050c030609030412391508010b 70
    0x213624000b04249a202d20304128409805c0310032100c4580d19450101c105134468850301001d0050b0002103291040c489048508640c4000d840d103080500702c1d01c41d071008061601c541c10a014003002500948c06c0412082c024601d40c0802408586241c000c1c007905248107090310280300c820401562002601015120303054440c41e103a025140c0d0350f81c03031007600140650400d8030009040f1403000914551641c2048a61343c4c450180c003901501c4026003583d03180000c3c0148030b54200c03004e1040d6850013802e100b82d8a03d4800034112203500104c400400c40a07404408032001903000000c0510a1010170041d803c014120707901411034920103101d0403124031801100010030003a0180c00c2c502800410003420b40034290041400007040e4041c50410703500c800d1900468003a004140000759010004401ea408640040c64080100c20060f070720501c101c0103480b00326440d075410081008240003004a041c10580081080c0e6201c20300b802c07040e00c6003003480c1a141e010040b43d800140954003d44065481c0c1c80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 49303079 1250 49301829 49301831
    0xf0604140a0b0a0905060108280615180e06040c12030e0a0906230a0303080a020f120103021c0c050f060c0609011e060f030212010902040f0b120c062a0a0305040303080109050708040204 81
    0x1603583c641a0064540c02604081813060600c3c0071a50380108203440140300153381040002100194003580c86200032100542880d014800c1000100541590f03101c1c098402d18ac244401c1c5840030016000c01034035080b0b40e031f92550b100380078030007084960112242080c40c000410981900d207000998036a005020003001c000d1310401141e600c1255030142d03800c40c080d02c0070381c6450b5605d44064112500c800d02c82a8415407403600001d805104070803500f032159801c140403070091410b18060081c00d02141400540194040100750060f903070921000d801013084000100301035481036100105c400a4250b113140c090b03e043c008201c015880300049c001c481c1e050380d6260143c1c817544001801460400c2000c0e400c14200300109182141d80d510400e01030f8402c869000071082c009022319a0f82c401440c215070041410000d107882c40c10254190518403200700741100404030aa8081410a0b032a401c084011840c007190a10405801035441805082d9100040180386003000005000c03100140001e0f0081e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 49304329 1250 49303079 49303153
    0x7030b010c05070e04170324030a15060e011502100c0507050102120103020103110408030909040609020a080708060a1404060903022a040e0f0604140a0b0a0905060108 73
    0x240d00400c844034020342c0000c00d50340c0c215940d42d1480c01c02001158100c2c2c4003094500b21407901c02464007500d01417842c0a07003a084030141100070b02d0740c4d16116003076a0391520800284c4400642c00d80c508848901c800c070030200341706140070400c00c2405010f801207400c0440d2704107080307074150f0700003000740303c03881d0440f8040381c000c094000a480704d12609501800c0740d400000c03180082d03a81181041d040b6807003a03070200064521900c10b10303400d0142d030141c41134517042006030034030138688026104c2d00039001d040f001583c4181c81d4005054484242d008100582000324100000c08090100642c00240084144402c1010220710815140010401003030f090317441e1406010b05108001a003900410064141118090f440d8410704a59200c10558840c90a09884240c003200c081a0701c10f252440500402154407181d84840044510200c21040c9100300342100c0086006c4501d554041e09200c10001800b58250500506004050f00304558507804603108010702c1061030042815002031f0101860300c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 49305579 1250 49304329 49304351
    0x203070303051b03150a0f12291311091b03070216090e0f010207110603090a060204030602030a0b09010303121a032d0c13020a0203070605091c08010308030703 70
    0x100306083c1c0c54120806001104105150100713800e0001419021203c01804541e154070f050050090350184200d22000c9130b2004001851505d01144001c0440a0325645071303036610481c5003000030031200d8100c650100c2d500c00003170090282c0d41e40403a400503a54003500d403508090840114100c03541c8100710520010000300340a10a200340001d50102c2c072081d00c8007654480394440034000002058841e402140701801e02c0350814401c4030960f0790f1240d030130141c1e802d81804100307075608000c3c403010840c051501140c0004400788020000b0f5403051500507140c3c18681c090204680c25600013030301480483c001400400d802000304001d61a40b03a802003441d050043c031000381001c0040300036405208035013500ca12050b60b10042c0020081c151401806174044080d202e44c3c0340c2e068007900e508a44038151540203001290000c2c0303184503403401103d10340595582c550007152021101c1d988141c004000303002c0160008564070b04200e07054644480c60703504503229480f103807001800c0f01d0281562090031001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 49306829 1250 49305579 49305601
    0x609040201140c010606031e02071104020304020111010516030506030c0117070c050a080d0e1504171908060a06020a0503090d020d120203070302100501060c0308060616081306030903020307030305 86
    0x243c1803050028803240381e50308030140c060f151114030b14880d83d4426040d403200c10340d01d1080d100350680103540d0b80b0400d1a0001072000039031014000368104014044c07540b0188000f400b4403402149a155880607880290304010b0858a02903c142c2c400e4204840c016016030b40f0403a2100035003100d000311646034480d4201559000c1403040c1c0103205d03005160b000303c18401e411020303008030406090180040040120820344510f00780480c8400b0070a4640481d001c54a90088080401801c041c1e0503d48070250400d050404a1980440001003000080060b2410142d030030030010060f030f000804241a465881c08c1d00c81c0035446616014050580995081d50748145042103a03503040f0a20b4406d81d003610000070f481c0d602104050b805803080c2204415648041c0c82618100c0d01165190601c02059580c221400750001d40420340c0004107111101401d41c2160014880b9032007280440d559400c0b03072010010303800e2076138000000d040c0303440e14030302c046034002c003c41d8251541071400050998030030324865 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 49308079 1250 49306829 49306837
    0x60504090807021507020d110a03080f09120606060418020d1b03060f1401121b030608010b090408040b0f0d0903030605040b101409011e020d080708060904020114 71
    0x159106040400103000e108441c0010110316000762600030b00c0e91181ca031070b00564441c001000b50000c2d460b460800100f10a102460940840102102c008031796076103860110743c10000038203451040c0003501180b10b04e0300c402440910401c41e03002d044070b880c025002407198002c0384502c100d82c05004d060140080600e44c110741d03c90082000802c101c101508080c4402c8901d640c219002c00d1802d034000c03810141d4581501c08a5940c40d07034004a40c844c00c00111200c030720107a6035612184d00d8045070502d02d000010301c5124900c050341c000803402c1c503080c0d4080c01e42e419894018001d274504014003000c179030080c4c2110306413400b800380195105100c1d0501032880c8074810300c01080c40d150001c21801c040d416003100e012600d0841d03091124001050401401034850903441021802c1079000d48900c1d14007201400e10000141400e1541c1c120700e600d255540415182e8100068000079410080030350811030154100c4030602c2c240c002c1c1c0c41c0c420017080038240050400380c140840d802c00d0030f400c0172a01d0116 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 49309329 1250 49308079 49308089
    0x705010c050304050a0603050612010b03030d0b03010f0903211104120201020f011404020a0e070e01030c021e0607021218060306040f0f0507020c060f09090601050405030d08070207150509090a06 85
    0x2462040c0d0342e00c6c0010005c0c04140c3d00719201f941d003900b40309100e65050085402c4410024040c2d8903140d0f441c1030070340007011280c060581654075005070b1068140f051056846450103500e0380e800c0c000e0040d00035403075010001c000b0070070300d4030f0701040d1302ca54648041500c0546450000c864800c811900060389403541ea074080010139802c0804d583c110414807480c20740035a02c240c0b02e021030592941298042170008503048800242c0117682031295601c00d0300555031200300c42c01074031030610919522414103240780d4401152540024103108143e0741c10014008036a015050807810854500c201c0980c80b40300716000340c4903050100114640303540b16404001c0c0360301d40d810204604112041043c002e404212200800360217000c2c2900580e040c8541100d0380c000c100861070386054070f0113041180b174041c0030309040c0c100941440046203584003001000c48003151622021103601d044d460091030400d007604a240390303031009800c2c7c4516941100c1030b82c40101080f91500d50584d10a00b0b600000c01d0141d01c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 49310579 1250 49309329 49309339
    0x18060e01080a050709020711010305060a0f060e090106032f0415180e0132040203130506060303040f060f020c0411040e0105040e0c060307020f060f070e0306090705010c05030405 78
    0x40c100d60000e07082408600c02c5003500e81c2c00366140170120490007400d1015041e140d21360803420300e035840307984031a9212000904000c001a2585d58000700c9000316007054000c180141f20120403894080c01040c01040c440c6001c1c4504603840c038400a640744540c0c1c008140341002d40184001100c1d080564001d41503041011136010013050300100102c54104400030041010360010a040101000d442d0584600510242840e45108002a5400007100c0c0103c1c886400e00070110ba183e44600055014039407100e0902007a00050820500f040700240c5054030030303841048100114907100c1c81c640700300d446e41e0030a82d02620f51080242c2c02c103000000c0055009103000c2c00b500034010882c0c060010303101d040b40c1c0300160b0783e281d0381400708440200d0300e50381c442e0340442d110706030514090004582c440028410361785803440201c000b5241010a907240718400e403900302044911540aa84400c10703c50481c01080142040d40800303032a004c0c1400b40c1da0400010b206000d051140420403078004241c0580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 49311829 1250 49310579 49310581
    0xf0516061101050105060f0c030708181005040e0c09010309021906120204030c0b1e0c060a1112041b0518010807050d0507180603050d0e0108090706020718060e 70
    0x1040921096500a14010590029004070759400502c01d05041c0c8102030003441c500103159010500a402400e10140e191008120010000d2095000f0b4990101d10120405e20740c4c0420041151001c604030903c2c0c10407000b40f004004220041c5446a008040d442c2501d954846000c0105d01401040c207020750400000124110702c032003020703204d80480700d807543c40301c207010b113444031800607442076100103040344100030000d0256940d030702c0003010f24441e001c010607800c2c3e000c58681901c0790015600d560580d00610104034a80e0514010f192101c441c28030345914007420202c074240003d0001c1c20151001c101c06144440c00501c5412160140100800504110f001665010010720003402060018040c107000020a4200302020104950340500a08001414100c1501401204800b04401ca940b01c0c88000045041400030151041c842e6540c00070390784580d0005486180b01802d100141e030b01c103503000c0004a0380460600f05561118219000008039015120003520658100c840d84500000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 49313079 1250 49311829 49311853
    0xc0905090a060b01020703030503060909010216080409050c1c0c050c030c0703020f09060109060e030307060c0c05010c05090a06030f09140715091a030a0e01050a0c080c0301030215070f05 82
    0x1a070a840d05124034001c0c854100e2401c0120b07124103c0e0f10000700802c1b810f10210300b43d481e150704c9040d070103448000010b0504000000071500c407030980e90162048100040c0a002011b4a406441c0e40020308950710351601e070100f60701050440d0040e103245d8506542d0915240214132810442e01e01155610407241c55807a0071a83e030b42c6806840c1f00407882502d86492443c0c4c04d0401d8040c56201d0301050311104003d503e450020b075640c5140b00703c04c0c0e525000400810001031568442d5102c0748180c0d54554000c4400c92901500b1605804029000d021061011700d0300d96580366880701c01e0b5085481c01080e0590600c2c00000903118104004041d191800a49108100c0004298003240c640c0000d4912034524110281c82c0e800d1503024402001c40440108407aa5032841e00a50b088109078100003034000080d5102401c494090302c06034400c98440303203c0c1d110103a01c610b1090704103242035190b901d154910740c0002e000c03a9003101d44112406010032000c00303128480164006541e086000c0d02c51822960b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 49314329 1250 49313079 49313083
    0x60d0b031b030c09060616030c0b07030911030105090309010e040605150901020601090504080703030902060d06080601060f180e0403170103030203030f1e010b0903030705101505030a0b070c0c090509 87
    0x8034095901a200744000300c502d03403078001d041314051000034080e189000c0724a6040030349100350070010b5003030100001d0400001000549680d2040c200c681d00000c008035140340040d4100074402145100741e0403c8240300f00c2d150b01000310754102009013030101000400c000400d0142a0950005500084c00103042e0781280c8111300801e6000c01c00d9081e903c0076a00d41c21402c0072150b0940b4040c000c1d40741802410300203406680001248c500082c055070501c0f1400140209481103a004145180c011301c0c010400e2a40201d41140e0548041c02c06d4014080c1c541c02c22181a040d0b441100080500f92010800b490300854405c101d840c1c140540c00300035070f120706000c1d55950081e40c01003581800b280000300400705024092500c138040b02400a466440c02034800f60581040843c1075040c0410443d54001540401c0700c0c0d607070010b080e4000705031404481594108012035620a500a400250b00d03100090394403444142c1c010b6140c10603065030081801d2440b46d19027140c100420f001c0c0b402c001e11010541c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 49315579 1250 49314329 49314373
    0x1e0705150a1403070e040b0604050306040615140310151203020607020c0d02030a14030903010f09020a060201020a090b07030504090c0203070b011e03031428021b0a05060d0b03 77
    0x7060700e030402011451942c601482c4422110380c4001409140c0107039542c500f98020200c0721a0092904c4e06054607a800241800f20503a0f08a625640d07460180e61749641c4002c0400040c0840c2081811011201010030b881d1030f001d030500200300f5600c011704000908034010b80d8010b40013401150003003100310700c2d01a50703800080c3d88000242c494020410150b1070560104c0302a1903001e8090103030841aa40d0701580c0100c020400e01150006021402d841d480910400f98802c0c0c1302100464068044d0052060164041c0c00500031640101b20300404d49400000410403201d140100c2a80d4511030304040b141801181c100300d03203ca05024030300e00141d5000012b0300383e06e4010904856140d0b81c800000c4c2d90340c2d06144202c00000d0071910208042801030f0701d2441200c0542400900c0e00000003030070120b411806003440c0300b0105c0e6502d016a03041c4c2c100911800c007500602c08565403243c2d000080c540146610441d44a0540081da000c14620030350032554002c2c0c03000e0100c50915000b00c0c211100303020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 49316829 1250 49315579 49315597
    0x4080a060f060f0504020a020c130614060304020906090c0d0609020a0305090a03020705040b040f0c03091a010e0c030414060c030a11030c09040e0a050d0f091202031e070515 76
    0x4144003441c03440c80386501c1140c0888550060008001e0b14040074000603411800c0c0500c06d5018064a10489071200041401d06101ea250700041035400c0c1010341c2016625084860f000b42c0c0d0502c10007005031107149030140c108004a13050300e081d81d600085400b29100c1c5485104200d401c0500000716001a80c001c0c280000d55914148100d075a41400c241c0d8a0081d000080c00581c8100e4041015003002d61000c40200b0015101007040007900314401d06440e4400d289078002a0746804110a00104a07003105c0d984401d035051590951410307601444070390010300020f400c0700c800004502040101813145040c2120107003a01e2451800101c1107185400444100d4265800c1030034255200e81c03800b003240d214442014400d820405010181300042445003840709040c030503101c500b00400c008000600f0900084d5442c01c0c02000d5000001b4001007070341e8044000180d1100440c00140d0700840c8030742c0400404100000100d018908946c5001c40300e42c0020b4000400c442012138090400005041d180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 49318079 1250 49316829 49316831
    0xc0705090903030f040b090f030c030d0c1403040611070f050c010e06070b0109020d15030f02041d19020118240e0907030207050102070204050106030e10061215090804080a06 76
    0x29640740d42050726031104450800400340c40d18005000561138184090300500d5120803210520072129499103960b000c0075140700164804580d542c103642a6009056402d00f0301c2c9001c4104451240300903007640000b4000030311035510f40120980381045141030b66141038001d248800b4515503410007a445007503506400e40000e0046050700325a003400b00440300d00c9640030007610030307981ca4104888000c1d0003245506046a486803049090301c4546500b174000f5500a0030240031003906841040111110140070300d81c01d524082403c00110030109942d605510040c0c5220a600030500c012602002d01d49224030000514160100340d0307410a000c08514090a80c8034141204c0003803109a85480924600590103206100040c00140c4290040e0114078403520002d820110301e50300150940300b00740c211800007075a4840d039043c00b141c10010224410309074201040841c0c03c24080120400612201030401a404a05181582c2850340414801a008145a91110f80340e44071280c82d06a0398070706550721 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 49319329 1250 49318079 49318081
    0x1110d020309100b0618150c0f010b0a060903020f0406050303030703021e0717070f1226010b0a050f090406120b1e160201020c0709020a12150e06060705030c070509 72
    0x1c142c0e9407051300e14004000b440b45040a50798001e01c014448400c140a0304400c003024001d0342110914090080c1d001108007801c081c010401495084039203020000d8840c0303400c4d0740e04004050b0454410001c3d42e4040e56a4059034680c40d0102c0c028041c16407185400d803100104000449034554040c01c040080b0800e9032950403181e180ca80c0d103030702030760b08041c0503501036040701800c404240c0c00507c41244100480600d4001d07a4036540c0a00c00c06010480c04280c030714a1403080d0510b003203d40e90042c3c411010200c415410084016118000c3c081904240040040e001143c3d0b000174041d44c140e00802130052101c3c60303c0f070303490703401d031004c0320b0030865003020407130003042d815111500d001403a9001c0c640420120340d079000d25541820141188402555402c202d007000d81710050104002400c001000580d4603181088020440c801c130180c48258146070100c09442d0210304000702c012034a8541c02200c440e118403002400610034100001d00c2c5120025019a1301000810900b00710340044554840d5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 49320579 1250 49319329 49319353
    0xb0607151a0d0803060405091204030501060f12030f030203061306030804050f120c09270c010206011a0d021b06010f030c0e07020c1003060503160e010504020c070902070501110d020309 81
    0x910b0302610002401001c1c1400010030500382070740240d0344912100220f4058003c00807010321294003d80050303d40b6515410184481c03184003050000030401e891303211400441540300101048460122082016000000303e00c80d03550343c504220510f403a00c402084440e9492800c02d00c554002d105480c050f0100c1078205da13140c070341070040724a500e0101015012080341c20b010040102801400001007407402010440440306640c0c1d07640140d60040005c100b240b0144001a24016050340003a01e40030443e41100718111201d426241c4405240c00f001d078460075042071050b100e00c020221a9070510503a4000125200380740030010440340030702c0c400121162103109015240000b16000cac40540d02117040c0342044d041140011069203400c1c50300042c11620750300064204100034245c1c1e15450b006c0b4206100c40400c030b022560040004071011858801e6085044d501c0340c00d180310320441a9030104004040c08820340040074101c2f181242a65580201c21010b4003c0d0412341d100540e0388540800161 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 49321829 1250 49320579 49320589
    0xf010603020303040e0402150c010b0f060405180a1b05040906060305010509010e1b030106020d200d050d0b040203070504080606030d1d030f030a050c0d050304020a090b0607151a 78
    0x41640d8000d005940f4144c240495001621780c0580200e0704031400c6031118624401a40140c070040c290300b800410755407400020081c004a10b105a80c0c07180b80701704010030030344e9650780314000d2020103101d15003c90340d12420920003c3c142d06411850880d28100c20480d16548036004109131740c0d40040070091140c031008120111202405025000b0500000500c81c030450706420550104036000c6107041c9041c0c2d0b000414164000307034041c1026a000310818108142c10030200c4400348034482d8401c440c0070821502c01d64805103420320100380140020350400d035240316005100c01c40b034043e00955490414550081c400c4c0c1c0300d0b1240c850700d4007510b800305910b0f00c3c01003200a4030078140d41c0c802c580303401c00260300909446007001481c0d140c410404885602102400949288000c548509490f80c095500d030714104103000c4640410000708108100059039405003002c165000c0038000a044040100464014851800301816100e69500301c1c3c02d6032152070704441341d0040784107010204564440c040c80 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 49323079 1250 49321829 49321841
    0x905060a05010305070b0d02090a06030b120c0607021903050106030807020109061b021c05060a0203061c030503130614090618010c0c0f020a030b09010207030e060901050a0e0a0b040609080f01 84
    0x304a80c010f00c000700500b102502c0171f44070000f0340801c010700c0d145a0200080c480c1801e588034902107521a108200d40e40351000c041c030700a00c0f84c0005414075001d600002200342c0310f01d1030001e110310300e1030008849411088030303d40055640400200501a1203003020303c0190000c2c40b08a00043d0001c101045440c80f0300c0d070611031030070811180c4400e02c03020303420000c40300700007a032000b41c5441d40314042011034010014540601400c040c01039981c102002032000c50004013403000f800003071201c141d02c0001d40c0902166072051104403150000340242c03500b18041c2903072040d1050003201d06002d202d00b01d40d011940a0141200c51050b4a0310341c094905503090301c1a40b0042000702e103400190101244005901c0c5290600c02040d0046d040e850340d0701d20403d580c0588000320f107694086007a00400d42c11480300c3e400d40e9000c0b50030324200104c2c60002070480c807802c412070040019500c0c2d910b199461701f1203038501030802c039040d0648590300c5000040c1030209500c42c48503203104030301d001d0030550018801c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 49324329 1250 49323079 49323083
    0xd09080c0a030f030c0201140406050301080705030102030c0d0f0605060711010e1504030803040c260c01030510090e010f0e010b010e060702031c091a030103030f090f091a06030106030905060a050103 87
    0x2d4483c0d040291401d8a55222655099052211944650786041c20302002007000c0c00e465212141c0325410504a17526101c0a41c200318000e0b07204109010b14002d1001c141d0f40c50200c05440440c1c000501800c0034040c1280c0d50006810840126009040101d2800b40314030392402aa180c801100c1a901003206d040701c03119040c00403081c104414000b00c0c0c0d69400960b0b20074001c44045904640d9035042180c0c1c02102420a400344c03003405c0e40070724081014480604482c1d400d10382030003203050030030394082d01c410303a440b624540c42da42e01c40c4030384499000c0d0810324039204000c008001c60b0450043e10780c080e0007800c602c0780c0043c00c030000140f042e01c0c100003034600241d0064001c08040303584064081000c03581c03110001c1401030460002a0703a45000c40131800381380c104102503481e5451407401070700c03110011000364248803002c0d10070300603903607654500130850b01c1c4001c1c045002181c00031448a1a50804c51107900114004008280c45425801c40d40c0f60902c200e00700c0302103a881d0012201190001c0c000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 49325579 1250 49324329 49324343
    0x120f060a051504080f0703030f0201060506091003090b0a050108070f180506010c08030406020409110c0a0b060402040513090b070503130605060f060304030f0e1c06020a050c0d09080c0a03 82
    0x1007442282450048440004008859645002d488828062410440041440c0d0710f07032044c00140308151b840901110a081140001c0c0009800c00000900602440320039900619840d850a03050512030f4010010980e0401d014244909190754040c0c0600307024054145244924040040c1482160707800108540e15100340c00400040142503101400001e003070141000000094400494018170045d400749110344401a45d4a10741030b018410f03034603150380b06000c1c140b041c0720320b4003942000b14140300082ea01c492440a00c2c0d507000c00040003030007640c0050390808803a502e00300120360203910942d0b0b8a80290040b112507520500202e59034072044440501c1c0c0c401c40c1e640c07031001400c1da40025400010081112100800c00c102007002a04108e4054000442c03070816000d1941c3c10541c0443c9815041d138600c0d1001d000104070300c540031020000100455400258024103074421000c0d17410007034800e000d45a00842c001001000f17550107004c0c045003801188068162882d242d04988200c03070303200364 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 49326829 1250 49325579 49325599
    0x20d0c0803010306050c0426010606030908120a020408010e010617030703051603120c0201020703030b0f0a0e0a0b04020a08010311010905090604020304050f07170601080304270b060708120f06 84
    0x10390f010181401419020003884140008a10100b4107400200c0a100310410890308c039080441080c2909c100354421020305250030900c0f000b04a0701070803152070500b0042132400320780b603a80d0403d00a01c030f181e12402c15075191440d0030480b1135042d00700008480c0f440c0d420050140e0356840b8903880c3e10400d940103004c07580810044003110744030320071038104502900740440d41c004400382c2c0d1019940c4001110740181d5001880703000b05030f010f1141d201480005c0d100e9044590303100011909a2140d1b001d078404a1901000180c61100da54200c003031840e501510940d11480682409028000280000c9808202c090f002c1401544508401c00c01c0b80c1d801800c040142d280c40c01440025030019109942c14043c5c0b0181d180c04080401c240401089010158001003c401106608008040c3c00142c1c054108100810000610910100f1228604040b001e07001f04215154002000540c0030385800031000302e440401e1021090282008002e02f50503404e0300d56a01301d01180742c44003101d4156000e0302d40e031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 49328079 1250 49326829 49326833
    0x14041b020a120e0306070305040209150108070309170406020a030801080a08090409060b04140106020706112806050106030501051302070210050f09130209031911100302121006020d0c08030103 84
    0x401c034401d01c50220704001a00a01c08001300c0d007171000c2150024003080c0c44030240030450400380280e039403143c00c0c2100085c80d2401000001c080c5140a00101c0405894a1001091000760100b40001c075040480c0c180e55150344d030101075110701c819681580490b6200300001000c0d0004a07143e4941e50344008142d24083c0020700f00402400c44500c00d50703420380d07903818040d06504c80b071003200301e05031410681101962501000034503050340d83d0007410800001c440a0301d8040b0b00007843e008034031b009035041c869070501c2003441110312034003da0140801e41420000111180c03da031119040c2d810541e00100781808080403c0c09910130b09000030342101b5803412081d06e1a129802805000580d501102d14180f240f10008005400da1001c1381402c942c001071141c103a00d010810002d001c3c440107804104202c2e41c0c0c45103020100c11820040c09210b00586a2450030700c81d41c11101d004280c910300c5d4a10303060224060700d2043e4240503040240c8200010180c0c2075008008482c2031075884017015285a00395 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 49329329 1250 49328079 49328093
    0x4051003050d050318061e0105030c091b28030c050703020a03080604020d0e03030f010e04021327060c020607020105101a12010320091b1606050114041b020a 69
    0x103117600960000ca4003a050000303002c2c04100d019418000c8694880078040e0b60043d07802c82d069011511039031102400c1c0c40203840340e821617648100c8507005030741031020310981c03d02e09205144108045000c1d00200920744004c20403100c51a02060750b0400800c02031240c240e03180e110b031103005005030340141810400280b090400c00c4d44000041c0c00581441481d000c03000550711200d2080807580c002000300a1254107a40c0d22500401840c44104501e04041d0042034600c0d000e1751410031065150210156603401c00072010348007500c88200d82a01d46c3c1c0c58102000100075100c1114010300071000072540480c414054076008a00c1c20140740d02c0d05190294041c28032965407030110386410240411402d03a0300c00341a0320b00860041d040c4040e10307500e407851012142c44004285214481c3d100601c62044c0b0307129070050540321140d005036503400e01c201c801d100c0c8982c00070005101741e04140c0080b800d8180e2100c202c9120b28151014045024844407141c0c1114080313540800580c031100600c03004c1000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 49330579 1250 49329329 49329331
    0xb03040204020a110f030a08090c010905060a0504030b0a0f0f0b010801060309050a02030601060509030f0d0905010815031e010c0935010608071403010b031e010204051e04051003050d0503 82
    0x203141801e10304c064107010418241111000c03860141e400100b13410390b030145c0012645a00050190241c501c162511002802400341d6005642c080c05d03000c19000c003098023440071100074681000d242d00c2249411401031022305220001105c45604260540003c0c0c541d902460725510416154218183e080c440e0880041c61040c50a407018840c014a180242e1020f00c0414040c0a060b030718103559804040a061a21203020400c540032f502101d038159019500119400903070741c003460700e007416440e240c18618a402c10480030036818002c00600480031110109007001c41e4542d10b00138400581c11901c244d03100d140a205051014000308800d50f40d00c2000c0d403222040c040712000b0798105980070407540e400c540054000c0a02039015513801c0c00030282403c0140b01e0f15004a0092014441090200e92110048000714034844000703940703091000420b4055401030080a4100c03e4044554406001e642c004131150901603482c003000301f4000003034400804c2c16281c00130300524283c00c0d0094210780f5580 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 49331829 1250 49330579 49330597
    0x1103040f020f0301020d090c140306070203071b05040c020c0307060e0d0b0403030e0d030903080f16030506030304050429040c02122d030a0507050306030c040207110402030127060b0304020402 84
    0x141c03c00c000d0200000c0e900c1910a5a80182032340f4000c58100400118440810803489110354450f030700308808a503001040342e010716480715400b00d1884481b041e56424181da40c10055016040c407090342c003690380c0000e5806034110218111410741b641c03035505440320785110030780c0364201244002a00c00704a0038481c031600607200b460000340e1010743751402c0d814007240114880000b601c980c400000d05a1241c0c2c20b41d004101c030a4207004034208045400c2040c03200819010a260b260000500c0c1613409205030f90040038090b205004900b440c107100d810340080200308004e00c03800c0c43d01905640c1400d2240c00e04201c11900140500140301700800c210f50000c61488030614840c43c01c041826941c00c007480100030586211540f01e05002c408038055801c028001c0003044010710400102e0341e400501c0d0401040700303076070044c0c1c2c0d1401410a4401c0c4036400c02100e8016000000004218251043d200102c40c54145880070700c10700c0541c0a000d0703c04c00c1c45607501c22071007440850050b14083e40104144c103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 49333079 1250 49331829 49331831
    0x60702011d0c24040f0602060627070c0b09150108010c0203040519150807021902010e010c1505092401031208060402070c27050606030115022e1103040f020f0301 71
    0xa5038441d00800c3c582c0c0a90411241c034800c0d05810429141c0411203140c00683c12281d8210f6402c030303824140310b444c00c2c210041040c1e10380040818945405a1400c5c031171a50400c00c240900d141002e01550303124440e840c10f584140e00d000000868120622655100c0445640a549080d162404201d401100414031138236012040300001841110b20050044444858075500502e01d07140c07a0190a200e40040802090302105040360700603a8440070304800d410090034032000d07101c1d03242440c501317035541500d21440c418500307000e000c0e400b00d00140380407600c1c2c0004141e8030821801103250461200a200090070441d58204200d4450301804000e030303002d00094001070404840d5250440307814282c2c0d2110b03c07507100c2541c401100c881c070000c1c80c801d8071150800a01207804d0617004500244414441d01c24003d8034140c0742a1010302c03d1048a00441240c0c0c042c04a070038841c440c4000003000130868a280c1803420205003912a20001680d1185400069504080b03986030240b000201007080b400340e02d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 49334329 1250 49333079 49333129
    0x3010b0309190b04060f0213030204021e0c0a020907020706020606040f1e06050f100504030f020301020c1f1a010219031112030402130e06042006030108060702011d0c 73
    0x807081242c070801442e030103003110726001e05250620004803980c0350500e071580f500411007881c04000c1401040120b99041d540184e4800e81800281c0c802c0d4103d140c45403035507000041091401c1d80010b445e0040500032581114181c80b068416070352003880d40b14500150308140c2c000b9003e884c20354082c00203204034582c0800c3c8000704000d600200360720301c600e46002c3c950f10708051107503080458030717880c440320b0030340c0c1201e1004c4000c0c0d0301510074011480020000c0c0f480800f4001192800c0d019541140e1400c401c4030900c2c045c9a9030b04500610030401c0e81d040318948481000c000510721041e002c0c5010680203022207241c07012100c16120a40141a011702c001d03900510344007401001070704140440c09400f03a0301d07420184100800700d0003011381c00d03008a0a10b801ca21101c140826019001a0b201c01030300050510711403842c481003030700c0600c1c9034800c80101c00001d0581012031200d100380001c2d40200248180010040040c50500406403002d5021020b14031440c103002d0341070203001390106580d84c80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 49335579 1250 49334329 49334353
    0x603020a1d01020307290106020c0312130b030106080a0c0f0f080403020f03040602160b04050a0512150109050403080a0908031f0f03080403021003020f030c0a20010204050f0604080303010b0309 85
    0x402461084c800d4485503070a2911b00f40812000000e0240c0042c5c4040c0c034a8014010000c1d80c1c48044515540003d0000240d43c207a6600e045400801041c1212a840d03c03580e4804010340b080000300c8841103003609002120191a10030710451840220a0315450001d40d0400d00c12030309540002d1088003548203981c0200c496400c1080a00014441c5030300501022101c6141149000b22035881840f5260081c40140801d980d030402c41019540c00b0350781c02c083c0c140221925460450300e1050b401d100301d444400802d10062079001248118020f480c1d03040b840c1c54110800781240e428082c0600614000d00c04244190701510040611000748040d505090303860740480041c80e000e9500480300c0a0700042c0070001c60a05941c102072612150408604080c0c1c0c1d80c095808510006084004003000010040078140c090350705401440d060440e441036882d000e034001c1d8000d600600850740b04204d101c107020424600002110107a0703031101d0156055920301a8800b003141c0000d01020710500030f040c6e440f00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 49336829 1250 49335579 49335593
    0x60815060d0c03050c130516050c03040905010303022a09070503060103060801050c0d0e030a09090f090b10080f03090f040b010908060a0f0606080105031b031018050105010603020a1d01020307 84
    0x2450194002d1724000c41c3c0881007008000c2450300345044c65041c5010040ca03003400e10320400c0c0c02002c0d800d1065498201089481c2584159002405858601800030041c0b590000d42e20300d120400000d82c25601030050800f0725075440030f0013030a6001d051580002e450f1440303003000d181c1202c03042c18049031a50319882e10134203448045417400c280513030110f503640000c00700e40113880d4090780c0b40340594900300100d0f0004000740c186001e05004151100c10101489115a22031030f65150844180100b60504180801040005110317240c200d2107211450318910b4004030450b0480c2c60014403801805000105000280007428900c0e814403002c1d480000d02e031881800158492450264001022049041e14904440c5903400420801080d807005110a44001900400000f1411020b00c43d14240c0b01c0041e01c3d000181000042a500f020b1442462400c08803040305000e12400081c04603a8841800724101c2c0183c208403000148030511074180b031035900c80d6035428a501803040d0b038034150140d25980703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 49338079 1250 49336829 49336853
    0xb0306012f03030402150a0c0f080f030a0f06050303090609040509010906240e0402090109050405160803090312090604030f05010912080108061602060c13051203090a0603060815060d 80
    0x20741d203400000410045107002c0c83c501d011144035030011800e00c1d0344110001c01d009201f840080c100c15070200c0403810f02c050b040c1070f201c040014000700c0d84c3d40d180420098010340707610071103055803605011010946c1e241c0030050307032030041000d0b0105040000382d2040202404004c0c3c00e00c2c903255601c00f40d0750302103000c502807400b01039a41080b84c5440c09428070701c1e41c40c10000b903215040d03150701201840b005a0300c859813070341164026840441e05031120304100c2d0418241325009100705807800c600145925011010382119a42142903070f180d01500450002148a6200003e6002c81d04010071310015812003d14081980600d00000d1900d00c50365410016101c495861800326100d640104030f200c8040000540c0000352080c0311880304030f04c0c1c0b40a541c940014049408240300420601c44c2e00300380f5070346d810042c54000c4c00b2310700c003a40701c48545480c1d42c02052040c1c080c00d145038000c1011030280c010320080f00d107130a0050030400c0300f22100700c2590030003820b09988075208190f40c0000c036500314111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 49339329 1250 49338079 49338167
    0x1504020f120c0a09080609060103060509150103030216140303090607080c01020f04030c05010c0321150b041d010303020a020907031103090f0105060301090317090a020a060e01080601090b030601 85
    0x41d65103a03c1c424014050200316400000c040e0b01c08410000071120128030141120b610910201e641d0b2036a0880604000407040c880800c202108000024141d0020b810721100d00c181c00c50702501d5444440891002d044002800d4040d4410040d1681c68100f080080032890301680000f81881105e507415400e9078808039400310200381c0420140180700000044000030705003424803419130405560042c000c0d101581400020800102d6200300700e40759900011202c6451610841690f0385900503d0f82e280c2180c0101102c1d44c1b440440d408900352802101410b076038243c0c0083c0740705481035003084800b001c02001c1c1c004040d200ca91070406040100091401150810042d1052a040b1042182142c0006200921a070b042015803800b003504056041d0306a52801b000e4240c5660b0b01103580e14080d40150000c2d08a00d01d10400a1580c1d8410000500090240c1e46c1903c036071580303001198404c22074001d101d500c4104001207a059802040c1c055480c816170310340010f02d00c0707001c03100d020b142c1042000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 49340579 1250 49339329 49339351
    0x13030b090f0d1b0609060f020f190207030c15030209060c0309030f0c0607020405090c1c0b0f0c04090b0a03080f0a020c04050c030f09030f0d0e060702061504020f12 72
    0x110910309005000c0400d0b0112580303090f205446250441ca0b0a022180401515050303a45012900f403048541000a21100c4960190340d100b003800c01080b0035500c201c21a0000100c215940e024017440420007008076500702481881031401d043c022004500c44072400018180c0c00c00c2403181ca501c03030748003400361003074007001440d1110008010705040c031f80707200140d0308250030180141100d0368422050700c2200390161000907465940c0301000e4600a130044901e640a002915001401c9801c464030007041c921440340c200041d12080820140c0c942c0c00e48019092450901061182071900c0d400242e0400740180320b81c4070b181e80c945855038554415802201c5540d80055100d1040d034040080081610094808008030303d0081d070582c0171408007402502080500c02c012680d032240400a40310300e4a0001d00581d40c9046031140c080007442503445070051802107500180c03600c0d00100750789204080105454403581b4480c4100700080d4445007100101c8201448178110b040b2180c00e4a900c40c00c646c8071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 49341829 1250 49340579 49340593
    0x1208030c09041e15060219050309040510031502192703050601080d02070302030a110303041a09011e02060403030b01020a0803090c1908151015032901020c0613030b09 73
    0xc43c0c81910494000c03421100e0000c2e000300711642e400140001c2d03009110104101c00d0406142003800c501c6a402d120354480d080030700340501e10740281990320489106d4050f515500190b036410005a000c3c1101c020310540381076a014840e13030300403501c040c0048c840c95503403801464071102c10107024a590b003054402c2d0303010070014410b00e00108008400320001c0e00003858000d10f5540000d40d10580039400404502c004c07013580ca40c60310700304140d4020380390b16000d106200312444101c182d160015548140012215854960503980c4034084030108800350b8040c1c45c06691b00d0f03c0581c0900f0f1034801040c11886422070340c501041100d4081c1d401002004050300c0b010640c41c0c100b01003d0020507200e519103030a4101004154400140198031000031039000b10542d9485201d000e1305400303980140c02008030a00c40440465169201d01c2401c44150701d100b13000d501c1045030001070004009024056403113103100115914158018040d4058124011100c541d202c0c0d846544606090341c1d4100250300c000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 49343079 1250 49341829 49341881
    0x2503030501120206030604110c0307030f080606090612060a1d0103050111090604060e060904020d0e1b060f0714070e09191a040203010e01180218011208030c0904 71
    0x801401d00501c0c1c2c032209040c120790150009501803102500b0544101c3c1d5416000d07041d0b24030a01500e01c2ca06004080d00d0302c58950341006000d80200d43c007c0800200844005007492070305900361440d10102825250410b909a82c810080786400303420b003588151200c50010786841807414104d8800e0510040844552441c070f442030075070b2600d1003840500c50050000b03458549840c0280c0e0111009494030260501700c0c100440c071140709941d00c040e00310740009802d95040013990018000c0c558481b0499060070000c05800002c0c8040c000b150754000000c108254280142d40b01030503505000d580c0c814101b8403d28442c9241c904194440c040481c884d50420480350780c01c0c401c00d00f40d40c03561a010081c1368810341e03940700b002c8810f4150840c1c0146c5200400d0a5450035840341d1100d10b9600020071050f01c41d00380100c80c040d032016040b8400c40b41184241c4003200c22580c1241200c0c02d552400d022036255070340f1301c8941d0300010b00c6041e1400040c0481070059584d80038440300305200c40d2034803442e90011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 49344329 1250 49343079 49343081
    0x1060302120c0711090a090f060518010605060f090a0504090c08100e03030a05040f050111040503010e0f06040605041407030c0603230105060a02070803042409150311250303 76
    0x104010a042c01c00d12a840105040c98150746002104440c01600b030341e1031030300220080100c482c002d0840b1440c801d03513404108196014a000d141044401d0b0024241002e03414240c03007050043c690001d00c28131408698155804c060b151610300140384082460701d407000f203000c031801c014058a1220343c45601304160241840000113061048000307100601c444020aa582e1001034041220036135500d002505011519805000d640c0d809802441a01c0681ca540d0b60550828002c991095182c40050540e007100080e2080f050200040501402d03134072502e4072002080d0041c419240381c11189481d40803018144282c1014610514207501a681452401021142c540031116898002190300c81d655042d1140d060b41110021a5010b41c0c0b0300c00703042e0803420088141e0121800d032001060200b841c109138034252180700b25035115491070003a46801141d004420340700f020b440300101d44050358401c1c8250004060359008060440c607104e1410b0a680d540e08084880203440c50032025510708041e45 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 49345579 1250 49344329 49344331
    0x5010305070e0603041104060e07050405060d0e031602030c0303040f0312090f0b030103051908070b04020415080a120507080406080c07080426010501080c0609040b0d032d0806040b01020f03030106030212 89
    0x11102031040c2c00d203000b100117882031046009051044200fc2050755540704290012440c10f0043e40c00da0380c84580816580c04000761041d400ca120340920030302050942000020f980441d4044803240c0c0344685543c46202080d120303004150704202c907004000c1018542c1c3d0200c040181000b0160136900e615500b400c0781040d44034a01c00c1b40b2200c0000601c40810080825200c10580101c00090b458a403840010018052001004403051648800081d0001301050031080c1c2070181070100104603058504075443d00c146080249195001e00045c000584207507001503004290a400c949404640e49905807a50002e51007481510301a0001048003010710300040e02c41514040240510b50410005c2c0d600d8203c1544200e001f40404070380c54520359103681224044203406407840210980300d0900506011100030001580706003c055229985009409258098050303560389040e502c86104010150449186660452040c90710003050208280002c2d0b000302246c2d00c0059966072000e48012451320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 49346829 1250 49345579 49345589
    0x709060e040b0f0f01090e1008010e0609031603020f01021305030d090f061b0b01031a0f0f070f02010219030501060e030610030602031b0409090b1302010905010305070e060304110406 80
    0x20074000c0300304582d10f89079040740c40a41c0465030081c034030b80d2040c01250b0b1000c03250b01c06a44500c0c2041031048825480303403004c007a50741610003400640c0740380842c1980c4000c2070300e80e00440d50003000124204112240c0e400c6485202c1d1060b2003002d03507c00044c030700b6238100240d01d1880c011222410485807400308140700d40030007581040450300d0710b401101000d06146109400900120105500010342c400d800b941184c1d500202600c40c03075031241880140181407201900c60041140c020625200b000c5620a00c50340c0d405c02c110301145c0e516201210629122a000030035507400f480210640318501c01d8031042d0b40c8131a41c0c002a590f1400c1801410702c50310705c0c1554005e4110300140054400140c0d40b400c00d60340c010a0150340c070745036640e56411050140f5142c801070344000c04c0101e0000340540080301100d0041d500f81c0820b4941c058a41014125900f000780442c9025008005030f500039003107154807248500b048040c035a68031001c12045d51084808a5407890b01202c0c40303505203000c1c891640505 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 49348079 1250 49346829 49346831
    0x70f05100903060c0c06020706140f01080703020607020d0f030804170c060609041b0806150603010e0610030b1806030709060e1506130e040b06060306010203160c08060709060e04 78
    0x400e600d0005009214103001c00341206880b6045040d22034000c142c01020558440700c2159a4100ea0410100400c8051210841c0c1702444000c2401c512206100a050700e801c007014010340d030300d554204211503100b10030807078003d4042200c2c07101003244448074082d59402074851084c2e80c40c0601e021111364401a880d210011400e1240704980704c0001001e03035000380305640e004c0c0c103901c031800c0c201043c916949030040a41c1d489540822104804100140240c40400c210704441d914282000305a000c00d006000c164500c0c100080d40928080c207192400740d03102c2c01c00003451300e581d8011807582030401245102c0800d08105100e4039080c00c120480040003041400c0240f182040c04150310090040c00d0703032008001e501c2c0c0b906860b940d4081218136022554141c0da0145607941c406208212040358180c2d01c60101d080040d6940c01c07e001240d114000582c0918500f81c3c0c0c80c4098156680a220182d842e103401d2000030514050030070070140070303c51a403244580607150603c0108081d07194078415001d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 49349329 1250 49348079 49348099
    0x130501052a0f06010b0a0206010807030b06010309020f1003090201080c131205030d0f0b10140405041104090603060902120c030604030807030e1006140109030206040306090c030501090302070f05 85
    0xd041020300306051205400d444080780210300c0c21500d0800c140050055900a900c00060300e404444024203000d00b1940980e10719a80e54600d0300d441e0a201d00c0084d02240e803100000320158440c0d8014129144020321707024504111101185682d18480480808240ea6002240035980c012102c684e100440c401c0151901014800f40b80c42d102a03841352080fa0741c0684a07060400a05005582414601d004104407107a1088001070240c0110074a140c050000c0000180400380700c1d01c40e100810340e29031205880e103442d003410b200051004c45100c0f403840c44244404120441140980c9000703502524002c14080514010002c0c1c20380e8009113042d035035220b041d00a07844c1d00d01251a0b9070142d003506001c0700640d103d850a82c080c00d504102c0014500440d080d080e02800d89034881000d882e4130b0003400c2c0001c6061401513a269400e80070103075000c001800f00f00005860381d000b4110742845001545003460750707540c1d414251180c08030121301503084580103006080322000d101005050444881e800c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 49350579 1250 49349329 49349347
    0x4061d072d0b091002120d09030f03090c0e09010605090901020307031401030c05040207030509030105100305060108010209060d0908090613090b010f0c0b0403020c10030218060702010f0503070905090c13050105 92
    0x703148588520f090190b8241213100344207900902c1152000b501c00301c0099640d40351109000000c1055101c120041060060300e540114800c0c400e00d032246a00881c402001400e0050354030480000a11004596490380c0000c1100c1e11600c8074203000d421070000150316070030401d0b8080c1c1510342000244034034122580042000c590101c0f26442120001e50300140e954a15090490b4144680c003a119059801d244c284112034003000e01010803a4094400c1c1c58159807a00e0a8900740e11400c40e01d070394020400d00100c014402a6480548101e1050b040c10703203000750900c04030385140c000d0520308501c1c039280d40d42001443c2c454098200055400d20b40702149098070340000d008038810420141200b8000c0000400b098001c010940103500003c0000e85254080d8030014040d41c004a91a05018001c4081c3c0c1110304002c0305848020f58140c48584c00e03e254901c04031400d810091290082115082e000140c17521280422402078245005082d40c404c181070001421138000d84c022410804108007a03a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 49351829 1250 49350579 49350599
    0x30606010f0f0f050d0c08040203010b01031503150204080d020f070b0405103207030201060911190e04020d0606110714060a090801021612020303070804061d072d 71
    0x20740211500b03000f01c99225290044410b40101d102802840d0b01d0407401620080d0001c42041c170483c802c50090007011012001182a11015581c6104a0213150700a00c0050b154150b0000100081e400050500340d84214035032030020b2070358100000d03070082c50441c0c4400c101403100402503c07500154034030f41854000802d10303051000003141c04026403251055100c450b40c04441100c118440e10070361903410040c41e4010355078401203049000d50300e00440081c40240c14001d2000c10707002000a02e082002442100703a01810310035a8078200402c4d480684401e5845101034181c0ca00c280c00b001030190f00703251014141100002803841c980c0c1c00140c0c10803504003034103c0b45800e2030013501d541c0d4603041306c0c0c2c0301540d14140ca0340120409500120300c0343c01c000c0000e41c0c21306509006510071450070000120603070300c0f4841990700800085401d0006400b00d211a040321010341c140382a0401440042a507103414461103411035000400320702c2c4600201c2000c0fa40060b04c06400001c084c400600c0c20301408 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 49353079 1250 49351829 49351847
    0xa06080318011803060c030b120c0f06130e0f0c031308090d081204060506010908030901030209010c0b0403030905010e16170102040b040b07020a15020307033605030606010f 76
    0x46002055007a441e0600c1c0d11031420112080351000c1e071006040d44915141021305840801e10000038038180d000750341807502c190b0801c045080c0c2d81c0600820500c01050103040710710240000e030800000c00108560003000b02d0f1010041036003445034019410008a0b248401d80007030700c4035920403030520510100c182d482461940b281d5003c08503079600c042400c04107614550326800076115007400305d520031607001e90a0845208038401c0200b0849941d812005440c185143c2c000d00c1c540d54814005898a54020740c010403440310141090800c6000c1507039800c3e40b00c401214128006502c842d906000c114090003000c1003454070a0241c9441c7c100b9565090203d100c13803040d410008005182c0c0c40400c80d003941205c0260915803012642e40e83c03910324200787c40c1c2c00240203d0080800d0400040c0d20001042850103902c0594059803415500d81c8049401c1805030840c44a880419000d20107854a031190300d4615407018441c26041c1845d2404240c04c00100404540c1840b0441400c5241150f103d00b6030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 49354329 1250 49353079 49353097
    0xb07020c01030b010e12102d02030c030406020705010902060c0a0b060f010c020118050904050307030801050d0b0112052505010801080c0907120902060d05240f01030c0c12090303080a060803 83
    0x14003151b6461100c180c42c01810448481005103024010f80c048511380780d1103035020500512031703074100e600d100b9004220b2104841e42c58482030144003150005005400500c081c500410022400c0400d680008045034459070441d4226801030f010340c810018250f044d6035101c00c007141d407141d100000c0300020700302110300700e0028100720a00444810003008418103034041c02010304031041501c0e041c58040d983c1c1c0d102c3d00c010740100c0d42c140000101c0f85001c0003248070242d4030905074202039103021002c2045001c10f14040b16070b80106640700c074030380d040300c0800d1f07260b0b1005440303020f0001c2c03030040054502c2c10103070040c0c00c05802c128102c45481d280d0a10064204401d0b10300300d000c0f484000e0003840108034400000758004400500198080c1841e0400c1c0e004829050700b160a0302c02a04441c0c0381f20410080c1da9410100580d20040c4a43c000d80c02680e00c0c2c941070825100e001490351b200d0464210b075217012404540c08142c1070040c164881c004503482815040200580c904080c10b141c2d60740613001c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 49355579 1250 49354329 49354339
    0x30a0b06060a0908010c0504050306011502070603090203010e0d0305010510090e070e03120a020d08090f0d050a0909051e0705030702030301030f020604030206130611030a080a090807020603040b07020c01030b010e 93
    0x20040541d0f101d011000000c080c000000c20601c0e28908004050b50300511030b0501c03c5c402d0034004507805000e12601c0001e18a07a400400416107040700c00e6003d02061403090b41c1c155603e008050321100c0c20302514128407606e81d00050190b0403e020006601c00b4215580d00308100c10000303020180300c00c111725402200c2c0e4144000003c55240000e880e0000d00c0480000803500401c50744201c50300001c14484910b55504c40903410340d0380b00442683c402c482403422500d1781c001c2c04081c4050340a00020003404200f40740024086881c1c07150041901e0095410a0004405d1080e60741c0452442e03684980104071490018a03505124a000750f4030701040c040038160f03d245405038011541c4e8002110029580178094689a04140c0d680030000840c40c8a8400811043c654070000342c00301000301c440c1d400441c1c446503090380b50100c3c010018100004115107100003004403030090ba44204c0618440d61013183c40c0511840d120b031700242000344401c0814107050070222a03c0250f81c1000303000b013041406580c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 49356829 1250 49355579 49355587
    0x5030606090402040b07061506030b010507240608240f0103080d0b0904060f05010e01120311010e070b03100902160305030403120c0c02091308090105160b01061706030a0b0606 77
    0x1c00100244280ea0000074640c100041090401c101d13a000749605220440c07041c11860354494054050341c071070031145800140100403210000e4445210502e01c924038400b981d1f84011001140003c40e0247d401024a96118107554880c140030001c4000c0b4402044610300c8403800c1c00c0925075002c00060000030481c0901141c509250042c81d4405005c055000702180007604103800d0030390040c841407d501070030074107150001c03070b10611408005040755140c16140c004900541c504540980c00c06c2250601552550b44a10140f041008102c000d0401c0b01c5410340d0317900b4042c0c04913854501c95072110416500501c501642d001c00c2200d59106103405061030365a0755110300d801c58103050400d0003085103914102c0740b000303119402041602018800e403034500e030303686030046822046104550003c00c0003004200d80b9629501ca1400b400980711540340307003464440f4a40d41c148004909030003000c002070a15241c01800f8036441d44441c0c10030360507805041c484110761655013140400030320300c9020b610001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 49358079 1250 49356829 49356847
    0x60c060609151205030702031203010e0f06030d050c0a080c1c030902060d0b030307141e0f07151704030f091e050105030711010204081b090f150105040312080402040e010c05030606 79
    0x1700072550f85c5a40201603a41080071035074801010740081c028101824070480000300042e00d126681c1780281c1008004241600111404884680c072203545501c440c05031250f80400580c400c07010b0700302c81c1d4516000e0107004045074842c2e86010409260328081504005101340562101e20454a5a00c10003002044940c4054042451841110401428020b0288801c000c0400100303020405d410032298a81c0e58858492500790761300ca40404040440e000a0000c01c00100740d40c46000800d003c41c00e0800a074800d007520408416001c030360981c0840c041609401103158411200405402c0034008a400400d0020601506800c0da010f540c2c103000d0000b0100300303851701a150104001a0100007555a04d4860202c03940300c14008269003c15108203c0c495580e02d0030916451080c9000203810440d55110603c3c81c1004d14001450b60501c601000080b0115444000320341000c0000d459410150801d0b00c1400100c0b00284920081649018100c00c4155480f50440ba001102150515140c401d04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 49359329 1250 49358079 49358083
    0x6261609050c040b03070c05010b10080c1b0d08040201260a0b01030204120302030405040c080c160206070c0303030507020609010e150612030408150a09080301050d1a01060c060609151205 82
    0x5600003013010304021040018140c0e000032038242440c8104000d010019044084c004240505148040400c800c003000542d118000d00107000085884c1c031074a24411a503920113400d20b15074280100026042c40c04000030355130452109100b940d0a02e440d2040c0c1d030802108482112005814001120b8491640641a0b80b01e1740540d07028007269958401540d401b860040e40e43d078014810340f03000354104181800f440e40107013241c61040481d81415460002030f0888060320340600c00c070890b44103205011031000b0400c00711a110245120343c40005040c2804075010f46040300c000d00c031484070381c180b440e80b40c03001c440440d0180e050010000241800e071a1b0900080c0e0015214500c041d85200116000034142c10020b001c40c601d841c60200707403003140c81e40d201c00c4054444940010384030320020401000302c0c0c01c01049000c078182c06064852050840740701da260000100b0703408503000a608003401014400382d0300c0b6400c000d20340802d080000344840200c1461900d100d11401c20b04044015903030040c0401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 49360579 1250 49359329 49359337
    0x8070905030303011d0c090a1503240306180309050d0206040b0a0305070906050a020601050907030b0d0b061c0c1e150206041101030510090b06040906261609050c 71
    0x80141500e442c1d6840342c5841142c00034440c0304682d1510305c07801180305001d800f000c5540308040601480d044504040c00c600341d00ea40100c00f001003550760707194040042d09094010200010fa010041c9115245040860603075905c0000c9908049035080c21500194000c150802251001d40300300311410f0260002805038011a0703c00304481030005900c42503168903511092040038961151700005440740011219809101c0d116005032744480014881450490121588403000d850085007117210040070905801458908581c17118200c002c5c04401e141840241524012994540c8010012610f58440024152041a04140c802c181c803241407411440700300050481c054081004000074000259240d60450b01035800210703040c60350780d42e03610a000750b90048000544000c142410102c0e9000105604944a035028604001c0021805800d000349001008400e4041201061070340907c401d0605400b1000516009211360142a000c014940019690b40d86000100c40c2d841c1f004000c45032107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 49361829 1250 49360579 49360589
    0xf0f171e040f06060602060c0a1b05010c0c110402160212030906040f0311040203010b03070e0613060207030b0907060f03050613180203100501080307080702040204050405010f240f080709 82
    0x28840100000e202c0040d080c9039410b0302c00c84041141654a01080f80c076400f098444501c4030404121000b610340c441d0348116500c9000014141810303002d651414211a80f00d0b0888000c00c60b154517030000d00c84818210015007105032019440c2c503019050f80402e000000034001d1140c8103c041e207d0700c05608009075982402d0281180790b880d91901c0b401c5044d03501521080324101c0503940700a600e818240242c9041341d40c440106400d40e11810026101d200d8101d450640284003070021f05100d849104441000307001d1500507011490a60030306282d55003004108000c0d590103131604000701540032031600340b0815945800141619903500107400e0340302201d40354200e00d041882c51110100800d0948000a100b2011202c0503071103206842c0940d0804d1050f0a21900700f8003504003c202101c008100491000700010f00c1c00b515907002400311079080e003105902140000c0c091141a011213540180222000586040c60005100040401c0e0b0300700411333401c1111400c0810020350042c2c4040020349 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 49363079 1250 49361829 49361881
    0x605090a0c081e030901080402010e1906030e0c040c23070c090615090f05120a1a10091418031c020c010c0c0803010e040311120a0f0f17 60
    0x10340e07550b004541e60709020a800701d541c1451035508080010010486a0000c8180c48080803942d481e0010350304540c1044120360402d910710002c0013054516007020000e80302d00c4e01c000950f0070821181c1c0d03207043c4203064000e000717618010303403451016081110a400c0e030003c0e0340410000001103125181c0740c05400c600074940729010030041075841c0150071107000e90300038a60740072066849130703030454042440c2d03c41e07044d109c21040c409109900305408104680c50383d890495040d055941c1d075202e07560a440380c240c40e0740404102880405c501c4220306600906030031109003e28400b05520002011000e003884095a240c1c218240e824001802a6861007641c0c903900e078010f00da00310400c0040d500c50703a6003185a51030324042142c0c103070007041d80c05800d5130091400e0382540c1c2071110b8454003000281c0b086d0306100404604694500c0100207c1e0b84c80c1032108103460b240c11784d0442c003a00b03002070941280c0c20b001d00020b500901640c80540500388595603009852161038a03280075801d0420806110060 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 49364329 1250 49363079 49363103
    0x7170c0f07090515090103030518030316032705040f1e05010f0b0a0504120602040f080708060705030108100c0509060f091305060904080c0705060d0e01050609010b04030605090a 78
    0x10340041a0401110b0280109001c2640e921601e0000740940e140303069842640c1d0001400401c2c859001f500c0c44071602c00304146001e400b64002880c5400112000140c40094140f803070416034068040340c0070888050801092010a09541c242d141e464010980555951061441c040c215a001842d01c000b050680d1442c0f00061084100500b40034061040601704558000030740c1c298590440e0031300c1d00c141d5580d5003007908050000d04605440041500d00c19001d10001c02c0446030081000300500460703008204080c40c107145903003041001071854091000a000400c240e841c02304001d80e5801c40c00c80c002803400c406401c292114000e404a26801c040080342002610b201d1100901800c5800c4a400b0105403070600d596058540456041d60044c8240002c00c1c0003c0c0400c010b005581e03a06000e551403c1d03210b0001c905036401c1040d405031020307101c002c070400442083c8506600300c402a1221803140d818240c5820341031040e48801040c0300ea07240000340d1412010b0102c501e103070b80c0c000d40784c1c0e001d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 49365579 1250 49364329 49364353
    0x405070201020d15060203040302060304080c0723011805010c03090305030406090501021504020d02220203041a0702160513060b030c070b07031802090903090306040b150d050307170c 80
    0xb5040fa01242c0b03c00c0b4070340b0000340e100c0192040010b0448030503034000c41c500703400c5500784000744c1c00c058000c846101042c480504004010700240018200007110b003c8412000e4a000503000b4884100c42e05201084400b0046a00b01401c05030a9502c20301f0000b50200244c6401c9421000035840078159000205000c90840d61154203201110026406c40700b407000d02903480c0b1480a01614001e501840c0d56410304018180031400b038410901c1906148500c0000c086d80b10180da20449085440c48001c501540c0039024540d442c581000d0948000d06c0c12040600c00d2401d080068014503210b125910900c9444002c1a0070100192a40c10042a1070b402d001e200d05101d900075041c02c844040045000952144c4240301da0b0305180f070a0743c5544d00104081c1c080c00100c150150082050340002c00101040b41c5082000d00d0040d44034403690b50b820700d00a0b18181d070742d10100d1501d51044102c540114041040041070303c030711982103030501a4903800d02d0b10700403840c86400813040040c0a138200040c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 49366829 1250 49365579 49365581
    0x90409030e030709020309100b06120406020417011b0e0409021503070201060602030f0301090c09080a0b090d0306030320011805010e060106030203090a0f060b0a080709060e07020307140a020405070201 88
    0xa40300c001d0b011281626100c0d01d4040503800b0881d0005441d51040c2e9444141002a81008180007005401ca5150240c00242c94142c0c8400700c5042e50090313000601003111b5410b81c4511411030104c0c100801101d110f00d46060380b0f2944607030f00c4c0381c100191400004183d5a5070340c000b0180701e500a240c141c5401c4190a0700da1140c00403205130740554a07160b80010564000b004507900c070303440316281c540f035a820009103000070300ba1401c5900404c02207030f001103010030042204103042c130b0003400c0607a050310b00550440e182c4a4481c00040805040c0300c2d0400c0001c0c0c004c02c6440380216201d41d940c044030004800c040c0149401c004120710440200c03010401e0041c10761211903080001c0b0155850f1341e0300c2d2a415800ea10055070b100703205502c60b01140010600c042a40e040f07030352251101040c0c00044100181100c0500c0e00060415013000030200b000801c54800d0034000c009480301018140380880300a0740301d004d07165000e0f00151104150309000101844903900d200c2c2e000304104224140940024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 49368079 1250 49366829 49366847
    0xc0206040801090f140606100f03060905090c041a1c080c07030b0a0c02010c120213091a01020105010f03020d020d080c01050403030e010b09010806071b020d03030203040215040e01030305090609040903 88
    0x164410805d100460141d00c4c012481c18403607003004d41398812142d8641012034242e13480d00c0d441400c00d5507a27100459005114040d041c0144881c60040003401142820070007203c0008140300c4000349041e80c4806503071158045040c001d9040d141151803072042d8203100020384a0311010303c2032402155404030401804c8101c45005000e911010084a481c2c000d00340d089400e01100d03c00420b070f074510340001c1003a03590001c0007c43d1215504642096840c0b008606580300085030035000307281d01d0090020341d42d09102d9140100a21030282c10010300d1600403900500017854081c0c000d9075181c0460080c0400c2004407800100008000c000c14500745c100140240030390b01400c0e20035401c0c503030343c251246004210b00d41600c00005c042c01c46a09c4030201514070b085840b800c1105110f52901c450090796a00ca640b0742114001c0c0c40142e56071a0500c108490401032458800e120704e030030300c01481404007a85205054076450304041d80e4502c00c440c00100759010311352800fa8090700b00300c007950415501005407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 49369329 1250 49368079 49368083
    0x3070506220c0b090f0a08060702160b090607030c08040308030a0b0103092a0b0c030301030b0105010203030c1801090302060304060603120e090a1a1314010f060e010c0206040801090f 80
    0x1d6504030004401c06254108440c805030188448140a02150301501c0c010040c018004007008540b5141501003524005194402e0342c20f0f030801d0003040b204c2901070000760641c203600c0c0d00002c0c03050704018590700b041c000c0d0381c0c119003d20804145441094040c224541c00710b5000410135840d540c0da850010403070f6004403403601185003000729120380c0394001d00030107403001e6200300505400c40d40502d04403081140100340254038190141c001034001ca51000410031030b40700c1000745130b030784d030650400500c0c030041a800941190304c00c00801103a110400309941c0d8614450401c00300320600080101e80f0205c80760006940844000240010040b060780b040007241d125440c6101805080c10081c0e03560072400c81040e4010a01c41d0002d030440b40c11350300401003014801040b001071004031020507583c170340d041c0f008443c5542d01c01640404807250000d03103004207811814180c1c4113007003e40060441d00c1004100303040c81318044643d0115641d880665000c0c040241c000c10250310141042001100e40c2e4000f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 49370579 1250 49369329 49369351
    0x5060f01020a0b070c1a37090203030421020901080a0b0a0203090c0406150305070906120b03121b0c03030702150d060b0c03040513090f02011b0206040e160c050c100903020303070506 80
    0x850a0601d10307c0580e07000f4440001aa4410f44004100c0203010f410008800c030f0380340c00204008206030924400d01d418a180340b1002c0c0ca41c40c0070f1031060101c410010381001603994858400000042e0420395065440420042c01582b291203511100d858256200c0c030490b8010b00704000400c080b00308901000381c1d107445580500140d242c010081d40d03081141d006041c00601005090300707000d0380c240c000311120b0001400302c070b60607084d517504401a90400300c0400c0e815180c40b0981c07038060404100c151401c42080340510314240c0345a0006490302c5824280180050012030401000c008a03400b51000f0320072410328950703403640340f80025280c0d4000d00401d4400d10542d516410600c2062180241c8a0750010056401c00083c0d0010745a1082100d25080c3d03524012812100603100c004c040c0004010626403240113040c00320380c220041c5c40340c017031090812400c1895400031400c00250a5010202907403d40181da20700304048a183c845900042d4040c400025004d040010026905100d070320341080b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 49371829 1250 49370579 49370611
    0xe070c03080a0c05091002070806040308091605061206211e060108070605070f0f1203050c0a02060a0b0105040306090b010807080706140a11010509010e0105060f01020a0b070c1a 78
    0xc2c403000c0f40c045285140004005200c07030096820720b1040c4410480c85030044a01580d0740d000c0341480e281044038110001504007050080b17401042100407049201d44088000c09420a030110308240203801302201d1030b00489000c180191070b400740200b1491044406805001d05500f42641d40d25562280f04050381059140381115060100c0d040d8181c0e2071071405881d11600d03107541201e19421a1030141ca580100700310490025400341009003220307204100d000d894801b000009402c07510002e1170045813078020803050900c20340c00f20b0340a81c801c48001000030142600030040f61540215000201007510f007a00300c40601c1312011a0324100d60f0010111794001d51100c0d0309644400c04c2d441504003040d15965064140406d480c0504030502441c948013030b04d0321000c0c02180c2035481c181c0d0341c1861170b5074a00030394400b99801c5c05181c0d131005060307070101c11188007400003d54907042084054010003054012515261040030400e0920350000011090320002205064009200799050f05104c42050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 49373079 1250 49371829 49371841
    0x2091c0b010f03150f0b090115120903080414011d03031503071d15130f0f02030c040605070602090301020c070f05010903170c010b060c01020a0905030106050a0513060e070c0308 78
    0x2190810070360b60320040742c00303134801603c18034006030806080d0811314645641a0a000d611a940c0701c5000304003400304450607541528024000c0b40300b2038100e2100c1030511003d0008240c11082c01d6811551000d0703030990076101c95107800d0040c10701200b2801a41055291107007000c0c8000043e50284200c60303000c20b00c400c6031004160340c640072842107440426003a44040d8146201c40a0143d102d00c1030840000d92500d14400600900d403808252090b0f59a43c40c03a40ca0041402e00c0b45000080c10a1421842d500f810050030740d8034000c3e0b21860040060000700b40d010001c4540644040710307005802035465a1050705071941700c02150041e91001d0710401400205588150582421241c00c00080c00640b1407150745406640c2c0901c060300040c0d922808404045e03200d640041c440360082600050b03d80d824064010000ca840703a01692180c3e0524205103c0d65403500058012504101c9240a540354485d03c2400134014075400021348008040400107066000303000320200502c40d070360b5400300e40c2e204 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 49374329 1250 49373079 49373099
    0xf0a020f0a1d060319050c0c15090a1e050c030a081918030b012d05010804050a0203060403050c010b0409111c060213030303110c070605030903071e03021908030a0b0402091c0b01 78
    0x40340e40010981c0501d149c01102084100f07460f4004505d81c0030794034082c5668035226410301100001c64040040c030f042c14414060140f150280881c8100d020309924181d50f240d103800d900440d00005c0d410424201d0448629014810700c1c404c449001140e1169590350341006840341009105403584010450108001e800da2940901d038252064076080001c0c504140c01194000c4c0010021070b014800d070800040541d0701000300500c01c42c400d6035400e82d0b402000340440d003900e910b6a4524011410160300380005000354000340d0454006490600e803410342c80343c0c01c02200c101c83e007000d40418400999000c1030b42403101094280c9009417003d010215040c02c04c02042e104240e40083c15811401050000394410340c000d40e005070299089a040201c0380d120840d0f00d40c88460203126000c5c100f13101e03604154045c03051400e0800c8031050241050056103030900caa00c030080511130101c0c0c4d920003d4050355240d5060b15030900000e05104118106105016010300559000750fa000144400018020240e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 49375579 1250 49374329 49374337
    0x30b01050a0909020702010306082a0d02010206010e0702030f0703030c0905061204030309050c030115030209010506120a0e0313030303140c090d080f12040b0f0a020f0a1d060319050c 80
    0x116590300304082e45000006402900b1400c0124105601c4903400180700358100301a403000700b085101001c003098051040510401000c00643c040d0030b1018009026031f03008981c460450324061600700042c0c1c1c94040490540c440d00e03d404a0300f4801007402014542e0503404980040201d44901c401d4540718030812480f4001c82203920500d00c507203c001400a40300e5040400e0b1984284100daa4010060b00040d09441d042c9010b10b21141e4410810810361a04511960060506030380306498204002c0300035803010b000410440ea070a8a4030424001303980204100c1318041e08d042001c0c12099103d140043c050706001c1036282c8000003c4008c075901046200856001d004010000c403141c10341d039a58541e40d50085001110540e2050019000c13050302c00041c42e205034451400c0320814a0030303c4060500c00c00c00713000038019510500c9540744003c6c0d5002150032034161420454075409800c10524100694070700190382001d4048140000b03c43d05011078902d20003901024801030f82d48080d10703a40340c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 49376829 1250 49375579 49375597
    0xb1617041110020a06051321091a090303040e0105100e010206130c050a03030320040302011704081317010f0209030c0402130806070507030306050103090209040602221203030b0105 79
    0x500030003072070541d1509a040460141e02401a10b1110607140c4598003103030000c8801014208200403060304001001e0705150203002c8443c26107244416a003802400005940a4010420a400c0c43c216103151100b00b9910300d900020200c0340e6603501d440740702c41e40580a109150003070380e4441c80c480360180500a01e505200d41a030041001c1c1d41e80b200c00c80c0c0c050881c01d40a8840440100707010929840300046040075502a40380403610305c00e2404500384d14501c030010003102c4d59090009000503a44004d400b1030302d42111a0300d03070068549050600039842203121b5207a0105200c01d0026010410544500c0c2005201c4002c1004008024a41090340b0440c1078040d4103400c10700354a6464500395000c0c03c91866194007132007445840350307095031910000791003250103c1e4001c10b00108041e0f041c0a02c02c040c10080c40e0134040420140d02050b0110ba01a00040070300c1d4020500a408400005002c85000d600d0031500154a0395106082510742e098881500081e00786191450194010300c11500d40c10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 49378079 1250 49376829 49376843
    0x15040c0e0d1502040b0705010204031106160605150301091b050301021206040903110a05060105041d0307200a141908030304080c0703080406030e060a0b01020a080306030a0b161704 79
    0x70303140d0720200c008808811601666909100c08540340041d100900513143c405c60005a585003142401c801b9200300e841d0691140780d080049890103202c0700e01001c0c00c40e0740408041416224046200142c1d4900e4070820f4244d840d0411303c0e0f041c01004100140b400c820009682502030300c0c4c1040c5800e03441060780001d4440612400300d062410b080c5d000c0c040b054040d1601132014a000301d1401e00f0440104419100f0b43c3c810304c0103001e1450075102d107001c00260f01560320308070081008480e03100d010b0380340040d001e151400c101a0495040c02e1003070324001c400800e11b90360141c68281d80c10601d0066410140540f1700302c428090000d410590160030f8481101c019402c40d501c540d15400326521100b2216480e0094150000005410f00068400345c9030030b0b2000300f02540c1045c0d4051410b80c2c0184480301c114101440c01610341d80114429450300d40164040e9036942d00c00010900d846c280e910010811841803040040411008002000c60010b40c0c0d0f403180351415611705848034103070984000c0c10340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 49379329 1250 49378079 49378099
    0x30506030c010c020a0515030f010b0a0804030e010e130207050c0402040f031410020f0a030b04150b13030f050c030d021203180f1608010c0201021806130e15040c0e 72
    0x56008910a101e03c030303c0103282281e11915840484c040019011076410714160100c140262070300701180050140081e420f20714101f4807404401071400c40007a10290900180c1c283c0743c00d150b40b180c0d110940503040a040500c44850314808407000f5440038000b50342c1400b82d0f0710324841c940341c140202d500302e684a8605000841c216220001001c2c012072030042107115008580d14612201e00103090400041d0814070388940210030302605545140c8180c500ca13525242c08031091200c1d070f000c4081a04e070785448154503a40c802c2d1485103084450f800c0900700000a02c5142c082003400103488100c010150143c441c94003668001341d9980d800e00001034001c04090002070040c2e0b1064020201360b070240c0f002c40d14000b010342030b1141030640d14070043d180400400d4040c8840d0600340602501181340348000c40ca0700382e55007007100504e0504a0170034460100000c01901010080386580050320214000c0d040078108805070888120000d07000c540658100119030b0f0300113015690742004036001a002c2d082e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 49380579 1250 49379329 49379353
    0x70f030e010513060306060e01020105090607030c0302040b04090504061803080f0a1803020f120a08010b07020409051504051603030806040f060b0c0601031406010b1204060f020c0c01090603050603 86
    0x5480800e000903042003820f0064240c52207220007108020516034800080c01818080010501d0480341140c030f044d681407400703000160300001400d175403021544c0750020f1641d90240b0210060f110302c0e0b111103d015000708010400d83c81c1c41c0e100c60300841c440d00c81000f0000d030042c41c1d4030b900c2002c02009408039122500081140c00f00d10350300c5501c50800d41c000540140803054403403030705203145070640040e484000389407007002d81041940003030785401241c582856046030000300044414000d190941c20702144030341c115151500a910000d90200a4078405140700307926100d0448115010303a021b00c10b0b9060710f2030380e038456000710041c1ca4050740c690416660305400d010150603000c0f40d0800c00c5036581e0000504181c20302c05080e41c4022040546600e51550800c05481d159845010701542c010340010414070703102400312550042d003c100e02e42903560324100f0358010402e0550740b01e100e80c00011700103400e07180402c2c0202c903580d00740c984c0b209154640c10202e040342d10440d074071501075000c2084101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 49381829 1250 49380579 49380587
    0x140105010215070c060f0519050619141201021c06060e010f081806070f0305100b03060108040501020415030207050105090106141504091107050f06040b0403110102071704050312070f03 81
    0x107504e0340201d0012a000d501400701008440040f589002448810448150a02c0f124001e040d00140b04440505111101e400d086030f40021511800750118400520b060040d00c0300001160b090420038001c5446107940a108040c103490090500e45880c5810000b18040b800b5002e10a03c42d0310683d07420302800f40c9194103961403800034150405031f45040852011200d8200b04a901c035081c2a60b516a084080d00c101030203441010b8079461040c40c0801e418050320803000c050b254003038024030780080a900c1d541040c900a2013036420410309840010400220a50160024071445115070000c10041c1e840c1104503080722158016859141e44115043d0142d1404940c101c40405890002d18034090703031181c9000480d8002d44401c40c14650206400040c0b1909005043d2004080009000c0900d4142e40d0100341400040004040c003c1d01c43c1d80f030741e8440c404d605540545500002a41501018080c2041190014440c1522910810900403802e41c250300030b82d02c82c2c5034400442c503c144201d43c1c05032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 49383079 1250 49381829 49381847
    0xa140d090f0b0708070c0803040501030b041e0209060409090c0512010e0c1005040b1309150602030702040f06120b040c090911060d2d060501030209060304111903030314010501021507 80
    0xd501028180175100229103081d502d08000c1400000239552a8503090024064525024041d44958680302003501c8007094071417004000c1d000f50300010707582c10100000407007a000f9608124521071818120200b0010b05c61010400d403041250b170349048500307800c0d026090710704005002c9030780d0304181d417880d14a0502d505415007110082c107040d400c2c80e40f01e007250b1900350084880a082c5404001c400c2000e0480c9118000115040c240c030410611b081c010060740e030f44550b000081c000e903518030700c0d11010111544810090140d985400403815502d041402e01e1103001c3c0c405a40080060100080c000258414004c4199110540c885104c05100411404e60000300c101c960b2143c444d0b20080100004203556521070303101102113401c928504c4242c804440700b03500b200d0b0500d1320411008a440c2c2d60503040c2d980c00341d4020465045550086c0c0880d0015405e007204000140d8850004030806805070002500c2184c0740c100e04041e682d89000499840101848402d2230842c0f480115440b503100c0c100d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 49384329 1250 49383079 49383083
    0x618010819020f040f05010908060f0907090920010809070909110301180b01050a0f030206160501021305010219022b080708030601120902090112030c050a140d090f0b07 74
    0x1d55400c40510606500741d80c054194019142000101840728030141c8501d400640400e00c1d00440036810034031300c0c0e070b034031500034101c5e10000e07e10390001424002c08000c80d030b0141440c10390500032040e0928201c14100703e003c40003c0c083c0300f01c0e0305a25455105d810003510803c4501c00070980c082c0b408078840014405903000391012085424911400c1d1424000c510244400c188401210364060030003000100d81130300700e00e1003190b525404014918071040c00600356a01111384a940c0c040d009144038400c0101000100154004501da00d10844c4c06284c1d0030844500b0307002c0e03a4601d124030840b544681c101d898000e40c0a11a5840c1200200d2500c1907100041991b1025864490080c2c40c0c0071810f411110702264403030800400c020b00b6503070101d45490190080c440030b00212060307900043c030164050150580c0b103005505440e0905114041c04c0c004c9039041001e586000905042200c07100c070780c90ba071080d4a84128203403c4061840b501403c802c83e11461b6055000c0c41c10030203021510340c081401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 49385579 1250 49384329 49384351
    0xb0102010b09010f050a08060708010306180203060705030115030b06071214030109020a031d1218060409060602010506031603020f12010c030b0406060216050402090d0f030305041106180108 83
    0x1070810603403218103280c2e010b8511600c9404c04149400200100c601050700160b055400c0107091240e02d03500014158190b035480324001c1507804d03041c190b903900c5d420401406541440307100700b0311100703942083c000c60696508038035019580100740d4058080c0d6014044441d00010100000030228a4500d003007192740c2d840b450100207646c01d4401c0714a035078000307130007441c010b64ac0003411181f001c2d01446507501804014210b04220300b420810a901c51166420f60508003c0c009607040004c1c6c00c8600d000c058440050849440e16150011000106007034007034000558030b0b01020580a2500080700c0c206402c80608180149003523a081c820a102c001c1c000c01e0300118481040c1000400a018400640340240d40000c0c10740303154001c00007600d0a6a0211301550000700d8920f512169030010031055880544004d40e590070700b00041082210032100191024a909195004042c1d06810503402140203085a0b0040c1c50004e00300706507849a01c80c038070a080c80002c20741d60b03030303500a4416940c06130b10b07000c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 49386829 1250 49385579 49385591
    0x60d020f03040b0a0c11060a2a020a02040501080c150903010609020d150b0f0a2d11060708190b030a0206030a0603021801030503030606070c0519030b1b0307030b010201 74
    0x40c640260020b542c201c5400c54654100440b010007071043c01c01c00c001900c2c042d0070034400e0050094903040050311114415031034000e0301030320b00f030049000c060790010444030161031525503030020745465011800328803960904d000001c1c204400203010484500040001802d42c03c107410301c130141c0d809148001d40654075400000303048174007480501212000c801c00400c01401c0340b01002c01000858000d0f05400205114460b9455202c50030784951030900d09140320147c10f00a030a030b04001415070540b00d84440c80383c0039016680c0c82911138014000348000c448032515441020340b1100070440c2c500d400d40321402d40084406070150040a502c240c060706844a103950394021030026401120018001500d5500420031030030034801203014034901c54105820b550540c3d65081e01c1b4807006d050b00b0310814003c2480c00a01c0715a00e1414000d0100a00e5070754220200705a0011010703084c0700a641002505000841103034001c000308814540015032603184d50303100401500101043c50046045669920b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 49388079 1250 49386829 49386847
    0x41707030f030302030105040b100212071a0c0703090f0501020c1003140c13060e090a0509030f040602010605090c0703080a02160203030301090e12070c151101051302010e03010c0905060d02 83
    0x281da11180c2400b070f07030b00503980390b0401d024003041e07440082d5018082c400c2251145440d42d8007003603c42040b8600002d40c2da4036560b40c100000444031401d0380c084d05420340c60601080f131501c00014591a07101e0b85510741541d540d000d9240029020b88503817030258016030024040ca01e030405124100c880d6034180010594038a1040d09582c8000700c0380d181c0f40e004006900100d00022600d450001c103c1c0345001c00c405441c40000c16044007014008800c10784e21000419040d0318240142c3e20180f600515190f10b441c0e032000028080e2495207d1940158a1407001c03ca292114800300c402560301616503d030030380c480d002d20340000d501440b543c0c10040074640700f01c40140c0d4140002c40c02003821100104d80c162940b000641084001e8a800a030100c00300100000150602d2800c402c5403640482c43d02c99000e52002601d14903c000d0709500e075035180c03204000f01c102021000200160003030fa100c2c2d4800803070700c05140c22162082c2d400b0b004205d1166003000711b407512000611001d03e4040c2d016081c05109 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 49389329 1250 49388079 49388093
    0x402070c08061602010e03090d0f0606052716020a03270f03060f090507030b06030c0a03050615030d02070905060409060207050a170304110105030603010605100203040f0b0c0304170703 81
    0x199201102c0100d00f5118006480d824041d09441d01910b42c0650f241c440904c00244e8600e15055009050000181040f81441802d6100b000180350140280000f11446002da4002d02c0c09409000300e034940010200d0a40c0c00419003d6110504d01c0e0000d00c2c3c907602946003034901d0017980600c13031042c0d51b014090041f62115aa2680014503c0300401e01031356045141c91001d68284240000d10b0510300000c07040460800190081102d42259012215441d00c40c0420305154000304401e40050020a001080200021b01244180c02c1043da034031800d000c00d070405448103100806440107a00c550003d00c12010150302c400d801204c004c3c000a0103044c603031389200036078100513001c0d540340d0007496410090082140c0b0303852040b415a50807d01c2c5241031354a42049407003510403d03041020100006206840075403080e4040c1200800d02d0008495012000759298003038010160485c0d11a080007840740300f00025240d860f10b4441c082c41c00c107070030540c80171908580600d415100713109001000001c00c40da = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 49390579 1250 49389329 49389331
    0x31206080d0c03021209010203040b030a090204050f04020102010b01021f0e0a0b1501020d0203090d06020d0905070b0a14120711100c0c0c051008010303080c0708190f021501050402070c0806 83
    0x98071411403a00450034068200403010817440c00001041100040c540c7e804412101622140000326481e9158403844000421201800035007043ca0081405051008440300e248118400d0f4001e0102d0852080120386030400440115020407452065100710b4074207070040300c0204070190450388816003d032034017080110140d40c000e00d400f0701d02c03600711595681401071382400301150006510700814034021884c48030b8101000340178194041003107007000d81143c1185030003a4120045424203522020001c2da180c1c08080030801152800034008400d001c2c410568075120209400c050040e90f9a09045d600710484080054280c0100404010380715800c0c812210410001d540f10b45440f1a40c0c80d09100e568015008070703100d020001044030445a00038001d60550b40e1515108801c0c1d112501075080368011010002c0c6181d60100795031403181785009801c010303665143d4030044080f000c040700366195441c0040c1100040440d8006010b05d040c00d40082c24840d11503100702c0c40080c1d80c0ca842e00e0034000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 49391829 1250 49390579 49390603
    0xf150f17040c0306240b0c010b03100e0c150a2d0e1003230402040b0d031106071715060c01090305030609060d0302190f0609080903060a020903030406030902120102030c132103120608 80
    0x41ccd1030210012401d410403c40048d10025207410310000400b00003050a80120b011100070007042d0810600103220b181e171000510103802c2c1c4070861800c040040600800b54400c461401030702d07048154441284607000b004c0202d10200112f00056018982004a4210043c0240d81003070f1600c4c0350090707039104e52038014142c6019030f949012064070851141d06000c0090310a50403c4402c155100840500f00c00c2690088020441c0c2c030b008544403400b18845010f4540056419403808031b180c000d06401100442c8990011941c4650300c1d0399090421042d850b42240250046c1e20a41066040e10303001049540b00a00401c80380340750848903650750040d9182400d00300c4070004040780354401400d013007001d550801e401540c1541001004d0012950324000ca1284034201500c0310030720000e544030b140c079542c00c0400380402513561f45042042c04805601c250410740400404001c0001c5081c410803403030036480d030613282402c02190a600c04903003543c140403090a029907242e1001525840c2045070b039403018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 49393079 1250 49391829 49391831
    0x30307140a051b06030f060102150109020a18080a080f0f160b06030c030d0f0c060204090b01020d020703020d02040b0f091f0f150f17040c0306240b0c010b0310 70
    0x34450302e0b080d410403002c10001003007101c41c202e0641c03880da5480700740ca80c0500702541c518190380d201e200403480c010310601c40c118280528000443c640c0d65039001000c44006544400c5494200903041d0466821603209807006038109201400014850f10010000700e17050410ba103040042d0720600710f100f9030040c0803501208071428800b40412031a40c0c007180c2e201c0000c0b0040c11100508030082a01c450390007405404200802400380c250303d02448000d038081d6000b200464965486d203181000500ea8665a80d015102320031125181510000310041500c1d8098030026203101c00d5820700020705500414554451420310601415440b10b414080c801c01b444490b00010003c88140d10010080e42e400c01090311204000c02e110541c81c0485c010481c055500d0007030500c0840140c03c40380f10070310b51110704c01130000d0b03000d000501040c1e9401c00f06903401a04200702d2660380700f100d008000c07600741d1802541d0074121707010001d20550300701910344a02e40c800082245080c201c002030409045c100c11180c00c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 49394329 1250 49393079 49393093
    0x10501080a15051c050105040605060901080714060304020a0302031b010e04020906040e0405010b09010f090c050a0f0e190e0a0507020604080d0207050106050901060f0f21090203030714 81
    0x540e444055140c01c9038a02404200030844850840c2180341180140c40c01000b01c1058100b106a030810148900c9400c840200100e08040c035108000c3c0c4001d80d1214812903024001190000001c00c941d8212854035401c11355401c00c3c0360911915800081099034040b08420000015860038040d940e20400d080410088020100b0005400101203000c42c0d8080c51042c41120300580f10002203600783e9a1601c005c20b0786640b14608070380074000616895802c040381030700000340e020f450141401550b41c005000c1c0100b071100b007400c40b494020700707806000140e442d013080b440c0c40340070707080d90b402c0c0719809800381c4100b18802c804921250b06940c0400303403014901e820040d40f440544074064201c0c88030301c090545400e02c4c0e214402d0303a00421340e85100c801d81c00686802044000d501050003844090203801880da5a030310050042d82c0c10a200d0381c08543c082ea66403c01b1440b60710f00c10080d8003422000315041c2c8074800d40c50010013800394120303014401048144007103030010001c0202004298014818 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 49395579 1250 49394329 49394339
    0x3060c1223010902040605072a0803041403190305160501050c0c100b0105121e0a05070206130b0a0c050f04150f020a0804090504060b0411030603010c050705070e06010c05100501 78
    0x24070324140e01911031a44140414440030f6841002c417168070380c100101c1e4040082e036840c0c08502c012032030100c0002d00d00e40c5000281c0300728048082d108407801c001440c094407100c40d00385a101c940c0d81c82000349062420b0048070000c0d0045000d0020140a00001c0d01c2a410700d607243c43c00c5400c1030f1209818040301040c40c01444404001100540c0c400110502c00040140d00190990242141d203800741c2d40c030315001401f80903a903c0b16041e0246070008015050500240000042c072040c1c40a000600035100051340032005070440d80700300f0351301100d040390301d640c1d100c0008020712890301503208010302000581d00c41040039001c2c02c0980103103d0801900418107401501c24080c0f003513a0700564101c10b07980700200b0a0117058a0440300400d5000c15259518a08030000348002c3ea0004d81c0031b440c05134070012464034070f03022f0340c40750310182e000308110814100c0c1a205030240800c0104158400082848a034185040b03c641060341810180d9085406546003828084030030034071203225640740d004103c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 49396829 1250 49395579 49395641
    0x50a0e121c0c0b01060f05120f010306060801151e0302090103050d080f0903070807080403050607080405010b010c0b0402060a030b0607030f02010f020408030d050622060504061401080103060c12 85
    0x10788820700c0c240081032880e9550390040b920030504c940800d10a0111103000c11502510480c0e0f5440281b86c00420146801242200c031048280400d0340c2759440d084c00800e0040051050b5242c00100725480881c05181513001a0540d030000391080500490640000041c1c8541b00524040d5100d100508044940090020101c14004120310400041c460034031003800c201000711104a40c128461585c1c0760034030b082030306080c03207240e100400c0c1d40329482c20800c0456002400602841c400c00080c04240d201a00440d203000c12490046e01d002c0885c00894010302d0070720000c103624600ca00300414010341c1000040c10729040405c0584c0410001c3c0e90082e2000d50a100300070003150703444411800c00d403d12500c285c0d07134010b007003800020941c2e600c0420229602c5107101c001e080400044440020354001d219070144c502d03841014000c5041002c0450841030151224891000681d02c403840c507841d58850602030f0a1445c0542d00b0300440e0101c2c44204100390003001c65000c1110704003c03200c802d48240c12 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 49398079 1250 49396829 49396873
    0x7050105070801030c03030516150b010f0806100804021302030c1207021b130f050901090606080705010509090a060e0403080103031b150b01020c1306050a0e040f0201050a0e12 77
    0x100c100582c00c00180b0008001040280940360075241040d1100b2399140f01c62070512212001070704004209092816080507a007126400c0300080e80e13031502e141310a00c01071721911001c0c0d40155001010000401e21a4460a03000380c1c041d00060800d10164103865007201241d00940b466080c41c0000500c230b912203400b81e401190028401d00c000c08080d19514500100c0c6180d800020b440388089040b0601840c415070462440d142c44108100079500340450090b00800c4c128404685043c101180000c9048020565108451041c2c513810710300070002003085031184008100e0311250380c5e2800c01188800381d807010340d4415407180e140c40c2c010354114100075001140031440c8201c46002c0f100e00c04d001031500c411110340120b0410010809400e0a80181d0600200320800c1e43c01c079603044c09011218030035400c8881264000d031001384840b0f0300e8008202a0030003c88018008111100705c40c001944104000c1c02102c0c0d4515100c0226a507a00c0000c10000304d8140d82c46a507070000d05500039544440d6080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 49399329 1250 49398079 49398091
    0x1080906070903060506060706110307090902030c0403030e0111030d050a0e01020703020a080918040501020304060b010f05070f0213020c06010807230405060307031407150c02011d190303020307050105 88
    0xa08031881c080038018004007460000030507640d181e07800300c1c90030b0301e55134256520b2940c0002e05103d11216803010341c03d42e4204954010028903c602d0004803092140701b200d00441c1c0040e043c6240c1420341e2815108542245010390420007941d60607050389005101911180c6140d00c000b2840d0f0812a501c4819209401d00d880801d910402c261000a03400003415004540e010104944464000c0300107a40040c1001900c0d81b1160803a041000304181980210312540c4035003010005e030b601340001151100b0000d04002c4c0420020032001022510381195401c2451004140802030340030f500200040e83c01410310024a540a480140200701c0c0c2402031901500c038507803490b450904100950712aa89031034540c107004070343d50b501141e0903880600c0101d0207190086c102201080580745000c2e0b81d0b02c403074402d131005190b21551352240d0b540324038035210200e0b4059451481d019512a80c1d05490007000440303c1c1d01c440451905c1c451341c40900300300b0740218003a8014548030021414402e081d25401002c2c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 49400579 1250 49399329 49399333
    0xa0b0a090501082109060406120509010510120c05040c020319081302060c0c09130c0e01060c0b0702070302030d0306080c0f150c01090506040c03050f0106060e0d0203010f02040801020306010809 85
    0x40c48070010000b0084d04c0071607104660b032004128588503900e03621509130b1050704404001400f04181e500800308120302200c0b190308010560710542000c0c200da03410f03070f240322011001217004c01a580380b00101c0400c0320b000b40c00e2034558035543e0340010221040842c1120142c0c101298100c00603034071003800702003410300d428524a9460b2180ca0300c60003903084c0038001d22810000c00c0c1c0e1b566458080100181d151000703032620255050007090001403a01c00801152003032542c10001c50380d24010780701c05040302c0981d200c000102080381d43c2c20b0743d22140208580f007148224640000513a4003000002c22240f0140c8001500c9400c2203d46418020303100c0c002c0d801500c2c900121483c58840c0390700610710b0803c0000554881d2000040640905802600035005203c3c400610042c4401d0708a24006c484c42000bc484044444107d41170a80c1c010388131303d00c0800d58107039807080203042011010900c14070040c000079684242c4880c1e0012038015070480d420980d408010031281d540c220802c00e4105c0001e80c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 49401829 1250 49400579 49400581
    0x303090519050f040e0309030102030109060e010609060507021c0510050a0609021315021516030e0a02030a1209090218040e0714040c051207020a030305130f020f1203030a0b0a0905 79
    0x2181182040c0010390780200e90326201401045c0b424029903500070801070003595a5650341c09198050440c1c0e01507544560004000040c1403402413021104a0303c15846150510340c0340d800b0024140c6c21124450200c08040c80e07881d000450602400c00c1c864140300b00060142003484198048030a103422609540d4410840c0300444000f16035507000b01c0f4403c01c1d09800c0548032440480c1004144091045100d0310f40041c40517410090110032444982940e042040100295100da0388005412004e07405401ca10380110205080214000d0700144ca4244440781c240d03680b10038012a80080f592100301d03128910304401074901405095120a902c3c8002e2014600306101840d444848010032845075580f64079089200303004a0599102c1d03040d080320307031030355260401d00a503c41c0812607080700020314103400030b44119101220300a00c039030404011507059140b50300b8410040455414a03510480c0303c0310000c01080104000d5105001d20503011943c03900030008d05c244e0003101c0e0010040581824 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 49403079 1250 49401829 49401839
    0x801060c0203121803030f04240e040b150c070e06030606010f270b070b0c0408031b0a062a0207140d11040f02071b061707030e06010303090519 63
    0x110b0180400803c0d2400f6511006001d43c0c3c4003207182c1603491509400301058a14058001740c02500c22110840c6189404003c481c50048000b028003500c540407882e0066224160304013035104030326401015020704900300310586020000d81041584036840d602282042c0910381c01818400c0e040401a0020282403d040340068400f50424924030100a40443c110381440709109903004804450084108410b4076142001916480b0b150103031154545030002c12040c200c03041c00c95088503203540c059810301400484010b0010047e0240001d280b05041090012591622500303842c5900407040c5a00c81914200c42c02d000c0082c0305045c4255080032800b009805100c10200c0071411040300c3e00c085120300e07480c100207501c00da80e00c0c40750131626100790003000d00410390042c03050a000d4521141030701748544410440f130100b4002c400010311a440c1c4800301c1410300340b00a42101a03810082203002ea0183c500d4034010099000703400107120600c04019034144500368104221100c1e1300a8007080c10700c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 49404329 1250 49403079 49403083
    0x16061b021203040606030b010b0403300f020717010e0706020105070c06092a090f02160b040201110607050702090606031e0726070219120513030b040605070801060c0203 74
    0x900041001c1000020000d000c11640b0350100020f154040d076400c01c9940c4440d440c003820707002030200b111500281105200416809800c40200c00410b14a842144414410844100210000c03000a506c14510041383e18240201140c2c104030001c400025001f0000c0704551414449900040559141c042440742d0254000c01c118882900004089017809141c90404800c02c000100c008400c60f040c82210240034a51003100c0c125103c50318103009144070703405a02c1c2240310b0540c041812580368104000000d2a950105901c94014104034103445004212281004802c42e038020000c0c0e400580542140b070700d4111150884d000b9500141145030480504802003550000010050905000950480c6c4203040b0001d8004c0d6004114248580c1096140103103081a261038015006a06050803c02c1500103a0319003030b81c01840c40340e0320422816040d604e5900a4550055610540c0d17400f0020905071030b0003c0c0900e1042c0400151403401032401042004107800213001c00200c0c060040140e500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 49405579 1250 49404329 49404343
    0x304060218011b060b130905070e1503070312020a080703051e0f0307080612010f060f09090305120618010b090112020c0307080f07050f0a120f1e030f0216061b02 71
    0x11080002400171500e0f4005480110814900e4003070604002c54041003240c04900c0c001140c2e800a072035000380d1604207080705150300c3d4028540d0560300a02c1c1c00c0000c240d40c18480004409640180c480c4980c1944640041e41d00054054010410018030070f940c10206000e10f0100380120303801c2e981030240020300003403581301c00340c2140104041c2202065950343d841030b00c000504841d00080100c420711000a00180800b441503021080c0111000184024107015080c051580b40d0f03581454001c4000c0c1100c0804005486640c120820520095500290002c80d0f030181c440003604585662860000501190040c8a440040e41c010711a5a02c43c010001c00c0d80c803065407242100d61554281143c4265600405801900350310444075041a8100082410f01c0b056008050b1420b00c0350400710240c80d180e040c2040303040061f14a549580e0103060155030184220114680880c14514110803141a6005002d540b55140007400c940c4c01041520b02c6103009090465441c0c901003103400b040070b519401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 49406829 1250 49405579 49405583
    0x4030504030615091a04051b090907050405132712030c030f0203010308030108100902011d0105070c140f09010f0306050903040807091a030a0209010303050d0b04020304060218011b 79
    0x203114101074400e002d000f0401409002c03011401c02a0742c900803200d0810451108000c0d00491509002c1a40c003105c8840000c103003481014180c0c5030080082c1804840744008100204000c401c0c0800710741940d660120038044a100c82001c500700503131008061140c940c50082003200c5465007424000503400480e200b00c400d149080000f1404514030090780544102003003800300302d01c00000803040015081c09181640c070400102c445401c9a80883d9088403085040070740031030122007444034a90480c0c0940204900180b6003d410000303165a400b41d485001c0d0014480c61241c1c6403101d215040c462081e07a03080008550100c07441d40f40000d01c0509540a01001d82810340700c1000a191354002c000f142c00a10b100c904841d04e26030340e071175010018200001d02d2041d03481c40d003507013031040c2c5000180c103541950000c1400c4126483c40d50107480960146941e82056502d03881203c07049e41c0e591014511440c0154009655940040107401c20080110b911a051001c01d982f080a2b540c240200011096 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 49408079 1250 49406829 49406831
    0x30309010f05030907030503040b0c070f0e060409020d0b0a091101090b09040b0d0c0f06080c2703011d070e10080d030b010302040f0605090907090b070602031308040806041103010203040305040306 86
    0x51940130350282414095080544144400600020701041400060151103684000d0700d0565403504006031030b04079039100c1c42081e145110f0200d600c41c68568061303088644020504e0000c0149980c500000c0e4104071042d401183d9582c1030070050014010300680c446109182003081039040808660407401207000403402190340f4400400d40361914048150060741088a0301d032075503960406039155035502d0046400180c0c8500100c2c0c41003a011050b03400d00006801a6541382898001120608010104190345503480f440201010904a00c00b9148511540040d00c281410001201400c45015208003494031070718004116601d00818546000032503840c02041072130045004801900031504004156102141c0004019801c04000d00007150290744501d9540c0c1d4020007914003183c10300c100048004100b2066000854035401036600240700030712204001c10035110300c0f03265040fa8012208a5000790144810302c2020303005c0c05000c01c0c00300d00039403661410340e034024418041d6103c024000c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 49409329 1250 49408079 49408081
    0x801090b0a020c03040e0c040506070506010801060f0506030105010807120e010603031115040210090902040e15040e1e01060306020304140717030910170411040b030a020d0210050f07120905030309010f0503 90
    0x11f00c0c82400c0303500610000300701c2901c0d40d03260304045840c0c000030712940351690b01c1c0601c00074003441d040c401441200c00080c60141960300e88401550912001400901006040d54405a4030200da00c03504981c002508000200a0304520f000340005202c000d0403040c070390140da034260a403281102c106612990503101401009070080050315840ca290300003034196400450301080c1c5180c0c261620f440751490000300c80c41c0d00c0240c001c2c4001c403240100c3c2908550415406110b6402e0744c00100c1103125103c600000e0090f940b9150030080742c0080c1c0c1c0071030300c0740034009251003440c0c420800c03e0701820400d290320038400c003003115042c4d8a20501c041c60b40203807880b030307808200c85010301004007441c0c04080c0d03101e00781e107004d1411181800d0381070065485103103060035000030340c1000541041350a9015281108440382ca070200405c0d24910b0443c5001c028003003040e8200502400b0181c000284640941e61070021200d1001e413140c20550409400381c1c0c000d20050300d0aa03488540d110001a0900b88140c0d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 49410579 1250 49409329 49409341
    0x606030a2003090105060a0611060114010504050901121110051204020112050f06190f03110409080a03150b07030c02010305060f120708150405031e130801090b0a020c03040e 76
    0x1d85034041c1044000603901104000d14400c041d0402c07803040c1c0e82120708605180d00c40d40b0584010805901141702a03104c440140240100d110401c1c5200105040032801c0130f503540700080c0182026008100318802191400c2c0402000441c08207440d00125182a40c110480400034554040c10b064200e0798001d01000c03600351390045495000301c01c8482400e00803494070742c1d0144c10024050711100c0c083c021320320202c00030350724144880b02a03c4583d0100948103180da242e69a00340001c0d0b0307101e507000c1c1c0e45e0b03821400010441801407180c0c808544010400301d032001411801c10f6030356844082040c90801c50100065400340780941c040d6424240018182c41c3c03880400d1340308038852881c98002c00484c0d0301194407140040c001c011904420200c4e03408400310800c03000e03170510030344005099030302c18000c0c22020807900000e85810f903140c3c0401c0d820b2400c545030300d010820b07141d40180d002c0c0e55030350407040601c08039458190703120380444000d510305140d4502d0140da910880c400d145030800d240c000300750 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 49411829 1250 49410579 49410611
    0x60210020d0b060a02010e0d09082d030408060a0e07031509060605031213050406030c060c03050903010213080d0801030201080a090302030409090629060301032301060623030606030a 80
    0x401c201d01900e42d1340c481d007205001034002c240740c240148045c4560114409a00e2282039980203486081c40a45a4440445e2551820508142008008040011400380b014038100054001041c0710740040005040c0840703420100c4660020f84151904507a82c10b2006c100300b0140d822120079003202c0015610741d281003013030007014144c01044c0d06010b1100501c2040c12444064480480101010b1030070613030380d01c1040200c0d1000c1c030004104109480041080b540100e90103004940031b41401da01e0101d902000038220781c025444480100880d41c0d0070b010358a010032030b107202d084240c14450003039415034001a100a90041407030000d580c03a050014200340c800d205540060050010510003406613107000c501800410030544100c500030420a104003030244a003030b0701600040c0c0424503590940d1200c00d030034a0411046080d8602e082c0da40342d035824003489914010f1415640b004d0070800448455401040b0144200c0e0041c01e0034018044186c0d9160110794004420300b1002410200c07148000c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 49413079 1250 49411829 49411841
    0xe13020105070c06030c110109020906010507081303050a14151512060c03010302030c09070e01051b060a0905100c12020901031104030c0807060c050303060910080a031d01020106060210020d 83
    0xc03c1481001c1c000943c05400d90041030a104040d200c41031a000e1080c05203080314000d0001035400041d500105040e0750059004101d803d00401c042d516025410100d401c0605c11740e0303c2215154041c0b400300c0c00b80201034005c80d850314201310103003d080c60728242d0415140c0380904890608480b00440414543e2841c103a40d00c0c0c1481c280607a01940f4150308950290b0b0003d00c001d034040d000b5402440c88601d89102943c0c46080540c40f42c5846216107801101c00b6041105000e40130310b90880c1240b14964100440c80c0b18171901c02e00464900351626003542031214005450001c5410102c60400150b04104044120341c11980f0050329018901d0048000e0a40178804442d419030000d0040284011420080c0a442c00a01200d8045a40d89000c5508011280d40a007058200740b0104070709241c03140c21140c00803810b107021030959171514038160074061100002c5010a0307411500d1044002d111048004298090008104080c03509202a480b0198a11400316680d800620700c072484055501c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 49414329 1250 49413079 49413083
    0xd08090708071205010e030c0303010b030618040b0702150709060305090304090903050c07050a03080d0f0f050703090c0b09030d11160603050402091302060406120b06070501060611070e1302010507 86
    0x4452059450a800f080038007280b800382e40c25400c000010500c0742001040f01c1c2399a02e404010b500d180c1c6409042c2000b0f80002d00b105600c40107541c0300f00c00c8900c4803140140114001c40501d141401d1000b0081d18141241c02d411040001c40c00400c0701260304074800300121800307810082005c0c3e5404561605603c03d540158a02504c0c0c8035240050542c00000392003000b201004403000316494100300704240d081440001c160007020440f240092031260403007a5031045030352001c074030141d00911003026102c003111101300296681c6550700c18000c40420b40001401c0f02000d041ca4080043c0200303480340040d01c80ca90520051034000da0101e00e04101300c0000c070300095044401a5155640127011344030030380e401c0c3c0c07203542d9110108000c903805549c43e01c82d00c1d60040010349004d1400e60260341c6842d8241c00510140d60700c220790740c900d80b62480200101c40c8141d00000c0d441f4180031340600b80303401280313030704903203a0113101c0070b02c1035082e0720f940780341c2049842444000c039003590300c012100340c8151800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 49415579 1250 49414329 49414333
    0x14070213061202150310090902010c120302030907060806090703020307140f0307030605041e0506030a021201141305061b0409020a12050109090804180209060c03030601030c030e0d08090708 83
    0x10b010b90034000103445944212022080101c0603094480c0358001034850714503032400d10204010b007500c19440109114410f041c089450405620391800c0141c100e420707240840e03000402c01030300b11400c3c0310a20140c4107905168096041020205041d001c0050010062580c00400b082e070b401c1c024507160080310b41003090190382d102070080c18284c60300306860200129051807808960303460240202c8100e2040301c103c100c503541004071107401801001d00340c50f815004115200005d41c6415403a14559104003002244e40034546118416803034006003043c2c40f802d40c2a88800c00180701103840c40d00145118124100c101c0400b1484030144215072100e00990f10000700780c0e001623040300c01195000d100da4800c00050b030340c42e440310342920519803004007861010030050241c60015001b2a0880907184070050078440010040b80c0c5650000300700781c24603840070041140f50b44c0d041c0168580580c4525040c00f401c4145e15406035100d82001203001800700e4040010b0500008002140040000000f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 49416829 1250 49415579 49415591
    0x3010603031d24090f090405031909093602150309011d0f06091c030e0102130608090d1404030206090102011122090c050306090907030510050601031b14070213 70
    0xfa855605071302400400d070042522a8001c3c2030b0b4507009480364411904030010f50300e4084007611803582048100300340320030b0090700b5102103070711603141c80751780200100e414180325201e0204030840040000b240990b000040e0340348201005131070714280c0040e01e20315442c20503140e403250700030b803030250940000c4403003c0303000c50a0100c8400070000d10002e0358040703281a28803d887c3c40d08025183d00c1607924144413194008081c60b10b142c800c0c2d1020b0300d980214000141426000203604401040380d610400011b0048801d201554205102e20640000c1074145020030180340c4030026243d01881c40042c3c0710f40808107840d04140d0003034218002011005a0ba10354404c03140b10384840a4440c80c0d0416040101c00c074020032800400c0c4039204032801513488050540c0d851004108481500610741202801400d10010000e1401c0050804c6084120f03004119403411a00050440e030a840144000900002004c20700c50740108605c440e2150782d4040300d6480c54180081000032001c4021481c0051030b000e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 49418079 1250 49416829 49416889
    0x50a0209031c1211030414011407120603021003020703080a05160c02030c0a27050603060103020913150b0f0d1502030c0f0c060103060c080108070501080a0e0105071d03010603031d 79
    0x2130011803045104240010128403111801801c0343d01400c0c90510a40d01c410202e042c20703000c1c11132400e030502100b0011807010703241e07030200e40c00d00d05820700346000c04e4000c01c0070b10030950084426a40014140d5040046107051441c441410702300542c40d0080c000b00808030320954509000e021000940540160ba0450b40c4640780c0d4178180c0e460307e842035603034840b1540b81222003460140500800005005100f280d0958080000c00d00d800b911480001019405220019075540554105110030000c001034100640083c0144410024005842400e491244100150480181600488441900507141c1d0b58110206140b441040000000080c0103d51181000f400243c00c1d4140c92041c4000e10001030a80340a640f988801c0c026020306401101c0d0034459540b181d014940d001c00b40e05c00110300071200480050840c0d4040c0c8080700001e000c0640502c0c0084d000b40040c0088400303070b008126103855034800400e68104401000508442c503d258840c5a44801c09a110140f8240550b00001098 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 49419329 1250 49418079 49418111
    0x2070602010c020a02090402060a020106030b0a0506040b01090b030a1a03010f020c070e2206150806040203060c0f091306030203070e04031205040f06020c010608010e0f01050a0209031c12 82
    0x2446440015800d1000107202d00d440071403180e03e403584c0074284d08201e8545a0800038039030400081c550440d941c4c1c10002002c43c0c070316101c0034015201c20b51700007a9810a43c040c0420b03907070310415140c1402450401002225841c00407240c1c0080c014000207043c45501002141c0d035110b000e100b584c19800c15410300c15026213503000308200b01610382100c92080e80d40081c4190010111040250f81980d42121410081c02d07039001400306208000020b40a1004010311200d459503030011001540403100f000b046080810440c0d0300001d0514146050131328100258070b613407050015183c0504480c510205a2810681182c006503a0050588503080e80b101c1100ca20f11604880c190300056543d00c00350000000352040741c0c0650380240082c6c01540303031500d038440654464040124659662003000403424828850740b1b08441000001e49a10040014002d0940e0700240007040010b2040050022507a80020310004905881c404920300b244115015640c19204400e10000c403403c04444c8642c02c2c1035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 49420579 1250 49419329 49419343
    0x2040906050a050105040e0a02090d0b06040e15060f01020a0203120c06070c0203060103020402071a0703020406030b011b0b06031005070306030201270509180a050c0f0118030b040305041502 83
    0x5109400c2040079596030400c421503000d07118082c0400c0c8104820303c64908529222940590030b41c901610702201600425860205801c1c20b840ea4212034050020341d242900950b03018041e401e004121031031051400e0f001901c40681181c1c8505000030403500507900038000d103014140c008007a03035071988841c000f0340260b501c500d4061415001d240002510741d030043c90031b8903c0e01c1d0051b00925640c0c5c00c5500748002980003000c203886100c01c0649142e81203184540481c400c0119a901580703c0346429005001d68003500000f41c184200d1000203a0410103220548105541101c2480a03030b4440c1c0c030102c4c0c03c140502d00c84880041c20030b000c01c00b6035a056080041213070702c01c3ea1f410030402c03006000407241c80e00c20540c10081c2801e0326410071081c41c0c040c0110790006c035005501c40d50401400481450001903071400c441940045103800c40a241035421544070b00b10a09201c10004c0300c040120b001c400c20780c040140b0302c1c031038440400c0c2458030070301c207071000350140940c48040c1b00014100a0f43d1040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 49421829 1250 49420579 49420589
    0x110a02060705160312020c0f0709180803040b0a021b0c010810080d11030c030a1d0f0a03030507060f0c11010f1a060903010b04020703051b150c030a0905100204 70
    0x100e010003140301c2900c01d504865002590126034001e0000355641215400c5c26400200145a000d008091030032000707100e80748003082c0840091840e5450011000190303440d09451050254111421a001c00d800c04101c0350300a5020294000c40e07078512481c1c0000380030345c44c4c4508140345560306110094800107609149140d0980350711f000d99031390504060419001c2c0c0902d4000d5004401b0320b203401c1c0d0044c00000b640c503807144141d0b8144006000083d18507040480e000b03002034412511080b04130703800c5050040030003080e81d620540c1700c1d008010600000040c48020100140050100207118441d40009102c400c001d9081c018010f200743d00910014040d02d90800383d520309405000a40342a00c520412001114801e020500000c01040002d4002d83c1440c3c1e0555211064403009a80e5072008248042c4243c03900c58440007031312030482103008410202901d550140e41e02c1c0404500280180e07038800c1c071b00e50200707941e0390341e09905001078014224010083c0c41403030b41c021005140c0c4d801520031780d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 49423079 1250 49421829 49421833
    0xc080705060316031a040e010f060b0a020601062003040e04030f02060f1f0b0a05130e01030305030604021b0601080f010e070510052505010209090901050601080a0c12110a02 76
    0x36126000c2140d148000d9808480e54482c0005a02102d8001e400c030404040000031500c0e40d48140c500424181c8149101c407580d9659100c580110548262151034050120001201d090081d01c05000c0d58920040c05201c05000303414880a1075031030304903401c0304080381c542c05407078a913030b9071f9a2289084807044ea402c60224001261003101c00d8800500c0d18800e0031414500b503010341f00c55112041d00d843c20300303207181007040403e40856a4090300b40203100b0840c0907a555580ca0a007850b002501780c1c0540c2281103200e00b014010800301e035110041e07a4011500303d0f0b005a071f4941000e8610801d156801c00003809000e12000050304a034003050010702030341e55074024049200a0300300e042d2580094003c01358007010302e50140e4201c900c01d5010b4400b0070486080740382411720346005403c10340170203c0100e07040d82d00003c00b02c1e070712704141007038640000c2120028009030a00d600040c0c00081c006008903000ea1b901c101c52580d45201d11303503510701119140c1c1308110201d01c01071150455804800944054 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 49424329 1250 49423079 49423093
    0x5120c281709030a11120708060f0c0307050406030c030207020d030207170d05070605150306040b090d03020a020d0e130204030b09060601050702010c0b060d1416060905101101060f030c08 82
    0x4482800d080302c0d10514028083d004d000c14581d50101c40c0742c24a0101d9400ca1160407048881c4401000020003030070f50400106200d14100d4051001e1180007401441001c80030700a00403000d030400309540a541c2c0600380441c804603400001c6009000b02c0390302a602c502e800f103840007450b8000c07644609850342444114108002020b00b19030750202d034101e0700c00184041010320003050303183e40b0041c0c01080c6031485801040d0341c4400070f0328100065500f568480094002e200d4281001c101140d15150702c1c0c103055040008002000e13440710386604c0c500c428040541e4041c41c1560312500413111650340148210b440d00d40b0303810b01204459085a80b140548030300804030b100c0758020030a6440ca55416511440801526035522484c060042c22032074001c1881c5c1090000207048861071011843d092005007140c0c0003900c840d0003441803542c000014400c88000c140010340742c45818401c0e21040b41865440100180161401000c107988903103c150482d50f4040208420504c000003125842e004035008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 49425579 1250 49424329 49424363
    0x80a0305090705011b02040e070609091506080105011206030b0702010209011d100c060e031801020c040506010807050c0309060a090314030f07020d14010504150c090305120c28 77
    0x41c52442d402214041401703407060401031404480042c000c240f000d0004038201140b4500c40d443c01038141c00a0340851444841404102828880c956207020380c4a05044904d00d040400340031001c041c02080d04100754140d002c49180010380002c1c000b0360344500344140368a0000b000a000f500b00c064424002506000e080515202c80382e1074000d2301100402000c1400d5171400e0545001c03100748401c8411680780c1001e442e9102c014005445148014002040140180c1c00020304001c001000d00744102c1ca0700c1c09106850b40c1c84615140d00c209241011659a64075082c05441d600600700c40b0755001c880040c8107081607600c15400320459102e00311004084e20100e002036101e0245502c8242c2c510700c1404080007500c1c0099a2185490040d40101e02c00c8010442d420b095840440e03096841d0301d4052144039280a80d44030343d464003086d034603041c0d034400d09503910291508003049802c1810800412200a050310134041c0c07940e4420101c04c110306110044134044583e40c00d02c1802d031003a48021103d428 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 49426829 1250 49425579 49425583
    0x1506050f0a18090314030403030519090b0c130801050c0a02071a030705070c050d0b06030601050a030b0a020a090509042108060117040c12141e060403030506030c0904080a030509 78
    0x54a204582403401c0300c4810741c02c0d00c002c24807180180d040010b82800c4c1015204203500440c0943d01984c0c0116042c0f034003414040c0da107104910700b50002032500709000d01140d18201d40315004036802c0c104582d602d20182c10f0010000b82c0303811055855107000140070a9000c440d00411450556409441d81943d1712646011b020158000d081d005000c20000100b000d849040209105480380317005c814840e8580000c20a4011840400c0b145041e6100500500c2d1900308022030061800721504031680d400e40da9100d034104405020482000e13000f0602d08907070f900400381000a0800544980b50340c0c40d041c140b520729040c240c4607140008a001c8c040b0101c540c4110000c611909060710f50401a0605205000e06108010000e4603110094200414140f15000c08001c515006810104e4410309100100d401e0061003210344100a1070003080210308203000c109654000d400d414000350740c2c1d4070346021074201100013a0595000710b10104104c00c004040d800340c080d440441d98100110350f9040704040e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 49428079 1250 49426829 49426849
    0x303030105150c150108010207020307140312030406090203010504080304030e15040303050c0f120409060905250c020d03050a02011404020310021e070308070212130b09030a1506050f 80
    0x5410107000760701c415200452000400f1005404022501d00d00c403240008a81070900b0707004071a10340d4000910006604c1e0030020440604020b012048043d615100007a50b40c6860f031f0340748601448003000144c103210899000c82081d9030090003d000f50f180500e010807540c0d104030380880206aa6050100603820500480c0302201403000750303035180506684003601c01c1d40114a04091611850007004e038148001d22040d182ca20070904280e8071030f410094114280c3e0421703002269000e1800c03041048840e482c4d900c0050726140031300b11018540f01e48030200d41c440741014020390481d000e07028060806901c04024021001c2580c002c2200c1e84005c043e0000003801618080d5155101c500440b05e400400d078000c020860714000403801044100404086541188200340e000c1420501004480703501441508001c0c16820642c3d403511441520003050104d1034000d0001c1c03880c010440035410748042001c034000c241c21814480c0c40328461241c0038003030140390140f180141e1880300c0100035800c12200003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 49429329 1250 49428079 49428089
    0xf03030a051812030106030606050309030915070501020f04030c05010201091109070e1f030e0703050304031716050a060b1c0b06030703081c05060d03080703050417040f0305010b03030301 82
    0x51495500c94044000150002038489000c11800000c1c90100000410004486500078090541c807589401c0d07020301110803650040702400410810480c40105c0403081b1820300308121410079540c1c503e0201100140501d050081881d0300c0040c80100849000c40035100300c81c49a0140f00401d03440702c004a0903030305101c600030714041013070b0103c41142c50f1540700d01c5d03442001882c0c8801440080000600b2143d158003102810303085c1e140030b9891842e810f00480402d800800010f1122a1030b640c1c6850340c0348103611000e48924600c040281780d414130070003120800c440e00200d812800f580c1d400e0150700c0c1c03c100a01254483c0c5001460b151509003103201c43c2036015090b4110424070095141d000c454038000b800e00c0c1e03041c0103089010000070341407000b904e45528201705004180e0030514841040350400b401140c4140403000c081d10005c1d07404a0700562040031480c2c042016161440c202103521188014200c4216000c2000710b04240042b41178030840380074200030700c0700804d00400d241c0c50748420701070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 49430579 1250 49429329 49429333
    0x403020a0909030c06110d06060c02090a0903080106081b030103080c01151d0604090b09031917040809010903060c11150930040303030b030c031204050112141f080f 72
    0x80b40000c1805d980c400e000304902180032901d0000d00c0b14010303007201c104e40c01500110700c00c1d441c3e403c10342c14611901c6d07901c10000c00003003004080ea51005041c0400500c115000c22803140c001980203030140340c11180b10002c52000d244c8035616440c00700f800c1e410030480c1004540ca4015155100081401c0074021036607803007410100227810341c1a103032000700000d09007500320303454552140009104003d5a8815180307076000d191100d403c0d404050603031071075021a604000b04007001c5405044001d42c1d1a8201c3e500904e841c2d500c0c58503900584071281a075002808c00f51400c000440070701d0308000d47c0c60185d203180c0c2c184c80810406c00d003040b01910064403a0306581c0e02c00c44000d50300e800e00d0308001d00e00100c001010b038100900c84040c0b00841d4031503002100040d49038560700c1800d017010050103946000071005010901508080d20305640114401c0504208003928a05079a26a550183d10116a80703048104285411000d800d008508280e903070074000c841c0c3c13000280483c03022810750b250080c0140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 49431829 1250 49430579 49430597
    0x14150c070309050d0804150914040509011d030c07050a030507030f02011b0602040608060402070201082701020409020a0206060d031413090e0709050c0a021905010618020403020a090903 81
    0x4a8542a00040411018009200e00204841c0d89902c0a185058421028244c0d11414a41180140e9030622024011701003140414811081c2401030162040019036000460703560b640442c0b8003500c0d491281d19000144a000003003610008030040c03080c0c01c0e200701102c0e0255595010b0141c00e00c00e07803001410640000400707000040e01c100c42e04009a00500d030030384524403810200d05986c2d104c0001114001da00050800485402c07801e215400942201c04504009298001903c0e880300140701c01910729810107040310041c2e04031130311695000500b0085440d0303521003801000075030024250030094460140004c1480ca8902a01d616566055071900c030310562900c02510b10713805c0002400d44d4892910000300d8114401d2240040130001d5500400080d442c0003884030444402801c101c026040130480c5001154000403a21003418207180896444401030410b0303030061225030003050390031540c00801d181081c01e80d0064419240200c0715075060720b94415844003251041c080060115840031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 49433079 1250 49431829 49431841
    0xa0305030f0309070e01170601050406031509060204090e07030218072a06020c030d06171e0114040b010311010201060e0f04030c080a09031a0903030112050106080a0b041415 76
    0x40c0c091600f00c20440100d802c43c50722180004c550401c242c202140c0d9804a10070020209010020280103040907581002501c0c10740d2140780c0c0103601100e04c115641d8480b00d003030381080000e0b4101c0380102206d113020841c8800c401d91142d03c641e6903120a0303100e10500b66400e00f507080e60a00c101c0c0075286a0300c43c0380c0703901d10411840f0030500c81100809640b800c2c0c840b80802203178441c0010700200c541c0760041c581d200c000850000445089405c007a00004048468041041c4005a0302118004c1030050244445400040c43d0242c070091101105003100ca1f828481085456a100c0b4141c912800c03407035005000840c0120300f01d0360035215030000d12150002003212900c548000d180c01c0f41c02071400d030742d41c030605446030b02a0b54000c520309070020ba0340b000104144000740302c4d021800158160340c03088030b0508541c07140d0340b404180a20400404c4c1500008104442544554000d240c4201a04c000e008070f8241041c810800302c40654030548a0204a04410400301d40c9500ea02c0d08803414a1082c3c40b04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 49434329 1250 49433079 49433107
    0xd050d0515031e12070c15030603030210022d13090c090e0402011803080c0c0a0513050c0705010501090605180906070e220917070f15020f07031d0a030503 68
    0x1c0c1d40320140350300501202c3c802c135400c2500104080b038050341c4030b00c00703403481c00040645110034505500d0415103041da0500c0003076408139440d58401c500500158a4000383c401c0300c0030f0410034400744929140b1301100d010f55a002c0c480a000500c1110080268041d91480d00c03800b602d0442c4a1440040d0f0001c2040c40107080b4038500c9078001d401890004001e202110444011a5140e0000d40b8040c001203450480f54004004401489405807503281e940c1d442e01010038091802e244140e01090340707480c006070760700110f034041d100b100760071400a01079960f403403400174000d200600419005901211080ca003800000d00154018030440004041540c1c1305c0320215903542602001035400006040307440240d00b8068544808403245d8000021116060700c1e10803800c555210404c078101002f4000c91001c52606400b10032800e801505036401c100107910000300a00c518400c50f0000580070541c00c0906074080070340030400c84042070780da0180280600708146150a488020300a92040010201d12920 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 49435579 1250 49434329 49434373
    0x1090c1e0b0f0c030c070f060203070201050301031412040306050f01050603150d0501020c010603060509060601080103050d0f0e0d031706030c0a0603020c03090a0315050c12010506090d050d050d051503 88
    0x12030030424207100c1c04100c500d0845d03202042c2982c0743d60000c1400c1c031801848040070402448280010741c50007602c0d90010301103010510015000d00d100350110b40542c20207100301c1d001101c9881060350f40d2a141d11f06038008140c10b0360b000005000080002c5245c1c1009021203000d032000803424002032006500b000160248220100c8030755409101150582d5001d004500245205041c04661803501b0b6050b64504880100a00e040248a00c010000f04801040740c480560b100e1030700b000000c400d05801e40b0400034082c82c607500007842031680c00c24158807040000c1c40c1304c801151100f83e500c5444c1015a070743c030100030803030340458111801c001d214029401001103030603140c2075034104800907001444c40c2009600986022100004510b54440c10f480f840f0707881004884106d0515021061004100405014040c01505c000600c1502035030354080c03040752564480700b11146401c90b401d0040603500003608000310141050040380c90400c0101c12a010140c000c1c00030b0200c551003150441e06440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 49436829 1250 49435579 49435597
    0x70620071113020301090c14031e0c070c03030e03010c09080c04020d090f12080709030308071b060e0304060908060402100305060d0f030201020a09060806100807110303040501090c1e0b 81
    0x1807002c9450748002c046001071070090040c030b080002c410a0521000e0700e0b07814924000055140100104480a03a04e031104462500c002000c0c1003c1c3d40d19078902a00520a0760405440340e00606000000c040d4004002030200e0010f030002d000c00c02003008145e400e21418064440c0f40c0d00305144400c501e0a1a81c0989030300c82c42c40c072000c28100e056407a20031410500c100280d0300342c04401325a0340c1d580e0700000c1d001d8010000303240180d02203140d0f031402019040040d02d00800c0060307c0c11582e00303001540003603018064001004100c501d60900443c0da813540207102c0d0340c0200c8d845400005200102080c807600c2241c0140c48403100400e5188120014100100a6a4000d0b083c1c01c070380c4013190880201700c0c0c00b580300e42c00059a8407030b07010025202c03c44e140e200d04104890141005117036110310008500c01c40b80703400c02e2240764031030100c291184800322181c01e8540c40084100300c1805815008080041e0051441f45552503e65020b01d0380000c00041c111030451003410b0401c11100600010305900c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 49438079 1250 49436829 49436839
    0x11401020a0c15030b0915040f0b040c031d030c100b060f0f040f050904030507032a030203070b01090b0603130501021303061401060504050f01080603070b030c0706200711 75
    0x30905035900103150220f600000034008143c4003011000e0307010703c90084c05010444c0c4400843c40d100000400c05a01840500c1c0170740d0316005034005032102c5810034601103c0003442400716590785030b0700070014441c0d04010003601440075504210600c021003114908500803020b000440303100010365000d0203040c68a240c01c40e0301000400000c02403d009421404039040500d5079071854100348040109458101714440e0804c2c41c01d00000070342200c11142c1480c0c0c5030902e100c900342d41045000f0604000820b42030a12460303002c40040603408070003841c20340c4c0300b0000c034403041e601c2c1c00c56070085420132112150000800c1000c1080d0f608144012402c1d40c0c8030b10000351628001014040b00083d680e4000c8880720b8460030315103120025090b545015190f0b618141e1f0a1524190010342000451040c030790600200070007184030368406014039405843d817821364595908203610110305a80c48180c0a0b1101031408990306c1030300305040100b505000d683c10b2910305100254880d55461900d40c070610b0b0b485 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 49439329 1250 49438079 49438093
    0x30f0403030c08270a02040c18090b0a030b06010c02060307122f0f0f1803010b041b0302070501150b2802060a050a0f051006020115030b1501120219090b0c0601140102 73
    0x50f45c46000d16100d0230440d95541485083d404820040c0000642200c3e010304d080034002071050b02c0d41440001169044205045241c691000584809c1310040019401c081c000007000502c07a0040032580303a100d10210104800c440303803d102105402d00c0c000850ba011851300074102401c01d45030240095820314182203103000004001c0406941c0021103404030040d0348036981300d15140a02c65640c0c2c0b000e041d102480f070924074581c09010003c940940005040c0d02013400402c1c08025031002c5c240484580c880304815450700842407481e006446020b1040400170844640381c51690700308940940c15400520151300d60180c520041c042c0200141000ca9a410040b8040003030f83c01100e0003100715086081400d13081c104002d00707541040040001d07902d41c0310020400100d00d01a059401502c81542c0c4500340072100040707605180100034840c0c0301e03001241103070320141010101c40359172100e030f200c500d04035036908070061081c040c0291814180d0080c0b00100400c0c1d1208112140030385051040d1146 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 49440579 1250 49439329 49439333
    0x8070e040512160b010b0c07091a041806110c03030601050a030902030105040c0609151202070201050903070902130e070503040609050c1011010c030e030406030c03060b030f0403030c08270a 83
    0x181c203c9000081031031410000c0384180f0600c00d407814051306420007400c2c40d0a40403040ba50307640c0781d941b04100f44207564010001d0b5001781001210781c002c00080081c4041e5030030780c44d5103000d6010300b4801d4075113518285e14030803800c1d01d610442c0c225000360b00c051030841d5030b42c200644803500070390424802d140d2600303052001640c083c498a40f003107106828001045003003003001001034509420402c50702a8080c541c0310000d400c503008c0504148503510140c2e032400540700480302400390800c0150148188800412040c0301f40c0c000d0042c18240902241010380e44140d9240d22030815500c1c140401c10820125012924036003010100501400c1244d80d80c1070080c011441d080070080704000001e003d6010604914804c0c081c0002c0c1900a1406100c050b2640000f02e8a074481c0c1d01c64641407503030710445421114000d4009000605601d8681c42d101e2030702481490030a14122000c43c0040c4c0f41807840d2600a001d00842801756002c07c5000503052001c040c1d242024200414500c141d100d11f0503c240 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 49441829 1250 49440579 49440613
    0xe070e040204081e030a09030f050a0c0f0602010e011107151b18080703030503010509070311041202010806091005040207030207051521090a150b1002060105130608070e0405 76
    0x4003c0018200a0003c404c4a500c2480c0c50440e9100c04a2243c000300850143c940e03104140001b0f07281c0110710320302d034441180f0b0305d02c0c50a481001c0c0101140d444030070001c1da04800d941a08226002d9030000d1010f1302d0300d9000a403c03691710307a08040c0c251405101c442d010a114000940d84c80307002800004010300100f40e42001c443c1c0d51815440000e03100b030215600341101072441d800410b01c5100500f1020304550f40a091030005005040c060003c0300c0c00550210b100c0d801010042d07030711b03010150303503680c40d110406241c41e100c480c140c0c04141e00101007051030400c43c00143c42898122003000305d00341004104006980f09900a404600c40c0c01d40100f0981d40d060503a51070051030041040d59064848181040f240441080d104143d0707421040000403000403c5000341e0f40d07805000b842c01d000645003480c00030b008a00307085421001e1046809805500060102d041cac031011520b1681031030301541001e00303039a0035004404075a0402d901c100034000424412030f800c00d12a0742a00c0b100d00a820103c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 49443079 1250 49441829 49441837
    0x20a0f0806060d0f050a2004090209011b08040504050f06030703030e0303040b0301120501050f04050c060a030e0d120513030c0206090303040e0907030201030515030c0d0203030d060b030a0e010603020108010e070e0402 95
    0x4011301d0382c80d010700a442540b44100340d00250188600306d085900c40c541105640036034400c240d8000d03000140c0307417070f5680f041d0306d0711008560488101c00e40000c1810300003141e800034000c0b0b81c0074a02c0c0c0b1010500800510f07803458401e03c3d0040040c0802d9046035800c44a011741c0015090300752006100204031120220081c6000e0f20940c1045192440b090a0283c00e507517014000f2030480b40040c082c800803400200f041000040c0c203488195031881c006a0803030007004001980002d90141e408030340f99241c2d2010028044c40050b81080c42540c69410300c41d44c1da09003a040040129521000580050034448054407078a00000d0a503410b050342c46140208601003104d00c58165003040c00144110360b01840b900b500180b030650751030f1510b651072010030380d6a0106a0390920440300344101104550b810812200c0910001b6003c3c0040c40d0340725070406150304259070303608010381000c41c0d14001d2141442840120b9405139541100b1342d2900e40c0071002c80c00701600417000c011002c1484000b94031980010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 49444329 1250 49443079 49443101
    0x8040209254b03020c1b0a0b04030f05070807060207090f2a022a0d050703080f1312081b03130f0501081302030c120a060e01140a020a0f0806060d 64
    0x140c5080207482c840b1102c00070710140454145803061103c2030600000003403044070060f01000000355a02000d00080401c0029403040c00e05201c00200401040a030360a0090000c0c8036500300c402140c0c681d01c0c42074a81400740507560040e4050001008142403903002598941601c1100042420700b071210050b040c005800d4003400089144004802c039641000030700e003171241458401420801e29044030702c4240721008201c0c03082030000c280105000c0c003445488011544455190f54a11940302034060315000784264220410891a0004410f00316040074840700382c1c0720741868a088560464102d18030740b00001504240f00600c0b1102c2c0780000b11120782c02031f100d044e201d90b10691802000400c1d51800410081c0d108a80420380340060b10002039801194400721020303030080d0055040c03d803810030140c602419290034591800b480c00010341c0080003480f80d001c4624101da4404418100703034460906c0d890b00084288440d609041d22503120160020b40043c91285404013a001d40340c191201c1c9c00c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 49445579 1250 49444329 49444427
    0x906010e0625140c0d0f050c0d03030501050a0504020c03030708090a0b010303030203041119090e0c0a090605210d1b141e0a08070206090a0e070804020925 68
    0x6164180004414200200c5443c08010010484040c010440c0340e04458030080030300c101d10343c0840402c0030600490005000c003500e259030380b0302c40d030070010080c04080c802d0741e008047c41080420141880c5c022210f294160a00851444e00e50250440715850001c3c0303450503502030040c2d2400002c680e4041c40d402140240d50150f2a2b06043c20010340000094414904c111110034401404100721803041084075054800018003401344c403440b50511440fa54215403000404401145070f40641d4800c000f81c032004c1e03c410041d061082400d84400009442c8400240d001c1c40c3d00e911054810280d600940501110790708440109965140e002141e02040d059150001c1005040035400c2854050300300359420b000b0840590941c499070000e20074104068000c18001034088116220390748158003d0009044459552408182c010041401500c08a118414480120f9404005d041302c440b10040032001004070700d4000341003500c90126903102e0346460550315000014511001001c844101c1e94100d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 49446829 1250 49445579 49445647
    0x408030a020604060623040e010e0d050408070501020307150506060706090f0605070801120605060a080f0a030e010e090a0902180703150b0301150819112104020906010e06 75
    0x6007800540c4c110380c010404a81d80c186c612601c5025040340e500c1803481c291000100ea151503c2c4881c0902503e00d0001410b2059801c4003c0069212004000310341c151025500d00c1074888004903183e1164590152121450001c2d031401c501042e40017a40240e0000c25081c60a000d60380c0b0007090303500710481500c1c0c1c60a07000041003070050f1405202d03400065850017091a60400ea60940c004c0b030080e0f00500000d07500e10005416449503040540034201c003400329001c1e86a0005000d079101c1c0426000c5000414079210100d8950040348080515030009000810550340c01140b40e00800315000c09a0340720240c28142000d60742c425007060300541940d03902140d0b401001b00c00c0d00c001c0310343d0744c841c000f4404100b0040005400c5d6001100c070304401e51902c81081d485140065042400c410052010329140c14840d44c41414400000c01c0c010000039440c0c42c0c03501c42c120041800c10f10032500617410100203000211950f20822546130381d0b440c010203903800c0508190040400c0320201c4012440da4458030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 49448079 1250 49446829 49446833
    0x130302040603200d03020613020102070f03080a090f120b070c020d050d02011107020303090d08040b030906060109080d230408030f03010e060d030c08030a06030501051609050102070506040b0f0408030a020604 91
    0x64001c0000403050384c00050300641a1780c000c5d130b6144010034a66000c3c52600c81441168030a002d41c44c02800d58a00c8001ca13280c607030400c00456031081d07000402082400e0300c0004d00301c401820302e80c00c40e1100c1030101c5080c0e809845480c444c20000b804a4100f00100352500010303074070001c0d040540c90003a4020916401c0031080a4211a900c20361080c100c4000e00122006941c00400c880001d1011ba514524081940c54015a54040e03038115400301d15000c0104503d001002540500c01c1800340d1b103030300304aa0796070b588a07101c08400340c4076000a2510480028003180848541d0f0032072200a1035145450341d900090350450b088084912080a000001001044007624805030040d500b114101443c2e681030350084c10308224220300400c4000040002698901d01e40e000380011a003140091155250062102f015040c034801c0860118034400b0011410703510005040e02594005080d003882d182c20414042900c1e000380120f0b81074010300300b00120b1412010300240c1500d982c2e41d001007030241001c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 49449329 1250 49448079 49448123
    0x7090e06030307021f030905030d05040506010e0610030c1202040602070305010c1704030e030a231005010b040b0304080702040903052502060409020306041413030809010506060a05130302040603 85
    0x2a000074072940c814002c1002680c0d910100000391444001070752240c80c10764000340d0107041581c0d0094210b020200e08018100015000284035501c6941500c2841c0c1e00c50300e2110325800c05488098010740801c00c01c0003280d01907441a2101141030174031698201c441a410402d0340c0c4940c00080058000399801c00800a007405810390540303071b5040005c03140b085074241c6c80101e4801480501001400030b502400c1e40c1b001d0200035500c07038210242c132030803485450a0400711090801052124450031981c8240380700b045c0b2495040c1c2d50306102c2070303240615112030406560000b8000307071101201046a080180e40d1413050906840c869100c0d240c1350082c081c83c0c03106100190310020940724020303d480e03005a0b90481110240d8010800058507071701c80c00c000c10010100440c102c10001070b02010b00c44040a50b10203405110300c295030b040c820341c0e1007580c028247c8009440441e0009814000000c5150107800980340c1140c3d180340000015a407a00040c05584199001f03a404e800c1c0315420281101302 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 49450579 1250 49449329 49449331
    0x13030b06030a050c01050f210717040201022508030309010b010917071206200c1002090d080a17010906061106040308040611040b031e01050a031a04150507090e 70
    0x400c41c0541900e070099120f0326224003403081c4560400000050b1f45800002071820766060f803150402c0c8002e202d29041048006190568003940800c0d540080d8958045500320301600c5664180c0c0901035031407044210b4201c0d91404408007803440d00804010420900c1000514861418400007207410030720000094560001d0350440c02c45c3c000c040004541c0800002201d200b111002c081101e135520f01818080f00a10503901c1080c05042e0401500e8000d24020307026203503d48908080e29601031102d4540f40c200d01c50629440e42201000e040b14001c110f201e0003820f40300030720381400c1d5000e04406c0890150320400b60011a09503039214400e0001503400710400c540c6080c0d0300001c0c030280c1841d440141c12030800502c010207242d00d41c040c0d82c48030b410b6002520f004001000e6056141c0c100980c01c0c19600f00c214040a8029107440e000107035510b005a40701040720b80040031400c00841c0540751046403040100280c43c85a01ca01d03200e001c100c164403c061003014255031340768a4a05050745a502e6805c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 49451829 1250 49450579 49450591
    0x2030903031501080702030304080d0b060d050105030c0a08060105060a02030f0406170c0f091009051302090f06042106060302090408030402030d0201020a090618030503070b0405010f11070f051213030b 88
    0x401003080250264000044a411a81080ac00c6440350000c862010240005810b43c581040021801d080d03203c0c2550091416100c0440075540e44030b852809002d03c0e8209840364030100d5009400402c0305081c990010404143d1610540b0700c0e02074000202002a0f100b0b520440020782804803140c5a0204014401d4016580c56016494128640c01c1c1c04058003610048a1040a4040d4211130700790281741460010301c00548091000e003511503528009410100c9154024811031040303500f131380340c034500315400d80d0742030000107800c2d0b8900f03d0f0b0121414001c460072108155114404030160740c822503258443d902c80c01d1010703aa443c1c148189800c0c192040c1d01202560300510001e1403958000c01000c043e1900b914180300032a18540225075114003661001e00b55000000b10f2100b03200040900c60707c2913025070024020841043c01e08030817681c5504040014100500c0700c840001c41e500e00c2d004645000c1d1044a12001207484403040c243c0c4145652407468403103071400c0003048006490b9992100d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 49453079 1250 49451829 49451837
    0x918010501060c021003051e0705090a050d030f0c06020909010b1b0601150509010c080a110d05040807140621090c04051308030c121e090a0c03110102010f02030903031501 75
    0x80f041e6808031300d42d007084540143c00c3c103440320002000f003040381e840011040102851552941003158000c0c105902007444180a000281404584d03420040441560b03168103070348051030b407504443e04075003203a081a01241e00326004c20440c1c0240d60f40c10758217070103400b401b184a40c2e10205403949000740c0c4441c01d440b5030940c1080004000c20030300c000440c076409140b42405580e40b002040126140c1b4031500c40202032442c0401d252024640c00f032901e88a030000f81b01111041284020155060b0149224801d1140d00030318085c030504180700206040d80708007922035410a00c00d25000c041e120f006d000f0b10b00e400082c0c10200b00c031415082080e140f03c04002d41d030801030340c1800c0b1541416000395100c05000e04c140000403a00d1328280c002103c1341080d003680084841c0c18400025016800310942041b1000650800f04040440104842c08000d40c001a01411030f85107070380d1912400074000f10a41507560790f0b01c10003258400c50000318402c050300400380d81d403494084004ca00440c506800700d4100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 49454329 1250 49453079 49453097
    0x809090112020d03030c0309080d1a06040f090c0302190314100609050409030e030f060105030d1106060d02030705060f070b070201020a3618050705090d0f05010605091801050106 78
    0x2d40c4a01c0c19203041282c140c034011a154803400d40543c00740c00560704c001c00ba10b000040075402c100300703a484401e442c07006035044070500c1031540070400b040c0a54003642d101e80c00d03016001c003c040b000e54003180035070700241005404c003180320405440700781070800e1210100c6d484005005040400c0c4155940c0410700b80303460300b010f1b0f09101c001040761030725019450250355150a40c00915000703e40b05040c0d0724000701100c02030007245401d603442d540d0a10800f4040d2065040c060307170040c001d14007010300c0483c00d4010f0129580352010403180450840080e0b805001e034036004141902e480d40102401c1603000f02d19681e0385502d180480c50300310001e0a0381c0459206011014070140d00000b6070000c40b0358070f00308180e01480d0744c80212201c85514200c80b145101c00303d0000c0c0c51003160b8004001d41005400401c04d070303503403d442a2581e1142203140350b480401044074500054110007150709060145c0c00000b8901c2c0c444010494108007610310309510800d5441d640350b4507000340100c5001d07014a103001030003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 49455579 1250 49454329 49454333
    0x150f070f03061203080a02070c0f03030e040c0e0f010915180b0a0206011208190e040c02011b051c0515091003030804080f19050408150408030a11070f0809090112 71
    0x100d4000390703c00600300618080803c1011489805440405401c00e00100303e0a41d07807110282e00506902c4220080b44001d80842110300d4a8405d0808011f02ca885442d1081810000c01c2182c00040d02c449040c844a60ba02148048000c40b50002c0040561215080e680030400d040c5c2200d00c0603440543c10b41406c05c40e0760700c100e80c04540c1c24111a400c0e9040195842d96160003c2c01b07004807010b01900880d54045a40011703403203000400b00100031f880400c401c01d05850228203030345a07818502c040c4a00780c2100981e039032082c2d0080c4605ca02021130112104840c881c858151801036030540c0f038980414003141034a28091a9840e04608803e0069520514555000e41290f800400103400d600f404108255504030030004c0383d005143c81001c5226465082d54040c100f90030502034020640702d0a038900c2d40c407030412a0050f004a800403806821580e41e029a07801501c0d04540041d0148003c0c0b100310001080740000c801da2a104400356500e0f00102c10501441c03c205074462840e003541c21000f000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 49456829 1250 49455579 49455599
    0x1110091703100b03040c0302150a0e190f14040e0d0903060b06070602070609050c1005030a09060e07030501051b030106050d0908041703042c0117150f070f0306 70
    0xc44908011051038503540c40c14510340301c2010ba540700c48100180042080b04106031165400e0544c4c3c403c0740d0407003402d5041e442030a8180100e0080d0404100808040c2c40c4500d00808a0700f00c0e071070923aa202d5209500c0f9801000e51074807030b074045480c0c1d2290001900c0b0310326050084a0890134074400504840302c101c0001441036015200240075541c0d80d1b020b141c1c545d190f0400329525190001000c2d950f81d1702c0744c80c04400505511000703541c940158a45403546241418108048070711540d00d00d0b00310348800f2200d50041411020885405680710700c190310315102485a100158020800054245006030810b4801440c0007500c4100301401c20040c0401c40d0410103a9188520344017001407048098500f90382c281c42a60085494025603400846603140d0020040064569082180300c0958000401802000504030100c1400c0c1107c40140540c84440510700040106c03031b000c0314001c41e0f00d9078400c0740544061f03035100c01204107a03080100769500840700902250741c13840c0401140340f4143da114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 49458079 1250 49456829 49456853
    0x50405010f0b090f0c13180f020405010c080904020702040e06071e210b0303030a060303030b0603060603060d1a0a0501050f0d02030d030218060c0d0f050c070902030603150106111009 80
    0x40f80d40c20314802140b0303019480e600382d41c0541086c90f52034048589030302c0c0f08000c0e11000641c0700e44550408074200c2240717400340252803c40c0ea0603141c03800b4110540d5110071980d00290130441e042503090110a0140e5564002e6200d003100300e4025013014103007454000e101c2d4801141441c19900c2d10188450000d0707000360030010590500846c4001c503001000800043c00d80082020b074107120120a2041c0020a0780c41181241d01c2500c003004010b80100078480180000c42d50594400700c00c2c4002041c50a010386514030040c440d041c2101039114000070b82111100a6820021080d5280e005200b103041c03d01160448400c129041c60000c022a8000382e43c40d89c1c0210440101500840c0084500c0d966800844c6a446c00400440d00c42900302e11103075984002150020006004100e0144014082c1e011140004c40c0c0e0400303442070781d080180f00c8001e5407004e000950540706004000c280d260300e510a8a0203015a60749541d241c00300b110949203881d030b0a6078401949440d0150010020314041d040b9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 49459329 1250 49458079 49458091
    0x403030203090d150c05090120060402060c1c05040f050909250f090203040c0506040b0a031a190e0a0c080112020d05070602030a0306060903020904061e02040306050405010f0b09 78
    0x55140202c02c4d140c41c401042d0380e020054011400e0100030000250444003910805d282170703a801c19200100da0030840e4410425600302c5050f0082c0d000f06015040640017480101000d200302c4218290740c00c910b649116a10b0640c000080c00441c05001091030500341c500200821030300522542414004541c4504850f101c0b41c000c280244d0340d548404c00400c04a1000b0091100d440c0c2e6843d07036916016021b0360080340c0803107106134500d002182e03502c1c0000c1034600743d501e40c3c040107003480c014000c04d500800000c49034224489000c16124500c0d034503800b001d90600307aa9207985210070310b003800704c42020308040d0440301e04d1428090042c40d8a0360100455044a210700f0741400410004c1c0081050314006007070280c5640102d44000c01c8aa070000000c1c050740741180d6040110320ba4649044501c6041d42c00001d6201c0d884030080350125150b034201c9031002000501c0c0c40c005143c07072200c50080b64081c0d801140d505171201e040105001c4207200b200d1132201650002c0c8800302e0003000141c0820b41c01460 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 49460435 1106 49459329 49459339
    0xa0809010e07180501080a03020d050307020c040c0c0203061b120402040605040c0809150601090e07140c010603060f060e070c0302010f0c110d0c0305040506090d05070b041802040303020309 83
    0x86c0101f09030550b01800c0b800c2d002c010115459400a0202d604600c1000d5092003a40d4442c8985400320199469802c59118184149814800300030107503440402400d101d030200d001001c048610410340e2000d492841d03691440000c004200903008190032a1074001264805500544400c0c0260003450856101e00d00658982c6054072084403218000b4805503001c1014519150a1035040340090030030006d01e0400d1000d4429a422048501c40184e4480b802003081c00510320516104240c1d01e801400300740c1c18402d1081c0a80d1014094a00f044425006002031510030b602524070010500c2050041c0c4032400801000428a041260b850380900851209481c1c0100710110880742d054135240d04043c0380ca404c0040641104e4000c81c3c02c0340700d8100744400a04103104440103041c416029a4a0714100b0003680c0000060300704504420384104414404a0f8001095a002c8402120 = true := by decide +kernel

theorem cover : BRFrame.Cov 49280579 49460435 := by
  have h0 := BRFrame.cov_init 49280579
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49280579 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 49280579 ≤ n) (h2 : n < 49460435) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
