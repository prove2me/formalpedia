-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3390
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:31:24.356053+00:00
-- url     : https://prove2.me/submissions/0751e8f4-926a-41be-9a53-c3720eaaf1d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 609532374 ≤ n < 609712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 609533624 1250 609532374 609532393
    0x6130e0a0f05060112150503190b010603061215060b031602013e1e090907090b03010b0d09020603041113050403021e0c1306051302040b0f03061c05 65
    0x54250340742036540e01c100914100c00c0001c6685e00210a50302c94015a50004040342c00440f0342c4054601e54201c40c4e094418041411114500c201c07441c1c031600e02a1081404a980781c003011810350f4810321503010360a00f52048407020400d221036445203c1400c400015000ea80c40c281010550001c07500410440d4110486840c2c007038082c040d01307400c0d454151461109001481404000701231421710608000b9450240d80940d140090884112001d200000c01c0d1990400052200650044d50340a000740c005001240190b4024005c0e80c0a4030a40e10007681141c0c2805c484e1704940e041004050415911b4442e00d20268884400460085020b03000c02071217260b5841c240010403c0c90f030b003103804030b610301000c2102180c3d000c138a40d130444001141d401c1c10400b190642c140780c034844c80c2c4400e42c00000b5000003a080010b580c4070070101e41e8155424a21020200700402c103d000d1840341c0d0340d589108200d1a06620022030045520010040001400488120100e0714113100d0a82c00c440c180d1200844 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 609534874 1250 609533624 609533641
    0xe10050a0e0c01020109080a030903110303090106150c1a090309090f100605120718080d0216060c030e0f0105040b04030b06010e0618090405121c0c2a0206130e 70
    0x124042c2c4000c1c002070041c0d081a1b80d800d60390f885113204441c01c050b40c91422404042c85506c80000195405048036141e04240041c1c074001c2c0000c1c410350ba40160114503c5041e6406003c1c0700c48402c2c2c100e0488030312840e0114001d4441d4030010b101d9542804104002070302c03170f0381d110311081c028200d00505070b019145c921040d051800c2c80c0e8103c80c1c1408014441038041502249589511040a15003080c030129035602d590101d62844d00851a80d00841d0644841581d000417005141e180403542c0415103075588400ba2140344441d02d0203030000d0981003451000d414681d000c0d101071074040c5441880c0541d0b6400840b80c503041078100f210002440001e120725036a01130708103c45403004440c4a40381056031034001c0003162845002d20302a40300d42e800901801014000f03984c03000401e00445079149101d400312001400c4d510040e55141c1d180c41e244100b218400e000b850012500c080d0b255603200b40310421031480381031011040ba03001004002d18001c8160a118860091a02080042c81414200342 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 609536124 1250 609534874 609534883
    0x209040903031b08130f050c100201050402030105070f02070303030b150a020f01060b0f0d0917040f0e0c04030b06090916030b0106081503060a09020a030f0305030f0a06060507060e10050a0e 83
    0x3d441082051540c18481d050654004850350554080e030400001c40c480e207865400c00c2c040170700203640310781071040701340b1050b406403c4188a144214000c2100f65110340043d6620b03e1640c00210059000784c40900000b40641d000d40780c0e1500062091a0a18034010400800e0f4000b90003040141c01903002e41c2d0401c6001d0051b035019007002c802c81030034200080c1c9818001c1c012950b807005819113414400b02445540080f880d6510700171400703640d542c4d84070030050324989a00d224150740c9050305c1e4000307414414401d05840c00d0766404900b146540d1a034800f00010204003602c1510240a541240351107100e14030758403001107101e00c02042c050b40c13510310041d01100006152410300720749182c07810029500450b10b40d0380120b40e49e8001a440b030840c0003154100800ba00001d10760081c800700941030541210140d4846c208042e100107a41c0d0700c0c40207030741c207031541817103a4004280d0030b1092a00281d4140c015030251032440d011201422401100c40013525400d5501c0c00c105a034a103c4200c03120030901 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 609537374 1250 609536124 609536171
    0xc03050f120d02070201030f05010b0a090905090a03211e05010b1801120b091003060e0f0a02010828060302030d0306050102031b0a02090f0f0708150d06020904090303 73
    0x10181412640c14240d26099200b209080071442d90b001600030116130295000e65124401c950042103103607120015a0b0a0b031340110071403004140546d80c00520079540c2d0049a1017015542c0240c481522540c0d025074101350b10007001070300c14642200461441805104907180c2140052900f6a400e4810084608880042c1c2110200103810002e1201c40c48018500700c4122a0078a085030308107081c0040a801019401005917111072800c1c1440b0001ca04002c207401070b030f401104104a00c442c1301e143c0319918881906101456004001d0640166004845555001103200c02d1800c2201d02c000d0610404200890001000c0d41d45182c01c1c01541420054a10101d6181c10704010342400c7c880007030b50702c0c010510768130400d040300b6803c00001901800402e210b40d0b03000d03095914a041052a10310862011100040f4900221002a25507840380c0d4940c0d01401164a520000c085035009001802e070f01000240c0b12141c082010800940391403064240c0c4601035500012170030000d03170f0640010720118 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 609538624 1250 609537374 609537403
    0x40b010b0702100f02030f130f0504060315090609020d0b0930030901020906040303080117160608090a1e030201110f04051e040515100201090803070318050a0c0305 72
    0x81c80035800684994110689544407424055820340711440205d00d94805d5040071001003c0100745a41141103410314001030b00e148020350210303241c8130000e11084505c544006480740b020b03d141031071540140ea00104595005000124000000d80c0206640c0d0401c094220341b44480c0c6002c201c424581485081c8041640310840f6032030038051070082d03074100b81c00d00e448000c12500202080351540e0940c1240d141b60300241c4022788075641da040c0a40000c409109840340c0100400c0c2e003070304610011401d40442881003003e412060b0404c0030440d00380300d0040603d2464410400e02c00041948807454662034804c00d001080d14100501d8002d0a4403103103150819440d406101c45d000c041d90000540d0b050300c81c181d515803041c643d440c2410b102a12100300c0da58215150509115001039180092000c0740c0080d2851507603d030b00400300b2420cd94200c000580350200074004109010f1180d0055042100207110031b0340340943d00e0f217480e403e103c400d80d8215400801c0d0142041000b90a01c0100c0711171014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 609539874 1250 609538624 609538627
    0x40515100e070309050304050f0111011b090603021c0203061207080705012a020621010b0406030e0a1a060d080c0a0b13030f0f0908190201030509120702040f0209090f040b010b 77
    0x4c1e503243d950700d0190740103052198150038400130103644994121544901c1c520002d0084040d000d01105c01003510f80c1c51000011240000418554024000c5400c00e088450640d100f00d20380f503244400a400203031040354445131500740070b1016034040200d0300c060420607018112248c603180c005044082d00e4401010001c0102c1d90b20041d90340889144800181c05a0703034941c0c1c0d03254400d070300050030310443c101150700a60304002045694101d40904299245c6480400c547c41c84940c406985446012009102600b01011200c1300790b0005400c80d04820058025481d54205940701513940c1c020711012282070740804026000e00030b507034102e590001041110149030360b80d941c070000c10881807201d1034404e10240b60f551501c2940309505c0300008001c0241039410110301c0258a00141c514440160300081c10000490b01d039190219419002040c14174482d46008403642c20f02001d0702070200f000749019030138419402e403a1a8143d03054440c00b0b00445d40e0b0441e03e0980303407000c12510103130014045c03880c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 609541124 1250 609539874 609539891
    0x50627010c05100c02030708040303091d0f070f030209121b090106020d03020913050f070329040f020705030f0c120906030c0702030a080a03060f0915030803040515100e0703 76
    0x481c0d1091403e51110012a0802ea401000d03860f6101d16034008004102c0050008107059001d180304080d80c401c40014003a401001c1c1500190100039545007d031101c1d8080802e81e098040c070190200d01d0141e040c0036042031145400144080b401c0034644080d5008000c3c0005003007003507120303036200303050846000c001035040030030081d0b45040e5900643d0034194001101e90b4155900300c44070116400c008014049032800342100035100d40f0a880800219041000c10416100201c07200000c00c0b445410200520480d0700411000d0703c0754003002500140e080108801150043c4010f1a403c01b03041400c0e6039425070701c01d110303141032501601100c11440c1440480030039a558000c49030000004650301f92144104c1c0000b038244003107100001c041c0b40300083c0f2102d1a50309a0801d408441e0703808031203a402640d0f81c40007010b4682e1740c900a1a0202500c50030300c0010f585002554215020303200300c0f040c841c01c2401000c040e0304140c07200b070700744102d203241004442e070700c494503552014092400340000b10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 609542374 1250 609541124 609541133
    0xa020f0405010c0c091a01020d0c0308060613030c0b0a020708011b03020702120d031a09010509390405090a1505131e020a0e09010e0f0c04050627010c 66
    0x2507009060401c030030b44142d02c00340722851030315002400a6010030400c50814005e181e02039403501845501501074062003115403406460201559070300364841d29120703600e8004000d40e642c0492132600038000407031804804101910343d0507011749002d16086560310f809440203403070103003a9444081c040c1c0c188405007501c100b545c850900350044c0da041c007580f14030b05c40c400989010090441c0c02c0311032140c0441907000c141d02d074200e02d1040054407800070140d40c0d000148003204c44240101600601010080366003241e81c111182210055200c4403100084e88480741c42ea580382c14070a45426034030201d0240710601d45900000d4120500181c204000503040111030443d44440c031a039449007821680108108400e5000303103400c85901d05540c506004881c009000a42148021500144030040b81c00d080b8140040c0046c161003d800f0000d00355a6804007080340b4501c000c00d1040e014005100020f01911403901a0020302444501e0810300b0b540c2100c260301c007030100c02c80340303040100d400e02d10030102c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 609543624 1250 609542374 609542377
    0xf39050339040204030210030b040e2a0402070209070908150112120207050d080c1612150b06030405030d0b0306070507020603040822060306080a0b060d0201020c1f03050a020f 77
    0x1030409101d0320200444140018000b030103035600103508101d2059540001960541c4080c003c40f5007210104281901d0b501402d41d03903281000c402190700035841e00c90f6025000900c0c0000307007403001031000d498480294003003041d40a003900e1850120b01d0716102403007114414400d00e1581501054208525032500340084030101e013800000c0c0c04c014010300c6001c180340c401d1010304080c18014001890040d1540380000c1c80d54003441140da000d003c0c20f5405000080341028860448049400b03a00c11814140c0350250700e08030500d04400450395070b030038100c501d883e510090b512a41c00b42001d10703201c034103511880c07054819140c0c619110b90044010081c0c1981c20406498a0540640d215601c0c1d5071146000f0340300303210b02a032a4840e4444400d840b0014002051840d003a101282c6e800c0c801581e46201880c2d484082e02d50080110b0a4200002c859081c0b19030040e11072401407040f02c04803000800404c00800240c1c10180d500390114404079111078060107296040103031400210719003e25080303c0d101a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 609544874 1250 609543624 609543703
    0x11070b18010c171008060907090b0f060f13050a45091713031428020d12020105090706020f031b0a050d020703020f09040f390503 57
    0xc03d4030100f0848156100c0c40f101415913034040351541c3c10081030003607603942c4900c509943c890604003032500e541811440e590060340007804e418240128500c2c0003040c0d070800181c01581e82c203008000070741070b616014464014800761110000d801c00d40310130f00410302d000100444441100c500300403c96138184400d100942d0b0a14000250b036091451702c0782001c1055402208140c8001c034003907668a140d121040c0c03c8134401c4030f54170310341c2d049620456180c2030000c032040007482e02d240b11103c0c10455a881c02c014584004c0009018003c01c0c2c0e51148104484482c0100503903440c0200140e54004001140203000b03640000c0080e000c0c1c104005e59a40b16030280801200d40504130010100401c204889005a0010035a8040c102c4144003d50b0341c19548816840341d5032a6402807400e0502500403402150003c0c1d0802c82d10b0f0181d140c4072200b030801c020708060090300e80390b80c1101c0c2d15080100c080005a0400381048035183c101014070f480c0512000092060b911044032203212036044c0000c68 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 609546124 1250 609544874 609544907
    0x711210703120903230d05041119060e04110904020307030f0b0a030b0a0b0103090b0106022406031c020705120c0906040e060a11040510021510140f0411070b18010c 72
    0x9986038540084445c2c1c020004581143d604040510082118000c00c0408600c825241123112004100c05000c408402e88600000720301e030890b403044e250900d50031050700344100030601480c02c46c03424081001c0764801c03a079680001e5603942410203802c0e090b001e1a00d4052048907200121402c540314501c080c0406800c0c1014681c0e42c40c0c480d80242d00076080a026650003072100d0740551394440c00603440f001c04019025801210240501505918041141c050b40c40940240000500c01402680b0740108c1240c1c1c0d001d43c820b00100290590b0b4281200c130074a01154060710300c1c14103407400e002c1c041038050b01d042d00c240d051400384144140c000907101e5100b40e03000401300e2100101c9010420a105035008281c2052600c010700c5e0546800080c84698260b0700200c43c130060b0307100c5110714074880c25401001d60010200b510b14009103040d000b40c01d0060300080000440a929581060040e448080d00b110244031074000c008018041140e10a07001215030000e210244541c00300501d051018003c0780d9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 609547374 1250 609546124 609546167
    0x1c0c020c10080919080d05090d0c030f1e020109020111010b0f1908030d1a09041205130801020c06041208060f010f2007080c03150711210703120903 65
    0x1c096410411076a004200311440c05455a130050034190010b034480e422807455641440d003c5102d0280000d0400034040103992104501e08003a6400c071803c1400240c100204502ca0040154940d10350404c41c910503900d1f0000241050395100161048600b04104505a45054071015041e290344148480303a400440da40ca0020114800c4004940550340040007580700125566810a85950040707100404502070040c46000c0300b42001074000381200c000309801c0601c81049281800f96000d03220a0201050106c29551513041d410300726040303008640750300e034880307070901c0244003164622480d0440d039452b1402d1149040c0b400300d5640c646008c901c3d41001390081c0c90b107916900c1181d03900000760880c0043c1156040c00c62640e5074814550040c0f030002e0091a2460f001d03071900044085401c078030382110754031a0799a000c0903207030400b14410854090241c0b514601041d81400e0500c0b40c6042c400b0800d60310383d481800d0003000948001401900246081032100110340c11a001e88004942d584408 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 609548624 1250 609547374 609547381
    0x60503030714070b0301030b15040b030c043201060e0603150607060902040207050f0f0c28030206030c0a0912150b01091d090d021516020a081c0c020c1008 68
    0x10b02e840b03802c4d44129112900030001200308600400654080c001d50204005c4940d0403104101c01c83d500c4141c004d606038080c0561002d6810690480944580103001c00f610342c0c4c07052005c510304159180030341540a683c0724010f100460b04400110000345d0709a40050851401c40d85640c40c950001ca4810300c0b0f15030205820b001c0201c2c1c1c1d002454819806001135448240900c1d000e03694903540010b040403801260030002070500005030513401000d0040c40c0c0f01d0071294440d0194907030340030602e82403074040c07100401001517141c600042d406030815003200399550800680003480819990801c070b40e5020b8031005000801c00b500d8040c2e0756076021200000e604010b4000585154803664403801c031045000d9100c010b4050058a818401d0030703601d0540e0020540c06030201d84030038100c0e40c803621403039110020511480004a1100705503a01d401101c40300400d0307482d80341d00c2d03800c03002d0103091400c50312540248010f49401940415040b600007001c0d800b0764040040d6440c014400351030100585040007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 609549874 1250 609548624 609548663
    0x2091305010b040b0c1f020d06050319110607060c09060f090501090b0d1b050403031805030a170d020d050618040302030d0c020106050d0b1b04080613110405090f07090605030307 78
    0x40f9255200d8003446d500782c0888401560040e400201c1d00d000760350f10f802c4c800242410f02203204031800c0300d080210b82540200d40d65050000269103004c5800c00814001100019202d00c6035803d21006a11214207041c506480140140d000381130f00300c2046804002080b107a40c201001c4010f984c02070501c2c0351528682d03d000d1008054100c07186030501c3e405613120007820381000041050720702a50b01c15400301441c00b420f241a01c0144155505580500030304d502003103050f45031000c44040310038110b1404400310840400e0380c2064000c41c1c80141d1b0f0340c2c18003159150040c00c0040c0c00c0c1c01c2001c800c115103450323100a912030003213802c15881203441e0071401e8000c47c800c4d070000c4e01915004000284a20684c2008400c01508980b04c5007000041441c001401c0c002209440440c0c0f074050090100b6a20640d02c1d0548400c0d400c0100d50004081100000e1507885002d4544100c034200700910352007804040c0c45260043c26800100341524201080c04180c4001c02114280c60300100c0001c41280d40c0f181 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 609551124 1250 609549874 609549883
    0x30411010219060c020f0a0f17040e0405030a0801090c0903061a0a03050c0102010c020a0b0103030e0d0b0a0b041127210f070b03011202150d020d02091305010b040b0c 73
    0x91110395107400d0340d8180c080220940c8001100a103d07421580405505c4031b81d540e0301c809051016094484400850000540150300328550818141245052a03681d003d01014090b043e203007110301d50004a0701746501c2e036209076034a0040c0000e003020b00400c0a80c60000d0300a54071800080c0082c1e880320300b6290590005803883c5565035000c0e00440e035080e07407810034940b20982580c800e4015400c05440354080c1d480003440701440b030707000f00c840340035a40b0715a03044d10701400c1c6c1e0b03030b4154000d01d480210748045254007a005101d6203c41402040c003070362280c100011640c140940c0500c8500070f2050151144040250040c1c5800c52383c00f1a0000c001100081c1200c60201d110310541d0b24400c1c044a04050b021941001a40c011402c5450300e07610340e04082c4807800f003401003203005460200302d00c0c0035240840c2d041c11a20b03084036055150410200c0510260381c4100c00250300c0c144c00103910718082c10000181003205001c3c040402a55040408600c502d114038402c650300c0900119654600407014070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 609552374 1250 609551124 609551143
    0x16020c030d030203011e0e010e07030f060b0901021204140f041103040c060216031119090203130c0b030f061933020106140409050a080a1806030c050304110102 70
    0x38100d401081e14010300801070743c8240580203031601950039902d40040703036842c10401d4030054461326180c1c0c0e0070000042e441c004001c100404151300e410b07400000b0400e9102e0714020380450000141c0da405a400060728128403d03000c00600402004100300701a40e44154050489007295a5030359042c0400c0094040c0800150042d000c071000028041004040035404040310441d030240e0317907031119100164082c11020f01c806400401100700d8004149040d17005014116816004c4800040d1100412001ca800441e0b9042650300c540d601c3c5003e000501d0302080040c4070ba200040d00d14684000c0011071050058452390240c1c96110440060b0506110141c0c05458089402001188a020105840ca401029101070440c8041407203800b60f04c1802480f098404921a011041000c0800e0000038814200c0c03d8a1030b018420a02000840c4030004000400039a6650201840055007400074070300755a1001003414907082c130100c2d145400c1f105480d807180e001541d050a050032100141e08044425 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 609553624 1250 609552374 609552379
    0x90605010e060909150112030c0c080708100603171303060507020a140604030807050c15010b0403020a12110f0d05010f05160f0210020d020405060406030605151216020c 74
    0x800e0724529000c0e02442108200e402c42000d44450041c1c68442864950203001c094030780006218070543d80c0307003e84520307100c0c0c54500340c800c21f951103200c89030781e8540000b0b0094100210803c44003400300032175124911001000c1100382d00e541c0c0d40940c004203290550581640128401c1d0045243c48100c100642d0030600c1880140350051000352120f10162045464440740d55040f2020040020182c2c81260315454a800c552240382c0141e071a900500036900440c4120b0901e0b11180401c41c03806402001440c03820350703d0703500314410032103840b075a03404c039210112080803808040b980b1402d19041840059031001d20126a030008130701c41c0080d030f210203045036091400c1010300b003440e907100a12918841c240700068502000d0116807086a0301c10030303401603200300c561480d209181d600500380c044034020b0040c5440d40d290041190f50b00954400700200390744850810007424030704246416000c0503120b00b8940200300555050310b2038058a0740d8010b45c00d0720940d01149008200b4040c00b43c500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 609554874 1250 609553624 609553631
    0xc0b0a1d1f03050f0109051303080c2104020312120a0203070309060203010b0d0506151e0c061306050109020f0403081e0f09031c0203161a07110c010f1e030906 70
    0x100790024001e000e0689451010615200000807611086e105450099142c503580103400c0c81d00c1d8404a410440141a00320588410030216011041108403060880544003c1000b01e10701401003600f403402010054055038020480b002c001c040c0e51003010340c000c01685006840380c446001c100c00a000a40b401094070748000004034071a03419401802c0449881c090500c6036076035180a010810800c04624a80d51200b8028151a5040c04255081d445040c4407007900304020b18412502d0f080050b42d199403217841c4042c810f01031028074011035001d00a2008154900300c03880816116078030403444081c09105001c2042c071510b0602549541407403481d00c001d00d45405501404c45901d0307100e201d20f54464440ea03032518595061003e004d1520b1011a00910309000020058041c848469130045582c400c1c9001c20740c1102501403542800794009903a001c0d444040005601e01d082c0702020301c0c5042c4450881c0d403105146e40548400e0781654400c1d0404039104914000380d001c0d003441c0c40010031075800d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 609556124 1250 609554874 609554929
    0x1b0301090209041506020309060711031006061202030103021e031501141903050604020d0f050106180e06042301020c121e1c20070b040c0b0a1d 63
    0x10740280200c0602201c00f0400b40c58005a003611640322480740102507002485461014503004010300360190203a502c0310184030340b880000341840e000081c9040c100c1c0e92490144011540080e5200320801202000c41c1f4650464000902c44411014240361101003640882c1403500c043c00b02420071020844142500d503100c00040c140030600815642c080c6641c841c003d0118000000c240040300c0d001406440070707450b030f9001d100b4003008640307080d5041d40200304040b002a100f44a010003c002d1800d55421244aa0f280710082d074240d0f09400f40700c2e42c006030612000c20f07441c0308180c007100310201c4094070f0b04406030801c501a024411a0b0070b0039000e00d000f003803c210660303001403000e0520000c402e025841c6110941002e030040a4a00c60a0018611040c072104520b92010805007000b5807101500103116100c44155804440104c901034881c00a201c10000204800400f6284c445007182c10b0040d0103200a000c89070301802c0003000203000200215a854100b03010300c00c00750303038102c4080803107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 609557374 1250 609556124 609556139
    0x1503020f0a020109020f010c0b0c070204090c0e0f0f0403080f041506061205090706020304030807080712050702030606010905031b0a0f06020a121e08091002040f0f05030f03070b1b0301 81
    0x2c241304140d0240050344010074603588a4020b481f6640d80c069007150300da03258040016011b400048040780c00960303e4811001003032640d00b200b0002c02c0600000d4100d0b203488894183c40b004041c1415804800070030912000903007004980f40e0090700c80d00600d00329611418588a600c64240382c0907030851412502003040c6074010054800340b0b880d41e030140b1058550503405136480c01e061081c0c40058005000900010798040700a10f001c47c000d01917603080c0019900c0c0c100040d603c0560030b03c081107000603198114101417100390f40c00142400c16041240c504808207455460314009800b2684071b8642c03030300381c540e180504440501034206461050707549845001e5030390402c00700c095031440079046d10345141520503000c202143c03c2002d0071080c405440d140c20350b60a00041c005004c64020050301191401940c4094002800d101913105803132171070301c460840c1550311508868000d4000134084030038a100002100d8400b60300000284180d541d4540d61000c0308840c84000d650144000000194070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 609558624 1250 609557374 609557381
    0x90109020a1710050d0501060e0c071202011a01120e010c180f050604090f1d0d0e1c08160f03030b010e010503280b0301060b03010f0b131503020f0a0201 67
    0x40c880d5460354581c102c6103240d5070b500c034402220f2945802c181c0300002d001d07500b01003401c030300841d204500200d40640c0313910900c01e040c0f004132600b075100540440c1544c140078521031502d254103c20300082201e01950300312969814681c02c00da905000c071403c28441a02020ba10a000b150408002000003e206040007032039811203c0d001007100e0712805000c101110140207807011620700400040c505807031b013036801019114141c0c501880e0f1f0f9a9884096160221480340c480717810300c40303000e461955614440030300100c0b00421101d000da402640110081085a88642030450300b0001450b242c60600e2503074203071104916001807103819590096002c06d40c140d0001094030324262240c1c03108420401c0116428081142c0000c6000011019551012911400390000007409100401d84803005e5002c80e083da03803658010008100c0c000010442454545050400b8026150703015160407040750701142c00340b0700c42c007078a26035040009102910501907411615218103540e00e10340c0b10141914040d00a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 609559874 1250 609558624 609558637
    0x18030d05070816050315060d050403080a050c090109050f0d08070b0109050f06030a0f03020708031b0706020a020310050c1201090b0a051906032003011e05180a020702040b09010902 79
    0x20071085004a045a00c4a1030040b030b01a4030750703031602c0c2103030303200c50a4015501b400b10b82c0580000b4104005180602140640c51180b80240c4034202c0c5402c201403048103c400007481c2c00380b01c40090004040c0c40c4c0e072002000e011190111081200c591170580003858483c00d801c002000d45d45d000502004004802410320f048401030070041002d56a004404e42c40014200c03149a130503000720441200050f03454000d444103a010384121000c050325000010320355801070101c03040d0003801c20709640580c80104216405004584041c02c10003540740e0220b9501c01e82001c2120039152120000f40521070304406903204250425001e04c500e59445814500608941d0240c40c0103000c40180800d0a003841c11080050710390040b800110545848403c80003000c440003031815003030100120502d042c078008040c41c040d100c801d0210703031040d0180a0042e10859150300c030700d020704415524102c600000300781d40365000c90385100260352460144001401800302781c0105070311001d0a000403c14031035030390185c241d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 609561124 1250 609559874 609559877
    0x40e010c0f09080a1104151725080705010f02031e04080c0a050f040e0c0d11091807060305130f0303021918060507050316060c0f1106010e18030d0507 66
    0x524640b910b240c80d49903113102001400c8802c0c592020506420311394404d8410302c00c66015200c10588030031082603014070f010340c41240b80e070080400210b8202d141584480b40c3c40010340e00c169a034070f0405143d072100745512541d4140031416403202c889900920484504d4030300e6403031800c5800000000842103411600600ca03c41c0b050010104e02c5003040c10710a400d40c3d0005040b2007805201c50108805000001100350141c0103070585000d444c0c841c94119035010303114800c079000c80b143c3c40c8140602000020116005138aa440c1d00da0122000428a1001e880003450003003401e0f62201d06411600c076404000924115810801006042e4950702401c490719a00c07200702d001800b648001c072a40c0500d020031200c031610961081200c41d00400042000d2441502070343e00b05180038202850420000c40d0030345484e51521510103030107500c0701103c00b0300c40c0e95060006c6503510840c0804e507500014040c0440c003800b40341c0030680c1440e448105030714848c00507084075518100718000704090102035640d0f90 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 609562374 1250 609561124 609561137
    0x3060e03040f080f100b01050c071d160c030e0f12070608060d021e2d09010b030f0a0c120f021305060a1413030804030501140703020315090402040e010c0f 68
    0x200340c01e011400a0b903109a01c4010805c03400d11140c201300406404000b10306000c4c00300017111801d40c0500c601c42c000d018513820051200e01304c039451010301500a040d05000b2000340030b90741c4250f0300411032040385505484c1c10a800058000420340314045003400641c04855400030708900440003400c441036490380c0e501d00b50320b82c54400034000c00c8400c044009602c0702080c9041504401d2502082d6000c0030003c09443d403110b00f01d83c055814080c40959541704282000c4c1e54109414280f90160050140c03014582c51850000060320610340040c040d0b002403a2580c40405425204d245540490150300c0340070410b04030b0130b40400000350300a004050460b860390074001003070300d002e40c00e031a20302580b9160b40e40545850889039107244c0c0403400e119044801d1074404804100c070b0380c0160019521030000001c10048101030807000e1a00202001c0070075004000f00101c5032142850703001c9440040c1c59a4107681c48070b00c0020054440880720b4040e80d071820b041c1100544e80810f40203010102601d408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 609563624 1250 609562374 609562379
    0x20403140c120705030a02220207050f0708061e131b0509010e0106020706211a010314011a25030c030809030a050306100c02030a030203090a0e09070902070c03060e03040f 75
    0x1522041d403407091307a170305400c043c020802504141c402c0200700520b0441c5582c032401001c402c00c4c2207800c0081c0c141c907a544480711120b9200302c10082107000c2c10181e030040c1402d1078014030311501482040241b0421940100100d010801170461895a02e070340481390b03040f800d000c0340d03c4800200e8a481810720480d04400002220300c0d00c003c00c241625a954084c100b07a5040c50815114003c1c0c0300c1314844502d20326031040c1d1400d031b814450080080301d50409a40c40000400004060f6200e501186591412900040005095441a030052094402e00d000e072204108001c0c9504c1031420306646604070300801c089810160b0040003003c8440c8652038240c0036031110b0502c20368a0242a00d0200400d4040021910300e141c90010006c1001c440e14145500110542c04241001684c88080340541e0000c00d103030740c2628084541c1d202810100c1d500d01c0f641c1ca0304124059481302c00b071183c03d440301e41c00510641406800c1008502035a042101800f08840400811b56240e01c01d10441000e0f0040301c801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 609564874 1250 609563624 609563659
    0x7260a0b03011409060c1b031c2405011805040203100302010219030801061d100807031109060f090418031d0913020f222702010c0b0406020403140c 65
    0x4241c0a4244400105546e41c0c0d4803c0e62981da5201c0300011302034210001c1042d0001c0313810001801c0003040509480032114010001a0a80c3c0e810700721528500d40340100308804100041060080350360918014005200030280d0903000c42603500060307001800002008858000000c03500100c0703200b0b9085031800440300e80c90355010801440010005200f1100410043c0d11a00c140c6030487d0b0f0720030740e951003204408002024108004902c0f40482c03e030004120000d509403007800c3c0f400c041d03100110b181c00340344000911079100780c0507111030081c4003090000d142d0300e4950142c0c41c210341000d00c0d00031804040c200509489058030b0840d440c46940912005681800011030f070049100c040780f608003002c00d90070400442d240c00b02040d08450500c82100340710186031408001d440d0030742800110f883d0300c6212094505803240d1030841c0345110b1000000140da00c50700015900342c0180c0003807819200c51401d00c002e44629440505a40c0914820000006001c24801c00e510812aa002442c40d19001c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 609566124 1250 609564874 609564911
    0x30e0f0306100e0709090212040b0105090108121b0109050304030c05010e0f1e090a060311060408070e0702010b03150f0a0908040501050702040b15220e07260a0b0301 73
    0x8501041401002040040201c500c3c1d0458010182d41003644a45490300b0b020012a0810800c82c00014200c1080c00213100084070134901521042e0742c104030300d40c10728203a41c0ea1440c25082150000a0020b0300e012104003c001010822428100074072860585040c640d48e250050b0006480c082c0400340002503c2d8058030381c2e040000c0c005008a1000d00c00e51040001880c4920010b4000d6598076044c0c0c845644c400804a2165902031000512503066050003400142d1010103a03009520800c0240203800d80003c0220440c1d01e003a051502c00d543d105000c81c05020748a130305640501c41e6541c1c582000f04c0c14085079100f0b00080130741c00000d0b902c4403403980030740e00030fa034010380301000400c000d210b41e5100c2c00c014000305002034408602c101188001c01d058640c828100e40c8410b0000c1201e034580c0300452041d0100640a0b804a110a030601c240c1660300e050250848060005815203134503000000340c0071801c00382c0010700c03441c214508a06000c0240c000f115003a0701c0303540390816008030385601c540f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 609567374 1250 609566124 609566131
    0xf0d03080919020a0e0406090f060e07050f0a0e0910020307030617150411041509020702090c120c0d0e0f0f0721020d0204060e16030501060905180a0b0d030e0f0306 72
    0x201041d43c0740c2c0c585841c2c1c4d200b0203000b1b4030503a1074580701e09036200411802048003004c0c3d4840c9800080d55004910b506041c0f100b00d82086209480c4004004415034070041058191004000b00c0b81c440e80b00d000e184c914102c0051305c135004041c0044100079483d60107902c2074044500207008032600141c4004420307110040b05041c84252114000418040355540d0400c051b8540007800000c2e4001c0350000c040c400c0e001d01d0384a04401500007841c1d60442c2026074556402a052060740d9040c4420380500003400d1500510008910002280718a054641da800000ca103100201c1a1045203498016060316031020320002106403288060015200d00003980204c0e5004c410445619407400c03543c00c018146d84102c2c0c0c00d0764405d8848001064500c20494024084c1070b5100c0b1398006c40400490103015a203050f8840300500c0b0311031408000780d8441e00c4401c08130307585182d4003031100e5861100c401c008102500940342c0061388880564105a000540d9004409045985440c8481039008065654204a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 609568624 1250 609567374 609567379
    0xe0a030309201e0121060812070b0103060504020f0a0e1006081005091918030914130207020103090b07050a09090b0a06050a050c0a0804030b100614090f0d0308091902 73
    0x340c00210910f0441c85082c0100d64145000075000050038201003600602850502c0d5003541c503101081b01c01010451481d840164180407030802c002d9071602d070b1038128144800b511013512180081c0c21940c6d0b04810440c014002810140020707160071000300e8545048901101c41400e050303020883c2801024068414401c03546161401030601c020310014180103815040c0004074501c01840007a000e0242d0701c20783d10000c031181b1110115040040c00411a503004040c0030003416509220341c2c8450900442c03100095001581d0b8200620048004005450014080000003c00c0c03044250b4440000d01191115582c0d5401d42a1520400011200c816941d560702c010000410051540101301504844410f41010343c10035400442d81e0f4182404454100c800260003d410b208100304000c200c1e8000401c0c400804030a820040301804242401100f4182c01001003040c0c001c95640d1420240740f6000a0503806180e0300600c0c1c05040510160390b2000b46014048186041801380d17118490302d941c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 609569874 1250 609568624 609568639
    0x121a0901090f080322110d0807080a0e100903121b0210050415321c0c030f14010b0c0304090e0a061b05030a090804171b1504030b06040e0a03030920 65
    0x42000300220301070507c0c030132248107030244501c50104141c50040d040b418400c0e150312020351042401c1000440411041c84144a0800e0040c0085418401c0b40c920403540c40c2440c080c01c0ca01035001c401c0c0c0c80318021009520200c000103a41503207510601500840c2c0c888552018110382848090340c052140486501d441c02d516989000308480c000d50000847c40a02140f40c6410380119040005100d60101078244a40301e0742a10082a4144210709500340d8050b000c00030b5003000002d0384004401842034078580400400d4607040001c080c01241c0080c03440a000b0022041e070360004585a040300351060310014034000d9144500c400c820521540302a56581d51407035540d8140f07109004107400c25060342e200805020108181c00c03600c0c00c041d10000c01d10020030307a079085c1c2411102c9094040340168003a0314542048041007070058181c42c1500d50000c150341066458501003002442caa01c04c2e00d81600c40c04410710305142c1c040e448280f0315401a1003030f0050328505660b03120040301d40c4a8150300f0520 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 609571124 1250 609569874 609569903
    0x60c0b040b180a0c030506060d1112031902060406060515030c0f1308031314011d060903010513050d030b0f0f030c130213121a0901090f080322 63
    0x28a00c190703540010721811000540e061115003070700c2c19005000440c2c0c4d0b00740e009014000e200c1c0030803500350b001c8001c85404140b4030059450032006810621345900807050751518003911714051041c2c605a6813086003a21003505c00410096443e80c3c19101510094500507001c00c1070305000100c3c5900740c2c102c041c0380d4556286e00a000701140e00c81900261403000900c0600c0030780c07105041e04001005254001c5403944c07242034103940c2c0d8401c154013421445100010395038a50b41c00102000c100c0d0112101118440603101c08615548100344005a15500c0c003070410104490300d03288409254003a40444283c10082d1070141c044400c080d0749190b0003000354454100c58903040c600c0b400300440260070741d24190002000b0610f400342503c148060150045014100c2d17416194014004002c4451901246102602e914441d4014642e2140801c1c00ea580011b8132004250455047d0946c041d00020380f808290502a0050300261202d40305c180e415040c1800c40300d51009100c4a403a004101441401d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 609572374 1250 609571124 609571133
    0xd020306010303200613050d0806090c1b0d090602100c021009140a080c1501050d02060717132102011e0309140601050f0a0e01150302090d060603030306060c0b04 71
    0x8285000440300c540d8800003484030700000d00149000d800486c1408a19894925003c0e0a107441d2110324000c10080004008541d5100070140c1e41180c5403107400c1c7c0c0e680d82424142203420143c0410201c0c1e070312070451000300302070340900008200c0d8203540c03d6500b400d400342600402c0d600013a011000603440600200b600038050380c408004c0512805018035a0030030350f86445e0034a048600300740c60740d40703000c624a010813106100c2680d5032448a0542c40003503041a0004a914000001c082d016410100708402080b6100ca40101c0b078180024000e91100001410460052000d014100001101001c40c1241550000042080039030503112601059800c103101e2182c442008035407401c05445100700804524058a00042000c003100a049191304050030b00040e40c0c0401042402900041d0003041001100051107065a4803000c1a00b80c800c450441200680502c2141d1a0b000114503000e0003000803503405041201c3c40394509029240d41d4507000e079104500e120000c0d200c1c40c419800a00081e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 609573624 1250 609572374 609572387
    0x80a0228020f03040f2303100b0a0506130306110403020d050309030111281202120a0b121b01140309013e072a080105090606060901201b010e0d020306010303 69
    0x951b100311400c0c0c1e804c080c003000245420507040c086441c0703503540c1d060741c110703400c0c0485803601400050342c1035884c2030303044002643c1c003031468403002c0d1940365030b20762000d6080318000813a0015034005180a843c44080e04119840313600140380540304c0d41c41c081e202841c0303504030000c1d5142e120f02c40440c2041c05400042c050f08a01440048408210310103c20899250042c4042c21035080b20075a95952480c124104000b2a0121580c07184100e601c4103858600c1d21002580c2c680f22090103d0f96003800030203600580e4003500c0c80c400300c2003018006c8100300c0410015408083c052620000855100c40e82100101c0108102c45001d00070710251f00030006500d0800340101806441007030f01d2540c2030b0340e560700c03041c29084081303080c959000241b1040192039002d02440b81c105100d14094051070816074001034440c4180c045140c18000c0b2200c040d180041041500e9243e01c04a00c25600c54101020082d40394200340c03c03000740071032031480c520442d504181162004459000c0c0003000180d0840d141075425 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 609574874 1250 609573624 609573659
    0xc0a0503270a0b130f06020102090f15040b0f040515301305030f04080102040312210b01050d09030f0906020705090c030612070b0403020a0501030207050706080a0228020f03040f 78
    0x9010544d10001d481102090003800070000e580c001600c440c1c0007810820069880e480007840380f04418030f4491300e00035040c00c0303a08465800e40d503150350310380c804000c012034092544191b901c505007074a070b241406580801440c041c2c070700c40c210358207d0704550309500160030101864200d8034a044000380c101040e0388000520f07107009004803410a00302e00c040a000d81e010350408403460f50049020001c210130f41080010074885800d0607606d054900060031a041d070b1003030f55020704645071026920f082e4050021074021103803c81c41400f500b191420080c014400c1c9403072110028504940004070740340301040101c25110020800485902c0310000d03c90300f07800283c20306034000c8100489010140c0c0800803030005240d90010961514618010002c2100301c6034030032814940100000c000254001c80e1031740540b0454104040603403140300c0c08100a015280d000038442c10782c0c1c00304ca170051032a4400007880100a0f42106c002175107070701c01180c03280200d204aa600c06100c00c0d051000404901b03076182c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 609576124 1250 609574874 609574897
    0x10306030512040f062a060902061b0705060906030426190f03020702060720040908030a05070c020a0e090316060509010501080c01020703030c080c0a0503270a0b 71
    0x98554403034032a98104150654003500c0400001010801100310304401e01c020509401c00100b40c2062800c801c42d078606102c040c5210514090b40318040081d158400c03040c29401602c140d88400340c024500c0100300c8101c2c0030203098812340c8800500d600e0100700b203030180385014040340c2c107507107c603610404a809200080100700f09640101c41290300200058214140301c411030303c8180c0018000078040154620b9a9010540100030b008056101d43d01103c15141c1d010100d40380c007016042c50703c0e014407400c5c110694828105040d0070180284440994054080040100042c0d02c0b182d5060b20001040180250404c045a1040081410860a05a012000324180c03840c0041071508480c41c40007a40701218450380c0ca50070300050b074109104250150040c04014107a2580d0400041d5580302d80340f00040c100f2115450a80400a400b415143c1103401401214141e000d68030b001600c80d0810004d401c800b0500c0f0015142e41102c2c4403170000401800b41c0513040483c1001403401880d4007004404a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 609577374 1250 609576124 609576131
    0xf0301180624031d0d0f0305010f05090c0319020414030606030c01080c13050d03051801020607210207050d09080d05031303080c070f0b1f030c050402090a09020c03040e090d0207140103 81
    0x1801039400d20103c000c01405e03136a40d0b000c554950304050200d41c0306800c0401140c540d81410b10441d11480c01690300501e02c40095516547e480c03919200c080184810700710024000b040000f0821610030030a06005000c138103a440f182e5481092558841d480c40b01e2500042d6054042000101d1010080010710300c0c251300c03030301d81a880e80c000c0f44607001c0e44141100003a0f4001118161480d80d02103000601000344060991800c0c000e4000f0620421a0050b07841c149085042d40c4030001ca9504846960f607100c01901c0c0e440b0000314014200030224031400005000c0c0c070740151901441101181e1043c1040c2d800340460b905a52011114544014071280c407086040004401103100010041c0415209006060840c03510040010038044018010703a140c0241050500000d801400e02e441555416200107131160030070300028204602319401660200d1000500010038034011000b0819a038004212120b143c403211000f554807006203400d0f0006070003491050040070442c0581d00312941c2c0514012 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 609578624 1250 609577374 609577421
    0x705090118031115090904060e0c0a0b0322120507080702210f0c010e191a030105151615061502030405090603060907060c05030f030118062403 63
    0x814000890b04151688004400c10345264500000e0004414411000c201c1c203080f140004501e403e100600001e10481d2914080140c8034002c201c1e0400407040142040c0441e87d65143ca100184d0041d2500040500c050010040d09103492585044413544002c981c00504001c8a003103400360841d00c01160200400c01a00b405603030780c1d8005c10500c000950108040c40c280117959440c4c800d04810084451300880711015060380c1100b022504104161840405c510020b0700481d00d054007a00442001803100030100544042c00016606807941619400b10b14a02410000842d004001103103420007900301c101c0001852038484080d04503040c250100da481e40b190001040300c2c12142d900c5005034004036003000145401080542c01c00b80c1a4040d012a04011490030f49404050060100303014031502c0d00001c1290410888980c0b42c550000c00780c59503116500b44000010300328031840514140f01d80031440c0002d0f400314071003069501107480480c041880d01500600004c400c032200349039100b000c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 609579874 1250 609578624 609578657
    0x6060720040f0c020106090c1209050304030512030703060506040f0312030b031b0109090204081513020306133c0c030602030a0213080604051e0f07080d03060e0f07050901 75
    0x1072030202c6101d0310000c10740d5940010000d08594082d4402c82c2003900700560154400d400c20b0600400c1c024109010440000508109103148035603030008103e8032941c0d4038030b000280540d01450080c446698144580c541d60780403c10b0034000c900610804040220040000860307000c0c10b2000d500d20b9080100b602403526001a040000d800e41d1080d0b03454100c54954007541e4822503000103007030071480442c182030403c0740851303851094802e030384407070010000400c601c0c01a041382881800d5008003151214981405800b00c51541d10320111a408c20444c050840300c184c600300b490030780b00c84000c4240e8190b40f000c002410301c0111702c41650100c0d03554001001154803400210700c5080e1001015076242c115032000c001c51881d5901107450358200341d0030b20002500c041984100d240602108480f00641920b0aa0400d03a6203903089100348111180060031b107502080d00002c3d14440c0c0c50421081e683e84c00b08288030141200c0b14600d11202030005554079000700e0181140c2d0f05c0600d008014508044207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 609581124 1250 609579874 609579881
    0x1e040e090607030522390e0112031107180c17070c030e0a0504050108060f0702031303080a0509130c021204030302192d0c0506041d0405160e0402040c080606072004 72
    0x110200f210003406c2141c0b4241c0d165001d0a8000e00c0c0210500d225903241c0954203020709102e0708020300b04103141c080b00005040c101f282401900e101218198101d0320701080c400204015581000410b501910840364503080c1b26025203c1d403090f40703803901d1181141c7c1d0102d61a40b440e508540e4000726840c1d002c42c0ca5203d5102d11070181200c40001c042c40e003002c0e075a8414003440242160115801005000e002d4803905080008695104203502e450f01c0700c1e04820380e40d9003d044111500901c1c0381032010030000040d0421a8007603d81d401351592030032045444561445070b070001801680c814000408440e400d400b11010385070080d84015111a18140c500d03e5041400b080c00300f5402404010300c0a005002a01800520003124564500303031500d24421001106c0d1042e0071604400d81300054240700060084a00c100c4400142442554890400035051002550280e0143d490b0080c0c8880d010300500d071040c0034a20062407207040c1071055840308400c1c41c207114810042d1952420304280c50b00c2d1400f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 609582374 1250 609581124 609581183
    0x1b080f0d02030906010b0403120f0201020d0f09020922080702130606020d090b030f01060c0f05061e0c0310120f1e020108090d05030a021e040e090607030522 69
    0x103001682d6403d202c50a1454074070103800c414078030b00341000100300040605d8540342124005090901903040ca040c0161300a003d800011158242071855114540400394071204d0b0051007190304036210b4984007494068000d0050070074003011170f035038849404260700300083d15400f48010724054203251009040030543d0344a52010000d603210125a00310150044c15940140c28240c401c58203516100c4541e100750b51040c0305030b40910010007651400e1000340c848405165030000d00312200c504204e4261762005001990302c900c0c0c007540d43c0100750b0702010881100d0083c2c400400c0c0b030400034180741c620884255201412a286c081d0055800000b40384c1d9240c00c03458410614070407103610450700024002d00c03002807450500ba002610b800d9102904030703064036000300034000010707103e000c003030b000c080390001c9040440264140400c0c0065415041440c887c03088a034481a03c2040d04c80507820b5064400541d4085400d400040f88480903041110900c90703c2801112040400b511034045c6019090005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 609583624 1250 609582374 609582397
    0x50c0d060609091b090b0604050f0f03070f0603110c0a031404032f040209240408030301140f060307020604150b090711010b0d020a12080f1606060b0a1b080f 69
    0x31040100281c40d84c05842c02031008a506203c0e0700940030000d05944a9801450711610b00502c0480440d11098802c80d0004409011515480c0e00c400303c0402c00310390380c03051400080c1407091140d807128403801030300c1c0000701d07150007412403440f80d6800b580d0741700001da002c60141c2c03000e010002c081100198600880ba03a1014081c12403100c0b804c0c0e081100038031241c124042d500411036034046032a9081c4041030b4082c003c41c100c1c0e24079403289151a09101e03a40c003010103031002100200d50310045800384007289000304d40d0b00d80c200c00c54070180082400308881f01c0300980c000c10300181c086140000040a000403204001982e03243c0200081c80041e402d58281d000103000700310501440b40c00340f1408003035400c11071b004408802903900050071a40c80d40190303c0c40600031403d842c00c02c45d08a0999a100042560241e00c1c0c00315407902d014508a607074025980c0702e003070001c001143c180080459445601c2d40e41d03110800d80b5030303031044055414190b000700c0b15000c0c01c03c619403221801d1005820b103811031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 609584874 1250 609583624 609583643
    0x6181a06012c0f041d1c03060305070608060102120a031d19020d020f090403050c0607050406050301050402090109090216060615080f0924070206070804050c0d06060909 74
    0x240014440e040100c08544001c441c80b41c070b40003030716506a000000540031188944024000c40c049400341c410704d80c1419031034003075000d1000780c42d5000c2a0b0030400c0c60754038000048000c9892007182504d00510000d03260303411201060100c64856221103a205406004440d07401c4684004c0400543c030083d8402c3c0080d689070400300c108807403140300b0848620030a00070318030043c069002d814040031018009119211000da220308549400c125034982076070041410540b032500d802c0c080e0090348010701500c440e010304800602958092000d5909481c91540e4007801d45e802c0c4000d0000951080040d603040c807060040005280380c0600040602ca0030000074107000d040365280000503903a082d0007210403044590408030703049510001c40c9500154070b4450300780c25160350780c2060501d08141c1486050b0403c0c6650110000ca03109072060284000b82c3c02c8462564a100040743c0f41c590a460046c860313000740003a003090303103022541d03840028014a0b00054040c2c1d0798100d038080b5000750b40100ca60300710 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 609586124 1250 609584874 609584881
    0x1b03020f1b120c060d0c0e0306010b0a081609030b060d1b0639080f0f19080f010303182117070803040803100306020a020610060905090406181a 63
    0x82c4510001c918040380001003035400d4003180050428099817800c46891036070f43c00b030074030180c1c42504e54016054019042d03c40e40c0d615138440c4d0039250301608214010482d10000304080c100c07140c441000c005c00560f1074074a0613040d50f03101c019410019115035400940c885c100c0c4042862800c00c42c540c801d41e6044040b80c2171030007101411303c0b0f08000013400c181c145103000b061003d5514003281442c500d600d0109060080d60710f012442c030b0041388080351000300013203000d01c1c03410900001051106c080c100c0c09503400f42c00a404855660f400c0791141414803251004100003401070000c4a08606010070200c48583c0b12440c02c3c61042c0800b0842ca88014402c1480c0d00344980005120310724544200514034019168490003040d1002074002004264000300184846da00100190080e5506c80e1081d036540340d03401002943c0d0b2001f61074a1f02003a0282d03000240042c0a441690103c6801034043d4915030380302d884000013481c040742c2c0482813040e00c2c0000340005120a410800100d4101004501402d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 609587374 1250 609586124 609586129
    0xc040e0403140a020708071205060f0c04031a04021c0f230f0304090e0c1c0c051804140f100b04090209010605070b07090b12091e1b101b03020f1b 64
    0x2d141d0f0100d85a0230104510001191010402d01c2d8072113400d0209a00d5522900b001114a1040ea0b001815a000d41c8044041c211222460070b405140201d0f084045584245820748a101c10f048000b0481040d070482c0c40b0010300400200581e408941c044c401c80d618001f001141007140404080c40c0c00e420025052041c1106482035031040402070004001511068002c030300717021000001351010210200442c2c0400450070700c844050000588100b000221000c202d0b42400010740301198070b18124450b0544291001640a000d240d030800100903151541c0da101e0014590001c110341c000d0b0f183c88061001d1b0310f80171017281c000c05465954950303404950410038418000a88903000300f09600c401006801d0625040e1015814010150301d015200d00c1c54480c42d103944a032510784492151104026000808141105000f107524000f20258041400b00000c414039981600085a14540d041950003c00c02004452078443c0c0100d075030402c0e10400c132901e0301c1d214400b04619044111040c00490 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 609588624 1250 609587374 609587383
    0x1090b010536090108032502010234091a04050603030306040e03090409030809061b12070e0d030e03010f061d0601020f0102030901020a0f050306010801030620040311030111030c040e0403140a020708 87
    0x141400992003050420768000bd40b1460380c0c8401455038a406243ca02040c07902000c80000e41c541580d0310300c1869918100d5402405901a244010224844101380582002d0007004d00c22000240503500c3c0d82d603a507040000502020500a00701e20080c0458180303503da034451028664040c0e1034402861030071510413898610003c1c006010f02d92502c8110f020300799400c4c03d0381c03c2403200c00d0140e202d658136a6411140e031598402c0c0103512080860f6414103158121103103013400300c8160000d10114034600c1031710302a11924418618040d0004189510540c004840340b6001941407040d26070070002c0410003400ea070015503c4d100103940c0040c0070071142c0e8000d403501c1e01640c0a400e001c0d0441c81d014001800c00b210512002c1c14903a119000f900030742d81440040d1040707800300285a0b445607128102140d030100d984074541e02941c0381100b10041c403080c180581c1d115842e0401503500d806d08002c1c0e916503245010b8821018004840340c180710080c0b041c405008215460340c002d0501314036115032140390 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 609589874 1250 609588624 609588667
    0x103050c1507030c02040911030109030c03110106080c120115030809090f090d2a1a010f05060a0309020402131203031416031116050601090b01053609010803 69
    0x804040040b2800250001301d040005070301120000340340d0569042c0703045012303209480c40780e041d4600310070b140400d0b800c681150f10440c0680d494a000c010465000c50032500103005078107152380b2820070f01da19490b000c034101c0c0124150702c00108000c9024102035402240a400890f208080401d103855241080d48415038002d001d20030b00e1000707090001220b9281d0585000e2041003042d0f41c1400f40ea070f00912179100c01e2a043c0c1110140280c42c0c0f40c00e1121000a25080c81d02d4520b070200000144804419007003800d86030000c241034940030440750180c0050144406c102e801903002d01c40d60401e001000612801400d1086480e80700d16510715005040380d0079104102d1118140a090140030b10061440000d1001507050000d07507400e00c411801003600811540d1050907408207190000c000d404140a8100c1f00c0e200c1d020300c20680703d2401500d0901070031348000c0560920381c6c8100e03041c030b624030945007101804600e036003000e007200c2c1e0201c2c000200c00d03000580e503513100043e240040003c09904104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 609591124 1250 609589874 609589909
    0x102060105130203040f05031c150e16030e0604150b041512030302041701020c060f042d1a070f05040e13081b0d08060108070906080c0c060103050c 65
    0x1295810440080c281d0760116021058866002c0f0004082210940140800139000401c590700d9140702400d20b8040b143c0d020300048281e050580940c003a502d0010b004007503034414411414150b581030b0001440c2c5c00726801803810152580d158940c10030b403e0041500440c00f500068907004050303520b4505948001c00c0e0940540d00e008502440c03419100410010380d00a19281d03a00c0c1925401c00b100a401260400b40c10a1b20582e00d203480f41d0015070040c800d000d14101a0790f040d41c0da04e0780100e44643c0c11107001c0c1640c10007450a0700d402e81a035001503800c402c200010515401c00740ca03484c0115602c0c0d6481c50060a075442806400e540002c0511500d981502d846440e00342441d40c0400c100e500601101d030030a640103a10810013202100f901c00c1400c003030640806c004503400f001344d6aa0141820000072030081c801158180d440f40d25240d21803030f1541c540b2007000b89800401c64102d6001010b20144440506c04440e03c87c1082c000b0718003c50050b0b00809294801c28100415034196a18010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 609592374 1250 609591124 609591133
    0x180a0f0e030f03090a0618141519060306060906090c090605091021060807141c0204140a0506041b0f08070203192f060103080d0b04020417010e06090a170d0c09140102 73
    0x11027518031904900d52100409a081504a0414422901501741134100420070360a0071800308003620309a000344100c0e44003503014405500140300039503059440c0d01952001030340802200b480345c1003030b12034120811480d1a005040007a0503001d280d604401c0204411400e441f40c0d4108003c500c2000003501604600c980c3c004068458400244404c403c0700c0401c2404040e090424155541c0740e21030b81006158104039480c526054840f0001481d0494060f445203140505a11581c8079140d40c50207008404c0e00c40d0101e002ea4040300750360207080103040e04210310003000740f40a14000317030444030396980d401e803680e203801d50041b80c00800e100944494621803502d20984c1da8800c0718000340041c112a0800d0f10542c0d604008070554020703002c0c000005070071078000107000a41003070301603c94140d02814402000007611000300d45803500000e82d001841940064440710200d40440c1200e0444c189240740340e441d000c600030a44095a1980000c0800308414010030402c907030b80e4001660b00b104c000d10151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 609593624 1250 609592374 609592393
    0x60d02040b0c0f0d09170c030601030302070312020307080f07111005070c1205030403030f11030a08040b0f040b0601050c100c09081203010b040e070e180a0f0e030f03090a061814 78
    0x40a014071485189045500c2186e084a41002802171400d032660280545190b076844c0c0c10040d41d100d00d140300c1260040c03065200f040a0314070200c01c5d10115984038000d11b00d49881440d000182d500558010340f4234100c40c000720005c55441c007611520002d42911415103d085a003000c0060551607030210795803000d40d41860000410100440e01540c3e81810807450300c89284404580765180000082c0c01844005020101c554100c45800e100d03c2c801c5141007150303a10b0a0710101030380000e550003020020003101017541580a04050284078039040700703d81601010803100000d84810b02d0803d004501041e400b4802010140403042040c020007140522b1540f510002d5401d0788034034814440c02c0d03021240400d14451281c0000e54443c1d80c02804101806060700e01d01014044c1030f25088159031504020005600d02401516851352030304010310b00340244401440c820768001081c6002a0007054000e4000074018403446401d1032200c680d0022000c211b240881c0e00440c2d02c40001002c3d44400c000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 609594874 1250 609593624 609593627
    0xf0e030c0a020d03090e01030308151014030c07170a0f020d081f120b10090e0c3001020c0c0409021c02030f031605070608060a0b09060d02040b0c0f0d 66
    0x9078140d0503100401c1d1030760142000c039404495500700420740b0005400010a2690010080d400792640301e48501c00c00345000f0410550481c41141000840c010b51704c180101e0281201550740510b14228035481c201647e5074403146403041c0b00c160684c4050100740b65038001c0c0e11140e22120703058103000502e402d07886c14101030134048008000340340c100100c0c080d49812840b031091078802440d280c4d0002c400241103103801860802c003156903a03001c00c003540002943e200d241c000c2c611401400c1000d040b8000e41d80b414407100070b4400e0100f0702030f001e1118161180c0c070101d02101501c400b02d4000183c072840929491810075140801252140341400000c0f000b40c0c0c2c0b00044940203114142100808007850703c003190501c500304c0c440350010300005c10fa002e40128000700840c0a00d20500c20f5800245d00c451090303c503aa42900c1c00c50304400e8089040c00b400038039100410005c1c3c00207001608003d00c642e8044203981c003075080781002c0301c00401c403103000031410006078503100d8203c0d004d02403004a9070070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 609596124 1250 609594874 609594883
    0x10501081909030918021902060712020d060312050a0207122d0507140f040c0e0d06180309180506090a0213030605010e0f070512011502100903030f0e030c 68
    0x450710009540e216410100341c00b40c0b80100092041035042101070b40e16030319140080d0482c02d1401010051003000b4140c5503c04613000313202e183c80c0d40b11494540c448042c104000e40100e0800d07902c450b55614084082900d80d1309817640d00b1983c1d521980c0d140d81d800e070003d01b402000c1e03006d070390405c0c810003c81c0c00040903264076028403100429034400b0603040c0c0151081c000041d9034007505900407501c0118070170f00c040c10070100c802010b030742e0710725200006d4091008841ca0309028100140b09480d48001c103103821700c40c5040345401901c02080e0542c04048104488101000c224046807001808001e94040c061000c00041c43c004010841858031302d0118590210041401404603800540d01c441c0b42d001001c600003440d04a40c00300b06560310b0301c00e0642101c1003036464408060520340041c85442c4940110b442e102d101100070b400c6079103804141c00111400d484841c1c02d501440000240341051441541e540340d004e40d030003007414600c000702c910440b1007102450044e90801c22000860000c00034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 609597374 1250 609596124 609596161
    0x545010f09200f071718010e090406050903040e1603050108011b0e040f0501031101021e150414030a0207050411070309170f070312081501080a110d020406031401050108 74
    0x80a60f84000c0c0ba88500001d100f83c1000038507284051860142c402d96078070140180b080840c00044949001800541b1300110303601486901c0b0211500040025640382c008a8001400b00301b160705042e1648001164500100c0d605c00d524104d000000401075890301030580101000002003045d06014081400c142220488074014409840030000641e02c076030340403440188040c00100075030f5851740380c00540405804c50050051040c00d50894800340011569640601c01500034540d01c5c901080034120110000c20071354400b418441c5071400d002c0180010305078102c440d0f014081c09070030700d401c0004841e482ca80c406c03903045050120300300080d00b20a01100b41c03100700075500b0008800c500120314007094044104040e00420400104100c2c0da000c0e14840d0f1490f6803136a221a075a9010041c4899450790103450004540c40040350701c043c15644900051030b10502140d14010007000c1290980c0e0041c2d00c08400603907910f0110b100001314660303540c090403007403070f103a2401d041601100034041000d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 609598624 1250 609597374 609597431
    0x1020c012a0f120c1809050906040b0a0b1309050d11031e1e03070806030c0d0303050603153d0b0c073201090545010f09 53
    0x341c0003051941c00343c20b2000c0200d0041000b84905201c4d0b07070005110f110241030380b40b0312404004012074154070b207015240c0b1035920312000b4145562a03480700401c3d8000a044540c80c10b17030780c1005c11240e48806c48a841c02050155010400c1d66103442c29900d80910070078150304100a58100100000d004000c0b2804581c03c01d03664080f241d0181d1101c00c2d140305400403d200300c400300a80705052001e01e0007562080f400b64807004410354900c814076480d60520003089500100145150b40000e001f030b03000540020010302102c1d030f4a02c000b1500424a00143c5802038108072110400000b100c001a01c1c2c64111340e140c2d01040d000300358090711101c08042c1e02a03900c0071040440c04190341542085680024148224450a5a1441110510104e1484c1100581802c410030459038650042c0d46c04001c481c8081c2c0b2000350228460300c0009034142264207441c1c45072000c441150400300700c0c205042c2980541d10120641e525107014889210b81a9220b11051424000520010108454002640c4005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 609599874 1250 609598624 609598637
    0xf0306241c0b010806010b192d091a0705060114130f0203010f06020307050a08030612030403080901170405030706110c010f151a180301020f03070201020c012a 70
    0x45000140c01494212a4020400e00320085005002140d00b1041c1240c08001c140ea801e0f9803210b5007c1d40078400c00c0101e1010400002d10001c4041c800c6186e040262030404808403c1060842c18030b840503c01c115100009080e01000d01c2000071600c100c0e1002d90311903d580c2c0c90084c1c00e45d55903440310303814407910900c0441c02c1c1d1440c102d42c03540054421b00010b840303020004004100c40b04402500207015850720481401408240c4c50300010840302c0e0b05800c035005110f810349981e260441e6030300050100f500a000d40c0e002c080b0b07041c005c0000d00065881984d0281d1904006400142031100035003600204903081400e00001c5400881183e003250340000c3c010444c0c4031141c0c1205181d102c1c205100f82258a4842405c03448051070b4015400e050003550200c8a4a5442605941401e01c402071895580000c01510032444a00070702c502c0c3d05070016001500f0894042000b03d11070700112541000341c2d4000038600441e1500380b1400b1440d0840046d061880050407202400088a00c082802031108 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 609601124 1250 609599874 609599941
    0x10909020102030903030d1b09080c090403020717030904050a05100605070309030f0b0a20040501030b0a03021804171905030a15180501050607050c1507080301140f0306 74
    0x100f80101c81e070b10300000d81107944e111111540303e80244101c000d55042014046a03210106100c0c5180c003089039a1140100203070890f490800101ca200503004405502c81d00ba400901c100c4036100d242c84c0c200e008000f445d11041c08109100a40344004c01c40141e8500d00020422610600740310082a1626482c21a803100d80d2468141c47e400d446400250000c20b2501c44903003000541203415114035400001030100864000040c038001515000c0300303915510034001813000b544282e2000e001030354000d0008895942c1c03a00894195201d12105820703c8454034204410300541e0109003a8903d084e0510301e00d03051000b54040840903100661104001000011800072401c40e00041c28241e4440d440100b81030341c4221031551001c0300b1588840280c00d01c80001503d15001054805568010000e4050b0005179400c22004d0801000019074138501805004041140036010398060182c8a00380d103640200d1074100181108a489410702c42c1e404041080b40700380e901c1c8540e2450344c600b40842c40300d010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 609602374 1250 609601124 609601127
    0x150b0f0412030c080f0307030e010b1c02191401020d02060103080f0904020d0515030c090c0a0809160609090f051509060609030307060501090b03030f19200d0801060c05060109090201 80
    0xc43c0c41c18098801d04011840d054945100c8004602860311a2802c004c1c19001a0100d82a1009082d035254420058a00c2050030a18580d072007500746c0c401001c600c02914400c1c14408040d072181c00084411122881c0b8040c0f958042025002c69291800208400e41c0b40da40c40844034402c40c540f850740e003180401c001c80b041e100c60b0107a420616a40d80140310038602408840c00da0549201c10a00c284915144296181055100b46001d9002140342a00c1c00300e5401098910242c040c0c0181024403502d094510720380502e1510700d0141c141940d40c8110640340107151020303100c0d01c1e07039a103200303500c3d00c401c1c002d004500b2214501c2032182910a0301003540c84100045450040d00342c0a41c050100041401c04c03c42030b0f80c002c50683d83e00c440700b002020a05401d15590303014041250290840c00c01c441c2d041d08a040c0848100c0300302ca8508203507150650030b202d40d42e019010b03002d1540f65210190840a0640080c5158050a900e2030030005d02042525003503600c050600c2074411807039840701c2480659 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 609603624 1250 609602374 609602387
    0x31709040e01230604110412050a1a010509010b311509050306070806010804141207140609030f041715090d090602060f07030b0121150b0f041203 64
    0x200c5140000c0254000440c041d03045071444a690007115203d00c800100c07989498031030756a200c1004403081d81854200341040004400c0320000b80d61502c04d01c0c1c400b000240c46203c40303091440165a0342005c551606091014250f0103812284a01c6018060007144214017101d2642d103500300d0380a941220400ca07410a110125900401d51105001c003a13902c4143e0030111810860b4025012074501c0d64a0f0581110240d00030b4900d140080e480e1008100803034011006000c41841007425039003c0342d1039840184c0300e41d2140c0c804882920a0954114000c031080c4500c035440800b030300c091843c1c826040f590f81391a104070301483d40d042680b0450100c00407010802c9072403030600b922071070a46041c40c2c0711556545481013840c1000414040012480c24808101d6a00441440b51a59915140c2d060158050000091001d040141ca06400d01c00c00c0c5c204104404003440142e0000b50020481016080840854120749003074503040104e00000e9044a044400f22454040540d841c85160314040320b10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 609604874 1250 609603624 609603641
    0x3060303081504111b2a1210090f20030c0415050d050a020310060513020304020d0b04032604021302090d0807030e210a080c190507050f0a03170904 65
    0x3494005c01c0c07580920040410b64101500c00000700e031641014422444c0c0e4191180f868107081c5424100c000e6003901309603026160144403031003901e0131124003945070400c0310b0030440292800c04584d10305c0001e1001c1e540944551030040f02d0824000a9114003003651000151017490141c1e5443c40c0c0c00c140510034041c0d00e406007e0042940b204490542001640c0c1c00004000f42c0c400e00810f4559038275811684a02411103074060510109100e410b021b000080d00028001e0741c10503c10000b01000030301c040409442584262600c20741c0c94001d03223080c201804c2401081452100440c01d00001d6500d4121051a40303070001e4005d03a4622070040400c2c25081e0b807400080162a000c83c0c0c0300100354205565815101b0280c0301d00045142403505d00821403101028a203268001a50f8000869800802401c0f490840305c1101c0b412000c3d901d09103200440300c40195200d401a0f01e06006074a07089281060f5042c040790003c00c00303421510b03600700840c2d481080c4880b510001400041903112900729001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 609606124 1250 609604874 609604901
    0x911040b180705130b0304051519021b010f1b050c150a110a050a0212040b090904080912010204091a010807031a0d050c0108060a1406031806010f090c03060303081504 73
    0x40d6945c548080c41c294105507411240e601890f2240e44809030602caa5074801c0c101702c1104400104e026096500075030100b654003142800c03141008105107000d0143e112032031030320400040c2030302402c06e4262440516500f0842000010040082c519a00040c126900c0007a055846a00d840301c103d1080100981100943c6407440401c1c245041c1e40c001000d40040340e4140c007604c1002d0110344118800c1d2049001c4c0c010303080400d0000c0f07141410b0080b0580c4e8071a10807200e1703618090020001a40b42c060702110008613039000101406401058000e032124250f00a00c0d0901600b801800030b400c0300f400602c000d00b01a5105180004150b0720b103101e042401f0054407103031000d00941426512801d203070582c80d01145414020a5540c100301050008981c20b00d55611000310103d01040b03031943c0b01034100c2070508407001c0c0b0a0f000c01e0041c4080b500a104403400c0300c0149142c9003640d429111040c109806051420f181040800d8115403c0c40d48400c03000140c000c2c4201c50070003e001840030100d0490f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 609607374 1250 609606124 609606157
    0x100207050909100903020318010c02090c07060b040216020a08010c0c08030c16120e120618030903120a080a02070209060105220608011e03051506030708100911040b180705 75
    0x38189034000c0000c00d4565230801001c10f1500400c030040d035400c511008002c0d00894950002209026540050801d241c42030341c0c082829003060300082e00b81c0e000050b400c1070b14074006942c5011458100f0001000b880325a0082c005000c0d00c0c94060007100c40240f010700008000400103914003c01400c5903000800d010781a8a41d0340c4038201503030b842500c241d40300c0c0801e00e01402598645080183c40d40c090300c6240080020f0b07612007015022101c40360140c140c0c140700512031803045903028058026094800010b00d51034862b003001c020b120f135201030000c5030114070410514001d17885040210b036000c4020708000c0c0e640c1c980008a815440c0c071400803c400c480c0600000304106600804960403100d61643d8441da021244503070345081c41040c400100680e024102c2ca11b10303500042d036001d60000004066911150340c841003a405d200060202c04000c0e0b42c1c03460030700d0400c80c911015801c0307058180e0b4100b00017210b41d804104201c581500c2c04030f400c0b040100040342188204c0c21562641d40000c0340c40d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 609608624 1250 609607374 609607391
    0x40306050f04020a0b1c180c0806040b0606040b04051c080313170c0c09070203040e0c0913330b0a030501050f09040b0c0d0207060c0509030c10020705090910 69
    0x1c0c184010240c4089104031a038010020f80300c00b02c1d0b429100c103c10510b111802c0285a06418801402c0618410088400c4020745001040400c82c0460040a024028141c14900f600d080344a8a1000b0f001501c038035000d010034400d85040c40c0684d000c0c3c8809445240c01c81450701d001c0781c90034250140041c540e403400801c02440180da080c00d030400520407132107560b81c1c0b0f400f1742e0908845d00400e0803000e2107621549080340c06103041070105400405030300541e80b515131180c001c03100d43c8408030b0300f01d150b201001a050b00241409180d105100f5080d910030080d0048902954103041e03003003640c0c076205254a850907651074600d602004010f1044001840c4c0d0b40b100440040c1c091f000911905104080c50022420035003020b81c0401d1040d0340c004240c40441d5202004104030303400401e081e2444076400c2c02002d000422601c20144000322036150030381c5030702203034003014582a0342e02c4195001d5400f00000e5031101d81c002403c4000d6403000c0f16198526a9041e0b10180b508940c0c85201c1e40540c14100f6a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 609609874 1250 609608624 609608641
    0x40b0c1203090a030f030b010c0816080307022b0903030e01200c0406140a06110a02030d270803090409081908060a1202100309060f060303021006080f030702011404030605 75
    0x443d5000d03101303403507544032082201003d03000c1f1940c0c3c12005022880c0f240800e40002c2e810402070420342c1d840c28540990560a440d62000ca4004039004405130380035049074404800f164200c1c5054110400000010361a0140010001e103000d10000301030103001540880075a0081e81d84151031141003030300b19001e51503504642d5a610001c10280c4c010b501e007000108070880c07041080d50007810007070401c068180c54040122082d100d094401585802018420700040c0d80912a1480318040c40c1d13101070b101c29082d03000c44200655070240242406400c041041080d0002c000d41e412540200c030005800201401d02c01060700c240c20964100c840c840c1d210080980c2c100c2d00440c010310301174900c48810340e1205011115503a6004001c0c1d0300c40c80b984c01011045200360805040217100300004101440102d40d117805940980c0c000f2030158119520440b201c960503c281c02c0207020050041035003001084025460380b003582d130068100020401010040c0c1840c02c116001164041020011880c2c91240c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 609611124 1250 609609874 609609883
    0x30f06040b0a0606032003190e100501170615061303060c090506070c0519180507030c03140c0f0c1002040305120903060f06040b210706030908040b0c120309 69
    0x241440803d00e000008a0079610034820500b180d03405d032840d034000b900454040f0500ba08010100006041d0240503182840c095000b81c242491603100104a0704000104a00076504142c020703055400050282d4003140300000703030546c0c014000e018070b8000f000421012401c6842a9000b0a03041c1000f58800010003000f40d202c0a14001956030f5080815202c0d81040541e10a007400600180b80000051040340f030150103072a16401c80e200015665079a07858440060080100505c224680e18030400012641600500d04481c0380c1d4034040000883c0c03800c03001c0384a00082d141010030280401d80801d031810041c01c450103819903504613264080c5810107180654846d000444160250840d03140344004440c090307034140c40d4010003400055451607480554001c000303180c03d40c081e445440c0c007403042d240d4640020490469200900c2811140e085040c500034071540304a080516159400001c2102501941c082d42c0d0420f24080d59814090701c814900003a02c02041e03260b11002003030044800c400503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 609612374 1250 609611124 609611131
    0x12070815011a03010e0f0901090c030f110901120609110405011e0605040608070e010e0909010204051801033f09090f06180c090b0a110f0604020f0f030f06040b 70
    0x40102440b00618511854007003803140c422034020750070100d0f440322009a03025600c440c42c0c4000099001c0140c40390f140c500c0e1176070b01c240e13440b0f189001058140b007818008407181c0441603c406000754900a80001421074590001d0300b4180c1d101100810414840030251500300014800e11943d61640710500303071224242203038078404010100021f0441e014109840840b035050304c0d02004d6580c0c0c0c0707001703440894010464504115041510001c650f441c5170125000308404d0300010b0310b460038003060060320300031a0003c50000c40741e58010030002c1d101c02005d880c101d0750710100300400c240c200c0311044420f05102040360902c42d1664080c0060b036212454004540542d0300034014505807401c10fa040300c0c0c1c1405103420445120810039a0392003180c00a19a464207454440701b00d6940341005a041c0c0c008182000002d585d0300c18600103404100b14a005110030200500030904265002800d8040301c6101c1e1402440c4403510602a6070b030900070076100710648030555100b40703400e241c81802d088089 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 609613624 1250 609612374 609612389
    0x1c020c06090d09050f0d0b0103080a0f17011e031a0604050601050c0607080709090e0309030715050a12060e0f090120040e0a020906070f05070608040305091207081501 73
    0x80c001841c1034000050515002079941c40f400c0e0f60341c2c1050103100b02c44164a5105801c0605540d142d000520b0307050025000318081c0c66156111403103400000c201a00c04c418071020801e041035100003802e1240c4009044a5400e9003820380700e2901122840d240825a0004c0c1039203d481413088901c154a880709841200112810009907458400645942c042d122150401d0340c0914009070f01c1034028074295402040c24140444e0b95a546d000f80000e68448142030b150581000c1b54030100381c201080760402500700140c500440c51011600140302e405038044a00030400d203516100c000d000154070480c05031884203032120007841d204018020b002c006541040c650340c600800421543d50011b141c0344ae0b10031921501d4649403600c890204492005445000c425908000d40c26140d6a01c40c01004d0b181e00c10880e0084039249800c0c02c90404116a01040500854174100300010358494100d982e1104225007002c03500840800443c9003800c580c114107410301c1000c0c0000c10821500800078100c9440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 609614874 1250 609613624 609613633
    0xc100c050606061603140c0703261e0a0504090905030a181503020c0c0a080d11010c0504050d0f0c0b0904150614160f0309060807030603030f11031c020c 67
    0x4000601c4080d00c81e460f01c44c0c41d5014604c8042c0700281c410b41d03200100d11255840181041c100c410310508000d91365004594a84250950000d402002c04600f80900c241c400c2490070222905003180404240240c010560080001d40c43c000c5806502660060b190580080221501e64980303590349500003140500810040000911a40c20388412942524000c12040c94403246007030054020350400c0340d58907454000c400020315641c07540d10524005018000003808125245140906170040d5103141046c0d590400c110b10300308035001411201110425940c05021034243e052009801504400041448615600c006aa01314010140401d802e040300d04000c03d00e0490034103078190040e8807034040400c605e0b04a002502e0241d00240c03040d091107040d005d10400d0150f03116017040880c52000c0700885c24090050040c0c540c403608040e400700c05820100703c5681180c40180c10b140040c06c0e0502004480440440030803014030958000082201c09030f0390ba2550082c3c1540030750001004900c2c01d216 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 609616124 1250 609614874 609614881
    0x70506010b0d1b050f13030f050a02100e090c1c0e16060801030203071202131103180a020f0427150c02070e1609180c020d0203091e01020c100c0506 65
    0x30341601c1c03a8810071103841340c80c079024001030381c040c242e0041c08801c440941412000408503028000ca0f0241901c128080d000c845580d00c1040700d000c4003909c1c61001c010b60321107000032030748a950340c454011150700d05107900c89988161030100c10f48000404031340700b4100303080c21042450008002500001d03030304400385680d488101c02c441480303091202a50540c41210100019980d8016080040380064103480e800084581150240c7c1d40c00219002a1900001004107902c0c54056100040e44010007425094030660001181071301c802811038800d55840f540038070480804649210315140740005a81c01d40003504146145c1c040c2070140302e80081c20300c40141c18240c07001c83c406040c0d030b805020f07101c0d1030344070a1400b0f03a5000000030600d06100030a100410b05000b0a4501030031035036208004103c00d03004510090500606000c10425944140001e134016601c840415110502c2c1413440c61201d40e501c1d0040b0305d4150004620354001c00c0614120002650019681550741d009800300ea0a40c2c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 609617374 1250 609616124 609616151
    0x30e1f0903021f090b2101030c050a1208030a0506030120030618011503090203031c090203100e12071a07050d151d150a080114062e05070506010b0d 65
    0x1180f50700540010762001c60901c40c48500c4400340000c1840d040c01e030040c08180b100c80c480300078030a8000303513110540920100701c10704c0e01c3c00c0f0010140800300615035194100355100c038190300010f06003000b00781d09c0d4030020b24107403001d51001c44c110f0305c030203c1c0006240d00d07002c3c185950740c8165405805020304403404040280302110290407600c1c11074194241c5144401c040b0020105d41100305da0500080003071155002c0e07482100b4400103c0e080001540f583d0601c105403800840f00c0c0074127402400c102200c08129008540380d00300c0144040511394036105440c003500d9500c03070120b21070400b0001e038092103c0641e21601400d90560b12107404c00c400c410514511201aa1521810614940058580320207a40058031282c000d1f0f24882d41d400349000080000c0c44d09591504109460f80d52031445410104151102980000f0151011030100c1c0841e81c41461428030050b240890044292108142034800c104880d042d1303400a00303070b03101545c55047c01405070f4400c0070b41c44845421b0196546405 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 609618624 1250 609617374 609617419
    0x90b090c090c0a030e030a03050105120a05031b03090303030f190603080a1119051006140f0d021302070302010902271f0515070209180a030e1f090302 66
    0x41002801c160442d03031101100c001c590b202c0c1d100c507400c040c0c46090900f0418000c00140c0b03001941c0d52000300c1c842d8101002e002ea8110b60b00c400b1801540210302d00740c0443c03800310480700010307180182c00f205161a841c40c10703c1c62040b441003d415220010402c509000503001c0c0f2400340b00f481c240e407220302c1d0504150b9070a4407081c0c0005804d94404000040c1c0050007001e59a08001c1d054050b45c21681511a0f082c2e600c144a503000d48607a007040c051422502343c1c52040d10003400c3c0c00c044c0d0003222014280414404406814002e004210b0600300c4c009540e0b03002d0301071303002c078901c11070a550f150010714000703001e400003071003c038014001510443d0804400c40041415212103407142a102c1c0c1c1c55603401c074038004c148680011903410003000031503981c4420b800e01d286c800d204146150750f0000d5105001304020014400c1550001300142440e5100c0e0200791441c54941601d071000802d5664030004940d115081107002c2c40008000a800c44190003c3d030100031240200d580f0282100c2c4a0180d0165 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 609619874 1250 609618624 609618643
    0x10207060e061909150c021c030618020a020109050706230a021f0b1201050f0a02031003080d0b04061d0606090303070b040f1211010e160522060603090b09 68
    0x1070818210004003d06880e4800442c1c1c6004085441c0074841202d862070844800c40d10500042c0c0080c2804030458403a604ca00b600d0b006145002c102c2545440d0500324101014496040748540010303084031100d10035000186116046401e8800d20f44d900e00001d8074040d0580c004070f400a0050b80c1000d00e01c1c0703038072003030354100a00341d0098107104e02c0080803d180d6480c4588614039503a81d410909e078040d264a8007103d061002100000f44030305041c014082001402011403036250b004104103d0500f40011001341202d0f40141e02d180c484450101000140c24000e0f920380d08513146c02030004242d48007001c18088003051034181c0c0c0d0140c80342030901400c2c3c444e00c04101d0f05984100002070000d100b080246601601445031240c13125000c4d0f41e80c000c03010a02c460031001450a8a0001c001c003030a1280300000b4a0000007008890510140d0a00d51240351107500d115002110b0007003d0360b81d0b1803111581c1c60619110030400c0a4440e500540104420381d420388404004600081e40741f01c0020b0080c03803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 609621124 1250 609619874 609619891
    0x70602032502030717150f01060c02061309051315060f050f0a0b070506011d070f0503061309140c0904211206080114070206040317070905030708010207060e06 70
    0x607400d8000c110403400015050040740c044c4a2001c0c0010b41800d5101c01c000c1c2400c551018020b003400d4012890000d84010b42041c4a80c03046600401103e03412010000000354182e03511916029041c11180b21a003441e8400d5462a0403d410020031101c032415040c4a03034031403c2c007400c01944810840c42151882c0c052054285008107042c081498445081054214014054100d1546a80c002c40240d08251030407103640e0b0004006202c4559610200080c1080800e0315104900d000314008000400c02c2f00d4607020301c140017000c100551509400c102d113441ca410b209020881262900450043c0d07d002c0301c1c0941e0103003071144e50307241c41d007104610700aa40200515111010441080d0803120318a645513082c03144148090000d01440e0044200819400c4000103503100c050382d00c91260b8000400c2d0700e0454001134100400280c00604141d0403121528820100f90f44039902603880101b01d40203180e040c0306030b03640003030310603015002080103600c103140c00d100d0380c18000460340d034a24007500e0038903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 609622374 1250 609621124 609621157
    0x19050901051003060e19260a1d010c050a15060503011112062805010e0108041a150a030c0f0b090d1e1205030f10060e061303080c0f07060203 62
    0x7010030a10307086280c1c6200c0301400c0e2401003039040b5120f5940e8101c0030044500716180e45243d115030202c880080c2c1502034103003540b8238000d1032260060403400c0407490392491804084030940302d640f1501042d0442640709080366008655414001c9582d541c12092403012420000301042c07a0406000f080038018410141c541403480b107401056041e040200016042034900c01d100115001009041c805180310700d141c40045400c0a000418400400180c24180203d8402b8440000e020104e14100340000b6200070b4800d803580506101190300780c0820f0b0354060064400401417012641c401421107070f09000c0420b07925a698100c4169024030541d09030b114a07000203420100c5c41d2000c51000c0040d02e1414081c81801940c1d400d113808815130f240d000000c20120412002c12000300c0282d070070103420807509040500e0640700400142107414418060140850f0038001c4541d669911707006168804944c5490b0320030901c849944401d08421014244210140050401c1c00030046452080300c552450 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 609623624 1250 609622374 609622379
    0xf1c0e0d0804060f0501180b030307020a0b070303110d020408070e0405120a0905030712031826030c010e0c190305030906220b031512030304020114040e190509010510 73
    0x41d60000340003041070356055110318641d00040400d105082c080c0400414034004455188a028222000c03440014040c0c0c0c42000100c015940d8148044103c2ea076451410b940c5410b58a0114041c201d112098922541d0205400d46050300640142090340c07100f10440c1d80d0b15a490104020381442030303401804da50047c0c94600003000104000b4820f2815604041101d00d50b213402291801e003d030fa00054180b2000d031004420150300c2410749030304e9181c0c00c1285d031a5a00302007000600b500ca1008047c07080718454044046804140243c034010f000b01002001030100a07005030b910b0700d01600103180304201080e9090400c40e903031408c62003526008002981041c0144051000c4d89d4014444070300c4065034911382410411110b8044809025981c0300c0396242d04100c048040c050a0f860707002031040d02c0000100d00380d08400019243e05c2502444c09030030b42001024810031910490700808465009501000b0301000d00660400d00042c0742c2d28200080ea031440340c1117089030f400381d80d001040031018204 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 609624874 1250 609623624 609623627
    0x210c041d041505071e08040309050d2a05130506091b0403030e0f0607060606020d0207050f1311030f010617060d0f03020106080708060109060f0509010918080f1c0e0d 73
    0xc20b0b4458100d00b07080c61004007218400c4c0c400c01c5034103001c1000481d110104008c056015007500c004050a4405911a04555a9401140000680314055418027400d800520a240b14980004010160030b40312151020008100902400c4071002d00403421100446d020314104010b82c3c1d10402d910114a04040c25903070115900a45840f46035444103c0c964403410650f101401450300320301c1100c0000d400742c075203800a810f000e60020355900b55002110b041005450388800520300a004441b808071800d030703211840008104000f02221103500c00310801c402c004444682c58140c0c0d840e40c030341078180310181d0b20745811140102c1d0020f410600a505280004410302d142c0850540300340004101d80780c503201d485183c12201d501c14445940503200410004036688203510280654000045209040c4000f0821012061080c0307032800e0307559007150461000800d034194070360f82d0014210347c3c2c40748502c0541000c0d03004010305001c0151610401071201c0f0180c403800c0700d0480e450b0060101c80001c0d280 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 609626124 1250 609624874 609624881
    0x3091203031b0302030609280e030c0a080c12130902030928030809030a0f0c1103100203040308060307290c0a03050c06151302210c041d0415 62
    0x40341415102c403540b240308180000d0b1090703407100d0340d03600580720703c2d02c1d90400c81d054402500541809144145903800b1000e4041e4540d5408009040800c00d2030002d07040301c0c694424480894440d002c0c02e8900342c10441500d0017001f51000c80022105013801441052100d4461111280740c1803a40ca0410424144190081e551081c001401d0f500c1d040c55001c0e2070300381d009110308000c604901c00801e0504140c0c009007800d40110783c0b10015402d210203407001900813107400e0316038400e11035850303000410802000e91100050601a054a480001d5415800041c1d0015039044011400780c80c00124103080000c2c00c0300498411043e007001c002440e0001c0040148a4811802c8080c400c01841192803820820307000c0c0c00d0711940e103041c0e580740700f030340880c0c2800e00c05808042452501003000c1d4040ea560640001d400705070810059888041c1e80f10010a14040007540464288010811000030401c0002e80100c911034000e014500c3e04504044840240c00c681c000c00348850040c1016550b00360340d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 609627374 1250 609626124 609626159
    0x109020c03040311031912270509090a0f0b06010f0f020604060b01050403083f1b041e050a0602120d0209040b130504021f021c02031b01020409060f030309 68
    0xc0c1a0b40c80d00c0400c0710204002441c0c0752040e1401c10003034400140c01f50b4061004d000080c0480b0721110310302c6144031a0102201c1c1841014452503410010620450301132000c1a052a404800803403c0c04c03061500c1005078504803106030100e43c0036201540c2240c0108071000ca03504055001e454907079550760b140002004443c282d0b0f41001020701020001030b40000050001702c8000002450f5800c1c0c944801c4003001c101c140c2e044013441040741c481c8040b025012066040b121045c10004443ca4000c49038039140200c0d849022400d00c282c0003804c1c02c113010b40f45481520700543e1354400c025211030040e42e45200c40140c100c4107020400c02070440e51040d50241030303480700007040031070208052000900b101c0d5a807015900c0840d528002c0c041140351524048003980a80348442510100a00300070351141c0e801c2d8070920307000c0002c80101c01c100d8403e00884c0c001d86a1990740907156a20580018000c0d042750150b4980e12340b42c10408103c4081e0300c500381013100c2d41030782c42e882058189802c01400c00c0040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 609628624 1250 609627374 609627379
    0x1104060f0f110f030304110f0d08090103020f0a0f0e0901081510030212030307181208090d021e0102210f0c10050a0902190503062e1d0109020c03040311 67
    0x440e400041c075035040c40f505201100b040300842c0c4034105030411460022100400c140b0504403849880d040340c44034028030075030a401c03038013481e1100c0300540141c019100b54003000c80b50102c0016440d00044d08013403030780e1158426a5402c8806d2100d0f4051051514003800740315807580c4591021011012940000c9a000a501900741d40701c580c1d90340483c45000d0090b1007039078540c101104000c0080c0e8818a0b40b0301401800c0c1c10029090f19011441c1031304150741e423020b4500351001a1420150303c58614006c18160b000d80710303400c0c401040a5004481c010400094014014826040155041407220300c007120f1b01164038514104a40d00550321070382c4141c0b180e6850340502400c0d118803e000d80309640c0307e8040704a020a022440d40b04000090003448122030b104412210140a60b480c00102c15a000301d410f01c242465514200b00910b180e88034940410b0505076003c0c003c0740310022110b01d8100c11129580080d02a601c50f0307030000507405049007000d41a48280010008900d80110440416401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 609629874 1250 609628624 609628637
    0x10305061f020703080c0f120f03010504090614090c010e0102060130120306051807020607080c0405060d15061b06021b163803070516050a0302011104060f0f 69
    0x1617946020603500b0404038491381e5005801c5a8108820a100404000c8480200d031072600001a440d0101070006004ac03e011369980c49a01080000070752040d64a118030340c044c44d02c039150828034265180c03600c1c04200c3c005529545640362079400003908034141d07130180141c40c5d03481c94500d00c0d03516014101c490605074078000151500c08078101c092032813401240b55501050050030481031000c11060440ca000c141c2d00d14104102d01140e005c90001c6e0405c40d640750149c80c0384c5940c803480b01c441c091508401d40c001400a2010b9041c00190310110b1504501e00600d130748160395800c2078520b2104500001105121800503000191140c0c2c000c0143c60028210890303148210040b040c03500d1715800c00ca90080e0750507042484441041c401510810700fa100d1000300360a40b00c4d500c0503400500a042284d11400400400d00f05802502520b03000d80702c10703024100000b81400c0ca2a640c5180e04c00543c0036500c0c08100300c210030310304400c490071381d076030368541040c40c0f03942c0c3c20100c80140c28602c8002c1007002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 609631124 1250 609629874 609629879
    0x204020309281208090303160e0a060203040f09020405030a11030115120b091207200d080403170316120917040f090608151005090f0403030b010305061f0207 69
    0x4030800e0b940b040d5a810300c41001c402d54614201490b0741c22280d80c1c9091041c1d031003c0140314400041100c2d0b100102606e11640424241820380341e4a0b09000321643c080302c50b46011500e954004060002c5a120b1928031459940c0c0d200c103201240b00300c0c040e031505500020f034141c0204807010891007150401600000302211a040001900207c0b600462081031180e2811410f00c8070302190640c00c441c0880150501c03401c5101c800105204a86005019a0208610398041045000f1104e0520320240000100d01210300d400e0b00e0f1075115004c1100e40d0700500000702441038120040d28880c60410202040302600102c0c1a1011030740003050905aa031100740034000140c5050b0803d00000701010020780f1241480081c072003209040d040000d24500d03010040011a0300000c4407104040c61000350b80389a1a0040b03000011041c1d40c029070340000c0000103126061050a48541c4038030b02a03038040007080503c00046060742d8081d03446a600c10706841085901903800a200007645180d801126000b03036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 609632374 1250 609631124 609631153
    0x14181f020c06160e3f0c01080f01060e03010e03030c07140303010e010909111005030601020f0f0606211f050a09020d15140c130807030f0b0c0c03120627040204020309 73
    0x14141907049190711700b0303612048558101000b030740085c1807090915082a19242001010388241445104200302180c10182c845890a61001e840126445c1c19681d4910f000d4022100940c4039480455200c00395000301c100846010050302e040e100c0401c42c01310542d103001e0090000d484200b009503000c21501302124003550704c0c03d401403856089912510f8a91810400282c101070f85098051100d4004088001701c80708003041003548030b5030880c2c826101c40c10b0155040d0f110341d03803a400c1840c0e03441071480905030060f00144440e0100a1680d040c031055554850a100b0390f019004025004159441403200152605e032405a4041480100103070010420310350400c03903076094402000700320340003806000183e03c1182c0e40014100034402000642e28541d40c25100c40420301015007002107a20105454020f5081228002090751084a40710758005000b40c00140080da4080d10580781e42c00100c000295080700c81c1614103680c0c00c4050b48c0d5596400380000703984010034105050040e0720744010300c00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 609633624 1250 609632374 609632449
    0x60d0503120a0e1c030b060a020304031203090506010b12150919021c020304020909010605031507021c030e07090c0c080c03041d09010e0114181f020c06160e 69
    0x11110b000500b041824100320207012240014629400340d0340070131023013040d01d80020403942202c3c2e004205d4030303085030a000d00710010440c00d00010100c1c09032500000d0b02c2c118070009405c010305840c0600c0310980340e08a0001040d080565041e07080309041001901c00d481001054103401880b040261800c0c1111001c0020040c40c2d1520802142d0b0201c140025418004989980820f8050017003041c030b41007070002030340c4241c42c80d0703810120320305400042c0c100c0d8401d02408111244141104007000b01d00b15000e005001c814841d0300c8180300d01240020010168014040100119280d0b40c10100454079110030590140250300c100e80300402001500010100225500100c400c0350300b181800c02c0b800c1e2278251020030740b4000d403d0b0b04000030602249a02446160042280b0412410728100c6402c8241400d480c190803500718a0414009080c009041e0020500e41e000b0400740d40c400d40e21086441201609442c000340003900080c0e54210900700b011114030306902c005202120828402e1001c4001d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 609634874 1250 609633624 609633643
    0x4030f09091503030e041401050d06021e07020310050601090b1806040603020c120301050105090609040f0f0b24030f0718140f010509101b02120a0b060d0503120a0e 72
    0xc2e0400c2c01c2003013032540c80511543c0194017181d0a1014413011402c006919406004507071044041c514900200f1000e94100d079214a90041403481c0c40000144000c1c0c20b0f0003442e03040c5e01a0240f500c440d0031b43c240320b12407144141e0050716903586081c01c0074511005a004071803d002000c1d030022103610540c0e01c00001c0d000506060707a0150b034030f5140001d998180043c4201d00301004400b44014003041c0cac0c000081d02e4000da0141c4e01687c864090784001406442144a94030b49240781280101d4140465001011080001d0301d03880307420000c4a401c1402148040200c103580c2d0814030204e2108002a000305801a003240341200d413000c00e114003940f01404940c4107081ca118203850104c0380303041082c0c8441805009080503401d04a1080111b101d010b500301a00c01000784541c13040102101544035000003503009403481c41852180b00181c0c0c0d0b1190032044c155209407842000403071520b41005001c1840e5409400345003400c02409890b544403a010f08400d040c56200d45240000503400c00c00070b080b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 609636124 1250 609634874 609634901
    0x2040509040b0412020610030f060b1011120a0e1309080c01050a14041112122a0a081b100f0b09090313030b0415061d060609010804030f0909 62
    0x10141000e284c2001000c02000c2c0745030641d044042000070254070301c1c00c080c085a40000c0c0c1117414269a1505100038151551440c0d0701c508504100424240e0080d240300d81004508101c07107000340b41c0000c0ca031543c0900300a803800a0880000d0310b9041c101006a03030300080b01010003248075010b5548404168100708005041695604104842c4405900500703020526078120308099040544690781c080d140300301014007039003c11402c0304c0800420410f01c0910082c2018280d100e004403041d0040400d00800e044550a02a81c0c41d4140d0410104800d10040d80c00961186041d04030750152138485c0448103005014007466901d4800d5605070300034008802c80642c40001c2000c050000c02018030800b5101e5400c80d07000b84450a141004680c807401a82c2d007022800c00e081d070300e40ca4440d8817040c0500b4a110820b080c000002560007081d100310f00e0a40e080d0540101d6039844006100182c00b9a000d9940041d40d80b00c00718001c24021086070b000700d0440e1509629a0303882d030b4664016140383c08480e01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 609637374 1250 609636124 609636143
    0x28060606050a031506051207020705030304120c050f0d021002010b060a080a051e071d060a03152103080a090f0507051002011e0c110604050703061d070e0a0204050904 73
    0x2c0c650340c1032241207102d03030b0406004240b45080c044024a1070180c240060070750021007021848460007001800c00071b00b001421250340d691519545c8000100800040300c21800741000410546450940300c804858040d080d645011016002c0040440100c1c00d0041036540e2588000e0039030315100f009000d100303070548a4040310f040611400088603c000c0c0205000d00c0c080503102400c031600785070340c0d0f00882c0364035110a00e100001c1c40c906106400000140d030052000900b031000c03d8040d045000d48140c0d4040034240243d4550310744c9004580307607041000c0040d4030004600002c2c0101841600074260a100240c036080710f41d80d0303c61034400c004007a91590301a40081002e8a03101d16006024549840280700c4648400c0c00f84c1040102c8056050741680c0303038441411954801d00c3e4082d13075110360390300311001400c090400391344590031404107490840c102103001040110302c0c0807400000141c440203000ba01e2400e01445900d01015040058094003040006400d80e28101c2503805a4014104c05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 609638624 1250 609637374 609637387
    0x12060501171b01030c110609061f0b1204030c0f0609060507050a08150d02030616020d17071d040606170603060601090b0f0d0f09061d2806060605 64
    0x21060050910604010341e80160000ca0b403100b00080011030002c0300782404116105061415280942e03040d140501a00c1313468104039605100284050040304402806840301d101c1080f01003900001e03008082002404010f24503c0030b11440e10075034071901a18001203d0720b00c0b43d907141180003410300207648a54440307105e082401300510400da0041c4c2203081a034584203184502403d0b0000041c2086014121a0f006400c01d884132501c5001c65a13004055812500c1d05c03481e0862703041d4040c000e0400510070004651495405892aa080128100300240c2c503980d50b000c040f14812180481560740190303084184c00c0640380c1d400307a203010b03060f50389a12400140c40d810790007101d040101190720070b5002c0403e101c0346980160034113091701e80c100c8005c0c0e0b0300d030180808005644114800d100a480c64000300d0701201086600c90b28501d44101c00a204c049141c6500001a4520006081c80354010b80a80300202c0107400304408a80c1072a8080602071185844a2003100c20562110012a00000e038a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 609639874 1250 609638624 609638639
    0x103051006090203190e0f030f0301060e012102090a1a0702010201180b06060703210e0c030109030e2e170117030412140106181116020d02060412060501 67
    0x540002c1c0c01c2e001c8007107045180507034020307000490004010500343d40e0380700d0f1800784107400d1000008960b802e00459030707201810000700c69154400d10034000010f071900d5402c00f00c1c0d07106a00201d0b0002c440c0c0a00450185483c601400030f42c02804c4003503101080c1e200015212114414414099a0000400303885407210300019096490f894900c0711050608500340f000100d90961f5141c02040a80d0082d440343c0c1c0c146425500a80c0040a2445841081004c0da00085041d000342c00490382100950341100f10314030500d801c0e00c581c00002030104100c5140181903060071b0020941c000079146030070f040821000080403904402d1550040021150402d1017040101c0e908028010720f11005c4101311280300051361620b9000394000d40250280c0c3e418100e00303101b02027080b0710f48610001c00821030103688090700d04420a10881180c501410000c02c1ea80f6032886006460715814000a107002050080d420805007000d0714400b20b85c860010310000c02c0e400c4d003040700100c1c010700c81c83c80010300e0b50400e1340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 609641124 1250 609639874 609639881
    0x21018050f1006080a260d06080d2a120c02040e0c091303020303040f0311030c100b0d260705060a0605130504020d0201080c0c0d02101409030a05030408040b0301030510 74
    0x800b4965034014001000000c452180703041880701504c007032178100c6d42201e107200b855103c0c910300c85060718107007040801d030321354080f03010806060b880e2102c00107480350001e4074940241c0410144010741e0200c0c04031000c0351403019441015030441c5401c40e151011075000904982c000c2405017125801803032230318030f641044120300303410812101a42c18074501c9607030000c0d41c921000340000e0402d15031b0030f11101050b01032710481984030140010f494486e084d5801d043e640e801000c0c1c180b01709504101a4280d981032018058411a803c240780c2c00e0b04401a446000034200c40f01c00c400440042001010301040d0140710240c0980503100700072840b00c1c43d00f41080618141e142904003418039004c18000180e5a41c24288a05582804c110002e0340c6c44019030700c0c040c003442c0d0885400b0b018440007401c8130b0307074003040c4182041d000714401c202c15070200241600858046401c2c031480e41c003c1003903024840c01200590340c0a0b1041d4a414582521240c20000942003070b03200b200c1e69071011508540e2031540e0f01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 609642374 1250 609641124 609641129
    0x4050c03010503031e0904060e0f06060c0309010503191d0601060807090501110c10051e12010302060706020d09030909050a0c0527030d0c15020703021018050f1006 72
    0x5590504550600c00025124811800c08806040c804076009844002e07020a442007540d000300204103595694103a540640c1081703c0c0c021481000c8800500d451512006079200c2074030034001581004140e100545081d84043d061040d140c503050091401d0120900a0074a2007211092818060a0344c41506280030382c1a0000e00912501d4070801c1500b50b0305c0805035048501c00d180c0004040032540400b41403010802d03005422080d021440e410b96078000004000501c030301400c04100e400c0d45000729159014502d009031201c0348280042015283c40300141c11b803980074800c0146001121240320003252100c40f401ca02080b4031403810441e1441600c1a15400140f42000344a0542c2e4400000c2252048070441c0b03140351903115244031074584070f244d0a0707158100901190707440e45280001400540201500f122256401680f819000c3c42500980f031003564542c0041c80481030200c031a00c083c03c0800924880c07543c000d0003103404a042084000d00700b1104001401280f203a003c1010151445034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 609643624 1250 609642374 609642391
    0xb0111031602012106062a121701030c05031e0606040207031e1d09070207150212030a0f0b0102030406020d050f0706050708040c08120714070b040f05010f0f0c060911130b0405 77
    0xd410487d040d2400d030701c420785199400700ba200c600c11a08901500d0b14a011600c4030880200d06002204000030107a00074140c9208908640180780001c0c06000c1c2c010500d40c0c09001c98100401241580c20540c02170710040b44030381082e40303034480d2410b0090b5100250aa0b080c001489600030304c0b030000c440b08079040044005480200309481e020301e0280d904c07440c610401d07030b02c060200240340c181d85c0b080c40350320010451324222070380d0f0703003032055541014103051691a42890315141c8500051341c00003048404587d003a401900c01c10580100985043d040301c003001d40e202c101086520000b070054441c61f84075841c1601c520183d4101410424540b0000d40c000728580d910072003440e03c0e03601c0c4030f5003610040d56101c60109144000400d91a003001c001da0700c280c1d101c0001041c0442d5411142d51b00100b40c0d0020b90300c0012210811108448901204040c080812100050440031961580100340304a005424202c4003070002d03008180c48001c2400b8a401c180e0b40c510071f0b0001403415002d81504517045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 609644874 1250 609643624 609643667
    0x50108060d0209041104090609021507170708090a08150a0606020312100302031c0314070906031a0303130311030f0316031b0b0a0b011103160201210606 67
    0x480480e1403503040c0c02001c0d03c03910b0003400007030400c401a0383c4d034030f40034502500c1072189120901e0284040c18569200328070419000c4000d52014051906803400ca9810101d003051141c051400d42003117500a507405e0f6100c100401003080d9640b40d8100c41001880c01074014803030700148100d01654440042d041e5410716062404c200000c550002c181da500303210382801c00701d16031140042d10200031400e500082d01130155400044110341c03410034503007540850361404d000314100210100d070343c2c01382294048003180d040003040c8034241c442c1c1d21030003600c2c0803c146087d0203c45000080e240d87c00c401ea002d1144060074005104212118203c00402c030b00a80050a50400322003a141e200d020304454002039002542c01c64082c544208200a0320039a480c8100070a40c031781e030500407002d9000311455003950b0709118814240794400d0b08200140c407001c4018500f440e800800c901c0000c1a01c1c1401d07410000c031016202c00c03034801c2c2d03e40c811000410303140002d081c43c50300c9805066141c0d0b14103280c04047ca03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 609646124 1250 609644874 609644881
    0x9060d03020606151201030303051902251505010801060f0f0312030b06071502071e05210d060b1e040f0b0307050705100c11070807150306170105040c050108 69
    0x80000b400c60f00548201e4411811541e4200c0d900301901842c10a8601200c00000000902d50035501c500d01482c1080010290700144030814001d0344541000c1c113250040804c844900e00342c40070000114244140b2481d42d0140c07807540c180c800e450080c1c04c00c0c002179654120030010f086000c61031742d0042980c0c0009046951440d01c456121a0001c4940c4041c9034503000d15000a0352038104407011507074071228000c4450030006d0f40000a4010403c11203064203c105070b07100861221034586001503200e8000c01e4800030602034203882c601030032600010070406211034091a0040d0048001901140d645180c43e04608543d596180704100000c0989010402c4240100300840100c00203032200c10f40307400e81e242c503a028101c0759441803080c0036206008440011880303c1c040c0d08580e024901c00e0784c51911034400c0240703440d2181d4103131140c94140d07032018404200004400d2105441010182800501c141d6100180071a050100402c00074136596030040200308001e8500c0c65018002c00e2908802928 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 609647374 1250 609646124 609646127
    0x60803040905091603030203130b0922020427110309030304080708040b0403060e0601080c130f2a020607020d0c02041a12030c1209091305121809060d03 67
    0x1040d401001030554441e00000c0080200300155406282150703403502c0050f82d2410001e4480e0048200110a00300040d03000561440c0602079178015100141104502035080c2c00e0300a5102000b40c90686a07502030100143c440c4001e013211103641e180e040d2044044e45d08441200440c0c00b003030107411b045030040c41400000a80041582d40c8030b0361103580c0030b503260002d0500355000c0c015903000a0043d04000b80100400c1415007000150040c024200c601c1c5980747c0c107000c1d403101d900c001c50a4100409040c07510003110550840e6100d600b00e4080014080d00c1046245035414444000000580c80703d0003c0030780650412200794090000c0c8040c01c1502420700d4010500040150041d214503154a85400010a980c50b044402180142003805005160b229581c89402031074040b407060041030966400c01d00e03030708100d807494580140f10001c2e0b07584548a564032540380799016191446464200d0524503100401405080302c1413045107900c5403030700c1c2000480e4070000d0049000d01411103000e400203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 609648624 1250 609647374 609647377
    0x1031101080702010e060a0902120c0102250506043b0c03040302011b1101060b18040903120203040809040b0f100e040e03161719030c1214010602060a060803 69
    0x125001d1a0052554030380b140101c0c05000864080d0140340540c0087c00801403a40d032000c1032552003600d01e403e112540a8496454a000351032042c0035820121900680c00c481c0b81076410f140382d1014003c05166221004111030b0b030030682007807141e840321094850031401120681d4814110105140c101441c034161001500c2c00d01900000c0755110100105081600079004502d01e0520f141070416109880d50005051401d025203000843d4602000400c14000c180100c40101e450203020300c062648500a000c01010035500c10390811400d80c98460014000b4001140502e02800c491034840c5410002c0200f210804094240b040005064400042d2240242c001060420341849402da0300c121001c14007910007007234100568080018604960240c14070002100340c007405151441d6081e02d407a1503100d01c0b444403180c4080e000040c40e00301c1c5500ca40c00010f00200c036031500b13141c0c9000e00303c80071095460000c5200d480001d16001402074603410003003280d1040b0340c803405000241c075000e611500d0303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 609649874 1250 609648624 609648653
    0x8070303020702010c140703140102271c0f0b0c03070c110301180f0b0606090d12031d0c011101051311180f010e070905280e01060906080f0103 63
    0x1031540214800707095a002d08040b50701c4540000003a02d80d10404422151901154002206c402e01c600e01e0386c45d003c030814402d031a032100300c050b0840000300410203000c02034001070b070031030b03501541c41c10f600399000c2008000031055901c19405100c3d015000e00e480350b0b260700000c00082c100341c0d0610420500e40c2e403040302c0c804e55542001e815824030380c0c1c66002c2070140a038807940d082c9044c511003580c000c10082480c2d9040300e03030007216040c48a0f1160310801c01244901c40c2d810b64410030500080001c2141081c031104070301000d003000a1400305500480b00c031049501d462210302d811040b044511541c00403c0e8200d01daa418008000d40c4c0b41500042c500000940c90181c07240036100c004115640f98440701c02a08400c80501c04054a094108412922001d00661445541a03004115140d0007880d00748203860009090108450309181e66038004002e42c0b02c110b405000030680007450b81d500204071400380c40075545130b038a11414072101402140380607004400c40580b410040021401ca220040340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 609651124 1250 609649874 609649877
    0xc0c0f090a09060e0d050c0606090f0f10080601230a050a300c0f060e01020304030305181806010318020d0609170d090309082a060d0f050a0e0307080703 67
    0x9031020300f402d0107001031181d0f5038000e1545c440c05461030041504100581f00006c1c0682c00c0310130036a690340612984078030560380c45091400074004610401c003940d100e1ba17070015160030503501c0c4a80e924a042e181c40700c00e074018034800900319000c442d010851100030301009801c0d100c481d200b501d4440491b241c080382c0e00c22104c03100707440704c00390b0070540c4004401000c1c04200c0200e07070b8084030941420100c4002c01e00c910b04080b80c0e25030340014914094030408010f2607058028609252560302c3c04c3d00c1540c0041054918503150008115165a0328080c80218880048041d01c00740780800014040329100c03020100d03401100200c03100165074640c0c81c0741a03e03500c00c101085d101c00b185010340c2d901c031210045007041c400103d8115001c12407544200c003003038000d03650441541c0d0380d8001c00380ca5005086c5c1109032800007400c81212000105803003002e1000c05803400e40f602039407803003940848030221418040c881d01c0c1d000780880300d06540075051074181c0c1d90b0091440e04c4c41c00e694807411442030060040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 609652374 1250 609651124 609651131
    0xe01050f0403050a0605061c05061f05120a0605010b0c10020d200304060f05272d0606060c031c180b0a0c030501140d020310110c0c0f090a 61
    0x480480c0420981d00195807050484411046520b0b01c04d020703105c101d42e50742c0140340c2c1da0101180d684131481c01d0104960020083c04054032507401c95050f00103c4000119001101c0b4400186500e918002e03510300001d20000d0400680c840ca402003d652069000031070346a03082c000d818016001007044540190110b100590340c0110546840140035013000d115040303a0000c404c0c400d04545600218480c2c0d114179007c1084040c1c00481038101c8e601030382c480450400140c5c07000015040180d5817000014007501704e0303615407184a41c84050f00400800848200f002411042c0c07a602e003040101d4008070100c46041c10b110407459915034a000e102c810a82419040050040700801540910105038945000446402d028200b52150800a486030ba0f11310345008580d07d00d00b40301c1d1040b02d05035046488801c000450384020405001070410702a641030060700c15000621110348205946402803c6030140c43c0d044804005040c00074a109250240413410b05110785592440300c002d80c401d0700c582d03001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 609653624 1250 609652374 609652387
    0xf0607020c210f0d08010806010e1303020a14150606070302060408031503070e04021c0209150f190611010903050307050c192d0809010e010507050a080306100e010e0105 74
    0x15480b82c00a0b0800c0d402e010300c210f01080380744040750001601c2c8050701e5104c10340e6607a404091380d07003400740b14074170420764031401007011880d0413003000100ca4024070468024040d50344031003101060040740c00c40341c0da00403002a480c0721400c14205501c5401114007030309009080c1c601130344900c4010801003040d88004001041069000c8140341d07102d83c060104d600d480d44a040c5014800c40175a0203038441c219500d01c1d9003c1111031180c4940b00c9901600c00d00d602e4031540e05c81d8a4881e5441d070401c0c0c4c05691061800c5840d1030303402c54006030100100c11243c0203440c0000140109040c0d072210015070341080e12840220741c0000849400c913007070303182c8207960300d000d0040d1508000d004da880040c050a00d040c84010301c0303104107980140c6110142a03280444200007900c4d200381c00c84000900c402c006000200c440c1d03000b507003030002030b95043c14814544802a952181081d010300000c030703a01000801405020b0a09480b101441702c0b040c1480c4001c0b800c0c0400103800b8243c860180e6040010000d00d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 609654874 1250 609653624 609653659
    0x124050f0103020c060a0b0a0824010801020313060c1b081b060f041106040801020c0d0f0315030b041416081c021b1306060c020f0306011a03060301060f06110f0607020c 74
    0x1d4002d014034416103141c2805401032031440b01381008ad03804c0c5010b01000124400c1c50602c21280547c94000007400310700d500c0c1d550640500181d45a0209205031001000c00d5040b24940d00c9031094814400385945418131042000c559800709188041503101e80d00b0400006e5140000c01d07001a0001d41494501d90218005407091040f50020714095002280c403202e020320020b60700062040b10740350707180113003815442103040781d030b03000031141029603100170070800b14414081c81ca801c24001c1c2001ca044510410f2810314000e0300d0483c0d0030f90320040d01c0c010080c0b284140400c3e00002400f4107204104d60580100035034030f0180800300f200c890401c482c85121507940e030011940070300c001d4000340200da0b81d80c040581340c602e0107074040e4065907030040707280d01c01c3c98085071950583c2c0c0f901d540140394407000c03299040c3c6500000c048503010b44d40c072603010070f89580d980e51200040c0740c182e448481800405039885d00704041c5800402c515488001030000e5580c0208615401038000e40f000112200003042c2e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 609656124 1250 609654874 609654889
    0x1704020d020409030201050a0b090c0703120e01140108100501050a0512010e06090d080a02040303050f0706020d1401060e040504020109231f020f0c01020a02040b01020124050f0103020c060a0b 84
    0x350b20500d440c2d000d404040d0190850307881b5041e00b0304108007180c02e16003444440882210b990900c200c040041d072001134060000400141c04d030a400080001d44584080e0860711040384400118040f880100701c1054100a034002d24194107206202d02e5141402240008480f8012075209842c018204041d001003544040090008a811a21203043c00b2500f25140c001410301280055004000034180c400035000700d508907030380740c2e45080c602454602520416000100100d900719000c010f120300180c158000e0b107420350a00b0510111552421001401d005d6001a0303040c01a8100b0041001507a04000c002c2d0031600c02840e00c40188120030509074400ca007043c80141c0c044210f00038500c5040c4c040e800c03804488126000c031940d6540388000c1e695280c2020300010700680c01448807200504254015900228042c000460700c0e240070129520b15a20190030080000d520b02801c1259284c800d9007203001010030300b0300b14030302103107050100c0d2207140c001c220700320403925401004020b031103445 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 609657374 1250 609656124 609656149
    0x15110d030b01091710050a06060e0d0c03140a0c03050102031503011e0b0409060e030403060c020a1707081903050901270b040203070509010909060605040b01020c090919060b090703090201170402 85
    0x200c100402e01c1d20800c1e1f00010641030045900240354924590040e090185002111030f8015051006180c50b60b6202a80541700a26804017400340405040c0081c4800071182c001c1d5114034005a2a480d158160b0040c141081462511985c10030307210205440010001407600384c40c10602041c400b4005000c05c028040c0002c00610081c90f04076840d2001602001820949204003024800e03030317042d14012641e07601c0c00385020307040c00b04010380310740d86400940c0200b010038400d05681d42441282581030115001240312140402d44070b01c100301c1c03503c0007031040380c9440b0554041094400040c4041c64106440124003e12400641003c10f0540d541000003100501000340840d04941e16100c2a0b030140c09940e5003141d103c1c0c00d1030301c0414545468003e2140d0320300c06900915451200c0405c0142000b00038101c03c105000341051300e00e8003a0340201045982e8011140810070340851828800d00d002c00829503820580707440d0290005070391181c0600c510403006180d2600071b0700d403400021001e20520 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 609658624 1250 609657374 609657403
    0x414070b070506060a050405090d030207300207091109090606040509130b0603031c15091803021002040b042d090506031014190615110d030b010917 65
    0x81641002c10800044451181e00141c404204d0240d4a1043c001600c2d810b0313880c01e18a4110340c0c800a6514469400790400c02c0c000c080058502d040d031640c0f2409040050201c0d002d8074940880c8024054042181d8030040c100402c3c2000303848050300302c05500340180800303d8441c0980d4004500c2d650381d82002d4a010b0040200903070514140031110440c2030300c01203001c440c11482000010080d00c4d01100f13840101e20700c7c2000e10751504031002034500820110b80b0f0704a052005103000f141c642da180c401c0c880d040c0c500c2454944c01a40070b041c0640303401c4050243d5850140100400e001600791a01501c0c1203c00704c1144c1e4034480720b1b614090744800764140c108206925460800134510406410042c06284150700791428030329044243c0c42500c1500c40705142c00500c0c000803955008480b491506002c82c410000909e054461003d18040005000d200c0700291004042000040b0140b00460024450b4103080002100b035030000303844580303140328420000c400080d0032490380405000c01418480c40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 609659874 1250 609658624 609658627
    0x20a0b0703110c0303090601051f0206060409060e16091401050d080a020a080a090911120103080313020d05031207023009091303020f0a0c0e04030203070b0907210201080414070b 78
    0x100c080c6d030b5504424403460f403040c00d50862488000c116081d1503a1681440e0780078200643e84d080512000c1c15962000700d441301c0da541458051220180141e01e00c007501805550040c51030800c101003503901132049981c0005081b0010495540c0d120620441130707a200b0761040e140c000480c010390402004d40d9024102c0100003403440885940300702d2031419110303254402c0012254814038000c00d40100f42c509010045588010f201290028015650041044c0b850041c140483e50209010b80e84901d001c4401e5440894008071a001c1c041f80d4a40c00380c034a01c020130195200c00c50341c1000c07070720941075100d10300303c4004000c108410520031140d805c1e0b00644003c005080458446140150400c2c1c158014052505080c0c4e403104040f0300c610030700350804195051642090303461040048060320032020352104022220005000011503441000c4d2341d00a44440c51070012840007500d003404565079668611081c4000603a040840c00b500f150300807078140e580081c496041031502c019600201113a000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 609661124 1250 609659874 609659881
    0x3020a050d03060e0a110d05150301060b04050f030d170a0207020a080a0209010b1812100c05180a0b07060203070c02130c030e010606090e19020721020a0b0703110c0303 74
    0x1019000031084800082d04140130303580d181c4041084500c1c41c0510403d020080011030070808464102c2034006d100960511048600b0308002400c46407140d04c03507410500003250070407071362400000d006034240c0b041e0090704e280480e40100401152003083c101d004a274024000ca00414983d0f4140c03459164090401150035407a802c2240e81c40c002040e08070b10035405100041002c0d01c021054500c40c2d00c6020038140300c45419020000d000301700c54901140f9100399448081e0009141c0503245600d0400d89500f42d40390071030390000118124240d111400313401d0000b02000044402012620319581021006813070303445000d4102c64584d850900694000302c1c50740c040c0c0700030a66a128841007049610100300b2221300307552003403d82c0c21a1280f40b002c99002c0c80100000d0059071a015485030b00742200140104400100d50201c1e04036480544109580500440c00c402c0305c08d1010b0704000340c40c0000c0104400e0f554480c11401030040c211000c0540b510516680c40d4158001d9902c09009101070740e860380f4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 609662374 1250 609661124 609661127
    0x1c0b030d08071b062a020d0e010f03020c0615010909020c0304050d080d0507121505100c0804230a0b070b0a0e0c04020d021305100203030a0c0c02060c1c14031303020a050d 75
    0xc5c034084640d2481c10a00d100d00300864000035400000c070710300d0344a404440788600c00540303c8121241d00d04060540801810300440310a001043c4100407070400b4503280c07240c21000400c29200c0707801600f00c0910410444109080010590f022201c0c11150000790000300e10708a0b9442c0034201d11410101d00301824444072075008000e072108040c04007001c0040e0f88002802c2c4c1c004000502c00c0d29001400001301c44441880f900004500d00d0050301142d150079030f50f01c14022806800b00000e544030b02e440004405502e45056502c005014030908a401c080442d01c6580202c400905080e10481d5581b10080f444401440303a1400c02c00020b104540300c1a08a035800d02a50040c03407851000e010b0b4540104461400c015604a82546540154250741d501c02440f00101210b802880c1032080302003144005940d0f441c01001004401000340018140c01c220305800c1088a4601c5420300a00030100f28002c101e14003648d0380018451070060710880103040a038186040720340e000e0031a0240d600c920001c1c0303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 609663624 1250 609662374 609662411
    0xd020d06050129090603220b04021801182004030b0609070306121e02090c0c1e0a0b1506030c0307020c19030f1103031c0b030d08071b06 60
    0xd408048032050040001c01c0c10305400f43e100c280b01d0015400500100c01141003080c0035580c003540c83e1035000c64403088450035034800b410490040b1490b800c00e074100003c508000540d40404c645410752098154140110750140340345844180c00004e5494180100b280c1403e2100081002d0082e8030690300c035181c2c10001d0401400b01c4500780280b41c0c080c0030511342440b070702c1060308452030f44244003564442c3d980c400e5204142000300000c921400355544001d40d45008005000f50040c41007103690350102d00f045820030074042840d22107525190840541204041000e0401d141d00c1603d125803a603d540c01d1070088c1404456030350300480b0200410034454440001036010f40460780841702c106980c08108400030001500c645003c0c6000c03401000003844900748030060b80c0c443c4002001040c1d0100101e899034202c85c002598400700081c4011000089101310f840d00d0400390081c10b4081524800640081d101501d52000c1002c10180c010014488000c1e241c0990340c000d00c2441694034101c0504841c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 609664874 1250 609663624 609663629
    0x1060e0a1806140d020306071107150804060c022d010f0509071d040f080d1e0b190302060a21110a0314040b070e060903060906150a0b04090b0d020d060501 68
    0x1d1188600c03450b8120324022903c00340c041ea0080084c5556602c8c54400c031b0725a0b09280103021284035203030700861400d150080901750000c05a480b4111441c1c24107042d025145403524050554002d2107078480c01070085a603c45500d50221101e140d2044401c840300d00416406045a044501d40400c1c00501803001c2980011501514400c2d1542d010318401a07050120030b40e40280000e0240c07410300e000030485009851803040d403c500040800750b80d8240e81c08000b1400308240c80703d03901c5007844450b192002c041e6502d0b175034024002494608650125840d8815560f2040c02d10801280361900042c0a9048051310000000c0034400c001c86801c40005075042234000001003414a080e031310114480c000d01a200e1500700d445500580c0b14058281e6501284101c00340c0c112000304912007060302d007080103034003034100c400080803030345810340308540750300c8041c040e00348920345488041080c4000c0780256010b8440083d00040c400031031400050342c103151000c0094100c00b000000100384880c95008504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 609666124 1250 609664874 609664889
    0x10e030c12040b030115050d2d06060e06070c03080c01060f1224111c05010503010e0d08130212100f0b030a08071e080c010e03090901060e0a1806 64
    0x440d0701d04650888890080e8003800b840914140700400102c0c40130604030100410361309050345080310010030142a01c1d90310802e140200c180840400c24840840b200d146a0102c000c420442c56080c01d100400500510325500e200d008040740210038003070b024172a44002c6034030807141980c0b800f04907080c6010b002107101c0c1c4c0b02c03020302e4113200045c1c40100c0b040954900394084204803804000031031008040460146480c00965107540b05204484414010b000e1032540c1d410060488100780c0080041d030304140c00c0a8001d90409401d461140000260101c0c000d8403414041016034960f0760401501c100c2c00d101a5206404c4203004c2c09540d0049000140304820400c103001550184521605488954402d03d4161748480e107494040780d07054010b0024180710b0710800c03264200725a13501d04408901002650005400505069240380912a5010741344902003e1414403280c400001c844650510a06050086441d00002550b440480c044068508559980ca5401640d03070004010003440c0035054 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 609667374 1250 609666124 609666133
    0x20d03150f170f0703021305040c230a09020403230a0807081809040305040605160c140a0906050901090f0209040c081b070c140d0c0e070824040b01090305010e030c 72
    0x3410100c000c240401a650054044001c2c0f19a407d2840010100208296180301e0102004030700c80c613600005501784242e41c452901c4e14180e290410075900b4041c4e000d0302215104110410014030403905c0003500c05a011a8a094a1414004681881410702c0000c09548001415104014100000d001d2030203603503800c000444000424003103078020581d00900170800501040156031f01c04d5008180220300c040c40201200c880755202501407050350080c00f580030300e0b40c019162608058241c607004140c1c105040c02140c0c60040481c0c6000b00c180201e04941c0d0300c0d18400d506141064044070b01c4040068420003c81d09070380c40081409005841d44400c4010200181750343c004040160350120340c00ac000003c99a2515a01c811070303807100400300390051040c00b220b00101e18074130402c100909101c26411070b6480d280800500380200188420500c500255400d50244c07640941d0034407040e800e50f00080d8119000700185da4035a01503100422a600389050b1280543c40070000e03181541040003201c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 609668624 1250 609667374 609667393
    0x7052110090507030507080c0d0b03031c050c07030f05030604110d0b04110c0714031203070201020c1c0e010c14011107110603010e1f150518010906020d03150f17 71
    0x3c44c04d0707a4050364903d0000e802e81020a203599001d01c010841d50003070342d4000440001d840701090943c0c12208460b2031020286030102c4041134240515580100c40b11081440c00c4201da401824540109030810100400880051100e44403980301c10600f81091140c151118409a800c2016200307244c00306000b142094841c56901c0400400d0301e40c510302c000c014144076410203030980c03e442c240c0c003280340d8103114526502d841d0360025002980907a0050b8005070b50f503c108120580b811680d410712007415a031640000090650003d02417120f003400b441c042182c0d014504008500605c070340a100859464941e42e20100c0194000820b081c0388a40c807102040705101003040b180b404248203d181d032020080008007055018220100280c80b034000c0741c520692103500c215030489842040d070300131520001303003425200d00040801b00350343d10034030302170004504010000707442e4a078111000d820700d0345a440c40302c0c4005c04241c400d005041002040d0b920203a581886403c022054140e40c4024003804c1e000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 609669874 1250 609668624 609668627
    0x1302040b0a0612090213050c0c0705030303010b0a0518040612031803080316050f03041208090d0509040216051606080a0203102105120a03060e0f07052110090507 71
    0x784100c0e042600d4501c001e40c07900325184050b00c03441c1d008a920810741d10b0004c0b0442c2d55480b882e03000d84120340075603858031003001a940c0741c09840d4004a20a6105000400016911104413100042c0c14031703000da252003040030150b110011040790b26501c282801e80102c1c40300030300700c4403c8804e07019648244280c42022084001d141d01d031300026040c1d00b02040040c0514140b10340d804481031051800e6450702000000d10401e5410656040300c119181070368002c1c50b5a1300c4114260005c41e82c2000e4104880c2440d0058000e00c0364400c10341c000c03500820b1101240b415200004c00307050304141a14241c419114070428012900d000b2680801c0707407100400c0850003e4400d4a2144412100c040c110354140303503200135054494101d80f4243c0154200c103d002078424451000001c030340b030100940381d50300074001605507291500300000c1c80c00803204001300c03441260403181c0c0210300c0c6d00f0f00a070340300c5070401200308170052040d00c82d2841c003039282071110381c500421000e401c4803416002080070341c60b10b150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 609671124 1250 609669874 609669889
    0xe090613240b030a3207060f02100906060513050609041106120a05180703120e041b020c010e030c01021c09031703041509020603041403040f030501020306090a060602150702151302040b 81
    0x40e617122540603540c00c0c40014094403070540050400d0044070708840c1c03000c40084c10307541d6205c4102c400d9920b40c40100028204080400581501ca880c103012514080300820344104005002038001080c0310a1172100c0d8441c0c100315900500418420246850030840d140301800090318401180d04080107031090264010a00c1010f60341c0c071098007069180756001c112820300d0807400f095482a80c44613141da440158000040c5103085d55009404242440340015005000b006c0400e8003917049104900c00c0c50f07070b000c40c0f0300c1c02226003404405828000d4003411240c210403a0402425448107031600003005815001861180340300d005001e10341001860414181d17200180001d4002009001040001ea8401a044051180c0304100c904055480d42c980090b075145038825101658000240b14035400c00b81801d503842520100d0500200380741500086d941ca96004c400c41105081d200800d511602c2409059200355842c00c100025041c180891841002c00040032403140b40b0f0840d803413816052444 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 609672374 1250 609671124 609671213
    0x34804052803060e1006080a02210703080708090a06090f06170c031e0a09030e060a0e0625210f140a020a0c0e090613240b030a 56
    0xe6039441e616664407400582141c100c105402c0c0200a018024946a4410000104500401000385402c0c034018041c010b0030301d80000b04510880001d6501038000040c00804582d40402c080d980d9901c581084030050050b01002d80d4000102a40000c1c01c0342d1092020081e074080e0400a194a079403090180c42006207144818003054507080001c0341150700c6030107144c1c000c90682608026040b01c03104408034540455909000943d030300c400750140341c1d00101c1034510200a6450364684004084040c0231540078a1007030307204140c0014040d01408090401091500103036407500b406c81c2441c40d00341440303038151915281009403400895030091080c00c2c20902507001d603c03444801150070a440c51154004070301c0300c05611030b0281000028820144c100021300d0710051104003410b10402d00c6082c0400034014075050a000f0150b140481c4039075014240506100e00030300c520851040190b005130064401c0141d0500655046400f406030758403007100000300d03041d0701004100610f003060354a6034008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 609673624 1250 609672374 609672439
    0xf0302071a060d0203070801020a1202040e0a0b0d0503070b07030e152e14240a03180519060e0703080904090302120a0306030303050c03480405 63
    0x802002900d090710359035400c90340c080c000808031031281d000300c0c1c078002040d4080260703607500185020318546d0000d5100d1001c80c90400552502d440d00c6031800354020058100d110550b92a0b1031800d0304d5a6003140011a80c1c1c0c84000d03030b0703105d0529003403040e01c3c41411242000824148188103402490100b8100070203020903503400601e880e860030550b0b90485003240c2a130a90405ca524402510007201c40000400c17080c041160200ca00c0d1080c045088940303251209419001c02c5618518030004042d595858004d01d000900c0d06040006040f5a98580b500540240038440341c03003031041d541c1100080c07054000c040c14400340c600c0100d000e41d100300030321001d4202c00042c44041c8851170641c01040069000e84120303120341e401d240784103c1c40d80c05040c0d4080400c5d503c140c10030802d505405520b920028841000e421407820110418186d000d070440c0c00c00ba410004054800d1496076864400a2020f140502c2c03080303445d1000140ea00e0340076000301886000d044030143e00d0b0201100c011001440d45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 609674874 1250 609673624 609673643
    0xc020103200a08060621041b180b0a0f090b040e03030717100f0605070506010902090907050a02250807171c0309021c151104060c061409010c0f030207 66
    0x8080e8200c40c450310180c00700d517001d0000c0220b4510240e40c0b03c0800071898204046203614240303450716446040c81000b820b2004001140704004130700b0380c10084400140100c40c08214910103d0004152070f42070b4000304100203100c04003007114078507a13101a48000382a10104000b03202e541d400c6030740c0d0004641c440005020322080000c1c0f18682c540d860303007181aa0155030010b58071200380318401c40031900400c0008001281000521004000050060810f441c0440c90160840b01050146a00612100510100284540c40144204620400c07a104001d10202c7c8880c0039112401804851203000c01c1480b500c07a01041c04d91074010052103606120004212800d0301d005111080300c4c1c0c01d040d175424150384100c0c0c6030250f225007001e5491001000070404401d0220328284d00007101200c048141b103490203031803128000486003160251121420000011206880c0c4000900500351058030903003440000c1c400d614605410220040f14961641d1100190112044080f4040c540c0090440d00a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 609676124 1250 609674874 609674887
    0xe0c060306130e060403020105070810030c03030e180109061a161b1215050a0c020a1401061e0305070501180909290a0b0a320d030c02010320 62
    0xc000c002d04102d00d8407034002182942103459482e0604504440640140c1d44480c100000113900c0111542d01c0710489201481c4035003541c803614140e190314000141808080b0071400c040340c0d035404100e020580000e0f038411442d030b16520858003a1425200704101c42c09500260b82007070340307035a00b65003000c1c9070b25064408880094031165442c84655504c0c5400400da90030100d6440944940c82010a0050b144070359000e00084200c3c0c00c9640040080d40d42c80d20381100b502040b0b50201d80154034a4000003680160514400340034018a80350b0b2040307110310445145404081122051542107a010b1000c0d2142c5694410041d034510f101e200620358004032400d010f1101460550004002c54040c08000403546601448400c1700010102000c152805080c1000910b452a010384c4d2804001560340301032152802c4200e4a04032200c111030303508010000c140288001c0d2003a82c4155406009007a1881401542801b034a44048110144c2c0040e0800809040000088004680c14680603000390324191 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 609677374 1250 609676124 609676129
    0x20406120f1404030e150c030304140f1e01060602030c060c07060b1e030d090b09280608100501020601060c0f2316090b0619020c1011010e0c060306 65
    0x401076661400241e594140c010078058080c02284580d00c241c9810041000940c10070048411407141042c90400c2001104903401000c400c2d20340056001d060341d01d40f0b02440c071180b8144144c030301d82c6001500c0744400d0842c00d100f0403d21040e005802e50003c100240e00c8400490701c03841400c0d0301c0c1d05a0350000020540110281c4014040f45015080000f000c0924400141d2030075800c602c1c051044041c25041700883c6030a214140440071039040010b007003403030141920054000c18100600c501b114030324910205450142094035100171082160039035032542c1026000c02d9095032424500c40341540301145035400000c0290588107036864030042c00c1c680c0c0d41d5070000b20000800850321201b64800c541900c80e800a081540c01071140f000e002100c04c0401c00c041034030f503907034040899142810020051600c840d401c0b9284403ca844642000c9400c0c814180c2c641046190140d4210740c01c02000c00185901016070808640b044009100c4800501d142554541d00c5500c0c0b150b00c40001c0022402a2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 609678624 1250 609677374 609677381
    0x10515011418130221011d040c0902070c0b070503030f010f080a170909010308180301021c0203090a0b0c0d0c02240910090812010e150607210903020a060302040612 72
    0xf02e040c40300240c41d01c0000c0848000103d070007038645805c4203649006000d0307049220090f4416030f500041c0c0c042649456207903d05060450702c82c0324446540001c6800501030316505a20140c028154080d5a505040c40d0039030b901c0d4000c44500001000840011500c005110907007011130f0b002000511383c03da0152104501c2011144c0b0030003812804000a0f0000d4907007108039402103008914143d21020280301d0b07109660300c501070347c5100e40d1040240850035001d018072045c40441d000401a1203540b2a5945850140c0030207018100880c0c0c042040b0300314441500516102c81d406005001c916000e040a80c0e0b941c091440d403910818502480e02000c0c402c240c0496482040102290451008400200102d40690750103440c1302c2070004168102946114080b801407101c052106094a0022081c40300c030b035013110300da5104190005403642884580e140c82c0050340001c008800000181c40c6014084200900c82240545c1100c03c00140440c043d209031002c44100d51190000d4420010707281004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 609679874 1250 609678624 609678649
    0x30804020f01030f0e0f1c080103110301090209040807020a0f0311240a0c1101080105131a0612090c092406070602040b030a0608160603051503010515011418 69
    0x40640d10100005030500314003070300092200e81d42c060813603254802805402c07e11203440c841c01e54988541c84000e80c0760301140480c11039803c40c0c41217002c101030030300207800360141310740107580301000304140414411801c2c000d0804d180b00f2102e1006159841c0c6200da80300d8000d20010b002590b02c518207811720700f001103610380084400e036010205400c100e103004034542c000e140d41078005050015460200000141c45078408042401c10345220341c503001c00140c602e20040b51001c90749460300301c02d0900c10424901e080090744020681c03a240c0c2515600d504d031180040700c41d01e0040c82140c035810200d080c1a4002802140e0f140440c0c2e0359081c125650500c0c5111460041e40c0110007008504003041461025102030704034410f060b5502c2c2400f803c0310090381c0c000d802c041001d8119103a460304440302c0e001d85d04111b90a9080110700c0c3e41d5041e80704548141d41c10300701601542442c040100c1e40300c2c000051640c000090b03d0707215480c0d450715101e6605008400d03000c10314145c8050b040f0818900031180814 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 609681124 1250 609679874 609679877
    0x6060109050d14030d020d0b040e0c0d060e0714011e0e0d02031f0203060901171506010c1a010906060507151d010c0206071b050c060c0c0a0305061b030103030804020f01 74
    0x3242e02e0f85076141c0365a0001580d84102c940c0818682c030480c90f14001c2c40318002040380c0901c460413140a0a58460140c010b0f42845848018900d8041005507000744445280c58026200034a940b151840c900d02e8008000e85e00040e0b07000320f03044800b4846504c00528410359a00c03141030250318402d010a860f460785060340d2500c6004881165201d808001c0044000c40c1d0001603280d06140302404071450044e08102c550040d1a480880b0041000408001c105005940445e45840314001038451280b202406012440c41310b42c03482103080010f141ca41240c00e141010803405a07122030407151802241e50080410f00042200f40e501d0109820590742c9140b0f0075a401c4d0609400c1188500b114005089000560010720810100503040b15584603a000003080750038801c7c82c00d55440791941580c24065215420105916021400402014072034044c003a00f4030681c16203038217040351b07601011141e0707454500c018000002000c116800b624103ca40c9034940c2d10403622507a00b00203c01c10190904c50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 609682374 1250 609681124 609681143
    0xa300e01021603140f0f0408070602150604020315372105010612050c0f09040b04031d03070e011e030804031e08030406020d1a0a06110115060206150306060109050d 72
    0xc2190200b6004002c4151500e0f41b641d50b4514000c460380c00d003202c681c0001c0643d0800460f14502030203d040726a0301c9481140c0041e42e941c0c402c421015001c8804650302e822107105a001e10101c05415840949a4081c001c1c0310b403070608042501c03240c17004a0003548c02101c2018503120f080340700d501402a52074403480c0007003189502d60700c088001c9035500b8801c1c0d40940c0045603007682c60500180c4903a140d41c0550360300300d492515403141500280050002410860101500d1130b88403043c03044c0c00c80d1713802c005040e200200c0d40c2d5422509802400e0054603904a00507a08110505824000c4412642d100ca10203040901c0d603180e0b05913095000e4007260021100ca021000024581030003140300b24841d5400613101d45e50214100125030020b0410094201000b28118081c1e950030a02021190146000d13201260741206941c090503258075200d039116000030300820600e80129005114400312035049100c6c11300c2c1c404040c2d03500c0c1c068840f280441c40c0e42100340154200661306600035405400c001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 609683624 1250 609682374 609682387
    0x60f260c070b0a060605180d120507030801080601030c15020f1e0c090405071202040b03010f060303121b0503040f02030d0f030e120306060a300e0102160314 69
    0x8410550859420415940008001040118252241d50081480401007025500b011800f030141d104910710324860010b410401300d840c0e44c2d11140250320542c420104201e450304558040e01d15000500120003007001e2000116103108000f64560489030800980f403a884d1400e0303d038480040b0301551003002c60203507005050b0000001c0001c0c0c8148140f00000076040206100491306004440441c184503084003000e100110301c0000e0510269140c10700341f400d498190b44002002131500002079909075080c034a02420005003a800a003c076400f94440400c1001c480c2d04000486225107411845105154035040e040d61140d000780d0381c0940b103102e540b642e0034400d400082c6088481000403000070101044813100300c2d454007980450803160401400900a8882104c446002c0100303460300901d00400d080711054401c1c0070041c0071151500000144401c0d506200c1c00240c02e04c5420300e0f24909010030110000e80c1407003100e601803801000a2203014683c3d070119a0400c0940c860307000b800e001d100a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 609684874 1250 609683624 609683687
    0x20d0b1e010b043008030910090507030203060f0c0307080711010f05090d0203041406030721050a0c08070e10051b07080d08010305031605150103050d0306050406060f 73
    0x2aa40a41500c0c8a40c0e915a8942404000182e1016030051070b0b01a0682550102400d41362408103019807084076a500d99444202c00e52134800820819080d00b418a00780300f00303204e0081160ba007034900903816075240340e03075403500d1100901c4103540003503059401b0400100c44610980e5819040305041c54212011881c400d007050031f44080c1d10000d00642d546005000038114108001c181700c0c0f0450001d5801c1902c0c1100c41d0f000507030b00040c00c500030000040020310031442913500021481e10800d034000404c04511020000306411180011501e10b080c5125000300d0255100c0c602c00c80d020340e51151800140014840d007000100300440a0000500c03415109140840201c02420a06c82c010251a860296030900e421099100c2d041440410b800501c04a5000b0080791a05500da4090100c820610324009242404800b41d614281c20702030008820000041602c45020b01d09a81c00e0020315103407400c007c11542e0a1140d040442c00750040682954094001d010340288074500390918118613852 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 609686124 1250 609684874 609684931
    0x90f020708180f0a05010207090b040e0a050604030f09030b070e0310020a020c03060a0218060c1204140f0405090304060c030c020307030c2309010504020d02090d110406060c020d0b 79
    0x12a00240321510700154250402c8030f00c00510a400300c4090f600c1ca880c210010303488609a0042900352616480072141e242c40b42e4000e002000000000c690b01c001007401c5c01526030b501607500714002002c1c0030080c101a40715015440036641c000d1184899901c0701682644c6c0c101c218a0459018091416011440000351000c0c0428800640123011011000010182002001484502c1e924414000f5201c078409020030400159402c0e00d1041d502c1e820b81e880d00340b804043d00d01031701d40f00800050100c1e5040c4d1110700340031304603402e4031446480d00120b82040159031003100c140400b54410301003041201d20030b84078520418002e0030701d40080101600443d00b451501e0700242d90a12030400308000068000010001011a40304c1c02903203d416400010581941885458410303900030810710f8503912a5411540806c02c010f0015010340001e2070300c00d80301d002e249034413881280f5003040080c5450003030402c420110f0f4002d10509a1032300c5669200e00d0034401400100340300700500c52401e014500020f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 609687374 1250 609686124 609686137
    0x51b25080306040c03050411100912230a03350c04060f08130314040e09101802030304120602090307060309110117040624061e0503040b01090f020708 66
    0x12031a9940b07107401410300c000d503180101501304052038070301004003245400c400042c00c2e500032691500003068681c011a040b005c0d40d04904030f060447c160001c10000003103603003030496681a0400111260600b40c00341c481c5001c40f0094082802d500f06c050500e00d01c1d0188056480000c04090120030508410740340204086603a40901c07039001500307000054005c1d042c0010074840c0d140818551401418600c40140c0a0a0090034000802e1100142e0368280b03050310080d06c07068000881501c0c040100c2c80e90b81c0341000042a14500e4042c140400c00300244015440076000780040d40f40c80c0c9896440015024041c0d001d40b440c81e401d000c01621a0b5052050200501669a001c103e030603c604100403502c83d0200a0750500151141441481003d480e00560080d00079500080c10441d0a1403141d01d8054840309650046034210003143d01c541160301e0300071600402c40b904100012300c1c07109592074441520007400d0031003914010040740180f50020303035001c01003080c00b40c104821030b070715982d0507000034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 609688624 1250 609687374 609687383
    0x7020d0219051b1906020a05010609023c07050c090907441b0427020a09151a0405060403021009051503090f01060b0315040603080706020c10051b25 65
    0x2c240050500c0230034028a4060000c200c4114980300c040d20341d00c2c0300d002c1c0c0b000240f102080380c1c0309103e062011800074556009000c00c241c640d9080b007403170410b4650f004448524400c1c580c80c004600f00310000901e440585243c08180d03590002c1c1000d203800e0710382d4050b44c40003407a950303090100101c40e80d41d044070944070522001407541c060708a09a408042914425600031f520344440b404d1a051825020040882d171640c10700300040740381c004582011440e80102100030b0034100c9604284010f00d690004642e06810452201c0751884520180341c880e40c807865905c14404c1c0005c3c0b01520b040c00b04485945070b07a0505154540d03503003002c1100003400340311418610034040104010781600b80b080040c10404240200021818466032040c41e01000e041e9030790540c00c45c5483c4005803100d034819005580c000e240507884000500d0400d01030340c408189065980070b000c10820303400b10300380a8540103540d54444580e0018207501101016004126404d062004003801c81d0224198041200600e5025 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 609689874 1250 609688624 609688633
    0x8130306150605070201050327070e0105030c0108060f2218030e060313141f050a0b031506100e21011104030807080306031507020d0219051b190602 65
    0x41caa08481d40200700d9001005010b0304124400044c1c2c1c1c400216a80039011350010914805409070034a5429140d049202c079038400c091012560050743e07060541224000c5007158600d20321500111580402564015040095901d00720514540710420040d031000200321500200ba260180e441078a04260404028601c140400b1043c1a403000b01d611001728183c8800c1d20b0f60421510509000080d041c01819000f0803030500a0070b8074082c8003444100a8128602c10f0300d44580200000401050310254400d52524a080c00300f0b05001c5542c0154109541e01003405640e02001d000c0f03a521130400001c00c0001803000c5489503500c04005040c01428019603c1c00a500006040e003103401c11518040600401d0108100003040c00086800c001c0c3d00040d0075440761514004285401c40c51038041020b174140d80c0c1080078031030380021a01d640841a508441c20481451640607a9034288100580399401816402c280c02c040b1320040c6000740c1000c2c1c00000080750360f4619085506881d00800c0c0141c02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 609691124 1250 609689874 609689891
    0x30c090f1104290a021507090b1317060f040b040203070906030f1a061e0307050a0b0d0506060a05091905060c0102070b0f101503090b0a020405030607030e0304060c08130306 76
    0x2030301003c10300790142c4620003030710308800403002a682d2000e26017883e1030381e40380a0000380194450401000200703800d0f801c0f10340303c4100c001d411400038541d010750400007120b6000c030341c2000702c0040e02c0c50040300301304120310702900c3d01d4444140d00f00c0024001c0e07030548210000040c244025100e02c000440c0144590303000d5642ca45040018001e2250042c12202600c40078000940d0301e004201e119900700c0c11404070201c450101003800c00c01c2c290301460303100ca0f10000000d0001607200042101c00c0303059004001c0f69441c401007002a0048403c500d00081060083c24114100900c82c2030b590000c02c201a2035099861000650742e601c01889040c0b265008a0050b00f040364080289801030b820300c150070200d28250890040089130382c4a029150482403801c0d03d80c2600951003070f0300d07154224a04207030501d04403400f0006944580300c4c65010f841540d0000d41d80078443e1041200740b5004501841c903003442c001048600580545040da0901300420160002124503400c030001107100c2e05001c1400d00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 609692374 1250 609691124 609691169
    0x90b041709130b0f040615051315020703030f051e0c01020c0f0d0f0809060f100801090c150e21070e04050c0307060f27120b040209010f030c090f1104 66
    0x2000315801802242441400e04c200d000a07c628084201280f50840d2110140b070070740e40f5500ca80740c0c09403061030010700b030000c0055404158030095a01030f4032020700110703080308115400e1140b01000400d40f040008103d08035040040100710008105001508068071613444c10705004044c0581c6000342e0002241603040c5d07400000710103040340c0600b8911550301c5c011030343c0c0c0e1316903a0090904104082500008a04030241205040608910710080240d28010701e07142ca5288098060398421020001c9680481d40c8034410756900c3ca000a4100080c071001c01ca45082516844d01c0485664025040d001c51040c6003407032000c0c4982c0c040c00003400c250b120310091504103134030780d00070a08100041c3c42c00b0300c04542004603c0840c00981030842d401c0015481c0c100c020450641281c14140c01380041d0000303002c14441c145000c0c60086860814590f6031380c1080192070510300c402042c01c400801d081000610b5503001000c045070050010514032204087c440ca030798003603040209500c0308026468100c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 609693624 1250 609692374 609692389
    0x6020f031e0c0a09121e0c23012f0a0c05090603060702191e05390909031e07031e05090d0203070302041a13090b041709130b 55
    0x354078030045914018003d04000e01c3c131443c90164001c1c10b41030800e0501004000d003030003c1d91544190049580003900d1414070a040d5652040009000035680032201c140d001c06142108442c0c161a0980d003950800c080b40701165107a501001285480002c1c21071448081c4100410540310340020000c10b402c2804100d10700d100900201d000e6886801005941500003401d020440d200c042a1141701130103103008050700c020002c814109141c81d4551000f04840007c000c030032150b8140303802c80c03042400b1401d204190410000c0f03a07000780f60321420013864201900c0048e0041500e4095038903140f11007800b09a0841400f1092200380400540002810303030102044070600d0f207417480b011100300c01400007842c1d402500b01300e81c443e032402d4060308210340c2c042000d500110b602400134044d0b482c009100242c5008000b008038000c00341c100ca44618002203204403a191684481c4407140c0d40c550b0707143c110403006e0380204150700800c100070982040c0e44c0e400d10902900540080410785248240912280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 609694874 1250 609693624 609693631
    0xf021f0f0e070b07240207080c15040c060507060e0109030207030b01150c0b0612121b0703020328082d090a05040b18130215070c0e0406020f031e 64
    0x140c02c841c2051000b425120111a02540c000880000044c2c80c51018001e501d07040300702d6040d0710301c0060a2010000450050700600a0761070035103501140c018407180e44400300310740050825907428803d02c81d5500070400762080340c1c00750344001a2084c2d6292014211590302c4015409a40803032400c108010090207402c5c09490301d80b44905d14804485406002d00c0580107000f800c1c0355403200011010340701c80c0581c0c1d00c6200030710100d5100207200b40e0080b40c254400055407001ca0305ca460143e840d00000128603003125406030080c203e01340702403410a55901142520700100784000540300c04103841c040a4000c0360200e10682070405030065142140040c0c0c1c0129a0720740505102ca5005540c4000c20701c800c8403000e07200807841f0410280040c000245040c04100e90401d400140800c91080c88840c40034548280c0d003100040c1c01c1016041c03000d0261f1100204544241081400346410b003400070b5400ca44901005030405400302d030199556001107403101580c00760791100c9812400d030550103540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 609696124 1250 609694874 609694901
    0x1210060807091d070303052803091103030a050d09050c100305070201200d0507140705060f1b04061103070b01060e090a1109040203060a0504021201060210050114010f021f0f 76
    0x1206500000d0b2592135182c01d200142c00c0c82404900c2c01c400c00c0c03540d0390b0595440c2c2d1581003a04071140700a0050000e100c403000c00d944100d0b03840e001c8030303650400004482010a0300c3d11028106900c1d11401800f0702088c200403201d50068851480091321011058440703035806803804a46441d004400900311648550081d81ca001003003030703465517410050704441c860320840c00c021905075251501030700c0700c0a445d24024a500f000140c0b600c2845000f141c0a4090301c4148000c1c01a41c40e0301440384100403c000561910b03900403c0308103c420300031101c524054281d10140d03800c02d082904e404a02c003009902c030001040003504090f82030719005085e2940141018400c0002143c028800902e50180c42c0c041d42c0520780c00000b081d8a555104031460007000700401c2075580b40703608440000c802d1800c1c030840b00544508a10617032484c1c0d560050700e040c0d0741c0c3c0002c3c904021882c400115410510860400c0035402400a0080f400452241c61503c03800040717000f040740940250f0071303412200400201c01c07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 609697374 1250 609696124 609696161
    0xa020d02150403110c060f070314030c041211130b030d110d030209061905220510121b0305060f010206040512071a010f181802121006080709 62
    0x450701500100181c00a8051070714190a0550202c840e1400b0400039070300358081070100c1c40b0748825a0a6001f00000c42c400e84e681d400c00084d01301c14060720701064564501e0424240001d21002c0c00301028040554020f821000c18003a0840c045100710390580c1503485026215070500d4041d040c1000340200401d207500c0d02e104406c0c1e400070080d450308840c0d09010700b0150006502070440d03071504260342e0300a00308500c2c4e41d00d00850030b0028103070b54803103072002c03400ca215070a510089002e21200e44080703400c00f90400d607041000190403924103d003000020038160b9101250344001c1c49030480c4c00540821500c001400341000303010056940303584041141150701c4107040000040c030206100e0811b4003454041c0d80c83c2c0425160213461b000c4d00e8030002001484401c0000f0b040c802d4520144112820a41c80d034039244005600a400d0b03c04040c00000e80442034040c03240141483c20b0410751400c26101980d40d0a010019108155032442e40320403100d502c0088140302600c030324424141101404d49a22 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 609698624 1250 609697374 609697393
    0xe091608070f110312090606100915030227130209061b030c03070c1401110615010504090905010911040c0c0f0302010603170c07080102090102031b0a050105040302030a020d02 77
    0x92a50a0060100c1c041204840700d08803940e00038051803800450030000d50751248554030403200014411600b04030288038110210b071a030b04203140d85c0c1e03650000a0380c81800c8a810803026200506a00e880d20b410185c1c00c2210031140c020807044080400d420032410790b85048114100880c1d000c0d0303d513038040340c02d104001000d0030b540c80d002100d00011910a9452002220144107400c6004044401c000e80c040012901c080100001108041d11404c0303d880c503032040b00340011185003002c0d0741d150326294080720102d10103041c40300e00c031050b420301403414070714141c3c40c0c190940540d0300d040c804581d0b070f030f442e40d030b21500308090741c248000c8a01060780c04001c01c000924000746899402d6902400c1d07040d6600c030b0401818400e40010018682100701541d266a9040d40e03035540c1d0780030700c10041c5640200000460303102c4041c0200ca0b84081c05900071424105000b000c8507400007050054030052190300700070000140b0a02030248a240079802960300d034118508080c2c18001040e000c1c0c0d045400c8490038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 609699874 1250 609698624 609698627
    0x80a140a0f0e090717060a0b07120924050306030a0611070b1f180f02040311010f03060e191506090e130201080c0c03070501052d100603110f0a0e0916 66
    0xb00b42502c841020180180e0711b6a00100d414400c1d80d402c0b40580724000070307804c000c0c0b242c4524010641d000030769400f0000c3e030340e40015070001c4800f444403200c410a500070f030bc0c4500f88100c01a603000400201a160700000b0340d900c0700221600d200d41d803009e199001c50303a1000d205450706665408000d61040c0031040804c4400c0d003041c0b0101d8080d40c00700303040aa00c8521000781c0c0d1b610110358401032001c00c45d569034503801c1013000f50f941c03031072028001008889009012882401140101d4038034001003031380c0741c5580d51741026000b625010040c0c896943c010b00e007412100400084024a842c0e03d98111032410915444a0182c0081c28802d40c080000000710041c0d9101e0301c200c1d4401d40508050b52642e0050207450308511030340c00c01a09035820f25040c000c80e80000d030115601c0c4251040b07800c00c01c49407004640440070302120b50300c402c400c2410080044ea0b010b03400094503451400074040c0b5202c0500059001c58100441e82000280242d1401d1054242601103640007050b08000c0806012007510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 609701124 1250 609699874 609699887
    0x11d031312080f0c0106030c0b0909010510170a0e010606021c05030a1b11010b0d030c0b0c040b0315040b221508031612110703080a140a0f0e0907 64
    0x10304607a8000001d00c01d818401a4016203000310381c121155952001241c21032070181c02240016074440000d000005611040001115124400500250002d0386404c0800c0490705c880361441d41845150401a0b54107511030a455100e41c640311000244850f81601107401c442c00342c4c110109560203641c50380c030305c0d211b10901030b4014142403600a0f940d0356241a2600a0a9221031024a1155250f80100304581280310310000000c04c8000300502002c000401500c07240c1c4600c09404110010004804510401c1c0d80d103a10003140705030304e4500355440c695030540340d000301c614a00d035104000400c1058545801401d0048004450380d08000894902580041c00c01c420985032a55580c001d02450300c000c10448801400c10406503134840f05000c00206201061000444a09881125619100b80694288503440d4255402031003942d045940350015580a41d201c03106009002d6441110035000320002d0100e2183d6680360608141c2c601030140051515001300c40c4a01500d40402c0a26607001c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 609702374 1250 609701124 609701129
    0x1090c050d080708030c130e19060f030b13020603041407050a0b04050409030e120a1b0f05010c06060816061805010f0c0602040504022a191202010e0d02011d0313 71
    0x4844c180d60741c40d1034108040c18802c42c07a29566103902d040c000030344070f52400501885081d0010102e6451202003a541e41101c9650060b00300c0301d26a4441030011400460360307168000210400015900700310b03000640c442d00119011904581000000540316406002c10001020207a40421a480c10074604401c140614007601f8010342d60740c0c4901d014136104204000120401500581211145800e0942c94901c880e8094a1008040240e0b000c0364400640398012141c814032003e610300d0609004440801d1408002d4440540300d0002003210320003481803c0c0e003200d020b880200518a44070026106160030401441c00020541e400c0001e642c000c1013403010440c440c5416420b0302c1140ca01a8024069908015045403000c640500804052103811000c55000102222460380d003d007019070b03619003062000230460045010000085541c0e0f00340c1e0160103a4000491501c000b41d51140c13521103c850f00f0f50040c2c0d11050300c29042a132842c0701200e22800307000558500340d10303050b040c10b80b2115403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 609703624 1250 609702374 609702383
    0xa0b03130b1e070201020a02070b0f221a0d0e060f01171e0c03011401060f030b0a03120309021201091a0915040302031206100804060c021e01090c050d0807 68
    0xc00041c420700ca04001000041c030b441d848a4005050a22000b03000303403c10030000700035118032031012809020f10001c0e18001000720b030b1158680440302800c1800300a1402c44c3c2c4545800710400811b9000d01c0106682003a11000030b40d90312200c1c80c0446d0300c242d40402c240302b004c0d0780121050000070380c4d1701c0b010360741543d580c0102404412034484c1241d240000c1c00805039007250030840302007540b10020a0f003100e054001c2b8002c1c4040d9000c0010704d08841000c1c800c3d80702003001e090b4100d0199000e07410a0030340200081411712010303075980700c0440e4555144051400680d0390f2080e03400b145403200d00b5032031441c44040204042c42c841e1b91038540c004030080342c000c0b0b031050040010340300e103504004250b416010705c0032100080c01c040c50042e43e41c1d0800e4021000104800002a41d182041100a4840619560703900402c0c1c40300e4503a00000c1600d64a000110301550354070300c200c0e840341c1790700c07481075907800000290030502400c0c465019032140c1c02c014460035040540e030b0045030717400041d5a14243c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 609704874 1250 609703624 609703643
    0x1f08150f010c031404090618050702061501090b0d05061207080c0f04060909030c0b0114061c060e180c091e0a140f010801050912161104020f0301050a0b0313 69
    0x700d08064820904e5603c00000f0300d0000280030580c081260040d030201c0b401110a148045000d42c150803d43c0c01c211244001a804400003800090821941c9a5042c4042c10000c142c41d8483d082c1202980c003248141e0301003622038041c031242d810039100344122008050040c0c40e005042040301303506c2e45010800e0382d12489000c44010709a0b5103e61002e8014a001304d0100030070b410618000c0d012801002058038450407040000a842040d0581014040f800812580ca0326160780d509401d01e501c43c40b141d03800155106804149440021091401071050007050108100f05180380c510744000004044d00032000714040c800301e4182c094044500c44505082184140e4034002e0100c004c004211048518140040a21034184603500005040c1e03072150000344926a039000555565035030b81c0c0d5456030210001c00410b91084142c2540404640c4503d075100002944500000d050760013081c0114215000040100418600f60b90044003c051249007603042d86489046682c2702c0000d810050040600c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 609706124 1250 609704874 609704897
    0xd03060303020d0309170d05010e1515030903070b1906140a0b071406040807020108091f051915051801180c0309050d0e090705090d1707021f08150f01 66
    0x2a84000c0c886c0032000350710060b1504041030010024110078480e0300c55816023403000c100c620540c52036900e40500050040e904981c2c980180000941c401030244502e40018410400011900c44a40b4080d903000d030800c40b687e05602c50340c60111a5194801c00070000301c02c0b0051456290210341808440481e50441c2e00c420b00d9061650b0f201c6042a007101803070045071300300010006520301400790070b4000e90303851215907903003450a655108900c2c01080c5090340760805600103480d940040d580304441031014003c04068640b100241d4150013a85210031040c41410701107030400041c00500d05180d0b404208840d45080001b0301c0f014100110190328580301d040e81d0701e84c00d000340c0000b2a02c562000844629560110703004001c4150302c161a4810740f120301c04100070034800c8040d030f405008018403071000f403101d0707959aa20031040780c00d0403180d5071428800c002c0540d0f100c41c2076425661541e4001c1e42d260345c1c0940010310b0780c40020b104c160281c6110005880c0c58403520090800c2200c00c1c2054034034001c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 609707374 1250 609706124 609706133
    0xa02070510031b0206071404030b04020f060912070503010f02030708070509030a020d0807050c27040c080703290c0702061812030a0e040e0604290703020405030d03060303020d0309 79
    0xc0002084085060038981e030803c5900050042c8599a1a41c1d4003909a80300280341d1020f01c22440080c206032040000308000d0f1601802d9070a030a0f0001b88000d00e44605840480c0c51480c0c040350007102a00b01a500308014107007030044001c022000c0070308520703511784260003038a1410301520756810007070085408084c0352070400a0f440c040da0010701040d02500d80d481c0c04443e039886803000300c40f18022410501100d08080140b104005807606030351000005103a101502000014001d030380e540652400026045824000c2c4400b660240d40c9110a201c05004400240580c0d0700440850300f007000e042122454080050380c2c2a6503040300c41544d14140b0320145500307400189c400a03846400da2410800300000000140705174101c0703484580c822402602003000b200c004400408054002d803000600045000001c03040c0380502448540c452083c403c41c080307103100e00715401e8002c00d500013820b1084c0c0c5820080102561082e142c184513090075a0f8009480b542c0b01e8103140240340c0c45a60b04010003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 609708624 1250 609707374 609707381
    0x804030f12151403060405070b07020315091612080910030b1e1e0d020d0213090f0311030903150606041e1409091f0e061e0109020a0207051003 63
    0x103008589080c00703001080b6804041030a80340c030880710b02040e02c002641107400e001c6202403155402c0005800307040e10700320b451195039001e880200d030726000f45401002c0c03e4456100c5a40904588001421844410014544508901e42042d82d103d1100e11049001466072400c90300e0401d41507c0303040004c0c1360101c013540a031040c1c000d0564070040c00505015240304803800f4481c81e440c1214498101e01c0344070a50242d1218900505e0b1300b00f10482c0001d0054107106000311482071024180307080c1b40e9107001c140811540070000480e14401008080300c203150384080324000045804001c0d500c3c1004450020769501103043d1746a0210030350170000381c1e5641c1c9150a40b401460a0381e042540038540c50251962a02e0721300400300c0e22801a6601842428014403032449031680d88010080c40e41501c200c071202c03182000d000c0d52003940301d0304580141d110038416580500703207461054040303030420f0424841c0040140c2084980901c14414900029030000390b450440300161440e20850351035020440c0034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 609709874 1250 609708624 609708647
    0x809030f030c0d0f1b0906030b011e180f080d0504150c020f030f030d050c0306010f08060f0a0b030406141e360705030102040b03070516050d0908011505010804030f 72
    0x1920b045c980081c4e0343e07600d20003515082d9255943e07280454803403500b81c0448100021080c0012001340c560440851082022402c206441c100443e1314180c0c14004149503103a5044040c45c034260000070403d4100c01c0044889001a50400f030f401c1c2030410300e55004028181011004200d01400450199100d03c501c1051003100039059485c03074501c401c8541d507258080c66080c01400d180c0000602407622100c02d69009100581d5901d0004fd00300340100e4042c10003030420355003c000480e0300f0038076640d079664a030020b18110018540f6440c060a0801c00c490340c2d041040754203018031b0f04000d4150407400700b07805659164903071400b058580743c0d601100308004440545e80c0c4005081c0ca80303400c0c0c0061401d00f0919141804a0b22003d488100f81402d0b405036200351210b0110500120b09503902a201400100d9504186a00e05503c0f50721014680031900c21258041804141c06000500d402e000700e0720001c440c045102c3c15545442d00007400800004e0014041107071a03000b2003500c51203081000d44 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 609711124 1250 609709874 609709901
    0x80d0b060a03020918070207061d032a030c012307060905010b121f240303180504051504050403120c0306060f08070917030d0e010203070809030f030c0d 67
    0x101d0300d4020001030001d502102c042e42c820544080c1c80d100d4406129030107445094581e014012061401d85c007514142e010000c801c144420113490b403440c54900b044034101035450300c020710140004501000510720303018080d2600a0304010405600b6036049480c0d9503040124191407182c000d056400521103004500d801018a804c00c25179005104054008003070040d0226012030302c28410070001580d51002107103110748003602000440c90640503901140300240c80302002190320840030600c0360b9401d582d400c1180801d800d12180ba510078050709400b801750905803030030072050519100c2c00341d13036507102c540c29071250b44c82c0c100113410140318000096822101c01403d0041c00703090940a005809070340604000600f0740451454100d04c5081482d000f60821b8440182040c103158202140044441c9060307aa0301c010022002818030034030902403d01c61000c00141c4904111074001c00d004030140008505d40d00501c000480406200100e98014012000007666031049940100c0541005070300c0c8038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 609712230 1106 609711124 609711127
    0x1801060e100c0b04060614010c0201050403020d0c030b100e061509090601140703020105150301020c030f0a03060302040c0f1e140f0c030408070f050913080d0b06 71
    0x75142595180522104100da01e070400308640a94003103400781c0c0e84079010882d040040d50080443d060074a0f020801c03007520340008006016070302010340704500070400c840070000c070600d01c1401580e1260b122052407401164400b080b200d90b01c9800d242282da00c0000e0303118a04402d0015413060329544140c00d010101c02441b460310b9009010505200d20b0790442d010300c032000000f0b404924400da0010480f0b20300035000000d40500075104a029a005000340100b00e14088207079011041d055803400d450301282c50b0210003501e1036610194201d860804203c02441c0e0008141040b014130f81c0f208214007a0482e40102d003000480d402c240010b043e0b90341c621a0000c0d90f40100700c4465182c0300d4904100e1102186415540903500c25030850380a0038080183c41e000c0e10035030000b00340c221203000091401d24032004444c031195a00801d0703020000741c0d00c02c04a10035802003081700805051103 = true := by decide +kernel

theorem cover : BRFrame.Cov 609532374 609712230 := by
  have h0 := BRFrame.cov_init 609532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 609532374 ≤ n) (h2 : n < 609712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
