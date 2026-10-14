-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3604
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:08:37.579317+00:00
-- url     : https://prove2.me/submissions/6e079f49-7409-4e43-ba95-e9bacbf9c214

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 648021582 ≤ n < 648201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 648022832 1250 648021582 648021599
    0x102010b0a141e010c03050f0c0f070806010e0f040809120712110405040b0606030a0b03030a1e0f1b0f0b010e0103050f03070b0f06061e1b19020f13020d06 68
    0x489000b0903180d40e2200f041c1642e030001e86404120030008080040c0050b0310f11502512206403210241c5c4942110302001c810605c0316503825040c0149034881c410803000255909441682ea40326514500095803544c55642c2c1d04600340d000080c0b01f90303001221103000301544a0412404c2c0042607483c0c45917010300d81d1820507048070840d44c40c0540c0943c0c102403c010100d445100925044901501c0e420b0b03495032a080248000e00c800c0303040e1030741400001803094840e03a1003a041217100741c40030416800c0170511101601c4442400e06c0c0200403400300100200411090b011042c1814001c4640555130866613452140201c0c00b40c0000b102c1c0001e0744018001c0c1714017084011070310300720440190b01d800b81c65100e04180105c01852a1828810030700000c440d80c0b1200c0640d8503a400300c0b400314424244030f000794003075a008021500c0d80c0f540d0000100c02040400584080e40e8149004280700066540c1c0900040e0001c0c504031035000714680c5009001000c0038802841c942058450000e45c990412044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 648024082 1250 648022832 648022849
    0x1300c08072a08091203040b12061c1401020c010e010207030201061a0306040b010e030609071e0f0314030f0a0906080604060b1812010903021c0221090102010b0a14 72
    0x34100d1482c6014008407400030022086103411003403141c1c0315080c2c0b03000980030358040b04510216010124000800380c4410300031b09003501501c40300803c0c90355450f09200c0440d0002150b0342072512a6011400400c1c400307440350b084081d00800140c80c021a05c0c4110703080d10240c070b41d611001d0394002480e1040c540d086c42a40302501502200a83c001c42c461034501284c04040c0900b44166a641c10b44d1009031f0040a03031101101018041e81c0072481e25808440c0c4400345489402038100000740c001042e10108082c034001d480030302c60180c6860f4110345500c4d04039a040307415401980310810016070b1a280b01009043c24410a995121050303040a000410011020781224003850411005101c070200000681302a00031a803080390005021000180180e000a16156020b5207001c814009165010841100c000c2c0100d035052410ba010300c40490750b58a8402c18141607007042030b039450440c001b8030010a2501d10520002c126030070046c0000e2071611041e84036034a00c1c0c40d07250ec81d4041381412041c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 648025332 1250 648024082 648024107
    0x2040801091b0b0423040b090a0207060b01030522050a23010f05060f010302030a15090207050127030807091d2d012904030317090303040201300c0807 66
    0x43c1d0740e042a203080034500041c00442500d018003110f24031190450b44541e40001c841c02e0b03000308211001c0c181030100c0d0b0000c0d07000000c223540d214206182c1076100d5000f0300615000d0a01c01c403112003c1200540084d100e600d220b18112902d02a40040c400815290840d0884209030201116039565043c8400381c2115110071515040c18106000c0184a680310500011500310030709000d6620f944136101e01e401805d01020a18000740c60760340204100003280e0103400942c1c4100000c2002a01202114440d1421056030f424a6074410740302c8400607101d501310641140795810070342c8042d9240c11424401c0343c80e1f5003200342c82030100000c002021241c2e00c246000c1e014103000c200110f52000405025142c414002d0030b65103051456090b0381502c1c00c103109851441c4500c2d1076a1034076100c2c5401406940d90052000d0716020342c0002c208003220100840307000c0c0368149c54140a202864005009500c030000f10070311b032208007401c03003504100b2a0007240a00c2499948958403890f1552000c0d240c854840d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 648026582 1250 648025332 648025349
    0x1051f090506030a0204090317040804081002130333020909010e071403060f0301140901060b0c060a0c0e0301050403020f1606170c09060c0703031e0f1202040801091b 73
    0x201070102c0c2c1c0d2008952814625010758000c40e0100181c1000d550503a54496140c1402c0122010842403100c040c01900c01d460355182a54038a01824240d4416802510035544aa5032400380070030005441c46030211040f5464004d6009a00815030800400420320880d4402ca039000680c9084a25180000c903000d400b500c4c002d803006d8101604020301030000f0b61300f9041b0300e81001001c0740c001d54600041e029030420060091041c41c401d0814110356200c180d1f4101c0d540d6003450008035103c81c06105407942e0400c1400100303d1a51180da4540c05400e9225132541845100b100078003080d1801e024940c880c6009400910b14410b03030002043c90009010715a00400750715200a104166202c0c040c0d1040b41d041e580c4808190300c540609050922030754500f203a00c408009155020000003140f9142140d0080d121452009101400c02c0c0d24005071040a000280942d5180c4240138002c2942c003a100740c40450050400c0c5c0c0340e03400c1c6130844a41080c1590341414030940304440001d090441d00c0a040307680c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 648027832 1250 648026582 648026591
    0x70306020c0c0a14010c05010608070305012c0a081c021204020906041503030c02060d1401082505040c090302041a030c030a030804030809010906020a030f0e01092d0501051f09 77
    0x1010720b00700d130001040c1503410841c40003070010a0003401d40010010701105001d54094661700d01d0141d009017200035400141540e851003030505000c2e0f001210185c07284a40107040c04409554420317040342d21402075030107141c0200540314000f99051010700003c03481c98018601504042c010400c8040009003128811410074081404074210b05910354202c03545800c0030305041c001440007481c18019188003444251030a403000d07a1100003001b51504844450003540c40300480c030713142c8408240240c00789904424500f00108402c0c145684020180c2e41030303141c03038440d042d143d50005060741c05d200845010b04500b50a044410f14081c454003881900c110b004003c08500e5a50144c80701c82d00070409011700020b540091000502904040c1c440d82c0d220f0000c550f40c203030012018006110700d00c841a210741c41c00c0c050000104d014850100c165030000c08d8070700324020310501500c0d2001200341422070100381c0e0f041c00e00060800d0141e1406418079241c0219410711443d085a4521810341c080045203060 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 648029082 1250 648027832 648027839
    0x1209010c051b030f13031e020306010308090d140d0e0103090b0402040902030a080c060f090a0525050d0614060a0b220e040b0601031b080621070306020c0c0a 69
    0x7104503511004140d81c2e01c802e203115590a28158080c40030044141800040d0700c03c0301c21510711005081c0d91044940115485111031403080c0410310140c000d40551204005001042c202d50142c00100002000255083c0c460b40e60b50541030500d2a080d801c5901c9052003003107140d080000b400003c03200b880c0800c1082c03001c2d21050784000b006040a40540c4c3d075035200006544041c44540a2680c2140d02d841c0e940000c0c1030a076070b803110112110f00903152218041080b41501058111403e904a0000c041c040074400e018850540300d1038640c0c11100c00e91f6400181501d5101d510a080ca000b540d0001d000468488400da525400401c0c142c402c03540309505000c0315001500342c4485511008034064102202d0008000341e400580144020840000405c0308120040004034442c803000e80e020b001035004520428009103550700070002180303403140010101d041c01d2409030380c2c1102560a842190b00c0c0114400d09010490f00150b84c202d070006010f00c03070384808105140b24880259a44000c1c0c510f0f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 648030332 1250 648029082 648029087
    0x10e030a020a02190f03050633090705091327050d030c030216140d0e0d080304170f07110303041809060603020627030106061e050d111209010c 63
    0x2400324004d106050030000d41c2903506a200304c0a000e0580c1ca0010928643c90f8108035075260030494102c181c45200d0f81c081d1a4100f4a120100f14040301c0c418501d4124a10808000c0c000ca40103207504e0800c0f00512001c4819960b46281040c6285120000540110007042100d0f521010200543c0040b1400b4007090010781e002a480c9001041c5150006050204203411400b9126441341c860304101d0300310b021414404040c610b0b0b00c82c000010708640040d00b02d0300060341c0600c110348066502414056a101c04100c080000b1540240306a142568a60b641c0b0b4620150741c110f83c5001050713407000700340035080192001c3c1800344110118000c5040030b280c884c0003c141503c402c0a100001d444d50382c804c04104054022001540d8010f00307290722180c00c11040480d41094288006032a5181000c0c0442420103214002c266408c0d41c4e50005000032041c3d503a03203102500c510b030390b04009003045195540701403885901989100e0301c0400f40e803001100c00e0625040e00c003400913220b5034901a0600481da8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 648031582 1250 648030332 648030343
    0x10030302150f010605030a060302130b040c0c081902010f02030f1b0c060a0905101a040b2b020d0c031101080108010e06040623040b06041b0c260a0809010e030a02 71
    0x40b00e030328066940b55191f4180e64050090780e40021f420000d102b102d6042c0030559000110320200a4404201036130090208489980000002901a9070100108440c85904880b00200e940e0180000b0629000401d103510881e801216004400b40b42d01062082140000c5070b2480c8400c1c0e46900c2c9070806200c01140e90b182d001c0642400e404590303074010081008030a02c003041e14005900c0c420410038600042d00b0306c0007200341588a20070351524105142610b007401202401044904d200c1e603812030901940001c12100d0903080e40e10100150852000506c280001c60103140b0035101014612031a9002610314441030300444990b9041230046450988000350995100360090408a81c51f0303464140301d41242c004500440e9083c011000300014811182981c0303004040aa804009821802007001415441410500c002038a01c100703100c0400d44021501000d0850340c020150002c2004c40c16006617880b002c3c034440444e09160411521031828481c18004154400140d858000f6802c0025281c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 648032832 1250 648031582 648031589
    0x60f07140313090c0c1a06030607020111030408030403030908030a0204090b1c12111e1c05070303050c04150c06200a120b060301031a1b04030b150910030302150f01 72
    0x1107a842e262024110b2040c1100ba008036041044910a40c84106c0107080a4400302d4180f40a032240c0c1000c12401362052040e9281102c0e00c0d0f03003250030b68543d03503115846580054021b41c02c0640b04c2c91070b030000c00c60510085000711803000c001039860307181c951200261450300c8151440742980d2194001d903406402072811040d980228050484909000705440c09445031003d040c443c4100c1e510540501702c0c13103280404950850046820346150180780f284d58000c45903884000620034850800024001d0700b100d90040c041c000c5680c14140c980c0c071500d80302040ca8140c180029911302c415000c0c0300c4075200c3e2150300000c0545554104541c1202441d052280c04100020070204107503654161200d5480f040c0c18840c0107160740e650b940d690500071181c6d0254070303585181212440100c1c003013416402d124043c2c4001c260002d81402d10396190252001e20080030008000c900c250200742c60380d0b548800b01e11503250112000241400c3d0309000b0b162445803554079403003521000a000c01c0c00c41940e00d16046 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 648034082 1250 648032832 648032849
    0x1208060a060305090a061d07050303191103160b0711010b090105010e1305010305060124080105120115060504081203010305190f05060a09030f020c0114030a02040302060f07140313 79
    0x20344c0c03036050503a4a0407440340405070450b0300e000c5d03990581c1801d407010600b0f030915800880d40300984030000c050320392041003c88410400700da00c04170041c3c2e0141c50700350849442081a6824081880d4aaa21034490b92404591540c19a01000b002030b80000c2c6005042007020300070410503202d0b0000c5004c01d0810302500d410b0081c43c0d068a0707011307900e031110140d50110f034840902c082c0d41c0d0391409503650f803030a006010200325144848d8204002401700001079043c640d6580c5044d910701801d000240100651040c4255224040981d00c0360384038050030010a1290364841d65980350031590790a00c031207000d031b40c92440750410040010500018400450010340c9165141c01c452615040c240c483d0074042c020298000ca40401400c80b000d80c0c03140c080303580681c40d052403078294003000b00d8944880001d000c1c0864080c219096018101c030000d0b46d405948a00014a8642c690b000128243c002601d40341b00200700003101410055010341c410103c6041400460400002c460035642c0c03204c071802160348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 648035332 1250 648034082 648034091
    0xf0206070e0406031a060103050903130b0a030e15070f0903030e040f0b0a030b0708010f050306131410020408070b090901091109040903020105041a16030203100914041208060a0603 79
    0x1207644a038000d000070345c1c1c040045206544401d143c104584021a0a82c0c08070313240074000b41c0803039004003c80d0707034400d02050034031102c03804d000300324045401040620342003580d102e5107501384520401658a40b02c0c244991443d4614002030700400c0c54100241c40810820350520400000b40c0188400c1c0c1d0403a400c540200d011165805036100404508050591203140080d00100b17205102400c1c030f020f0b00c2540c0d200f07030050b81c80d05600d4008100384c0c0305480d01684031a00045510290712000000581f140202500310f5441201540c40c0000e1040c04190003a40050200302031501081100c004119a0b48428284400600021158501485010b07c803e4981c40801d10191b550802c4442071200140204030142c01c600b0024001c003c1180c0840c2c1c01c6d12440100311059028035401441050402c013102c001c07180907a400c9010390800703051072812001c248cc0101d840c444a01407400c480c0c035000380b510440d140506081181034801400781d81031103c10000d100250301e90100038815030300f10b42008078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 648036582 1250 648035332 648035357
    0x17010f0602150c12011806090614060a03141e010801061202011101020c150f0a091e020a0b0d020a082202010804050c090a0b0a090b060306040902030f0303070504050901060f020607 79
    0xb601e40c480c1c1961000e07814002c50006c2410224a0444108220079000420505460340d20782d034120b417144c0c0600a0402d41c02809a01540b070602e008081b040c207240340c0480c3c00c402d03150307040d8600314095032a0712010189000c04044400ca5200540c01040030780001c1c02070074684200c103041401240f80c080e0402030300310790210407848250103d03240e01210b84200c2d0200040c0b1003000e08030060503154810b05206c08000f2840002c1d06011380800b06400c1320607041560002e1980e1050103d05110490b00682c03c210002450344201014005900701c10801583c0e4101c0b01760300618514008052624520f00c074003811068000b9140e0080704e80e9030a003892661501c540c20903900d0329100c3c400d800c0c0c2c010941800c0015044094001049074007054464401d00c0740c030303001050309807400680304540014040c80042c02030304d8150080806240003405030b03079010354016041815640100c9848020450002d810061814103214507401411207140c403c100d085036103c025122000640030808110a034903488 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 648037832 1250 648036582 648036601
    0x31b090601090806270a0b010b090a030c0e09060717010308032520070311100c0206070503191e030c11100b040c03020408070605160b0717010f060215 66
    0x801904a0400b1a1900c1c50701d080002c08a1700c10144c12214010550850003280b81300150354041c0c281e0001d204000c603800c00100b40c00c1500003100d010790001f4031080010104189001850150425800c143c0d907518042015a250040140c00303001040401d11500d1031129540f503c86040d04c0d80412607555a407255501c0d2107890459041d003004001e4402c28007071003103401242000c10b10350320b055101019020805683e448424078440034000d038543c6c031000081071038600c203207140c0e005c0d2038201f598142445402140c21900a480100c506600001d242081c00860070100c4500c0c020a24103170035101d070001d14240604204a48500034141c441c2c4c802c81c070141c0603040d201c0708034020000711120300c1000425070b0040c6c01e030b05518038000ea00d006044044280b2900848090f50482030060000718a4140200c80b00c0c0d03c0110b01d88642500c001c1c1c50300020785214400c0b4001e682545c1c1d007440e59504011501540981a80020307075070182c104d8200040782e00070034600b5401902007162151540c400c20304 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 648039082 1250 648037832 648037847
    0x411030f100c20030c01050702030307120213081603060f0c05070f02012d080609010303050a0c110901170d0f0806010e0d06020408070f09060f090504020d0213020c0c031b090601 78
    0x25082d110f4412940704000304004081e100001c0007170f00a1119440390032050740c0300c0c48162410400200c955050300c4200405400801d84070200b6504040c1c03440d82d4503809170411101845075038090300301c0c0e00c4c104140141030184103491000da0304100b00c2c45a4002c405030443c442e20130002c1c00c440721042d1700819a0b0127074240458542900c040040f5590300d05103048030040031052000003082030000420868144500040e0589526031101454042c1100c0b09442140c6840011148224042c1240100e82c4851640900801c443c0141c000000e40402c2c10328205a21001613074100902c2e41c4441c007503d0352041c00c064004800f030030003140b42c00c4444081003100c8200400a04001e000150000f18411700103400000c94801b10404030865848011080566840348203031400350030300c00303000c0c4140b44241e4055a04144000e000842c0d05c54164003185d82e10740d401148200465011a10342c2b5285800c0c095410040c45c00c0f005407900c04012546000e0010701c0130350060140d02340200084003a4000c980 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 648040332 1250 648039082 648039107
    0x602160603050f130f020306040503091c0f23010606030605010e01030b091f3b0705030c0306120f0d0f090807090b150c0d0e09010b0307030f061505030411030f100c 72
    0x348c034450325107410040e9032a44101d513441d006903030100600203410f0809840900359035110101c20074020342515034002400341e030218040700408a00035043c0c0d18800340300341401000aa02c0201d111441d0200244c4522076030410706040c54106072041003680d88020b6001d51203c0d00780e501d8540703109805402d4450182c590070184004902e8114505002c1c03604a6401000c0c01c00380c002200207400b44ac440380e09503070580310311000c05c2040c400318a5642c504c1018550042d000380175200090708901070a4174049010140c03281c40d8101d00b10522016a1200c0020390b8100d032070601d80707142850240e48581d10000348c454442e0307040d80d820006460b0360b0ba1031820000d88214421094641030414442c948441c0c0c00c5240002203842c174068503c10341010f4105038100c0d440c9428050465461200c154003411b0060221440f00d55600b001140c44607001031740c01c6440d2920b0b901c3d55120310707052500320200710b61680800d1089d0b2002c11002e200c1e800001d04071940715950070010030805c080c444140c0c1c2c01c002001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 648041582 1250 648040332 648040339
    0x618110405040c03050105030c0409050d0509030c0d14010b1c03030b040221220218091c0e010e0f0f060a21020712112e05010602160603050f130f02 65
    0x1420207400d541c145c104506030303a0f0860a07101c2d0009020b08110848611240080c2150040005590300034015005403800150180070b40b064020550002208082c010408540350020310341e010110003024494100175500c1500ca075140340682d00410840081108801030415844540c03c03d0705840b141c05890a06681404111440700c8030640101c030745a00315454060603000e003140003c03414090039050340f01d540140c4003088008840b00a8584002c0091922201d4802d070000107882a03081c005007144100550755502120011000040c10a1022424035100f400c0c600d0302e005140d41d0309600030705120800c4030303e156141407107807086d00e18000200030042c400050700403260391621140c0003030090320702c05e00002031042441d0034107840e14491180f4034261603000001c8118100c51203a01d100184000c408061005010007440800385c81c4240c01000c0140c001021070304013681440203000c003070095420184082d1900a640c8070007000300130001610071000072450018041a44484044c064000c3e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 648042832 1250 648041582 648041591
    0x40c12020d0903080906190c0e100f1701380403030206070e12070b030c0708030a0603050607020f19020411181207030308010509040318030b04030909061811040504 72
    0x70300098004100d80e0600380c003c40c1994000904440000c00c0c6039101c2da080090010041042406031802083c454403214148206200303140410380c0c1d0a40400c2d440c4803546d8034085900103001005295603004403840c60f40780c180d000184441400c120a11840c0200f0000e070301d01c0142007152074414030003202d03940e00e00390303d000401006140d40070942c1882195151170309202d605c40380381400842200c04842c1c40c07080e04240e1051100440000c01076410080e40f01841b401c0201c181c403007041c0e0798801d417000c3c052039a03901d004008024041c404958081024006004e0369400c10881a0f200e180001c607900344c080c4801081d80c215600c03a03200700d16981c030700004262624031544020b51b003c00740b1a011440b80c88500400420401e000a0010540b07926a0302c0d24581e1b440c010500901a8016000310f06020301c207800007202c00c403141c010f000154001d421030030707450a080c140a03202c1541a080180d000b401c10750705121080800d420340030526080600001c1d0b5080c03440621401340520740100382d005040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 648044082 1250 648042832 648042847
    0x1d01021906051605160b19020f0304051504150b191707050301060f051e0904050d030f02070209061002070803030c07031202070c0b1605012a030903080105040c1202 72
    0xc5901292083d101d140c51150241d031074038000d450030302507038030f160002000261001002a0a010050350032000c4202c969850000618500c01aa0844c501d101c0c5c485d030002c010001404001c11805a403442040c00d51042ea0038280c4546180c4000264000c40039602e64032029070300e846d60343c540440e403081c21072031b100183c0e03c42803075007100c00b40e23410100d4040c410070300040345e82c0c0707810f1203640111b0f4140342e83c400160303140c9420f00040c1c458407800c60a002e50a025481901d80302c0503031311840b17280310750041c00710b01c1e01d07010010b0100c0d110240c116045910500c0004016101c0541caa5003051046450070441200c10a00300d24142c10f54004900c40e00001c01440048190342e40a070031640d109445d9480b541c05084000d41c124080e09101902401102508103e4034003d03100500c800061174085d200500f0f256221035080d80d01c9258040418400c0c0782c0c4544002d0080c14000d15454014075050141000e9501c1c0242a444103026641c0700f10f40c2c80805680d500e0040207921075203140141b003951140d01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 648045332 1250 648044082 648044093
    0xb010b2107201203070e031204080703020a1205060402040e0a05100c0e060310060c0203030d0e0a0b0a0b01020c04180b0103050312070f05070f060f021b0705040209011d010219 77
    0x440040d5110b0714107400b60840c00440c004070344803104648041486040d035442460072589000d50181c1d070303034050042d1b800c0f401c0710452290040001c1c250410041418526600c1407000300c2801d50f01c600b4121009003d108000b54001c82c01c1c0d50800c1d011100412000d100b4440681401342440c0020114401c0f1004400303e484e25402c0380c600c0541c16103441c0301c4454000c092081c544003c035090114411032000610050f4010240844418000f4023220700342841403210408403104d0079a0ba10340d582c0520424000c0014407801180d02030365402d400e0280c113130502e0010313542d401c1400f17501f8440d41d2580d144241c0440040c1900e100f9507081140d0b0401540d403804e0007502c82e400521030a0b03c6c16001000181e550380680342c1035050201550b2018640502c546030392841e41041103048a109031941010801d000145c0050841498144505041110f54610702c500e81201c5078012401280107101200003603070843c1c004402c4040341030b042d5201013003140c0100c0c00e1074904c00c8013001120740703811103205101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 648046582 1250 648045332 648045347
    0x20a09092c0c0f150f0a0210110702030a06050411060a0905130b0901150c1a06041b090603050c040504050103030804110d0c03020d031202040b0705190b010b2107 71
    0x2500e111105180700688410a40ba00155602c00e5001641d842c800300b1541002d140705020002018215410b080100d034998819500c44070a14006a0003d10f04559081c580d2007000100b034400644140380880b141d0110f505c500c0c0d40c110141109035900002020f01840f5006030f6071134403000f0412035555070910809410903129000340c40c05030b074650900a083c05003510450070300410050850b112030f0b2910000c1080c0700b215403040820400c41003100c3c40060031031645070404001d6445403888500d051030a11044440e400d50119042e18503962030700f502a000003102056404614010a00e50344a40c2d212946d1710480e8843d9411500d408000001d069021111a0165100741c4200c8101c910020030070081580340c41014023121810300301000145010492000c60754400d05000c2c0112030021540c1e401ca0301700b07030322201e10b00400288034420000c06001c2c151000c652000442075204058a030b17401c001d83c050007100c54034440003d100c1c91010f289410b41d8058101008004200d00d00818002d2010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 648047832 1250 648046582 648046631
    0x6020109110a050a03080708070203030301060807020f06100b09040e060a050712091509020103090b0c1c022a071a090a0504292206030308060102070612020a0909 71
    0x10080d6011600c0740d140c00c090081c115040102642200b50071500c0f000700340d9104407001c58a0b048208107803001070b00c0a0028500900540e104c3c0f80c070500d0980c41c06414925070307080500f115049802004815406406400251803490f10243e454410500224009081100d80509548500307002c000c0801d540e900303c2c81c843c0783c9655810011001000645040d22400040209800340072140c5002c9410303541d000d141c500f4014034011924040d41d40700c4000911050381c5040c0390050000312010003910203080c1508151303201c142140750038000078423070185891300b103007442e4a481c0007160446681010800745010b0a00002c0611f5a5101c000c520070762940b148003100d004d5043c45000080d02e00e0184188003400c01e0704400f600c103030b04c1a1084580f410038000350b2913a01422602c1c1d8842c0200f4820350190000c200414000796107420f40c14040c0c41000300800d9241198040c110074000035500100c0f1080e407014285000d0307228a48404103454155098000004561400081405000c42c1d1600108034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 648049082 1250 648047832 648047843
    0x102100207060b0427030c06110304050609010b0316030b07050c12030402040c0801120615171e012d0605060a020a06051f0b0c12121e0403142206020109 67
    0xb146004031051045e9403a82d80340004801c260900d0020034043c00d80b42032041c0c8603401c0020f5000710342803c1e04c0c10f40c005036001c0d6101e0388035000304241ca403c2480740034a1400304400511150070605034041e901d51550100405000740c513000f191400d4090000d80c0c982d4a554000d48150041c94214140c45800807030b020b0f4440c03805c00c0c0078040c007640240070050580f20780032b00303042c021055522482c000e054410220303001520042c00010752030084074101e500040049001c1d01c2a04c2500f0071103a0041e90100c82c0100c01e91404c0340c01f84c4508020b080f48043d600e050202d0172010301d00131800300000c1010758001900b2100004140c200d140c0d000c01c0305003d1030701c02e40c010000744e01c441c2d41103644000701540c0c0020302c164410307040c4071044544c40500f1440c217020040311480d44403002041c20a80000406102003a80f4005010150440000e0400c50071074441c0d4110076440c260310010260302c900080c40d50000d40001c0c10511800785020b80e00d81b48010200c90143e040c2c0d903120000c0c002c20041106840 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 648050332 1250 648049082 648049091
    0x309060411060703050d09030c0b0c1e0c1e0a0512030403021b13020d0f06030f02090702010c08040f0204150618170c09100e01120c0510020a0605060102100207060b04 73
    0x1050300c2c003003054480c0c1c00c0c0c25646250519402c0d6085034000c20b4000c505a0034419000c1c50700c0300184602510602c2014801c80482e01c401501e00c00030540810140010620796040c00400007000380003c56101c0c600040c0000303038cc00000c8203540b5060106410020700980030300901d0209150002c002903000d1480ba50071034042040c815492540d10001c032070056800310494110303502c08242034000c1d05003845480c8000400701d250815200c1100c8540d80101c03030040c60052208103510b00380501c140e02078042d0009102507080c448000f0b2403c50b000344001c00ba001090740b0041176481c1e07940710b820402c0e6400302055515071501e40240020744182c0440e80f090440d600045400f5401c4042b0700c0701a007076040108a420f1015040008882004246460461241d01300164079515805da0350f000b021103444e050301d440c941e03050810700564540c01c22400f6004154001c90b900c1c7c0d0024400300f80503000b80c0d0018003510f40000403824550800580710040b40041000000c0c4050b0368007031403401008580811 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 648051582 1250 648050332 648050363
    0x30e1f050723070302120106090e0109060b0d0506072607120f0c08041401110a030b01140702010c0b04060b030115050a060801060504150909111e0c0309060f0d0203090604 75
    0x801582e8105010182c00c095410001402c0200e42a5100000c0c2d80011401c41e072150b203164101c0d01688000d800c1030791908a04414403001d48114411920309940d49104121241c850176920040603000d1070801070307075a40c0ca0700c1d203000140c0b0b040c0b100401c00c28881c0403424102002090f10b45889031081e0300c64500401281008801d120340f480181c4240c0b5103144560300d40e25164040c8124072080318680d5241d0b07103014864161000146850b0000f51000600c080c0140001001d00071064128100250704020510150fa0000341030b40e5819408449100a681c1e545401c1f800341c502da9444035019801d2105200038110a24000001c0c0c40003515561003095864604032070191080c0f28071804910b08210030b0082c040918951071b03101440e428080e00c0140e4404000c421604140a0b0741242d6101081001d4103004502c0e04450300d10000506034145030300603038050744911030100c00500c665000a0400410100107080d40c070607100d064030440d221300e02003460a8403088110303821101c6460445102c0e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 648052832 1250 648051582 648051623
    0xe071d032406031509030307030522080702010201090c0b0d0e0304141003090c091d0601032001120609090201081f0603090206120a0e1b030307030e1f0507 68
    0x403160403a200700003004a4100c055091202080508120303014000d00800d94800d0820f030380c0032030040052000865603443c2c5103200400322540588400301d100e4125100002c116086801111025080080607a441e071582c03005034010320314508001c3c0040c80c629800101144e848024104c0302e500701070107100c626444030350359480f0b104038003664891499162000c0f0082c103048a11044012644c03d0004102c4120780361412607a103540d120343d000b2611090483c29076480182d1018403042c41d000200929411595401060b43e460b946c1c4500301c2c00c40c4203182e2202da1040a9845085981c100704001050b01d0305100c10103895081c8081e8041588000460403140407500801010805480d60030340e0a420810304030046c05000c0c03010781e0b21500501101140f500881001402a001007a0001e001d2220a8280b41883d03440c4280d181c0c1c00d04100c070540e046480110403244c5003940b510300148400074901c000360140e007412000d4061a100700c1c0312095101e4005000b0410240143d426003610211000307107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 648054082 1250 648052832 648052843
    0x35070906020f1005100e0a1a01020a121215080f010b060a0504050904080714060609060105121b041707230d0f030219110906010309031403100e071d03 66
    0x11080d6034032180020042c9070044e4009034000c268503801c42c0490f60b86003107540b5404020b80b20541039590b5030344030200303c0c0300d282100d06034600700b0b0000d007006c0c480b1a140da01400202c0303101c0500340041031400c0803c0001550140c0030400c2c02c0c9909500140e00d60306c185a41f58409089800035620b000c0020141c1c2c5882402e403080a142c5584507860f0900f02800e0000309040600129006041401540c0000d540100710002910300b0000a00701da141940401403908000351009040c06000c002d000c070310143c0e00308516400710b40011031090440c100d02e180c0c0c0c040d1080e58041c2103100100d510710740c811440440c00c58200d8003900c040c8001038200d0030700c210701185c0101d07241d0303880030400d01084005082d548121460900070700503251071860000d4440414540c0120494481440d01d101c401d0341c0c0741840f65181c11134828601040082c603250b80c0a01400c10504603030030310000201c0000c3c00ac0350310031401009407410b055580882c1c100004041c0c0580343c0c2809540e1000c00a849146141c10700261 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 648055332 1250 648054082 648054103
    0xb030a0f261309181401091a060f040608031b0c060a080115050301060c0b0403021203100f44010c050309100c0e0d0201050903030412032d3507090602 66
    0x4072480d0340f60917a1050308401c640552100b8654940f5903a5022404000e5600c3d10601513042d0748015240103020091500500e01d038043c4503e141c00e005100b5040000155004003404101c0004012405e000c032628261005407401c0c3d2120001035500c80f107507444a075440c100c66211001000b81703420440186c03468002402500300107940e000c1714038081001194800c0c3c007d400f17401a2075081c18409031070401540f013160b52642076680300a0800001080400c0c003802010904049005002c0491b120707a0915180820310018410310892840380181d45410f8510254401000300240c0c1000b85000d000c84e001103500541e180030381c01c1402c01003a094002c000000200d5921405081c0c0003104000100c0c100b01c00990401400303025041c00d83e107082009101804019603001410801480c0052040306008512a0340481200300d15114444042c000407003a001d0341042082c4081802140d503810060700800401030848501d80c480751882010031a018614a688020007151180c1e01a69128102c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 648056582 1250 648055332 648055361
    0x9070318030c1a071805060f180303040803070b01090c0c02030a060f111c1808030402040203040f050102070c080c0a06020622330b030a0f261309 64
    0x40c10400291003020105509880b03880103405030201100c61141814080f65810085081070b20a036003202c0b8080c965500411040311031a00d400002d00c0d00c0c0d0100c0c001d4041c61180079420500d9401c003940d003801036802038a0004210781c0c840b451402c2012450b1428420342c000b103458241603040140c4241c48005009070050700070581c58002e9560880240740001c0e01d400700c955110302002460022000410800303e0520b903100c030500c2906201000c44001400d17405010402510880008070a007054035409501280c00684940e5141080d005145400900902c15480003c0c1c0a080000b05034102c1c0030b07241d074881103442d9411300c10107003c1000c06a0040030096407017100018500f411800e200c00000107804c00c010030344421a5140401c6019551607843c1b10300c1c01c0c20200052910082042290314071006090080440700f40100391101c0290307070040c0010301c1c2030006800f844a0b480180b00001d80c0c55803040d08030303901164144142d0b0007911010f854010080c10000750300c1038501448010701e8511 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 648057832 1250 648056582 648056621
    0xa122604061707090f03030206100e130303020901090504110a0f02030310120f0c06020f0609030a05040509070c080d060e06030c03120a030e1f2d1802030d02010b090703 74
    0x1180004040002006034082000000011405c05000703c607040046129400030841c1d070900001120000c0031a820a10f00442c10301c04124018800d40f901c50415034145c140161758074103441c0100c8000d40d66070452a041403c008011000c6400b035401407145003859503980580300000003049840784020f0303030b40e0300d241c66005009100449442c02003041107441074140c1e00701c015041c0c1d14401e050b0311075800031000d80c020b05a8980001414440d941d40300030301501a600d0104080c2d80500540600d00506005001c854000750301c0c00d000306c44844159070004110740d02c4038400084100075243d1800350740d0078569000301181080c01e0002d220040701200401030003a40d40c0c000700b50307020794100040034001c25485107004540d100040c0700c0b40012007140004015407900354403545081d10300c80745608043c44907903001c4440341e100c14a1144c0301640700503404103005242d1400020040a007d1000e03515004031000b0182c01901503200f500b034040700b901c49104994801c8803c3e02140c400c010ba201c41c0d10000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 648059082 1250 648057832 648057857
    0x130b041d0105090a0f0204090f0213170d030507051c0b03150c07030c031e080103020901170705040b04021e2511131d0a02040f060b180a12260406 64
    0x45e001802102092a401414940d5a4000f0310035102e6109020566507800601a6030088015114002504070003100d60240303260140c1ca5a521a41107010380308041d601c03400b1690f45480740f800c0707074a425640c000020030318462036040d80060000a020300e1091080517546240c1709040b50340e540c0700d4804220654140817480d2815a44014551011410003001103100f08800118045034103c410303843c6c1c0c403d102507041d44103101c4440410303004000301c2d003c00020014104d10002e002c03001d5420584000c00c0c541009030218011340612141c1002c0d402c102400c40e06001410710142c4407501c8a003012006200100080d501d00050308000501a00700111948100d800c2c01e0703103c1c02003090105000641c821541d025030845942d0181141c60399013202c031401056240034060400b0001901c01c081040d1880d01141913000e100e0840c42d501e04c103c210030014050f54613105808000d2080c0076061214010034a000b0700740d00501c010007034051019542d2200c0060401007524140c4480340c44940c1140b00c1c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 648060332 1250 648059082 648059101
    0x806030706140306150408010b040b0d1515081f0510050105040e1b030429070e0906060f0a0807022103010b0715020c0a02031c0e060f130b041d010509 66
    0x303100c01d1700854203074607004100600f00d0041000305244c1e000050b09410180812040c0c40c98502e42901c14903c01e200c1d8000b16100400c14101d6101d031140024080c002001403042c410840c0e0701c040c019005807a510800000820102d095094610000304201d07a00d0300c07051111035000f400780d1341c0041c1080c00280813103120005656040b591000c0e0300000303824481c40900c00c0782d01c100e4049515031400f803a20354074437444600180034210781942000052170450001000603a46841c2d1a10403c000c0c13002c40c035281c60b40011140d00018400e4581e0360341c460341c5006071a05006445000051081c40643c0c001c408030414071540b98070540701000d28503403801c40c040e0500d80180c1f100751855804440c820240540f42e100074801d454103a0040d04da00030280c0109800c144143c92000741200803024101c04d4140d120b444035105607011940b540e200c070011400d8901d68000c41070380b00340302c411522011450b41c02c508094000c4034200b0b0107482c1613240c13180750210040400c0c883d81c0c4d003007140080418105003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 648061582 1250 648060332 648060337
    0x24102309090f1e130f060e100e0c010507080d0513021f08181501030c060905181303020f0627012d02120a151a0901030b0a0302130c080603070614 64
    0x8950164000982113036114420468050342c0112082c60b901d60058002001c140702140d0524450001000744002100c00070351905006001c1604122001a20720100801241074400801a280e8100203500d0303c00072900542c0c8000c481a44919400801c043d070001180103034160f800895505c940081d198400046503000b203000401007075006d800c081542866101d1001c0740254010751000080368a0b002000e0002040c60b04514019942000040a01000f01c2041078200c1400303901c105900307185042c200e04100d0341c00c0d5200b40b1400782034244071080c1e0130b214109480c3c0700c022403415511a148020a4202c0300c90345001d10384250440d440040040c0704801a080b003941c03407903015142140c052500b501c0010700303c82c8003c201d661001c3c6400b40c1c2644181c10000350006413401100408880d94032440c9020b80700d041c504141d101d0300c00e88a00d840d40c007024801141c0c060000d035080d218200d0314401074403a0040101c000703040000021034518000400000701c5135140c8504004e07000c00540c01c049503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 648062832 1250 648061582 648061591
    0x207080a200d03150e1513020405060f0906070206030103030203030604050c0901020a030e030102040b3007020a0b04020a03140303160305010b070201030207320624102309090f1e 78
    0x100d59680000600085d000140c0307104496501c038280c0c002d4a0300041101001d91420000c400900c1840288540c0c0c03280c104036032888036402122a01d485100000501d98440d80a0082d001940840004205600080614010364040320144600d85d85c410403038259010f820601c0740168099a40b010120b0300800c240c010783c40014001500c0c242d102c00b124070142d4456894604091040307051030440080c00d1300e80048142d07160000c0d507500d051012000799950030100028107103811240c00304045554085000f4020b582c00030071900b115190044480d01d03608101c1d08055545084070703002a006200c0d2141fa4161521110511300345010707070300114000d420441301241c1425010303103004500d64131804481126010707110748194464004c0d10f141d00b4440302400202040c61307900d862401c3c0c400000e16001c42c546c411388d0b202c01d036019141d200310b03440086101040300c0004001428081001001c005003044082503034104259192006003c078664011100c014000702c00014041620120140f002d400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 648064082 1250 648062832 648062861
    0x423060d1a030d0c0312020307090e0a0915050a1b050f090310112109030403080a1e0503150d0b131a0f1909021e01120207080a200d03 59
    0x7100488000c685000d00c156003000c00b08540c0d07007100c020580d112103541c1410210200c01e40c19418500801b82000c00e45008509c6038100031030025019034180e600103455250880007240c98400d212258800504042d120b83d145241040f5814007400707041c10881a081d04d05503140340c0303000b41803003640c40150448440350350700d40a0742c01011041e0a450291840b803d504c0032007a6540d000000344001401d03901985103c0b5190007008224210300044103607000c980d00070100f80e682c2c803100541181c0350703c0c01c200340c0c92003a08015881182d0640c480080d40c402c05e4a041200902400e50040000104050700700401c8000c41c5000582031034100050075100c107203e5105100c1401c90522000080e10040340d14503404900007040000301100609145460324980f242001041c503990081000909881da00d00e540c2c60070101461941d91040c0504801c06428141c1151103201a24100341160b00a00401000508401d0468192520010074802d220450070041c0321031f08002e03409070b003e0b0500d02d9030002d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 648065332 1250 648064082 648064121
    0x901142d0406140f101704020409050313140409050c1203190c020a0e010b090405090c06040f0f0905010608040609020607080a4d01020702030f030423060d 68
    0x40d6034446000700e4016124402408005a201c802804a1003041c03403803440c880c6011106002caa190882c0b10076015548001100301507550720300206000c1d1020b40c0000f8824803001405071081420410307260191410300d6852085540000f0801003034441012000d441c0d5040714a9a200034600032050444006460080c0c80c10700c20203020504203486c040c030212021501801100003107140207515100503240c8201c04245650410a40c020300d0f0291001d418001c2d66641c0100d500c1e000200004000c15500400d880c0c0d0721612030103103000e140003038410703906041400f4001183d4200c69000e400d050b00c0007503598600c5030f80c2d55201e1074040d00640744240d030410000c00180001c03847c0c003002018544556140c2803020803800d0b0b0911540c2c0088200da10b202d40c403444c2c540c03000b00c021040c0444028140c2c009401c4a0010454a03402882601c20081d414498504010000300c004406013040b40d0808844544010000764042c501011012100e0345c03050701000000c00d24880c50740503208501c04a03103c42c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 648066582 1250 648065332 648065419
    0x40b090f060c07090b0316092310050102010e0105060f06161a0609070207060806011101061206090c08010c0e0103020c0a0c0e0a38010c050303070905090114 69
    0x62456001c2e6600d000300b60044a018044860a40650034880070141c00074100b00108104880b10040a40640c030007241d15400301a6054050030040502c0b0b4031303400342d12520b5041c4404444100c444e030740700740f40c055400d00c802000c004406200d203a11403130005c1c004a811119203002c000140d4003a601c0c2c0400442d000c41118003103900e02c0c07030005005007502c9482d285c0c4d050030070402264070401455641107511503130701449003d5001e1f41c9650408401c3c20010742a0302091103640c0940001e400076440c14100f6280c002c1482000c0d0041103045005070300400429440d0704c1664240d8150082070380100d55019541029540309070b000b005000050130503140e915a0550368034541d42900d40c48035150040000500c40e00c1042e6101d16542140240a03070003e00c4010711580101b080383c3d5070341d0003000103501c0b2100c440343d0081e0343c51681c440d400015030b962071400910107801d058886c000c00d402200c01c880041a02d0303246c1007121540b0040200101f1400e01c107000e00501d04c2e0240940100d410340c4045404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 648067832 1250 648066582 648066589
    0xe0307031e30030e1b1309080d240b0406081b160302060a090b040f0507030f0308040506070912120509030a0c1a03041a060612010e040b0108030f040b090f 68
    0x180028142c0072695040c00781202d0014203550241c1d0b001d940326003001021003940751503d03c3c0720300001803c0d030382e002c201c002070448a0010844644054800b43c4001903465242a6551113150441002c410b1502c91001c00c1d0300c04403d11205000709a02c0841c02c00c001d000103409210903a501628220040d45c1201c03000c02c2c0b0040507000449001d8240207200c02d09000c00d6010700146502108500042040c0c00140d1038115100c80301400140215515407150024808280080800707940c1140c2c00103448503071490b00410180707040f10300ba13800703004207808100520300c5070342c4c2d17902190750400310600c075104607845000c01c0346043c000d030100303124040000b281140c40c04d0002100c0d080c0101603c80a1a245c8988006268100c00d413175400800100100300010b403006030a00c41000c1c03c0b14403104142e4402000c02c1c428801c0074110407510840000004040c114941c516205500c2440405110f0b41da030714686aa82c02072400300c80704004107100a021b19440c9034007914107030348010000b0750100d20304000f1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 648069082 1250 648067832 648067883
    0x1602030a02040c0e100302090a0519030f0f06050f0408030619150903030e030a0210050a0e1f0e1807180506131509050d03050d14070f0e0307031e 64
    0x4004030f44c0d010160561032070203000c80820000c590506502c1c3c400d102d80040d075104200e009803840740111407440c05151070121801c0026513406000b048000481d400d0100001803a014219000fa040000080310a9400b04020340102c0d44061110b0035901c4103401c04c655400400c6480414030016000001c001c43d0143da40c1616640c944c54001c1c540c2d09508000f04000300000e0142d000c2d9016038111030050b201c00b40c0c206420074561602c161140c024410403544100c0a00e04503034410000070f0700034000d0001180301007105605486110ba000d4600c400c0c001400c14011850344000c91460003c3c40c03140c0100e10340c1c190400c0000e10300d002a604d450004089421000640541c0e4030001000c1c0f14003105029035032000c3c603c500300040300500e03050001d004081c41400040400802142020043c480703900000c1d02c40211903505000342c0340440d0024114085510144005107061840c010b040c2408580c050550350400030b4412600002106864902c1c15804d044655200c00c10b02e14802001800c070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 648070332 1250 648069082 648069101
    0x30c03010f020c010f1806050c0c030a0909060819020405060d02220c02070807060e0a0909050a0c05010c0c0e060303070c03030c05060609090c01030b0301150f0302150f1602030a0204 80
    0x100584032054400c0140c00c5500c00b0850881032854004c10749814040c0300038541d106c81c2c1c0004081015960800c0340c600502400303a04111030b200200c1c215881c640c00c42030010948445c50002c001003a501d50311685d86032039a84418000d800401d05d03040160038160070140e4018009000b10340c1a2040b5030100c1c0347c1840e0b1b01150760400095803001e24002056009038000960248018061541000807280e11101c0034402e00080c0000d00c9186500ca4460300342000040100071010844000c581c00c0503074558190b958100c58000c0c60040c007003141d6001c0d881c0d102c03143c1d4200360910540b80c18810040240000a400c2d590726110501419000400340110310001e14409e0f9034030075035520503140a5240002c06440d5074420f503011002c1200300e180020300600c0d1070383c091a004c80c9803e044401310b03004141c00c600300c2d08207a4000001050405c005148541102d100340d80d4060100f441410030346083c0205095048125401c004581c0c281201e007800200190004050f10104040c6a000a044888144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 648071582 1250 648070332 648070361
    0x3070f06030207060f0c3504080c0706091214010609050415051605070b10030507091509021207050a030209031501051e031c020304090e0f1c0804030e030c0301 70
    0xd040c4104004c038061404e8080801100f40040c40d45181c018000e00305c04044c603418140c44111408a820307117401280d021004076150b807600360502d0304045c600b40c0d0121303840911911170002e0004e405441120b00c0d40445429041500c103140050781c1d1780e8080340d207807080c698996403201d0021821140501c00e075030041d44140700c071283e03103641e42d203815007655001050101134402041c3c1d801c0c1015007040c00c4840381030b4403810420300703940d440600c0c9802005680014040d8400e500c4080380c18034156200e1010128260b0501920036a601019000d91103007030504419021a00085551540114050500342c8207a00700507003040e00c0a80400c0c0713000c3d1041900100009640010401c508200c0d07200742c06010440b004101c900040004256a0460007480c1c041403000050084240d40c8241f0648018100720482800f0707404c850300d00c0759900c0a1200002e20381d0b0151644c521141e06006502400c0081c09844060840c1e0700c0b46c0b8182e401c20458210581c0501480b07004003100d580a03c103055090340740c2d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 648072832 1250 648071582 648071587
    0x90a0e1c05042c06060c100e01020306211203092803030638070209100f0807141c0506040b01030308060406030308130c12081e03070e0d0203070f060302 67
    0x1080800c2480c01403400c070500040320410a181603014040c96952150050b14206e540f030644900d11850041000c040b006810714201008512903419002103005040880b485000c90320307104040c2800a5055004c110107902840000c003000d1340c058090b41d40701002d00143c17498034402030441c01c000407506102c8002421a01008001c0540600c10b0034041c140c8070b8440409468000c105034100840d0401c6041d01c02c0758040c5a031406028001200d0072203038064404002820400f00c450003600e011302480040800946c000704540c0400610807045030945420311101c1c100080620104299801480401110791000d60000c5441001214002d034410248407038658510304005014200103417046204a05102e0304201181c0c1c428a55904041080017070500f05509181904482510741c0c405001e03c4041a410070901494401804060300b00400703212218542203005c401600c41100d02502040c0c2c802c154401c00d0521041d80320810380b000d01103402140d1180102d40315008294400400603400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 648074082 1250 648072832 648072839
    0x50a0b03030d0c0219110f0312040905040c08121b1c05030901050c0406092c09060f0a20130f150923091f090b010815090a0e1c0504 58
    0x1006688210241401d03103441042c4d240c0c6d100c0c0049124000528826a039003054805265030910464516071400303448a6641c5540e1039800c2c029110459058900c510006400100388034045158071841c5118100140351440280005942c40320301074a600080c42401c10f002d695010310382000c419100c2c0c50b250300f900ca290203840103083d0780c1c004114400320a020f00040017001d401c40304030019660b445082d0103858924012501520811512400c1071503040c00600000800220700785000f04400d40b0401180c3c4da030306a6241c2510030200403a02404181f0f0662030341c083c051405070184103071100b1f050f644a503844130000c2c0c10640907044601c165451156850f07200c0d0f000306800c0d0080c8010042c044481020980c003120442d0000c03c40c1e400750111600180402046101e1201400e0001c1c0c911002d131600d461440c4003c119082c20b0310701141c01100445d0f0f2034202c403504216221401440d0344116074030003406501130006444a410140310708031300490b25060909135401003079070326920036464514 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 648075332 1250 648074082 648074087
    0x61e051008030307030b060708041203021b1c060902030d081009050114060a0c0503030c120f0f01030809010e031510150e01140903060a0504060606020f10050a0b03030d0c 75
    0x200a00380010500400c00104400032020050b6a4807010508002600494440209542d803085900c02049410002000300d00046100c1844860030b000360700712004200700704401c105048000340c0d06a8880000164880c02c40d511090701f001c12489140c012540c00515404a032400d0008040b00c0b001c075203c602042400d00d40c11006070020301003040240415450000201c08580d01c02a0070f501404000031030a80e440d000c0ca040040c926800700c11aa580d04d041041102c081d086500700414105807000415070b840604042103015220701d46000d2500c1c2d107956a900e0159005820040c148038802c91440c0c40f0b664140418030031105208440c132803a2800c500c1281d50803826801c0400d00003078030080d104050b94003640d0500608004e0078100324050000e81204654040c2c411a507526106400810202c2116900000d0240d440748100784181a180c6030143d85419001f0209540d6610941400e82c018180750840d40d007100d00c803400081c2d40300740200400d05552000b0446c1608644030224035040340d030b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 648076582 1250 648075332 648075341
    0x1603050c3408030f2a03041101050909040b01180e0d0c0303150801020405040c03200a1206061d04050c270402030412180303050409091110020a02040f1a061303061e 72
    0x164182140c071402007000345c0e112002e000141c0301030304007440001c4169050b4020000c1b140c03584002132480c1c00a1a040c41c1201094009010351442240b01c1107603d10580c0c098081d100c05030380c2c45030107002040600c050454240c550194103034205900c40c4032000f0740581c030010300000780c540f00c0000760381c80313003880300748030654500002070310403d4602241540184142c000c004419224007100c15a1015a1103040760405905034090040381e140010008070180c00c185114140b800c001d4000cad030340b06403070001c00040700d07801c80361941156020480824030821451117070000305214801c0210072076240c00400c0803604101c03001c40d0f41c1014460b010000c2508524820340d610802c81404540ca0700710b0340c0050683c002d034403070341d001c0d140c42c0ea2610007082200044562044400340c8616801d03244824000d5440d444948164040c61400104104110700d9008108066201c50490b1840c0e013820340501541d944040c40941d00740b52003900c040006040c81c050705140300c0d40384001e8801100c0301c40700c486c00c0b036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 648077832 1250 648076582 648076621
    0x32403330c0711010c05010b100c02010e010f0e040902041103040302151302060f03060d1b1e080c10020f120d1d0c13141603050c3408030f 61
    0x210082c00b035030700040c0c00c43d410580941000e00e80008440d860b890301e00e02629144864652141d0079104d80394040d544110100341c064000d80c2d40d91070504280d03005503405444500c280001800144545101d41480d4021140300c5101410020f0203001d4015100d14907003040d10100e0043c1c00c541b10440c080000020b195030041e1010401e0071600706e4036030004043e40b040c0c0540c8684440040b0005205070343e00c644001015800c40207800c18000d0403003c01101e00c007035020760a0321000800e01d8003245210020f0010544402030001c0000303030003110804c80c040d01074196050442c4075251a0100c140e0041c412600d6101003401c4003074450740c540381382c1c00580b85509440c40d5420f03842c92401304c816200284503070f0312100564003540081030281c140c0c00545108080350340d1400c080030a0100b10003240680a0000e01680e404210035120742c0c602141d00c4c805c132074a0340902c40d20390317100002c02070070f501d81d004880c3d0b1030000d00c201c41c5035142d55410340d5070404c4449544802c00301040204051207c02c2d0030851 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 648079082 1250 648077832 648077851
    0x4080a020706092904080f011d07140d082a0c06090d06050402120307050609010b030a08040603020a0201290a060e060d0504020a24030c0503240333 65
    0x4908004c1c0d5011031081c2074946503078107002284503210301c40c0c61804030760107015104180d40c5180d990405507800303456040310150300746032035602a0f074444a022038440f066074800b000740c04120070b1442c1040b0441c840001d05994105d420025014040d50f0301b4802c400e01480103104c142c0441038007842038103101824514900a280401c00401a07035030b86c034094011150303c240d00003000c1d1030364000310315010381e481070140e418840014000140300300002c1c2d040c40b03500e42c54024007141ba0650306064403020510030042018209200501c0001e0190700036105006051000090000d80311041d0032032281e000c82d41610802c4200030807500390800201c448050101814140d40e4401e808021603410b01c1100f03100000ea82d52080410215034400c4201001070a9071f000c030403070000201900d4030480015414020119123400203d01380c0720300600641e407040d00c1c10782c81e03020225402c00ca010000340950204e261b16005202c000a4003c9004100c2c080c084100c40c6520055a142007038404030002c05411080c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 648080332 1250 648079082 648079097
    0x40f0c081501270c030b0916210b04150806070e0306010501050d0209090a052401080c03060f15190201020f07110d0812160302120604050705040e04080a020706 70
    0x40c8191401c01150464080103c0c440307554031201510f9242200000740043c085007042c0410a0a56140d005029409000c4850902d01d8881c0721036a4428440e04110030081024040928024081c01000410740100b01038041101040707000060200c3d81d01e0300b00c0040c2c1c0f13041341000b03100c1a6801c200050f8003003484d050114118001d000040e0703654005109190410000081c0c1c0d05109030344d81c042d913240701c501405038501400c00b0139481c030240100300c1d50f480302480709182c0440421100d134181440d4034010785130700301c00c1c0e280c81e4246401580010036030b50b00650b8000e01d003006516260303c2402c031740300b150a04079280d203188400c3d0205039041d050039000b10fa0060045100c1c80209200300d440495210822500b00c148020226915103034140000d4441a800b089406d100700d440301d0f0540c032614030040001d0741c03454403010640c101d01482c055840045503150028816017040c0d0b0205d0717002811030030701609040da10307002101d182e0030440d002c94120f800441c01d0f2441907010000100a000c2906000341b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 648081582 1250 648080332 648080353
    0x601030203040b1911040e07021612020d17190e0d020307181d011e060311040504170d09110a0b0304031805100201020306090f01080316021503040f0c08 67
    0x8100070020380800b12136030049810f0b600c01c1c001640401c22401c0d040742c1c501d482e940d9500c0040e4010b042200c6070800b502400c0300320440304c2000fa90790310507580b0b05400000001915024410708c42d10091048803082c004954001d201e185a101402c601c4040d030b001d248a107a190302c002040302030100640c03030180251086007001603502161071070a94060300004080d03c1003e031040c801400c40c000422001b00c03070001d42c002c614901900704140050a504404500094080c0518212006840301030001065440d01c401c030ba28058000a40003400780300580904102d162944e44130740d00c0f81d5811000309558409042c204108000407080c10b9008442c1000c0043c940703001d460141c400100000c2c100000c1c01010003e0b1000e06d01c403c0050711024108071007020031010068000e500594080c2d120fa10440002a00c1d0109017400754162802c11026504103c0c80140035006406900c00882c0e0100091008a0803020584041c1d84180d000f21840105003419052a4141e0a0b56410602c00ca820030902c86 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 648082832 1250 648081582 648081593
    0x41208090a09020a2a061d0f03190e030f031c060803030105030a081b06180105181908041d040308090f0a02090601110a060606141c020f0c071d060103020304 69
    0x6800000d103102424600c054114113481c0002081817005008900d40100340c0400f080302500e43d44145052022500d0348950401d40680e207024400241e20032404221505404512a0301e00c0d00034200054103d912010b2043c00903400c0d40c20151460040190528881c0204e0505000b01c01c02408a00042d525650604000c21303100c0c105010054610a030000701c40000003a44609090200000010390300c50342401001211005001141d043c161340c2054040740492500c186d51216503510300c0e00404040542109d25051400c0e0302c0d0081d90844000d01001a036040340a10301091a80c0c2c5203103500481c68640390140100c1030145c2541d405500c40141489003800004015001603011038800c1c2c5d1560f070b0b8000494604c021004007651501407402d0500811010303801800590702a521010715404030380c20f044015005000c807500c49200180d00f0b42d21b071400d0560080c0b00042014110034909850140701740e00d0840325174000440000b44e01701c544c0f0143e990008090700181d0920701981b440c18a80c40c1c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 648084082 1250 648082832 648082847
    0x60503150d121404030b0a0f0c1b140f010203040507030c0e0403120f0609020a090305120c030d0b12030a021c1706130f0c0e030d08220305041208090a09020a 69
    0x484284049080310503c031419110680c0c0007560702801400e0a40f4012900c0c1c809811800d80f45040c50381440511001240200540e410b011054021900f506140b80c44819010100c001c0420180c0144034610850f28028001984924080c8008100b403528610380003907144c501d45d02c11f06e01d036103001042c040043d60020303c41c2210b510080e4082041551801d094000b44101d0303018043d03a40c40000e84c1c50b0503d400203119411603000314141d840d90107031450700d45030a10450105828a4000300025402504954018a035912002e0103083d0054071140160745107501a0203090f000d42e00102907030a407001d1004019801002c1440d140090a8800031071030040c500c050141c91094040c103400030504e03c11030340140100314a07400c06008040d410017000c1d083c0390104021a0180c0258030060142c1e501401c4490b010b10f80503038039440c100151020105c0c14561000d0114100030040100181d408660b0702e001c514580070300840c0703030f540d100d81041010168039a40f00100d000e005004c4602140d030010700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 648085332 1250 648084082 648084113
    0x3070c080c031b06130914010501030b01020a02240304150b04061802390f0a12110f0d031a030a0b0a0218100302040e1003110607140106060503150d 65
    0x9000214801e240c00240700d50103800340d00c0d400910712285c0007400030880d4100115090201c80440002d03621040110140d505a44825001d03900c800141c1005040140c1c0c80c01d074801160201c100c40100c0700342c00c45559401502c060340c510105183d2003030300980138421075040c45402c480400c81c1c40c0c034006250700f070280c1e15126181c69540c0440e101e101da13440c44e415019070410700c680c184088600d007251030440c440d4180e00d0b55468420404000b00d030b51400515090640d130492a8010405015230048031440c00b126628112401080030031041c0048c2080782041d0f005094501080000d100c101341c03819900007807100c0780309901500c0700d00041404124081e400030144c5a025946049203410401108070800202d40c0102c0042d529141259141e4094002e0b07800c1500401815140c91141c04000040340c040988a400c01101c02e01107407518100400010380b04540300740c2c9070039030120a00d00311038881d4031003030200344000100840c13600e41900000303d100044803140c1c1c0d0301c0700310740300c070305140000b1032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 648086582 1250 648085332 648085363
    0x40602030403050d0c1805191205030c190209070203090d1509020a0e1605130b07030e090a050114030a11100504181413080a030c031503030203070c080c03 68
    0x1207414148100116204e14450307040038080da90740c2002c0288849502000a4041d120079940854545070a8200c5c02d00350300e0b80c0f101e44102e1420504424a004c01c005d808841e144020040d11400800c24014003610803401001d500318101d85005111180a0007402002150010010010b26503100d20880d04800e41003c0f00c0080c810120251400a00b06001d007e036005100c0d0b80d0004909050281d018851940e90161900c0d44420b10700540781c1e80031300d128441c08501d03418001d00c40c0700c50903409080094000e1500b50501c001d40000300d007141d60160742199440351110010f20640300c1c01010402004000e40003010051201d498209400d41b00000903441140701c11020310710140b14009a0f409091079020980c4001e00007141c140003421014030010042c00d4002c00100036540c02d2021451542d00000300618081f24160210f00400c1c2c6c141c80070003403590302d8a00c0d00144908a1007a405103120b80c0066136140103604064400c02c0d0365904c011900c0d4008078030001c3c943c40c04030742c540c02140c042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 648087832 1250 648086582 648086587
    0x70804030c030e1305150a06021207060908030c0325023c0d090906050a050d020103060906060c02090f1026030d0203190b03060c18030a080a0f0c0b040602 68
    0x1490100d94010340400f2140c0d02ca5440b13182d20781c089000d940910b02400710040c0c681600c00b1104148100b407540e07441043c025170011250843d00701518802002428400d03400007036480d207183d03103a890a030001e80710034518031404810488450b6103056a03503d404035110303442c02940001c0c80d00a580341000402d8980b601450340c40802d002c00ca5040002e04214060407076003100e403880896941d80c0e00070b000e509000540059000503c80f0b0a84150025140c0c0501204015400c003001e102c4140c080e54403c038101039880301d0019000f052407040801070321050b03603107202002c028010004c910301c016081d121114410801e010702c103c800282d401c00c99070048129220302031030288800144c600303c1419400b9000c0004c0f004800c40c21640207503c03c4100215500c150260041c03003408031001d09000c15055849a00800d06480c42040a41b5400b01e1443c0e1400d02690100c012074100500e03240704899024004c16036100f0390b900100c42c80c58604103407800505121060b00d618504600c083c2c0050314083c2e00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 648089082 1250 648087832 648087857
    0x30809040b01020f0303070e2107060f020f0f0708150f04062d0b01110109050d030b040609060e04030305010803120c09010309020414010911130302040e0c0a0306140c0307080403 78
    0x900521103002250130a0300e4603403134002d1000c1c044c1611202c4081c0f040d011030002c20100c51280c500c10410b0480d010040c41130f14100074043d00c5502d880000e0700706510030b05840d41400345080252909824041015011041c078084610f441c240044441c120405440002c2142c56512610032642c85034201c000442c2011283e2030780c0350300fa40b8a9034524405044071244030038070841038000c43e4641400703995180b203a0b8407400c1840e00305c40031214024443d405c03070312403121807600c607030010b20001c0c20044c0000360f0b19580e404018120f82c00c0d68080d891f401d01c2c800400040c0364151146600501e00708010b146004600304070384402c5040144200340c03071103000c40c0030280c5074803d5021141c5294064010000d070040030402c6c2c0f81202d000d200c0c240060b404c0030110743e1001121410f48030840c130700741140000359040d40d003048042c1c103000481807014031070007441c000c0365503034691404015801030100050483d00c1c3c6003101009100100b810394003000030814000525032201013140d1094140c075003c4003d106 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 648090332 1250 648089082 648089087
    0x603063c0509150306160816110718061a0301060c060908040b0c0c04020408150c0c15150d0305070303180b090f1005040f0b280902040b0a030809040b01 67
    0x60340d00002d4001d00200c007000040b0303044a1811400b52412000c81c0c460fa516440c00e400155426408900003841500229805440c080001c1200344501e0810354036001100c0d0700d29103030285a0303100b04030b0010078410202c041c0100740b2951f4068072140840110380060384078451014070040c4903020800111249400a20045902c000d81c640ea006117004e5a8580d00e00300307101c3c150407015080d0814018143c1d0a162498140300b1102120301c000301915070310420200110b281035000b4a088101e803001c02c0052054801407203c01601400100d07140c6080c108259503031403c200310748280b80600e00d07100c00d510200c0d070000c042d40d00042e4180340c0401c110848541e403064507074141a004014044500c1803000200300810326141203c1c92000315260800030036a2281071381c4042e100600040e802d0a0207001060000015903400f03004c032002502050300c10100e2031205158070000e910241d55a84003032045140601031491008804c88040041d42d040d0380b81c7e032174140304844200d03115641d200b024012590 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 648091582 1250 648090332 648090449
    0x3030e0c1f1413030524010b0a020a062307171306090c080705040e03090603040206090a170d1e0225081005090d14071118070306060306 60
    0x40007010003511080f50040d09803031140c860208803064010080802c54404800210030340745181540d4040700f0381d107800c0c901ca031607500c800807407011805079503003100114082e401489a03400901c45403441c400040d8640711044480586403004110b124681e4403880619003441b50b81101011080101803400751130403000400d140b00c401050318014410000d260040801c511301120350946007404110094a900c070b40740c0c40381103100f50b800390f8107101050141c280300d0058102072a000d0700050741c040d12000d03076144100b220981c135260380c0d2083c03155104039540f00104240400c0e03400c9698406019200c006034840e11641060607080075055900d40c951004aa034060003400e001301642c9510755005510f50142038126019145c0388142440c00d14550b10171345c05840000f0403c1c018a0811000707079610201c948510040c00d6005c0403110788014041c6804540c076009510580b00002c0c424a00000501506c0441d030000a884820300740ba440200c9410084c00120320051011861031403411038490b090a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 648092832 1250 648091582 648091607
    0xe07050702030f0c090901181707051b03010b0406060c0b0a151206060806070503241e03010b030606030706081b031003050f2a040e0f0a03030e0c1f 65
    0x510681c10001103c40c0080390450a035142036944001036031362030742d459003641d02e00b0081c0c0c40200600c1c81c106003c15194019200040c1c0c09101841c64400d50361152460329080c12400341c102000b5451200d1589001d208008a560003558107010300c6103030046c09014000d82c80310103410b0380100c2001400394503640d030200e15003602e160850400c90745c603515451000c013407861044500c5403034104003189130309001440781d20800a5542c0c140c03031a50350281a0460a003c0060701c0c3e5611540b40c00e01c1b2581d9545500200e100340310660080c540d0080c00704142c01e682c110780b03601c1d000b0b4200c0ca062000c90f032030200b5000287c882d1800d012046031a220020040054001d401019130f000110511105150b2080e1000469004404131955100c42124440e100c1c041046082d1103420818a1706c80003c032084100ba8071518014400284828a0340b600350800400301c40201c0c02c0d40084408504043d0540300b407c0c0320440110040000c2d1210001241c1481400406004200301440c211107409108146d210440c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 648094082 1250 648092832 648092839
    0x1e020f0301090c081e1f1d0108030322030e030304300c1e080706211418010902190f0801021603030b0d05070b041505090d03260f0a0e15010e07050702 66
    0x5082d5950311f5050b071507031452518843c821800300001016040002030b24000c0d014019a080302e00b08482c101c1e010f0507100a412018018405012284d6a4041c40688024500150b542e2a4800421446001d42d0b588000c00d1296410b4024044080351303025120f00107643c2c041841618070460440c040d420521140d00c071540754400e82d01d020480304c0d4031000481128000c6486101c10310901000f440035500341c2d0042c042c4060704ca50001b000c4031035100407540140c000400015003c0c0c00303500070840c400c0c410b42425441d850189000c0107040400d00502c4001d00c403c00003141454242c1083d11041038450802504041d01c6261114507a590b21600301c0200d6440002c650100e603403a180c2c0130071500b180c880d00000c4281521114240c5000b4402c54032020002000da82c00303510155006c0d550107120302d80f0350604c10400c40c2c6880140d8441d04999029810b03048201c0a00d260500003c4103039007200540420301e03004803490358654180c0046a5043d20084502c0d03034001c0d515580e04485600485801952 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 648095332 1250 648094082 648094141
    0x603020313150b090c030103030c1205070812010311010201020708120402121e06070309030f030f11040909023111120a050601022104091e020f0301090c081e 69
    0x282e005a10442c1d4140041e142a559a80e0311212404940424400a0b021941c5240318900052030781c590f46200b030030036080103800c06403240c54800d01904560390401a2442c030750018020711420402c000c020090901c002d628022660f5136419090068804110300d5652080c04541150b0f44c501880c40c500418030100d44115200541c941078100340051021010700500000c9a05980709028451405405841c0d500c0c1c3d0300f074400d0301200200341d04122402070079501c45810340020440c0e0000d1000381070300d440226000d0b103103004000d25034001e1080c00500eaa0200712800b0020250b041c006c8601100f443c002420100c01101c4541901c20300107a034a413240c28008104070640c05503c810302942c400c0c3e007155046000c0d1502d010141011201191240e8000d2004018003103e42e00200e0b481c85110428014000701e540c0454140c2c2c12080001c050b00a01100510005415100e0790000c46003d183c03400e0b0505000d4008208000501c0014091412903c00224084102c0c90315000000d040120b105 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 648096582 1250 648095332 648095363
    0x90f180905010e030a0c0b0901090b0601210c0207030b0a06080c060d020c0d09080f0f10020d0b030316030206090a020f0f01020123012904090506150304060614010f090603020313 78
    0xc01c41d1b4410729045800e02044004a00f50090520400c202e6aa00600011940c1c0b5900d0056950403100030000a040011022070007119055000c0c05900300e003d50000c03d00c1c5400d603e44815001e00c014501802c0f985055170401410390009403c0018050649000c2d40d07503610355100c10042c0c0310300003c56038284110030200000a5006560008039200d01c41503840c16202103038110f4035229801000039041e4401840c7c0700b21500701e03a00405400740a8000000e110304500c0200c0c2c02d6400a028a0b241448030b85500f038107040d014800507034040050000307015502144c0e400941c00d944018840d0f8011140300e032004480c0e074000d500040c03269500d180d10141490f4550a00031001d0000d015404000a11407462040365041d44002c50815043c2400700c1d04290400c62804000c0c80000c2483ea488120b80c2c038480da44220701c034001c50003140545d0001c10b006052020741364600b09202c01e0b550410100b1188901481d0b844070f11003090382d8540c40c01596a0f00d0301c1d5120405d10300c9401b000f4181d00783c5002d034407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 648097832 1250 648096582 648096587
    0xf070c05100501291317070e0a0c09150f20030d0b0102070f06050405060f0f0c01091a1e09120c03090f0103020306030319021f0507090f180905010e030a 67
    0x5603200b0703d85000022452405000e216228007130701104080102e084001070000032221041c6d501401a05401c68903001c0e40d6a034030141407402964003203040e564a0758140c204a920a1030b4401a040b06032407a02e1940030100300502c0201c009a8a400708021495440c101581a2a4444074405820112512003400c0c004200081c0740c0f52011302e02510425600092007440750303090784210f88103602c42e582802e151409100482c4e1044061131910390341040b20040e10300e0844050306d1000071100001800031402c4c90318120781c1140c80b9419403400521400c02001004c141100c2001c0e07600b09ca5004a030752980d16200e8503100c04000000700381c01c0c010805845503007000020f460030780c1049541200d488040e00c0117500301d10094070443e0b055001003100180b03007000d5603940201c04006204075500c00c1301541c9a0705150032085190702c9829102c00501002650044008000d00100e165003d043c1d031400040c1055401c010210110143d00c403202c030001c0c490217500c11540040024156030b0303160140c1a00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 648099082 1250 648097832 648097859
    0x210b0601121407020715140706020c070303260103110d03021c210606020a14070306090b0105040f0b010e0d15020309010b010909200328060602150f070c05100501 71
    0x20010705c10468000f94401c03054000e402c10144c2512801c1410b07851541c070a02561003480c090725040e4081048030740d0b0500406c0680002c5000b56255440e001c000004402690a03c4411400c400c3c0c46d1001030010502c407400030a40210102e80c43d16031b200c2240b0701682407a410b100035001d0040c214a0828a4039004090040d1203903200301c0b030300c058103031032075005040b1001409070307000591003405014009042403021a407020041700485030311035034070b6880d8030981e0300e8030208840781c0c4106401088542024014a403001d40492018480ae0b5a440c000901a031049103000b0300c42c4d200f18600e01e05010010001c0302917100044c3c0e06669a15100c0703540d80c042e2002c18050783c000741000000141d80c1999106455520010480601c1da1203080318080080e5003010f4141d0300b480c1c1d500c040c052118100c40d0345d202039002c518080450b89a192250103400c000988044003030b40b040b44020806408038110311181c0c84001c501f803d9480c127065042c11468192466072281c1c05500d05000480c500c10003240d07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 648100332 1250 648099082 648099091
    0x60e09041b180606030608060112050f01060807150806012705030f0114060111060f06011101020d09110105090a03150b0307080c030706052106010e1c0b01210b06011214 74
    0x10b0501c8050343d900021003c4a13180d11030100250060f50050081e000100f109481480c0100c003125400d01c004680e860855070340783c1c0301c492284d0210204000b5412031591084918442c0e042c5030319549000d10018244860044103d0032622074800070722186281342e5000006020054210f88182108081e698002d05000c41c00c01d1494802400140456100f207a01001c030516032005000b8588407802000384009014190a05104822995000414091010313104106a042000c00d00e042142070000080320001400ea0401c2020030541c01d460312080758007401c80354090700300c107040c84403410750200800c564014140d040c0901c050002c6c05000002c0c80b0180101300318140c900041d5a0f00007030b1024032038048071018040c0801c0d01580350302124400194044018100f8809500c1300784c0004042e8000312072030090754400e49110409101c030b0806054058581401c180c0070a0540a0105c0800268190b006050112500000e0400d13442011050142c035980788003480029405c5814110f02d40003103c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 648101582 1250 648100332 648100379
    0x30f14040b060306160302090a0315150e011415130b12130c0e090f010c05120c160f0816080307110a020a0501050c070b120610020106060e09041b 64
    0x80c00300c0c2d40c0b4640816414052080108059064001900290080c0d040108410f50015201c90004041914245011000180503500144650003d5001030186060f1741060140446800050140d00c5101c01785654248040f111701e04000c50840c00007525107d6060b0240b250405000c00103244101c810282c5042c41190207181e4003540c40d89210302d0450100f8401400512241c4010401007200d102002d4205800c0c03016613004200002019081d1800b100202c40024400286401820b08408105800000310000f00389022000030b800c00014140c018003908400c02840c00004000680c02201c0c2000700d0401c0c52401041c150414501640044500b4000310f5030b0070103499007101010880e0074030f01d40d000303019600f101d040c6001101c42d9046000548224411002d01040b52401c00c00909012031390082c402e10780d8030b401400d00c50a820280b24210039a810502c09015454000707004502d017410a0768003240301c2d69030b410f20342c031440000c00340c15003400c0748403401041003022115a0445c298252 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 648102832 1250 648101582 648101603
    0x501020c01020a2115050609040212040b0109060b0702030601031e1209050424170f0708010504170a050a0309030c0605090105062d060c15390d0c030f1404 68
    0x106454805c0d90f050420801890340246801e11803441c10314003524080f100500300601740411001809032409083d00c059484511810040000d50020b0007080041c0c1400704080707003840076980c0425900c0f80c0c103010007400c0c056845210140080000010f803505070b04001201c0c0174045d0004041e1aa401c3c0d800790b203002e18201070b84a0313002c031021803415034070042500402070107a10b03040f8004550007030040500414016a0110074044a04004000191100b1800042d050405140a116050920f00310146c10941488640d20080c1c101e020b03119502003505012440260503d0120380084000d40003c003031a1400041c00400030b41540880d01c105429140d410a8076040c00d450444c80c5001e0f00e1003810718540345408101810b20602400d0f4403426002101d250b16800d8400d80307280c1004940399800d80c20400c0c00c5881144000124071440d8030b20319112003607080202c0401c09140326544640d9900c54803204182e503a548aa4007280c41440c590307204005844185468062042c020b03901a94108101e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 648104082 1250 648102832 648102887
    0x40b01030516030201020a03030b01090504090b0a0b0301090b010320090a021801093803070c05250e18030a0207140f09040b0a060b1c0507080702190501020c01020a 72
    0x2140350b014152a0160010b00c50020566011005050303c105610304001c0583c03000030b100d4980d40185d42a20b88103030355208003031420b8510b5400700d42c1421101da10a0f0b042810340c03070110b50542001415a0303001044032022002074403805d101c0d6014100d000d9000031501c41000f11500807540a0700c05e80341e40c1101039850324182e1004503148600342c0102c4003031070048542507401000804070070130b400c1c0319022038038400c40c8071075404186a04122090004103201c0c100032410050180451805000e00e00d202e107048104995144032141440e000325140404400003080c006c00015a50707243c452a004100d998075140c402c030080d00c1c0c203041d01c1084070415104520381118a40f6422030b425902d4043c181912550740e58079000d5803624003819020810b03a6601000c94042c080780d008080f103d40c6003850302c00c0240d2645400045550003401281000040424460340c0e5501040c013031075611750712041c02148407850070308034024810500e66800661000450702c0409130003da1082c10000e50450344c0f105400e2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 648105332 1250 648104082 648104113
    0x2428050906060a050108012715061209050604111c050c13110a0c0f0506270118030518120c090f09060c1809040303050619031703070c0803040b010305 66
    0xf058060389001c140c003c801409165010098895000300500b40429007100c0700482c00c0880e01030b00d021083c0c186082200f0701c6103070f41045000058141c2c4050400c10560b403525003a1722a4000b0700014455030a40d900c0a03c1a41c942c0e00d202c01900c07003030100c000742e0b0200b4507003160f07a004030b00d2500d4040c0315050106016000d080c4200d0f21101e0814224074589541608102c9004420443c00c070b41e00c03004415982e002c11020458280b0484100d032116102c1c400104650780099001241e0f4800c0781c0c1482d880c002d00654408052000c1941030420075100c90102d2004180b801c4008000b5400101c5148100540c100000e480000342c041a11100080c0d16500c80202c00c219003118103101d1a0b0210011900b089600710040c1820240a005a135030b40c4684000100e000009035420f4000a407101e0600c90140741c4001040703855561480000e0045146680b01a5200500f801110020102000094034107008030305040109030300507200c591382d15141c42c0c5a1a600c100380425141c40c0304003e06540d4804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 648106582 1250 648105332 648105349
    0x8090d170402010e13051504142e090c020106320406091806050c0c19080d060905040203010609050106090302010309050f010e0a05061e0c07110307090f0e242805090606 74
    0x2722801d03901d004a0b074644000c44c15140c048402d149068042041c1f81340482015080c4d50003603c00050003213030800100000a00f542e056401980c010380c46102e0071002c1c1c59403c003080c03e0445803000009002e083c0c4030000341c01404c0725406214005d0030a46540f203031541c0c02e0008881ca5208034170410040c1c6990440103401d00510b840017000c0d611540c62551042805a0360948d0340d0321840d4000d151804a04510055501035880b0300070050300c510601c000c61500303002c0c4601510000c202008650324000c0d004004100303034803020b8181991058080d050110501ca140107282c5903600a1000454141c011991690580d2050f200c5008034004148a210301100056050319030783d4942c807036a1200c18032100b490b401002e00300d82e502041420411251010b01c404802002c80030000a01210740b0f10143d4203440300c642e0072a81d41c1d0002445540c4024070546206a22024504046550f82e154119880356003643c9003101c04100d540c070f4507000c0480d2550085846a030381031054482580301c40e0140309094 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 648107832 1250 648106582 648106601
    0xc08070501020111090a06080408070c062a081c11030115170906070f0e041d0114010b030106180e2706060d0615051f08090d170402010e13051504 64
    0x258080780200420780c462300036550001c0c092001949407901c03039920440b49031202d03400340d0080b501c03240f41908080c800c81d6907820541e0380d82d0001408074486565003001072062521101500300c41002440401241c1da200a000f00c02d19083c07540d0344d50f11046a88019600566080300250103000e1480d00391442e4081c2900803021200142042e0322107080686681e2a1480410108a8001d203250000d664501a4040b41d00951484040f00e03c2007000540c25140d42c490204089410301c6e004101081c0040100d030304490142ca00b542c1500c01c50f41001c0c4817288643c0c800c400412100d014030404020880c210454a0011081c12101000d441440d944862044a03220f510118210204010a0781754104100a200352281c500c1d05035141c0c1c001960b0021180c44070301c08103600344012070003250000d5529401c016040300914281400801c0280b0083e03e02451030991203110303010404690007144402c2c0001d6000b45240c1200304103030710703101c011701086481c009642c0404420b084541803522404204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 648109082 1250 648107832 648107839
    0x905090304030302190f060c09090c0306030302071a130f051e1c1104020c01150608010b190302040506041409010603050c1b1005070c06050705161e0c0807050102011109 74
    0x40d170311180c50003089641c0c0b035100342ca00f8042401c410000840500c500780101081e61527000005003896440c004880c4820141424103161200520110b0740000d0860100d4031012004111130614000003035031802070b024224510002c200b030201c2d2140c1116141001e40304240d41c0d080d450043c0c40c0c4810301040043c0002e5412040c0341ca040142080d0440c4801d03c658040c116040300036080c1401b040c00c0b03038800c0d104c10010b03075555000380f45402c8014506000402c1c003403030b02807010350408849000912035400071107605696481c0a1111a00a03010741d0014030300148080c2d110b070b5841586822001104030600c0c4101801800030441c103001e07124442c0a0803004078510b017420002d603880c5d201410a421028000e108102e00e010407100980203040c0300b10003e030b642e044010110700c2c00c082581c43c00382c03580082c09414030800040b425160180c001103900010711140c807048000641004400e0a04003800354015030300b001c04c0500c8006881e1007141c40030b90082041c004001f09960a0340901d07210380e82d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 648110332 1250 648109082 648109093
    0xf01020421030e03071503050603150705210f0406150b0901050a0912110a0b090907031a0d1211010207110907090f0801140c0a36030503040905090304030302 69
    0x4010350740c403100c044081c2c4641400414100074600180c034200f83e0364407991440311000440f00940c1c2e4075000e06504014158010080840b00803414140e142c80103020004120011070000024440824140b401d502c1c0041204418182025605d44a10b0121401d0320780d00e00309400c100020104945480c221b400d5071810a00f4030b490000112145d62005a003202002007826000c61040e029070101c185903441011040c0e0144584010700080b18055840940090024080010151a51550660f00ca40785250020700848242840707040040d1100c00c003500403d0041c1d00004011010310304644040b030a032a0900f8140c0070021b10b9090388103d0500030504200095051035a00381500300c190403621a0400041d401e071038441014a8030150b500c640616034403031401c807891000002c0107681041d56040c0d9146001c950341c00c06000001c0d50800914a800c2d0111400c0500f030348090b11081000040c4e00207004556a03007030441e9250014051000724501d8603002c54006c1d07500108032000c4030fa05401030003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 648111582 1250 648110332 648110369
    0xf051f0b0a030906050a0203090f060f0721020a080703050a0605010c08030405122b05040308040212120a0503101205060a051005062701140f072a080f010204 69
    0x35150741000d403070502415120514040003824134000e075071107400320f50300058a07031501e8000d6031315000b100e10580b02d01c0e8100c607061003110841c460030954882c80b40d090011101165008031101301078180481c010662000c100042204c2e403251076903010760032a0342c05201a8032014851750480b0350f607100d0343c1c0c08119040b0303200c000100002d024652041c010816036030540e191151164495003c100b01c1446034480400fa0318502d000040c4c0010700c4c1c0500c800403c00e5240c103035400b400c4000058400b81c4200241400b4000100041049589901c101900b40b43c881d520242c0281c038540044d078440102d5203c62402003620103450005440c11900300000f000107444e0803a0240c02400e0280c00c110f10300c011054041447e031100001044040c5441c2c2a122484480181c059860504000a9410400c004209100300b226030402e403034011050748d0900e85d503020940b070b007425004040e1030701e150a200500c459140b03880c06d40d03000320225030140b000d6030304000306450760724201c0c400e5018070f04d1480841c46000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 648112832 1250 648111582 648111599
    0x3030c0901140c0a21020601120602180a09020c060a0b101215060816180b0c0c0909010203060a09090507270f0f0e0109020604120201120f0f051f 64
    0x100e542c0328080302ca45281c1200d10340c01c1c0e81000e00000003592500d008560a404081215580301d9060060b480a8425541401c6011426015007503000d09035580100346013400c074071014020078a070f00c03000300454032031030365558014081c3d001412500804d0203624005801040d1724001c8a9541000410040041c00c40000c00d0b91001040d01200e00c1043c2e89108203d04820005610300140a1645801c88545020541040044400b52403801040f0320440d807200b90240204061095031180e05416840320340d440032280c604050303d403032194050107110501000000640c000c502842c01540c441c034442c0d407982b8a210550320342d01401040350340268401c03c00318404860404250302c101c8602190142150441c200b600d4a98103901c4210755500350745000c80c00e4034864501e20500840003071003088581e800189940c01f503031003841100402481740070116031040000c0100401129400c0092422000140c8010125001c050140c00e1900000ca40c001e034118003144208400103803808025030814150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 648114082 1250 648112832 648112847
    0xf0d03051c02071a0a0c0c0305030c0c0610380307260702011802010c11010302040807060206010503070605270f120a05070f031203270501021b03030c0901 68
    0x14584007101181c0221001d40c103000034550b0302e0040300c215894120008082d40d10301c6024181300712140c030303050614440701c2d041200b0070f01c01030b090300300141c403542e03044003d80c80780c07154480103903050181100300301201d03400c885044192424643c00c46522902c202c0f140048807420b6400805030011002c81804685004006544c05600d80c90441e8003e0340c1c01c2130709030740003111160001003181d94408000b5100d609110341d03038a18603484560007085401c0e4001800c0740c0f003844405030841d00a200d181105034000e80488004101c43d00c21500050f654010007525a00e084c0a014800c0c042c840300081e1280c4908140d90040712100b40030b03032001015130101c0c803100c0b03c0d007408103070064040080e5440720b40d2800144010b5042003400b60111441c1842d10760305181e140d4100b40c1709810940014004500110342c01044021241030010301c4102031180301d254691070008440da4003104540358000c10030f0640242408590591103468140d00b459840e54880c0030464600080c0107003449000050f61003040c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 648115332 1250 648114082 648114097
    0x8010c0e0a170703021017150f06030402150703021006090603080906030a0b1f1b0b0f100b03190e0d02190305070506010806041e0f03140d0c0206150f0d0305 69
    0x322010700c2d60320b60225415003004180ca1010646032110030742019003135456039030b01070503901643c541d0075401c00c002228072701c40e500035500405020000404545a00d9070244040023401100303a00d401d09468000c3d940c1c28040c40b8010704904101c1d00140000c800d00500c0c0640c0da005000c0c904160108041c05025000100709030425526031502062548501d086055540e0515460f03074000048540090003103100c0700e50403140c2800d402d200e030000c606d4001c003103a0021036444107030b80640c4554208040d0006a80c110094098000013400300151041c142c0c1c440c1b40310309003030911404551985c0c2e0350700e0302607131001710700544c2011040740144030044e508429018800c0c06d049040c5451501d071180740c00002d8000805907800b403010b01c0207210304c2e0f09211160000203600c0000b8005142ea80e540c070022000c0c8010284281640c0c000c06000760b05041d40d00c4100c02e400d04002901c2107a000a564072401d9495800780d00170094000d04c0c5060120380c0042694015000200c0c103030b4950340464260340b0200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 648116582 1250 648115332 648115379
    0x5060d02090a0f05030115030809190315090201030b0d1a0907030f05010207051e031801110a0b0403120e060c0c1903090914040b1308040801060305060108010c0e0a 72
    0x45552199581c120b44140600540920ba8007440d0a0500b4036085855040c0d40d011210740703488040000510030011200c00c4c4105803070b400424000070074044036240c80354100912800006040e070b0348008440e44003030782450007603809102e918580c2d014088006c2c4070300406403645400d184442400100c01c0030391a0006c815008884810740d40c1d4458010103010120112226500040c5000c103129040100d603211410b804040606000405c120954910602c02400360100242242410710381c0982c5241b22100d40b40003c1d0b400e40d03401d900c0c01c10004c0320104d404401265031341070804c0c11140b075446000c00a01a400003041582c90b04c911807885038002c1d81e00e0341883e1054802c46060418030800c0660f08910030f4a030800c540381051014401c4d907114040b8621002411820040441c003030131401a00400300d01c075641c0030345205080074561032080f500038540e69820002c00100304100014070904940c0a00c00810030010301c96800c032070510101c00810340c820103810045c000310079014103802140e02d101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 648117832 1250 648116582 648116587
    0xc09030503090f3d090f0905060319050309010801080c06040614091008070e0f0a090f0609020f09030f0705030d121e060303031805100e031c05220b0105060d02 70
    0x643da07107900b00510080403a03140d080b06403002000b8403079194442501c2103085c9464a03034101400f036200000c2e288208510b5645860104a80d078030140000c0c0d1002482540d903c80620490420b40d076254081080d00b40081d490a00028011001080342000e1190052869240515081040700e00a00da50303162480702408114183c4c541d80d40c020b801d0044c1810742c5030080d4514240380082d01e007034000c0d02c1d1a4019201c9220320001591200c3c11441600c0c100040000ea1205090604005210035082110007078400504500070130099000b0b0946014100c08035280f9a82c0c8803412500d079111740c82003a405a200c6800d0a07203450003461994225070349048006002d802d6110354078403841044841080099a51405000745580360041c40944910030a0540b0300c044607aa655544649428440c0202a650308400c0c04104040c4203da1005000e5010340018034060b00c5810000e01c0141c4210701041c4e60340b020203944082c505004045160010840740c0d0310380c47d0a060103800c0d03209101240f00c09608 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 648119082 1250 648117832 648117859
    0xc0405060a1b14060f0105061b010e010c0e04060f030203070302090622051b0a021c0c0f08250305030a0b120f0a06050a201809010605030a0c09030503090f 68
    0x1542c0c90408894041d5021032040748032604102e00b03007140686071034012006540140519102c4000310b030702101d00040001d90424034548690700504460f246222554209402d1482003a07100c6910580718500315001c1001c02d640e9000940d9982d0303188002505508140300420141c0350400d1015440100986a004001240441c01300c5010201c45d00b031011688e030381c00b84092440c006000c500c4003100c50901924040342d201003e0b43d02c400c0c40403070001034009405407040143c804c03108a52060b5006400c0b8800c0902d5242c440502d81014903409a20300803030000801c0400c0c0d212030407130442d4051729403514640b51800f0103400742005043d09034000301f42da04141c11030101001480340c01c15051025010784901c0e031034098291030300a8517a008050900341800b044c2000907150b1110500000c2046540e41005140c010850312040900340d8424441800010000d03003280040d80f140303c00c034600300400c01c0d1001040d6007014044c0006042c0798410b20001403541812201d481040d1401403641040412 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 648120332 1250 648119082 648119117
    0x4090302010216050304090b063105060408031c0c09030803061801080d0807050c070b0d1407020607021c120e100e03180916120608060a0218090c0405060a 68
    0x4200411130311503000040c10800d504451141e402c4141c411945d0a02d00900d5007aa020f00341ea181080d540b0400800e080d1030960400060303940010103015064507180c50b611000715860747c002c4961419403d1140c052804000a64483c001e9011001e4613011085411a204c1d1141031f000146419040541d070100c44aaa03c283c0c01200d00a14500004021201a48000508802e0060105402d000040c0044004144080740f4131058035051083c190300d0303061424105018000c0185400c0602604000f40118142d020074403c0c03150007e1307004c40302c80d03242400b0046413a0080c1c490740000500c54042d9010602115001213001c0c00c0c0d0101103070000000011240100d4070740800d8000582d000044482d03c2c0d01c1040032060410740c084645034a1803038544215003030403086002900c100304d280c3e6006408100154845000340c03640740201d41d0301e4500146110007d50204080050289003a48410384500c1c0012020b449071448080e1541080d1408042c420142c01c05c107410414000030382d107401c04550303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 648121582 1250 648120332 648120367
    0x60c07211505090d18150c0602131505181e0405010902040f050901080304090c0516050606120606010e19030813030b071e0f3605030f0c040903020102 66
    0x18036080c000b0703035400d1802d102c51070500c0318040801440800c0852001d01040d2008241c101d40050720111441e10f130341e40007142c9454a03035500409240c804240c05965940d801016000d8030540320070b03e06085218039040e01c0f5802140c2c034043c5a100043c01d07040c51401c0410101007040381c1c0e25501c004000c0d0550000d03080c0c43c0260414880668046400c205680080e1100c04c0200416556001a9414502c2d03e0740c907889076005107001c00e0340f580d0240007214483e07000c907554859420020720f183d80040c542140c03104010354089110304169803010460501c0440d85074003c2005840300f0500804620502814400300066481c41da6540310000020031054030040000f150200c07401002281546046065004007a0031035040242d80405400c004600b0701c00c0c0040150341d400d00c0b60f441d00d0005800c5a03840312031881c400d40340803801240391621185250380d1058400d03809903803440b036498109241c0c0d08c9485004001c21584940401a003c3c203090f803240480901a200161400c08050040886207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 648122832 1250 648121582 648121613
    0x5150712091502100b011b0803041b15020d030b100c0c152303070206011413020a0305090c0102010c02120706021608120a02030103030509190504050a06050f060c0721 73
    0x41e0000903030048000114814100c00b68802d0910184110107d000c3d40e0240c0c41c040c10081c0385160020106e03051105d40740c0000320411288600c820207a0325080b80c081f030700090700c4201e8007600c14090301c00c8165001e40194140c400014000c80d090101800b821120f809a0a0056030b030301d04003150200d182c078039040ca8110034081685071340500c8440712145c010a1050190007088290b41842480341850b40840d40c2411a10540310408010568100058a40908a0b0142503803440002d00ca0301854061700107600c070b12000780603503040c1845c000c0107a003038981c40500c0364016045441c44103034032205900038204240c060b04c401030900d02e10900d0325004070b43d202004e4800b07400114098a081101e016250740c0130700100b809500b1549550b03000b500c18041c03520310030700c11107164000054a60501075400d0040c680108240614100414800000c000314040e550060500c04500586400d00c0000c89000b00b19880062042d1071030f111030325450b4a03080a0502c801200c104000c4e010550503000d41c0c904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 648124082 1250 648122832 648122837
    0x90111030a020109050c0306100608071e1d030d080a020c0f0a0b010e070504060f140d09060209040f061a0c150f010e130c17190f020109051507120915 66
    0xd043c62405c007035117000340340a0303913a00c29030012003009001c0d07a80711030031000c4540c5400c1088c01500e507900c05a42101d00c1d042d19001c202c1c008180014495444116404002d50048030b080e002203075030060549681d0030301c11000c040341e4030b06d0109056400329402001c540f20251300f600c0720300e090f5402981c1400c0100806548003610340005014145071545100d0304410030303080091400380780c0310004d07107070010880c08042030240407c20030b9031000600c0110f401415004d041000701d2030103490020002e402000049008a02c0c103902d43c40c10001d0b40c0305079020766030900d030740c030564030000b80c4000382c19800003015183e01d028105480806244107840f0030b0140346000031141c3c056061411488910350700410f10001981c2c070681c40c0000c100b0043e00001543c21001254444030004416180f6009014012a01c8888443c04400520030054a00682c02e8800d80c0d9490780f0550303c0040168001c90901d200089000401c948800114800300303010040d01c5c0c078280f07110565911b0040c1d2070b48000e0038913080b01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 648125332 1250 648124082 648124091
    0x60504020f030601061b0204140901090c0611100905030c030a2105010e0f04140708032709130201090b0a030e0106061b03031122031104020301120206090111030a0201 73
    0x1146032610789003489010640050115615050004241030361518001e03e403118460b2040701076464a03006800700140410780c00020b030a0030f04001d802801109004d41e5840b4500c02d0100d00948074141443c1030f5082d54006150562000c030124000b00401d1a0498081c030082001150710a030030b001410429207941c45865101e03040c88000c0e0502030007d5008a000740c5003030014440310000701c40d8650000f002c0b49443c08a650303540b902c000140c0d4000e060329010312850800241c1d003070703002000380340500c82d00948102c2c0d5481d101c00d42c00145180240d46500069aa000800308011a18002c40d840c0c0145002e05200ea40c6e41448009640483c0d0381d00000b0380c5030704803c0910142405044000c0c226440d1504c14000e150142c205c06c050742c1e0800904054454051400306901401510074994030510381d4285401c40c516a44629400b522003150070b140c0c646210031542c0381906c21b82c1c5c1241c90a20300d2000c102001e80c208542940144400d43c10301c1807894a482040d54200040c2032075820310707000041c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 648126582 1250 648125332 648125341
    0xa0e070f0e0a0c08041202070504060f09060902041415040b030103080910080903160219090207050706030209060927040b01090b0d11120a0609030806090601171506090402070605 78
    0x45108000400d4002c4040c14084038446560348402c0c41540142c10038031170152185100780c00ca0500e000f030344c04103500c00c0c20413034041041c01801c410071b402c454884800308a1303e50344c1d041401c107900a80c4103031036440a030120184102d00300100d800c151104607086843c549512038021000c0c0e40c01c00e0b08141c4841002190706801814a520a01802d404504000482e0b15002c00707081e540c0c2c810b5946800b020905a4040800c540f9000d44031040388205629040c44152600c1020009422018054541d403162a10000d4424003030b10841da03100002030592441c000440302030000820780f103c0c00c00700c040384e04000d051004a112031050301452241141d00c1c880d514000001041d074610415803445410070314804000611500714000300200f043d83c00c43e01804500002c18101002840003a10260501f4129010160b2104c1841e100f44800c4901c0700b600d8984000448004484e190a1084a1200c0000c034658104000760105001c40081010345801c003500c0200741a038000000849031291980d0900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 648127832 1250 648126582 648126599
    0x30f0106030e06060a03111203070503030f0709060c0b070e040207031d040b0a0521100501091b05180604080d0909050c03041502031323100608070b030a0e070f 70
    0x2400c001003000e00800303203403c1c1500082c10001545c4001803181607a9807031140144c2310450391040e00c0c2080401e481d2604070030700b041500c9600403280300d05a82c145000080049024040203400d89920b81e4419038542c44a0799486138052024081006100d0703100c0c00202c0d150b46600040a0307035440795858162072184043ca072000000200659880b550a04080701115107a24a2590441c0e0003117400e44d658480c0d804070b0001d01c640b0382e0201c004600584403000c840e10115000a03040301c0c1155003c10410b01c4001242e90f4500c60070507088000b6004201c6810f0340b8502d000e282d100d119000700110314041c2d603428440d00d444d03d0119030001060443c9000c10103041c01c2d10034141d01140d207207103461851400e030740c0e08201e104041810241665000c400f1510a0113201074008540e80d015003e4504ca00a03543e5180c0303c1722002c1007083c205c0c030030817440c1e124030240c601468040f1465840105089130500f1790441841d00b000b0004142c0d42c7d1750341c0d001c0001c0a800c101c000010016404841c02c8242000c400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 648129082 1250 648127832 648127841
    0x804051018060e0d061109030105250825021c02070f080303090a030f0e04180209070c080306010309020f04020301090e06100b161103070305010b12010506280902030f010603 76
    0xc42c103210325200070014503258240b4806500703a0003100004e9131981c8440259880c0680d04010343c0540c40c002c20424802003d100800589003081580f810210300d005080b1354012044a80000d0700c2d600640850b034100e20024100804003490059543c3c181c0010042d40d105040180c4401c0140e011250030002140c08900400283c058403025518601c2c061740e08542c0da030245400241008441c0c1d43c1d00e0b04040c4a6107076034909610080c4180003c088034281c403000c1441c1090141d108501510100705201c1c0074507940300f803140c2e100890500310354030400150700074108900b060760000341c20945210f20395207500c01103000e003541c00c100040503c816a111890b06e000200b00f400480740c2c0f05803c0c0004d0a52001b03451900310b003e40c1d503001d00320451411700c3c40c07250b00c00c00c1140c041c07050b0b55010080100642150101040c00c0e035014222014a0745c206003611010f851058025024000c8404004d80c546019050684002005100c141d5240e41e42c100702c1e84110759000340304402c040144003139079040c080c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 648130332 1250 648129082 648129089
    0x307030b0c190216050409050307120210051005010f020d08011503020d02030901060e010f0e150f040f05010612090b0c07020f090103140610030b280c181a0a05070804051018 76
    0xb020048201c2030f48c1c0d00d607a00d2148120103450312050140c000c404074800c006000a002080c4818403203402c000104074160600c0b4066035000c01e41220041d07031110310000c1e0103034034201540d0718000240d01c1d0504150101d150290308104150302000b001c04021441d000071070103224000300005169103045070a85103a18182c1202014240c408002c06c1608602d08409400000da420b600802034800b0b00000c2c0d0615403804000d40003410040ca0010b140071540c00385040301e283e52038040c520400c02d01d10700100d485192000380052045000300f601141f01c0b4024004851010740000070300c1900ca000035452001c03d0b80100c82400e400501c20f4145101444032a80262100d0456031030b413070460303642c1085c9450081404030110340c1406d04ca070b5070074030110201c3d4140c01140c104000241514400030000843c030314041e05042000750001035840b000c01c407101101d0301070524050404140144c101d03243c1e44014420b81360503d041c8400301350f0360f94510b101803540701c0684030302181030700300910007024250551 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 648131582 1250 648130332 648130339
    0xb010c080a0f020a150e0d05040b180a1205030403050106140a05121c02030a0e030c011b0c0302031b090a0c1d1801060f1407020307030b0c19021605 65
    0x215100140c09042039800d4600241000c0b03911201e5074000301e1034074544501c0580381d0002d090510043d0401c03a4014604020b1580c140c61580708904810b0700d051080c0d11034540740c030760304010450301010200029452450300400440b400f540d0754400100c0301581410980b82d13900000381c10410020244502001000d41460940e03c0600c0d010014814104501c9640d0140030f024201080f0300d5002e120301040241211a081c03209184904020b41c0d03508010000030120300090b002034074a10b40000c4444407000141e4500000c0c840c940b5840000140c0b0040448061052b44c00210050f9814055581c810740402d86100d0190441c20801540c10005000307040130920b413800300f024950b40f001e1041190004480034200c041c4410010402801105910080400d079010001c030308190310110b1085004220364a400740740030031030540b14a9206003030f0300a5040c1c0c001c0000308002400096180da00240502ca041d050507000c18584000615000d14280141c1100c00c00304c160840d00200c013000b401c4243c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 648132832 1250 648131582 648131597
    0x120f1e020a1107030c09020307230c010c0c170a0903170a031802030c04110f040e0403080106111f0b030a0f0605010b04120213090f120311190e040b1c05010b01 70
    0x58a400c94070300c1d000e004d1040030350340000008034018040e066441924607801200351070942603071941180d07500320be40444215401c1049141d083e41c80354400758416500071030840c81303110800100b40702e6540085492420312407441c800102045001403001420031740c00e82126540c40c000c0304002d0442e081141c141c200440c0070b150503400758400050131842d0300c00c20fa40c006981484111001031601940800e102e829400080c0441d503003070b40208450040e8480d856022a603601c0e09001c0e02c1c4503078401c2c003c40700c40d4007020100104242e1926405070113a084e003400103403228460082414540001c0040d200c03501410710758402c02015109a90040044600d01f074142800c140d6a400303401d00407203010f4803440b81015401c1d60b45060768400143c10341d010958503040661480c0500820700d07051203010100380350060041e0480501c604403041081d40e10480c140014590f40161103144003801d1a41e0015641e01010215460b5025080d20349044406640c1c4101b0041c6045400e40313200c1e2a0385810400c15 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 648134082 1250 648132832 648132839
    0x5130203071403040f060b0a050d061514010c06050601140d022d040e04080903010c080f06010f090620011d0f010c0e011d03030307030b040507030507120f1e020a1107 73
    0x841d42c41700049601403408a600b6510000203600110950815580710b10342c1c400c0b4204211076544886035989003606080b40c2c181d40c0e2595048850902008140440d90407542e01c0002081c55000c1c0b90f111074141410a07a0414490300c602454100f616150100d960000703400d0b08000c1e000c04546110203891480040140c0e883c183c507aa140258401c161403442018045010480603400b07a07a2021400707402003000381e4410394020030182090755683c1c091440ca0011070350b254411380340071404ca0729680303070340c00b50500d041011600301074042c1c03070b003c0704c00c000440100001c0c00030300440300030004100c1900e9004c442d400c00b650034446d0340c0070206483c0c1c2c5811100384c00e41c1c1d00000c01a0001109003011600c04801008600020b6200b550075507040c040001002207864240d8425101050265420400c40e42c90718000d508075841601c0d108003207001c480702000d41404581022010421184012505a5030004501359042c0c400311189603080d004200080010344c1300703808070100e031099801410440c1c40d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 648135332 1250 648134082 648134093
    0xb0a0f0207080933090a0b0a090317070203031213051b0102120c071203021f02270d02040515030601030f0512030712150305100b03060108030f030610090513020307140304 75
    0x240307004c001020b4000850644669550f01c013210f0000c040c1c803011181c0d00c000c0e40c0300c0103000c0811760004070f54036103c0304543c42c0c3c071402c00420b81c0c40d41540500158580100c5012101c8004002085400c0289103e2030030400140180944100031180002400701210200300290420900075040002c04105004150401c1000200c00f07044030004100c0c200404580d003022810710344401ea41903052222513010310b519185075030017040c9050b558150402e0748503910a18a04d610407201c0102ea012040020040251516034441d0340c011000251070780241590401003401c01d0402d07801a90512110401081405028088840c013000c0c850950361651030942000b60800041d0014074581c5542c803040b002c2c0d0721040c40c40c20710207075401c901200d80030900f03000c1c02c03c003030019100402d0081c00784100000c1c8800b400030995440c00414014070382182e481c1000d002c0500a00300d038480030081030100028564442903403816000c02d00550150b513924210f0005070012202c0e040784400301d5410400c0101245 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 648136582 1250 648135332 648135409
    0x30301030609260408190321020417070e0c03010305120f0715020702041109030307080d090b13060b03070e042924030a020d0b0a0f02070809 62
    0x7540304400107802003142c10300380340c1003000d24501d0f01c4a0300c1c14100c28443d00c2d02000a4002c6480100803103035a03071080800c60751515142d02005000c9445600c04020400b45404802c2c41d01001c3d050050906a0711031740c801410841c40d01e0101d0741d4201800a00000d01c01c40995648a0501c8040903d03652456031303810396800d0705282060303900c2c01c081840d4034a803c5034400ca84103039800c91040f82483c021030301c0f80c1c0000d6001840491145280c515058a0b000184041c0c4827404401409141041203c0d15114803036400702d2211012150b96120800000d4003900001d03020b94070161a19444c50076500c0c001085405200c040d91190340250303010424500d5101c5000e90003a80040300603215a00c02e03241c80000d40c41d142e08030001c11510020010f01405410b900c0d1500458007200f01161300c42202819100e604c03086010b074104d04d40340700c00b1000c80c46041010750007419415001844215603000c00080b608a01c10032075600c2c000013008507052510003000020581502507840c6945511908982c406 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 648137832 1250 648136582 648136589
    0x19020412030305010b121303020c090a0b03061003032001061502030901090b18010f0315030b091e0a06020903031c02281227050d08010803040303020d0c170c0a020a120203030301 78
    0xc0000c7d035076180c1014801e00000b440c4600117860982c071400e00341700c0040581904d222182c0640700311000245150032501c1d169040f00d806440309800841882c82c41500310858619000c41c640d200c1100088031711812500088861155002c0c41e1521080800101440c0726070b4040352946030b00f809622000000d10718408881c1009080c041141143c810041d0082e000320700404015030108040001030104401e80030780301d03503040700540c0c02c80d00030501036410b685280400d1148a80c00303a03412100041140e0300500c410b0341c009040301d08064084442c00e03640c1410018031340b465030300803500c0c80c0c0910800e00040d003212200c0106a0780703034091041c020110028540010201916140000074000303090344495110386140402c0c07075071104181890b40c0d075081d5002020001614400000856003004410f4605a81c0d166024080081d1250411640390051040980703105800b007183d459507900c0720b001452550a0b18001e030103034103010700401c004203800ba4090283c9180300e8940034010394020040300e054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 648139082 1250 648137832 648137851
    0x11a0a0507060e010c0c060e01020c061f03051e011a030a0201030b1c030309210207060f0207050406060c02010206010e011206020d0e010e0303040b1e0103030819020412030305010b12 80
    0x71403209040107005080701030700000300d5510740401d040f072666100981a03912400317402c0c00c0c00450343c0e903000103080348600340c0114250341040020410b0b52075050405080b40c2ea24020004070f16490751030761400d203400030240030032603609111411181c0c4428041c5c18802c041040108414040080100c0d44035202c00070000c3c1010307500d00180d001c1d030360343c013a000da85042c0700307214042041c81a180c080d00030403ca1074140c4030b01000c081c507989824940c0701500f00742061035018001103807409100391584450794403a2021f6000d80c4102007581d403210302c1a00010069542c0d0254003000c940000ba05091040c0c100622036950200103000340d0811300c22228482d40d1111005944811031120710004245040c80740b5070342d50a007a9000340201001001d103006900454010540e07441c2c1014600c000b1080c2c02800c0540b0f2140d00041000c42d00805019034040404080c031b500040c0e21a00840c03c0ba486900720380ca4000e0301c2c0d410301040c140d041c41240d000d404081612840d040c0c4800348201c0c0c0d0070008142008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 648140332 1250 648139082 648139087
    0x414070816090b030c0d0f0608010212090604050a170c010c0806130605010915050c2e0204150806040e0a050d0f08090c040c050d15090b030115050907020f0303040c0509011a0a05 78
    0x604200c0c3d402072a80f5800d0711f0040003101e44485155010b9800900e00c01c411807001800301c1e141d10404a8018001c6902500408030103140b55076440300c070340b524443c82a9400061001001121003801800941042640d07520001c2c603000040011001c2a0603648400300d2801e501400a81d07003000803282a140103d0504030b4006664904484034440d030b4801e001a07010310000c41c1000c0c203c5034440d0701e01c03070310541a220050700312190000407801a403043c2c240700c1400318040303ca014021076566800103400780000c50088000d140b071a1070700710110401c031010b83c00000a104d225a2120042c1d0700000585000c070060b0420b100c0d02daa41d01640703205603115a50351070507a603403940203d00b22006661245010701089a540c600c01a240e40640b00d240301c07481c14000b41000500e0107111b21101455074051100215041506101c260600100000158441c111000010407010400b941c40303a4419907503009814100024030641440c10b900c45141e400a0003000243c010080b820f07210b501c0900c2c42e100c1e8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 648141582 1250 648140332 648140347
    0x1140406030c170d0c030c060b0612090c030c0103111e12090106030b0709030305190203160f1b0b0d0f0b0d050606040506010e03070605090414070816090b030c 70
    0x500411850744014901e180700c000000342c1c805004005403018807078900780d0b8005006982d0036201d005d010100180000c0c0d0180e000000500140d2240744101000750040d800c01c0c0310390444086e440c03800d540018003584001c4001e040390ad42000b244045250a1030144034150014050b982c2078001c8005281000d58032034031160385801001c09443e003e03041d5807240c40b501c0c117024000d50300a01013400705840225003800040e42190041102400301c0398075949591401605810350540440000006021800104031202e2508501e01012981c00d00a40400c04080710518001c00700c0000d045503144000401c410402c4404946d00c25940070700c00c01040030842c500b09515441c0244640e0301030030340c01070902c0010010b000b00068000d101d128260740800c101d407902e100650b4101c1c2403100c0164180e0203000103002c442d04c40c10150001c0d1901a0001c5500ca80304940091441c50485048000440c00000c000801c2c0c0c3c0164440e1940609082100302c85040000442107813100400d0306000701c00024003203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 648142832 1250 648141582 648141589
    0xf23031b0c030d0e0f010c08011a27040905060a1a090f0408070c0e01062f0717190602070b01060f0906081f080d030c090513050613050f04061a090114 66
    0x303044d40d8141000030040701c41f4050020304108801e00451420310b030461105083d800503101110007900f48241c00f03020042c60b40c000c0c64030010750307540015081034850300f844000a008001190291044000100707c080ea100440308110240858092151005506001c100e008070b51003180c0064000c6091580c80b11582429030303030315000303500c41442c04c0d81c80400010240ea00030049038100801024401310707200c820344008140703081b0072910121504520b004002c00c800786821a03001050308401d86940c0c042841012550400408081d40d9003500000d12104014190342c4141c05000c55003841700ca410342d000c0e0b0040c06036806000b400b05010203000801c0d0508070000701c41070032000e02da03c10280710b41c0310302020742c030b0781400180c00e00840d0424100500b103e02a0b00b40700252a0060200b9929060800081d00074280103828603400c0200190b02c82886585401402c1c440c00780014180082e05151500608413105480300c0406503480907c0704070965107418865045414004c0c2c40d06070b005452000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 648144082 1250 648142832 648142843
    0x40c06050f0f1c0e1c0f020723010e09070507060504110d03090f0b0703121503080f04060909050c0304020922110f010503160f23031b0c030d0e 63
    0x60000e022400306100c1114000e01c080c0f90058103403900144101c0c20f0540b6502d40e1a0708204450b040c03102d81c82405407206109600d040c01041c058812121450f03a10071840502018001c0c8241004c1291600380441e56005211026003820550360710406d0714101500804a00841100500046e10341000c80c0c10f00c55480c1e008025090000c249504000c2d840c0740180100d050740c0300382040b50301d02183c0000c00155480a840b126500b61303c1c2c0503911030b51000c1410040c80324401403030110002040210102d01100701800c042040414125600c6041040150411172154420304205040c0070821140410101c1500e8001d541034807841804d841c0d05000c1c1083c0c030001c0c80c01d0200590104e442200344154011100d1750740d82c055625241901d640001112a40b00071100e500307882c3c0002d09000c00c194412034420410740214900b40351032403a000b054584007103008409080d07011b000b100b4084a02000004514000480e044007071601072445002500c81c013645080c41892a070303e640009000f03005210 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 648145332 1250 648144082 648144097
    0x10030807050c182a2514070303090812041202030c15120603060c070f0f0218060103050a0e062706010803190305060d0b07021e071d040c06050f 63
    0x940a644691802800681d00880d925001e440300406080148a5400004280d80701c0d0041130502d401c19003082101030488019501041314041801c0c20045010f5803010480801c00c0710282c030078289141001801e0710000e801900d0355801003503950640c1008402100e0444200c844400106507080c00080e0a00b204bd003451030308540d4128890f185240018024407031040340300c1e4071f02d100d07031151000c0c590390f840100c0390503480a00c104441d402184d00c040315a20041d102d00d40c0c440d42004168007240d194030b1818400a0070003201c400b44074540d078040c0502e81d40031405141c1003100e40300c036140080c1d40300009010480390549900002c2e0900c0040400e08180708154000ca45483d44d464030b401d5030320352046200118482590804e0940c062090145500458008142e400c01e04020303180d00c003000e44050003103001d42c41094213201c501310004c0361051800c0e06040c00382c14142e1900020301e20048500900303d09191240040000048031441d00c40c0540f0a640340840d00c540070110f01505c00d110703121 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 648146582 1250 648145332 648145339
    0x1116090c030b1f09080c13150b2a030705070603110c16080606060309070b0a03140a1407050a02100c140708181002030a030c020106050a0611010c020610030807050c 72
    0x301c0d4400c0b03c401d00c014111407140d41c0c4008501d5500c685c515210413000070b00c5035010320100414446030300d060304020385103c2c030b0f644615180c1d03654544040055002176030004003408000c0302151194003800702603400400d8140510f18040c69a82c07038a4540c41c0501490013071541c3d403c1154844119901900c010145410807200c1940c1e60000501708131079240306501541c0f20302c0001814034100b880c01d49006e02005c20041240038204184411960400e109400800d0b9403100308480d07a4a4442c8124001c40d107031040094a4012001c00e1221808010014814050100b09060040d680002c1012000e681140c00140c90110b43c1421074120265146680003c1c0b000b00c0c03800c003840080f030028002000e1001517a8100c0c0201c00c01c1c4050405000d12650258206001754101540a50801540f0a0103440001004c0d034a03070f00012210102070300702d480020050540e00d45003800c02d1007850407108244c0010a5546440400030300d078041030780801400c110780400c012080010801030402c030600003e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 648147832 1250 648146582 648146599
    0x60f130617070e06040207020102150403020c040204030b07081501020c010e0a030f050f010f140f040f3801050306071b060c0c050d0c05031e1308030a1116090c030b 72
    0x1141202d03540e0b1240d0180c00600420340e004243d040c94103100f00c032880350303041c0c002c1c00c1440070b8840701d07629084000300142d080d8000c100b0280c2c410703a20fa00c010005144902d00500e10b5090000c070081c04000300a000090590049480411310307070b0001601c0034000401d28110800c0d1607035a0200da500249a4402000e11003007151000802401080020507042d04074020000d40b0900f50600b800e8901c82c4402403180d140d250302103140a9000a1880d900c03d0080c40030b9012100c00750754100c44030005000c03202c12040c0e0516000e0815405034482ca80b104040848484654180400031340c85800103004442031080e09144040f1041c9500660310300705401070810014100b4140028218110321401100c2c103003c2c3d0743c05100014007616111407030541040046080808001810800d02c032107241081034483e0a001030013001200e4140800138046060280d910392140c20009010254980700381030403508088611a40607403000022412103040b820041450011507500740e0040a11580307164002c45030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 648149082 1250 648147832 648147869
    0x1d0a09110f13020a02071e03020901060e0103090f0b101e06080403020f070602150604140c1803011107020f0a06050a0c15090c0e07481407050108060f1306 68
    0x49220b20407542810040c8990400044006d68031f801e40780002540482c5000051091610942640c03400a206041c0051b03101c80c0c6490703911813041786c40c0d03080707034141c1e01841000b01884840b10303100c00800000d11540300300398041c482c03814000d469000b44010001c215000505240c803c012115246500c081a03c4107d602c452000b51907030303540c032244800045940c0c04202a0304143c811b1100d03501010760740c0e40d0651a141803e00c03443d40300320401105010b050040040310f650030300c103103042ca51401c450349564114070f1040c00720710224174a015100d903850302410070a290b045011644400620714003d4441e105510740350821342c0d180001c0b854501e10b810f5a0f1410031191182c000d05585140f09500496a5140d00456804100c000c409580c0b9600d040d00b1000304411101100f441d0011184ca1040f021400e80e80d0300107a119201d040d281c000d40a010007001f030009105041c081d100c00c1ca440309291904e0f034049094644100d03460740c020848140d480e440703080164400d2028105c0c402961020280 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 648150332 1250 648149082 648149087
    0x813030503030403170c0a0311040b0d051b0a05030f0604020f0304030203072a12020d080c0d0e01030b011d0a0302090a09021813150f061d0a09110f13020a 68
    0x204903001c1340800e035001800b00d004410180400d05c1040070000c2d5510303161400074202c000d0724910744085001c000510000c85c07000240d001500000d12200c0d000222490515800c0b20000300c80110b1f52041d01007002503014171540801140c0e8408c3d019404000661a0000440c0c002c0c8a00e001c42c040419020040c0030400d40c0c044020411940690050758402d17030030404500c8000c0c3c1c0c3d0540920740e41c403540401c101600c50003056248150000f084400d40b10450303103c0c507031103911804002c42c0b0b0307401c410465521031703070072000c110003903003081c0383c20040000c007100060498050300c2c0c2c80d5003001c0009040750f104c0e82d40d9003010001445d400b800c0c0d0480c0b400d10001460207404485402c0b44a151400c6801080790707400e00d4242d2160076142806206c032070b072350b48500490380c0b084818404220340340c803180c8802034000d011700c04c010b01042055a440d1110410f0032414948040e05a02d89541000003090109401c074070501d480c3c540861b4219441602e08001403801d0400c007902e5802a800810002200c54 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 648151582 1250 648150332 648150337
    0xc0f061b240103030f091503091407080a0c0605040605040b0d1d03031b2a0f0601030f02151804020a0504091104090b0306160507110315040303110708160813030503 72
    0x307104e40c40d414420400e0410a490f229000e020740510a540a1000c4841e14483d400800107280182030b0340c0e1641c5002402c1d641405a2900001e07080d07032002222500300135400202c0c2e401000c140c0381c92400d1505042c0300030082d100d60311590408540200b12080110f04940c411030701540900301c4044600c0003500c14a860f07400c21649000d81c60040361000c03080d590800201c1e00310041c0c0f000c011080f61111502003404408102640419100c0d41b003200c103564000f0002176001e10b0051100d00c02d452858410805401070190725460b610600748802401881100506420b400702110007503111042e000044a082c0900d51010444508040a00c0c00e001d201400800558045440900c248280d0505260766114161491001d52031f01c890088a014400c00281c03003038903c146d6512084885100001c0e107824580c2400b00d00840602c0140000c042e010722072102503c6641c0c400070300389800c1d5102c280d043c2c051030600b04820f00c181d25000d8200051942280c4081a040c116214443c0c0c90f1b040140d52038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 648152832 1250 648151582 648151589
    0x605010e01050703090506031005090408090405250806061903050a0e01180609110d0803071701061403180a0305180103021303020f03010605060d09050c0f061b2401 72
    0x5001184440c1607544a00201ca81c0c4503055168180018030740000e00149a00050043d60804c642c030002090960700c00841c50702503401101c0058982920300d0402c030032614050710303001c80c0039162447c012240300801607550a100c0070742000303240da82d07910700811818811081c0300040e11105440c400d60450701503009034055231800702e04000070310078940c1050880d01004030f0801244526100800046c09030740041d42594495003250f51011590400715105c1720000004031540d40010082101a9034420060321000f00c010720100081c0d451328078040d00c44440e0504507008410000b0008201c0541c01c13441521158800048554a0f207031810b005016801402d041061980c001c40c80c458150700c6402512100401460450405e83c555801c101000210102c03490b05552600c000003203a9840e0b40140c100c5c40f5114401091041080c030780070b420306100314a65841501d0390035804072261100300070b5484001d0070144c1309501d4195090042e01c0c0074a0000349540105001c8802900d82540301c195604a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 648154082 1250 648152832 648152837
    0x1106070c1103210a0e06030a09152a0e12151807060c06291002070b1918080d120e0d180b04031208010501050313060c0e13060501 57
    0x508074800c0030543c03901c403000400300b4801c940d40a1050806888001006411010b003001c2c100d489215004c121190801c4aa64100c9131341c940d041001d010386401e009031500c00c4058104a042003941000d00c00c80d8101002e5450103412070f0202d0302d402e02a814030b242d918401422080301d501d200000e2a510420f40100001c23000c230700e41c045406440c9c039020603031000d14800003038151941130007000c40d109040b0302025141c040d01c902142000c0041d002088046040c00001c0c00194559001404280d141c03413240c207404c43d40015010000c94109406417582c071445c2c0b0081c0c07080ca00b0328a008542c0346086500c007858201c072403000050390702c400080c00f490383d01c07990b2907004498600c03904036022901d135544140441d80110340c0d04c24086204003400c03090a0380c0921030303401705a1a03006059a41d00503030030440741100c141d1032140003150000302180c018407091030400d103540742009060100c48240d6000401707d80d1500404c100d498091103818800400181400030005226440c0c030b40581500c1c0b040350302 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 648155332 1250 648154082 648154103
    0x90b0906220302210d05032701090c060f0e0d0203070b03090f070501080601170405030c030a030e070b031308030403120c0503061f05070b150a15090f030c06030207031106070c 77
    0x80080c4d1a0760311201ea001200041c100e4180295411388a60740014046183d0200000c04603021009202101116a001400000e1584820315050712403101e00e400001c03d1190a40c1c620480c0c603030000b4860307500c131401d45d05500b48401502c040f034a45451a04845000d00b0007101b00304841000003204151510de00c02121600755a81005407180c4500780c44060000b403412100a0241c2407050100742c0181c4130701c0072286080703601d890140c11754000c800810006a101e510006416008005004c050045410101c0c0b40d820f01d007480c01d0540c0300d1b0720801007080c50044005000e15005105603462184491024040c207010544010482d91040382c4071841040c00c01011b03803000400311034074820380040e5210185000085d84130340c51000c2c1c005004001d6103450b80c04003a420f884d0040d42000a01c05035101100c01d40c032800300a42a9103003600541d0300d0012101d002c00c00314103e03c0c00c840859030b181c100180d4902035421300301c4506005130504240f500c40c07075080c440d110b940549e049809a0290b082c519 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 648156582 1250 648155332 648155359
    0x80703050a051003020906030c0a0b0c0715051902010f02070606030203060f1b0c0f1002070c09050408071205210601020f06040b060405060303040806010e0f0c0901090b0906220302 79
    0x4215074054800c08071a803c411814801800c0200c6019009074008045070540f440110000b40d21aa440c0c000c03d070303803600100d03031050590700420600c405003d11058003440510b0700040105a40110002c03040c5416001d01c804480354000c2d03200310609049200705541e91205418040003504040c4022400791180ba400103840380187c0310303840c2c05000201d200d01c000048907011008960004018000b0700d008001020314000380400140d0441071440d0400342e00d0b03101d1810030311500744159003c042a40e052404010004038032004641e5030136032003011154041011901251140a090403620b03400d1103c0783c1440180b205102c141d446290300360b003210600304216031002d4071594217680040584010b072000c542585004d03007040303a104034042c04603800d1a0f610800145000001c5e0703c17581c1076600c82c0050010031a6a03180e002e83c04004000103600d40040c42d0002030400c10188214014108081600a0266a02c204031076414082c0341100d140000945c110100c9056240b10480c0305219581001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 648157832 1250 648156582 648156601
    0x120e061602030309100e100e060601021905100c2a02090106020a02090c0702270103030207060f021509070512160e040503190215040f3011010908070308070305 70
    0x43c0c1c0704280b60801307802c170b03c1036040120024000092000031580108020701c4d030240068440d401000c1d00d00801444c05050040001e82440408270398080c590a0003003440f40450300029032a400b8001000300043c8a071400501180c429030b04803035418187c0310b840c0400083c0450301c51509200c1d8000c4403c04040d0740d80d0282a680c45801f01002908007400c000081c180300ca8050103006000d0000e4012100600449510408485000f40011007490420018414154100200005003d40e0305100c109010075600280d44d60f598a1911034070b1001c1d09002400c00c5005002480003004090590124804200c1d00c0d280c80710082081081c2c0e0060046001510787d000045c1c80d402103400101a40c0360010071407082d10b54400e04103075807081d07100701c411a4011103111340e1114450b178081c90445012800e9807424600005840300c5164a91180b0b1a251110748a03500c1283c0c248501810164804920714801d0b50144c401345802911880000c1418405c0c940c00885c010300c00d81c10790f5000c01041d176441020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 648159082 1250 648157832 648157837
    0x90e040b0915160c050114040b090606040204060e0f041506031d010603030905060c030913061d06060a030e0f0304061116060203161401050a0e1e0a0b07120e06160203 73
    0x34180303d05900d510044102e030084440da40072600800c0082007032613a0f5a08910303200d030181c0c0d04450010a4104208410400780301240d00010112001d43c40c041c603044000740702c0c0400614491107895120212003e0307030b5580c1e10004810b4003c20a4001240d42c8100c00790041c0107501000020b0042da4078691005074041c03050505480d49511036605032401d240030b20029030084081082039100030098046a5074071a5084610380c5444600401c096003024041c8010341e108694544080170840280f100f030750742d100b0594001703100c6403400154124110b0200351a10703003851185a00c5010004002c0f4400d5480180d0030b03224800d0030200d6101c071a100d12941520b510912904005820910452842c404441d02844421740215568071041c00d04203885400c480044d03d41000740b99a9401989103584188000490401c040c240355448401c0ca007030081d02d41c4600f0030001e101c071501e280050b40441c000e15644210b841a80f02c10815148281081035842d682034a1a1007122078100c01c8840c580c1c400000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 648160332 1250 648159082 648159091
    0x20a020d140318150112030306050607200a050d0c0503060c0f07061104180c0201180b150105070812010819210e040905061e0c07080a090e040b0915 65
    0x2a094a99a0303002503482d00d40c3c49142d041d400c00c0c040e811020886440c046840c6000c5c088901c0601c0369449549809002c54129901c410b018560500000300403403d06201c0c4187c0207820341c42c2205c51100f03400040c14044654112036032111081c4440b0051000c0d001906003aa8815800c494007510354094000b42406403d0080119603403c000450008807260407007688a480c1460b86802c25481c1d60603110a00c1d20501001c0c043e40d6528401280035609001b03074560310728080c0c03a080401c009620388607800000100205900705929841586a0348a1000c0b56001500800003c0d140c1c4100c808405443c1c50a101c1d1135464850a00d251042d9007000308aa521503500c1401c0d20000901e1020010142c2c101203820710a0040c0955085181d807110b00403c0b01c011701c0381d800381c08030b031030310340624100e1017860b0440c850918114810030100800307800071910aa50041105501c0c2d5035103503400c541e4a03040d0b8215004d001c42c001c090000308100c3c41045402841a00255681300320410514040345070207c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 648161582 1250 648160332 648160367
    0x90209090a230708100905010b0409021e0f04031a060112090c0503030c07050405090d020d210216150504030e0d0305070503030c0405030f010b0f01050d0902040609020a020d 76
    0x1010401c401c00e00e41c4001c8000d240c01c60103a0368061030000b9403041880c1155072401154501d000c200b003201d000341020002c3d000040302000355504020072209075020703a019220066a002505090104401040c041c0a1032040d05959461012003007840380c0350050311044445c0003200d0302c01d92080b42d4820429208075410783d00d044100500065a00c003420310300000f92079200c00f64102103140e880900c024402d88400d4801444d1051030001844200d0380c2c020500c50454024052034000346a002c242300120650300c0c500340b826000002040c880b070f09a1029044082071000446440980d1540ca41039002400f0b40800c5084601e0100c00720150341017168000c00080c10a0f6461060340340049000f01d009000b4542039080c5106d69440924592040d180c0d1000103101007800c01c11840e0401c03021481840400092000740d030403502148100d9204001581844004101d144010459510401c8215001042071003c03d940315030740c000035841080420018020695034582042c0075208118034400040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 648162832 1250 648161582 648161599
    0x1005040e04110120061518070e0319200105070c2606010305060121030219060b0306131709030a11062107091a03070e0f040f0f06090209 60
    0x2692042d40b034103564401c180c14450640300d180d0f0b8142100903e400d039941e035400140030505209817014030000c2d040982c0d5110310248004810507a5440b0341c4c054000c0001c0c14611020345071000024240b10000880c0f580701c00f10241014148108041c1006000d81c42e22109a0990b0500c40110307010b12034140050310700c02c0001030404c0100ca00d00102c1c107082801c40120f1205000c18056182025000c0e0b100b682c495000e50018042c031448203943d151440c0c40310018003a040300e6680c0103502d0f06c003c100344100d072440303101150b0207005407a001000c0032000203003554a54900081c0c3c2100214503200155404040380195080391740300c1d1421103000340307001001051540540d54030303044051011040b00e43c104005011070320a00035110030311200f601d0f040345c808080c0d20744030100414111140d07100c00c405001a5a4852006d100c04080741d8001550707250060707620026102043c0c00c2c140d607500343c581003817910340210364a18050780b040c143d0041e110428403100b955052004140c0c0204829994030a022 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 648164082 1250 648162832 648162841
    0x5010b1207050f0403050a060506060310031e0b010611010c0f1b060204050a18110403030f0c02210703020a0b040807170a050319080a110301090207030504090e0c1005040e 75
    0xa0185640c80071072882d05500e03020500000b020f40b504243d00846507075003c0c407c0303041007201a0150592180e02952180d0130f6244c40008040110990300c0b029214410b0410b0071b148602080207100c000c640c2000901b6190b5a680030000c2000c1504c445140d015407070034045003c039500c61030641070503c54903910b40601c035403a030000103080aa0305404a07801c80d403c100001e00d540754403014100801c7c1c90085001e41c6118150450243d600d03000c80341c03c2d5038074100002c0c0006600280600c1c5240c0d52450203840e1080184040380500c0c003d03840c046400c0011594103412080009020000d0b244280e64400781a0364459000c00d50380030350300600005811204090010340710054003241c1c0b00326603130100c861100494030380030705562050301c034403451959640110306025004112030340c2250b00150104928444102e000180c2d0006020340c2850903000100304003414480c0c0240c034050980c000040001e03415000003599680607010a042c099200d1500030300216000300306031070456001e901003460b01e81c1c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 648165332 1250 648164082 648164107
    0x50f06190b19030603061406100c1e0f02030a140705040204241205010e102405031005031b010f18140a270e0106030f0f0f0b0703020a08060405010b 65
    0x7040c00b064042541d140c00020100301180100d01c80d10302c0c0c0050340300060410401b40705030b10414200603028071110300c0d13552000480900c038443e80e00100581059004e00d03136140110b8144003c9001039414824590a08280422001c10040000e41d070713000c0301c48060b501e20621087e40624440c0c032955911396200d041c1c51580e1005610708400d01481c2200303240c0346084821044030380c282c00ca12405410101008150000070b00c210005d00740181404805002c0c0c0902240c000142800040400c4070101c04070700084048030440e800343c00001d05a032510f140902d0501500000521504c1c0094244500c0e421014051064041003a8451780c0d0414903505103a4a00c3c00085914252030308082a45000141003456005000344a58962004299451601009001e6500b14048424181d242c8001003001400c0111024400e032744c4030100001680550500040341c0007410809059034510802b0040040e0b0300d80e006143c07240c1e81d610390740c59644455061100f00c0d130003400b84003180041000840000d14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 648166582 1250 648165332 648165367
    0x11410080a090809031c020c01050c060714042303160317070c0f080d02010f020c0a1e0c0b0a1b0305031306240302040b04021e03070201090204050f06190b 68
    0x24010f1080c1440e181c2d188002c00c4c43c0900070414201c195039040300071011b0035814441410104d03c01d10f0500e00301100d00707481907110396001d400003060140301600150484901e90548000f42184c4407510414906080c0026200c085080784500c240a04151845142c214103001020b0704e80000c41c81114901c0b80c00025031a5100d5402036654499014000407082d2a070040c940241019202401003840301050103400d440001004005d141d0047c003074000001070005003220b81c6030b00040c2ca860300c4454150084075413625078801406410740404040b80b002d028000600903095aa0768558400140c1c450042d881c80c4c035100018000303001000411040c158010342c0001d1140500ba0015003c4c10100003081e41d8002000701c00c40303c8034852010030035840d15201d044031440d0152020362074010610340c607403003005591007100449d11000c804581c41500c00d50100d81070756800f40c020011400e000e41008020702c0d0860751544103504d03010154a10207817440700081101c0e200c44140e810070804a12400803017 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 648167832 1250 648166582 648166601
    0xf030312020f13032913020a080703080703180503061501030b0d03020601080d0503060f10020a080f0301050907050703020d050a1103121006020a030207090b0f040f05011410080a 78
    0x46800340300321103203030314100002c0c8900d0350790000c2083d8007440d5152050b00032200c440d03542c0740c40f007074134040e0100c1030260101c42e40e0280c9464100d4400d4200c92001030b5400d07585800c1011706110344240402000000c02c02002c0160103900c490320325040c0d03030072340300c0840549000303040d090341111000ca4040302e1040c184010144050501086c944050390104214a100040c2540164805001004400414001910341112901e4800d18600e0120045006402c603102c40074000e6281c4109100301e02e10070b005407047d041d80700f410a0758400325165551007981080c0242c03845528a01d01281090b40501c04840c131035035043e0058400c003150543c0694598000717074810070900490b4601c40c0da20400500c0280141c5038031a8124890342040d0002180c50080790b000541558001c403103200c0400e40002c1d401c02201d0186401189054000000c0742d0410310b01071295801605144011070001d0303090b04114142e403840d866074055030001400300f0148500200700400400c10040200741d2298107608031980d030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 648169082 1250 648167832 648167867
    0x312020424080702030a020c0f03011104080336150f0406120f0605060318010204091802090702010612020d050316080d05010608070503070f0e03121c05010f0303 71
    0x40ca940d0381d00085641441148410084040c2010030603515041906590030051070320040d810400d0516010350346105002c00c4a1245a0016400040d0780d400d411003000b41ca000850291a01e98510301140d50b40c200c2140d444003441c080c913240b8810000503407506d248440c1540c44999019240040c01a01501c0c074098244800b81000a80c2110301e99000800060041d40e0701c00900000c44480d070411500ca50100112841c05c00f40708002c40c3d500c040a0329084030f00081d1080b00d4220a0310300034020b11641e44050340c880d041c80c00202229002040b001307078940c002e4600c04219551007501702d081f220580101d50341d880b150030048015040005641a050344a6000ca914200d41e1800c6a181c4004411046403070b00c50026020341d2482d114000c0c0c81c01883c040c01c00589178145400c0190942c0001030a841c05c01400c0100da105181c4901314074082910003a0582300e8845a80011850303c1c0d1140b119108480d000c07c2401002120074461541200e0001d20010240d40c155a41210b0041014500c0c0c143d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 648170332 1250 648169082 648169087
    0x203060d060c20070605071416030308010303230a0e13062606070516051609020d0e160902031e09031b0a0b0114030a0512030f011a07031202 62
    0x441501c201c1c0307030326150780e10340c0c0c844059818007484501428074543c40c2c0760b40003080d0810000d6004000d8680301c40c0d22281d64080825800345d071a141072a00c0141d00c568000e40c0d60000140340c2c0000943e41a24082d07030f1480b001c00d0004041d020464207451021003c04810051400c81e0340c410012190400e80040c01d900100700c4040c081c000390b401743d4004511800500c0384030088401b031540024690b0300070704007610b49468000c602134014010b8440b45029042c0c1149105d0030001d003404003004032841000031554181d100c12442c3d00035002401c1a05519240c0088030114501c00900c0300c00c0f42c1c107184c0070300c40940d00300700c000400f0350000f4018100020a543d0849040e0404003203a81c0315003001c00003103881e03115880c06603000d11000c2c41c000e81260001d81131180454158120300303042d074460040400a01c80d940340407920303000d501e0901610341e009442080e40d981000000850045007040c668504caa600d50520a07018407821012514010f000c0011000182c015400070482204040e401030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 648171582 1250 648170332 648170359
    0x2010c021c03150806070306121212110a030504120e030a1202010e0d0221030606070b0c1b06040203060115091a041a220f061409060a170105060a0909020306 69
    0x1074120010b412000740b68000000300402c1b6940b40c8958402040c185a4035a2112007d440f2305011445002d4144208812190510045509a089624101c1c8116009a914070003904000d00511068904a070b21440400102160a110b40e2008086650040142203441c40313968848003401581782005007903540301c03410041004c00c01c2c0909001203549070040e0004a5100600c00c000e90012001140c0d0140d050040c0480303a203c0ca001d50b56429413002d250411a100d0001c0754155000c1e0440c1d81c541092001023041d4442c030b011071074070b000340d109500700c62160b601c400100180d204c0b10030102c00066060001003155000d50003412b04145259800d40740342940b158481030040c8169900d140020030000f4100100000080c50300e0360b150602c4485001c0703241050081c00118407580b1440080042c0d08054800c0d0400b0801200c1042c48002e240580d16441e860024181d42008400c00030380c48141000001d0905003107080b10380401480d5034144026080c1050000250405052690480310545111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 648172832 1250 648171582 648171611
    0x80d11010e07180c05041a0a141c1401030809090a0603052b09051509040b0a2709050712080712110706022103191e0c02010c021c03 58
    0x30010f0b00a0a16595000145003045420344030821000703010000b003000b081100400c00c01c500507100c11800c401c159100340d1010112242d21220f04c00c180308090000b4007599011030304400d028840304031034083c40b00784054608802d80d0309003488082c02d920020015a4010301d011090f42d030348100310100006400741c43e03480c1c00d4500011a1b80c0f007a000303110f40c5403000c2c2d44035640c0c01d480c42840740ca1500c201d0450800022900c480c3d0b1003800e03013000f80d002084000c22503441d50004050b01c0c101503c007040305c0c1d0340d80340d2106110101c4d290380418403000c1c8500703450719680b074010200d200f41c00c00000c0901d1450511020448a55484e0540e1040014007140f800520b400e070701c0700c0001113241d80c0ea0428100400f4094180107840d80a41c040d0b51261180ca5545406110308018201c0888011500c176550b02e9052008072000383d4015070744914002024140300e81040c00d40c400c00b44041c20411100c0d02070082a802c07550b040380c405000d6404813080c0641800800300340c144040c82c501e030110300b9024000c0c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 648174082 1250 648172832 648172843
    0x41502030702090f1303120b1903140a240b03100f0b10092102030a26040b1c0f09030903110a03170306040207080309010b120106080d11010e 62
    0x40050308009480c4055240401405420070000103040d4203a04201076441844c045000b002030600003082140d40600c4820362101c000000050034040003011a0108069100c800b404100c40c1d610403071450004000f400a0b00c104c0080e4014440c0e000f68880c4039071901c0085c0008400740340b1648900c2601200d46092001c28140060000c011810f01c1c00c17040010151504141c1440c05461003281448040d43d1000c116811100030181c900c004841c1040b461004000010010b0340500c10044880d0801c20b22065800c6064900c0900030700f599264108048144601e00c1139141062050010100800c81c2c480d0060f28010181d4000460309444008107040c1c84029009802054500b1410424001c0070800d01d124034604a503548215821543c6050600e0405444480080c8010000500603115035045401c1c0c903800c02c1c0c0c220b0312860f1100116010381a8082c1490144654203450359403400140120010303104580c02410140c14031a0f011202007685000c02d600d1992940702990a1950034010b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 648175332 1250 648174082 648174119
    0x9070c0204150e0a0f0216030c050708030a120b091510020a06110d05010902030603210405040213081e1b010c020904062313080a1106010e01140a08030702010c0804 72
    0x1c0900540c0307400a180c0040710981003403c0c2880c6d00401c11089181c003424492881c1c071b40d0504182d00103c05e9030401c14600318058002810740e10001500403511900300313040d108a90484802030100c220f1200600074002000e0707a81c00c016070802e019400c158907103005002c6031800244100e81d907405043e1240030980d0a180092a51100009002ca031041c030b281c01081e014020b110700c19803450404801190365450f81c030502038104810401d180000d400704c2812500201801401503403548408880d0b800749c4030151041c1c1c402440b40c1c894503000c043c00c1d00c481d810385403040c0014042400352100c40038841c541d640c009504200c4144561001a55441d01c0140110f000d8580000c2c00005042d1099001111600c4011507502d080c04000d4840b503031501008405a018080c26243d014020042d14024807401c5004041d0155400106504040a00b110b049410291201c4016030b040b009001195180703000b101c1c4241c00420842c00036501845a46410078032404050345000e68801c2000031403d1003d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 648176582 1250 648175332 648175349
    0x20c0f061006110703170306030304170106140916030515060408010b1908030403110d0f051b190902090a030506040c030221192d06050f0609070c020415 67
    0x1007081c0101a403120800303072102840002400114103540f03071001003104801050107107510020001c0c13810b84080c0300355001084405e0791840b843ca00300d0b0b0018017030003ca014440b03c0c03203807041103d9036500d080300d10140520501580102000b8191404070f001c0d03c001080c2c0841c130a1920100c3c07007151a01c0004000034400c0030000107820554204121008508014045214481010034071121001004460840f41c1c0070504a141a07441800b2440304c21800b0000340c1114010002c0d5800c2c403002140c00b0359075410941541e0616140b080401010800d802d1100c581140a050103101c64071072a8010b041806004007003a810b03c0c0d0f01d80d10a0324095040b10111002e02070080c0400c01c60a045550062011100400305101c4040d42c01190359071120310042a00494048080070a000b09040d00b0380c0d40203002450080658010041050718490b444001c5544070700c0e140000d51842d0307002c981c050080c85d004140843c192200081250201020101a07a1003952200e0304d24140207045020b000510300003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 648177832 1250 648176582 648176611
    0x30c0a082d010f1212080601020705040603110f0102031312050a0209010312020609010207020603070f0c05070801090516030c0b0319050a09050c01091401141603170109090201050a03020c0f06 84
    0x1045145114070390f0f00c42c0544070b508544130340000c0e80c050424240d203111450450b01598401004074900141030303101a030024500303d400701c184509804210050b8000f5503042c908030200100483c2d5038402c0c2c100320721420f203d44000344030400c514000c20314500d01900403519030764499000210324041c207034001c480000390025218600c1d42c06001060340b121210008509011503500400c01034440107080104101c400c1c07417081c4100780079002d5444119000000c44207160b488001d0744d40200400003080c0c420781b180701c2e0050300311880c44802c80d0999034440d00c171881d40c92500e050b041c120380000e0a04d4841d140164082480d402c0e061085902c07801c1e0350700380401d0303c00f803a0030241e0610003806403060400c8201c1d0b10600900d80721241e40b0145600c03e00e001130102556400060660049402c0f800e8086003805010040c0360f841111000d044519081054090741c0c0c03000f540080b1044488000d000c100248242c28006000342e000c1c000c01c07040d000c2510910a1540c40c600d00380201165002c84410381e1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 648179082 1250 648177832 648177839
    0x9110405150a0f0612110706140106030b0406050607060902060729010506120105010f050903120d061d010b03100302210f01061a09030102041523030c0a082d01 70
    0xb4810000030424888030030b500f03509107180101050450f540c40c04650351294100f500a150702d0040300c450390b41010003040340420014521814130003e12642000a00785191401e0340d14040c0b0613001212801800249000d0300ca0b031316100685403119042c0e078048405c1c00000045007040848240c05400c1d8244085480c21480c0b00361450a0180c118a000e96028000ea2054140f44812181510424280101644030a200403100c6105032210035070035000f0912090700300080d840c007030410440e0f4400103100c0c2c07946400a2008951405400c1540900072000410480940100854100390107009141c2865203980100302e000380c1d03004801c0e5001110881d1006000400d0208200c100403403402441214074010206680f0703005000f4455040e040043c105049682c2541110000c081031a40c10860655695001d005624452030781c0c4e200b00d1403210301d44146000704084078812002295101c1c2803610300c8408039080d0341c0c002c00b40d19112010000c801900007052000c20702c0c0500003002d050480d0304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 648180332 1250 648179082 648179089
    0x390c01030627050c0d06030602120619060509060706050405061b090a030803061825020a08070b09010902040f090606050906180421110d02150a0911040515 68
    0x14591040142c1c07614264031481040815030284401c0e03440d05000326041e2101c414600c268801da010542c96240b0b0103c0000410542e81c000d405510380050001c503031682c2d00018082d02c0112408500d1840104d13076010700003103000f60068100210301070082c1d8100705c4255a10b0040300c40503a0250341582c040c1041023080c103802250000030905003028141403500b4100403540da10024003006040130750100005080352a0729442800b00240740c000030300941000402640401011410010b207040104c090803a180c0c000601c034045c040d84242c1c1c1c03501c0e14469490307a66440c2c8000d00009015521030308200301507a034038010b82480c22010000010001058034002c41201c2c12948550700907490501040216520100c1181580610310480ba006a80d540b8142c0207058075502441c00201c5a1b644924038554801c2d545e4000300d24940841b40da424001c80c6c26070b40c0740c01d003100520f4111100400606001011f40004500078400c41c0400221b00a450009041d02d1048545100c000891105048580f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 648181582 1250 648180332 648180341
    0x130e090d0929271503150103090f0303051b03190e1c0315050315012601060b0703030501140a090e01092a0501050307080601030c110607020f010c14390c0103 69
    0x70101c0b16081601071169001006005c010880c1c07659a2003910030211030b034040d405c00011180d1280508480000d00d2038090020726058070303c5c14240c401c0d118211800044041200e000e60003000c40120100c2c040130224014000007124800c280c05a031380d01c4038881040c0030480040c41c03001d44002c145400d20348810818000290b02c4035210b6030020b212344441d65001d016180c15520440c1d0303000480000019500301000109011401c81d42ca0404002800000300001c1d01c2c84070702c41d0340c0a10240c2d90311040d114000c0245d04019521416244003008075040a61112400642d03550012460b0191a141e0000740c0c0c000c141d58004451000303241c140302c03620b0400e400000d00400d081003070550034445001803081100601642c107069441000c8003810b030044400890103000042222400d241031000251181c2c01c0b565501115070070480040019070080310851600c4021141070741c2448856440d60001d01095290448201100440d00c000e05504c0210010714004003002041c40c0c0c00441c00040855 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 648182832 1250 648181582 648181657
    0x1e031204330f110409090305040815060114070b0f040c0b0d090c060201290a030210030e060f0c0717040b07031805370b130e090d0929 59
    0x345400525a03602e4500343c15281910303400000010010034500e81a074081c03060784c10450340e0b4030a520100c04d803035051810f6240304060a0b07840c44c1d1280140d1640895038000e40c140208900e01000025104203034100d0466131082c0031302c40a291a95580074810540e501c85c4e0205c11a00d03403590150b20a126016451200130b001503c001c100381ca12442084105000c918148094541e5500079131100f60340d8a05088003070340c0c00610300b40c00c11030104030180091400003e030344803501800001804580036402130901c15502246103501c0d1079815510840c00081c0d10301e0090140384180f00c082548060000030380103041c030940714652070401c07016200d00c088149900c5203100d5407800c001d0402c072605d000f40d071141d02225120084070103181501c050002d140c0c1a0064280c8420214401400e416a0f02d0860110b038899581c0310081d48802e10026100c1e0540e06080e80480d02c144c0080100c00c02030343e43c110f403803280c00300c0b00c3c00116003040c07000150358045100038104c40128264007818207103030b240d40d0980 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 648184082 1250 648182832 648182861
    0xe01141303080601050d09080d0203151005040b0c03190e090a06060903080d020717130509041101110f0601030303050117061b0306010c080d0903021e03120433 70
    0x352a140d40080515200420050400801040039101003c141c0c2240c0003160344001c1c0c0c01e455500080c2a80001d4100701e418541d144d482d40c00a110604100c031395511010078035512507241500785034803015503034800f490100e42d52008024400d922550b1100b890840580c1c1d66460b1841901d200400801490284c0400516840c4c440c1c10000342d60080340307250860b07510001d09510303207410741a901e0080c0a030200c081c0c445a24601c204003a401000000e0990f5886030f14041e1680b5194000d0240703211044400030404922000c0f108525030081c0c038400700740403d5000301c1e06490368501e102400c0c40002e91048000c039843d50300500c040380103006404000114070f0010b10b140c3c9801c1c005250201401d0100000e1008008045032003644100d1102c807030b01c0c0d004070101e5038400040f81900d004000f542c070140c0050080c4030820313400c8120200062080643c160007035040040e0440c0c51200d402d07001c0c0c0110b40703403001c050308000c01d101c0e0b64141450586180d400441c0002481e00d108054038001d04440c3e40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 648185332 1250 648184082 648184111
    0xd080d11040617040611030a09020a060201090b0105040f1104090f1a0609101103070f060c020d0816020a140114010503030f12060402040302060f0a172502100e0114 72
    0xc030b076500882c95040b420480c5207903491620b4034100f072801809210000004a03000100700701c1d104c86290020202140300340c415001c442d5a49200b2400c071403207208000c10b482c440c00010040352900e50040720b41942c411000098141d80c040203460160310030350003280200d44030813074a07070200c01d00d02c2410300d8403146083c49014840314100003840f61141d41003441c402e4903020300020b0f075540b0076481101d8400c0018101c9640c0e20340750401040c111101380c0111031003801c0208245c4017038030105804a0007001a260f82d10b868861802460b052044c8418540031880fa1110600105182421102003190910000038815030750840c55480c001050f088a40030382d0007001000c2070010a031013100c1480781e0090004d80541c5450001402a21981e8006940060049040a1184000f0000701540c0032952a240312031030348824070640340e03a003c03100713401d44948029141070400c03860105050020050f1069038600c14034941e1b110115000f480302105580c0d515606100d2064045d2103450300480c00c04160705 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 648186582 1250 648185332 648185339
    0x14040b1f0306150c200a06050705010f0e1c0c0606030b040b0a05040206030c070c17061608070e04020702040f0e060a1a0607030309050304080109061b0c0c051c020d080d1104 76
    0x1c14129149800401a1480343e0105541102e4217000503d51000100443e544560b101d100078182d0b0014882501c00e54680500318800c2c070b10503c2103210355002c60000d410030094812101d540062181e170610180046280a040042d02c13a20417800078500ca0441081d11b0b013041e00700485141e10003042a03616910b08004d100c00340e03841c2015641d006841c038036041d0307540c172013403a003400a8883d03940a032039800703584040071507801c2d000705119128a61100501c01d403240c4e08081204ca0003003e464800214451203940002400c194004007000b038000780000c9103804100d030242d402c8649184503103120740c00c10028001a80c0c0c050141d0f11034880140301c1024400b0314030700050400d100d0540c000b014103a0f01c17070060302000000d0042d80c004024500c02003220507018100100544480b031681c88183c4040319054072003c0c041d282207240b0b9600101d407000420304050030702441c4c602000390200e0182412003100300513912103561001851207003130201c0d110000d544c880c106450b840704155428910900061 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 648187832 1250 648186582 648186587
    0x1d0f180307120302072d170d050415140c04090203100b0a0c0302070503030a050d0e19050105090c1c150f1508071a030403080717010312080106090b0414040b1f030615 73
    0x2501c0e811f8000382184001461010089014450501d80d030712154242800c2206002c2c51040c3d51402003d644000d1050040c42c90004002007811606030007081300511080c04002041d5015540c44075500c014540d0320390700c1d0514480c6641042c8002800221f56041910801d40d060103020010002500214204058034a000c2c0041c000d0744000038541d640c90500b032030064001c000a002046402d0100c0c0e050007a54101140a01801c8407840d1140c811800d030600141400f901d07002c550340d00314034102d14090490344c034010003d0304800c006a601d600d0715a1900003c21600c1801201d24030190140d0f615443e01d50003034102807265114080118501585250018901d401c40b980f003541481d200b00740c0d50300c0042c1920241c0d21461031184e0b00007540c001000f001410140d41014520544950f022681e940030308686d40c59071405a1060110184800c024100c3c00040701d0450300b000500c0407648400200200d143e10074203403041c4c48124001c6001c0c0c01001e40500c034800c0601240c030b03070b440780a8100c120003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 648189082 1250 648187832 648187913
    0x2b11120f0705030f0313110a0e04110d0c090f0b04020c120d02120a050f090c06090d150e030322030e0904060207060e071d0f18030712030207 62
    0x84034601080040d8035000c1120038001c40c4c40001c2015440c1c4d40383e080c000c003c54601d20100707030103d0700c000c004014102a854651216000c5072070b8030058642950b91603070341d14a030b6010ba885854004042e0070f039034000594125031000241254000010740f2641c0c200302c60342039032042079480303020b0f500c10006031800380004504039040d03002000700569920740d01c0681400902c51200c044072900105030600c59020982c0d000030340070341c540f500ca003401ca84604103520348a0b40b043c04180d920900811a2102c5410415000703284240640230800310596218003c0c0300392406443c200c2c460390000410021840d00d100404018841c0078000c03e68000300a66001d40051180d042051041d214100007904011076a01110401c0f03038808410b00600c0000b10703940390f03030780000d0013803400b071400442618140e0880c1e0171900d44100e4400d40004401d8442252050141000c0002c041d8280410401c0c0300105940c89600814502c60341d4005980c1c00c9070b410301001e040d54ac1c08078903050700700d4a580c004005210110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 648190332 1250 648189082 648189097
    0x5190e060705031f060f030b100c11220b0301140f0c0f09030102162d2006031315021801030f060810020d0e010213060c02032b1112 58
    0x1002c0c0e0303581e1659110360350f48a113221030504e00f5610140e000701d209603100c0d203e490b8400303154a0a100b402061800c2240c55000c08900d04000b900e803107005001b18881e03440c030a08101010b0711130101d00c2d0a140d070341c1d502c02c100b001090107015100d055a4140d81400d1003400c1500711490b2801340241800b454a040b60310014140c1e0103c0c05000c5120f00910390a002200c0070300c0801802156982040c100c020203030000041c0540c0c11b41580c0018031002100602c5000c1804020007412502007482d580303401056090301c50745d14606280c0107020b201d58a4200003540500d01c01c40c5145400e001034980804409021031b62940f80f24014000c400032909904060050f20f107003404c0c0030a043c000520480b00821496001c91818424132116245a80440d40202504981060203200b081d004d40304040c283c0c400c0d0210780002007100c0c81d04002c0c06101d0043e4501d610710050581d40441c5501e1080c90000e8a642c042d403842160f80c50f000c490a503000003008040c0420840601100d4844d0002c185503401280c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 648191582 1250 648190332 648190337
    0x6030a12050304021c03080702060105030f10020c0304050904230114010623030703020a0e0d0f0201140c070b04060f080103030207120309150206091203090d0e060705070905190e0607 80
    0x2c0401c0c2107648034014180038080c100c07042c1e0390701001030600501940d0300351401c0c0094000e48001244d9030601150100c3c4400070000140110345002ca0040c000354842c02e440015800144008603055403000c1c503c50085000d442c03040d0104001191001d00110520108035040cbe01d41188608940c0f840100b00c1c1c111109030800400d1140d8041c08051401c015480e40e200c09032001003080300458143e40034003450380d2641d44020314a10320505009851200380c1d0054560581034000c0e200561151090544036802c412a4500301041e40306420b00c1e2400130742040786c0c5900d0228040c03002d0f5a210320b002100c0c50aa2078611015490764030060746070491070050075803280c0040400b4090602811000004040c24440c102d032403180c9502c000d445450581e1040d0f224013402500c0700744040c404060ba0b00030034a82d40a82210841c2d80310682d41c0c1d01e64540420380048050090001099080c082d80d00181420880401c2034540710000581d102c080f1010020a285429030441c003a58000170315030341c400c0050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 648192832 1250 648191582 648191587
    0x6091501020c090a0c2a0602130b0403050a1208060904030e0d15390302090a05090a0f0f09170d020c07081614030a0303270f0b06030a1205 61
    0x4000403810b1040c0894055003101c0c0c0c0106110003002e099220b1001c1c000c240d6103c0d01c1810174414650340b0004804543e1050f070795080400408699960f00624556090f0045400c01e00d40e5415802d42c42e8003d50f005407040d400814010041c0012100e207528150000e2410307100503e4030000040b20508060409020446d42c1282030011751030b6000f4100c484d5400c60070b2002203c00b40440b80c0080d03d542d50b9106c3c03411040c0e65502c42550302c24224404220000039155610303c604d601c0072002900091800303540b10b419068001081e0302d8008800707000e0b01e80310340c0c0446d00341413241c4084107441c08d143c1c1c3e5945041c5402074400125070945603685010200010190340c2d06088159000a401583c03c1c0000601070900700151803c00041d40b1160290003640000c070041c0c0e00e6010315900d066101065805070003400e40394002a100754045080340b040c1c4060410703c8010101c80781103042c00c0c1641140c84607044112030061081441425034880710440003040c0b408030540c1c482c41c15401201002040c00b602 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 648194082 1250 648192832 648192871
    0x160305040f090506130b03071415070803102c0a1103010f03170a08070c0c0f080307060e0d0c0308041a0c0a1b02030304052112040303090602060609 65
    0x1400031a80105007003030351894219180d0394040028002610010b10900e4001e021480c00000750107403004201000b0302802010b460000d158074003c40300710529500a012050b00391040d01307148040d200c85070140004945a2070200e1160903040020380000314500042c003608854070301c52a054080085601c0c4100040c0d445402990000d07201c140b522884d400404400410701c402402c020000712801041e4030742c20443d000384110760600c510110341c8001090800002c490710300a4000c01442407103262070603079071503079135541498100d4541c00c000400d0f04006500014480280510059102103901400d04c0300b40c083c9001d0300c0c0000300d400c000e0502070190300040030302100d901f0000d0400a800e40d44a01c1d49490040c508a680c0f01c900b840000c02e54466011883d41c11103811115200e41c041d005500d0036060030100b0031181c2c440c1290305903241c036032090400e08080034058040200c4814011b00d85860940c58060165000f5411440456100c64204981e0303a1b40d5098154104c04000707406181f1240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 648195332 1250 648194082 648194087
    0x2090c091302071103250501031805011b0f0333080714090a0e1002030a180c050a170714010921050c0d020315130212070305060f040201051603 63
    0x31144401038080c0c40480c800f82401100c0f504660303040000c8003074070074103502e040c4400304043c3d2001800e211074003001002e00c4294003a61020032280034010070941c003001d86a66490941e40400800342e5601c80c0046082040380c1c01c2015008400603e040c20b1198005403682d896602c880520144402014185500001ba07140d071b01c10320141604105540b0169218600804964600f1890310f005102c00360000f0810b600e584290405a00c50380047c18502d54070074000f90203504041c10507442e4681d5011075003a0840ca0709045ea1a0a200700c0940354918078000c20828070a000d980441381c46411127542d65404000440c030340c0291030100c0700c24400f04010000494103503001d50012001c846075001001040f0100d4a1481c1c0054860301c2142d02c1015800140000b03055403c2d0000e401d81d020301c4c0d0610050007044840c1e50300c40c00b0309680021030807003600000d20400c0d000a1821454024240030b00500c0018030210340e000c2490401c0301c527542810380c002132292113051a50b02d402521034000c4e030109031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 648196582 1250 648195332 648195349
    0x151a010905060a3e010204060e041803030903050f0c010f0506010e1507060609050a0209030106060219080705190b040b0702011b050c0709021b0c030c060403021e040c0306031202060402090c09 84
    0x102d05681c1311903500240b824600035405405002c01041590050101c145454003454140e02489111000d142150317540c150003804002e501101484810300c003445c101c116400c083c1c0680441a000481c030800b1340c02041c02200d002400d141d0401070381002c5d0540c03944078800c0e00f150000700c1c000b0003030b03aa24050800500824072a0402c0300f07002d0500e010b01290010b150050400d0000c110000c20070556141030513a0b40b6001000c5c1c1040e80040c0036100e102040e0441d000c1c05240d40500141c03503c0d1044812016200d0701c122000b290000414002d120900108902c07a0341e10041e140020841202401c007401180140e03041c140041250001d0201c00c258014880400104020b200540d110302c07201c10011146100c02c21140c06911401d100901207180004040d14000000341c107007031030103045409011040b420361130081c08240400c0c01d24000794071a407140b0400100c050394001600340c00d52628021540300d100c00c034030456108000344005a0340d140007498004040e40e00c4a0354501800b4089084007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 648197832 1250 648196582 648196667
    0x304060b03010c030b191503090c0503031908090c150c1603081e0f1909030c0f0f08030c06180f03030108030a030c020d020316151a010905060a 63
    0x15400c21101807030061300354004004248044800c4010300c0340c0d18030141c071170b0007041c4135408800055103605105580254050781c4140c1c000c040c03000040e81c039807000c640746610400714105c0c2198204206d254140e0310200494218800344060054024000d001038010080003001003200303000090391190980c82013040e1100e090044803019800d940d68144090300c0e400450b0a8415101610549100080c60000b151601c0115030255410310b001035038031403640c00340030000c0710500c44c400b24040003162500e8500341c0102580800c02c8210b074185074081011b51180e0f8002001c591040c060440389901c0804c10990143d6a0500c1070b04482000d110313345803c4225600d00450b000002c008100c0b4100440200303d80b80003514148140001360000320ba69804085051006070414400000032150b00c011880e2481c1c0540a1070070601c030007007640c0c4e084440c2002c114188049103c1c1809103940c1090b0140300134a42202c9481c1001c44075000544800003500240f00142100c1004040b203484203004d00f80c68 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 648199082 1250 648197832 648197839
    0x2702090711061602011112010e090f12070312020301060804021302090d0305030609070906090e091f0b090603010c0c080f0f0f04081606140a020127021e060403080304060b 75
    0x9082026903440300443c0c40d141500154288400c0d1003c10141d007007181e84a040e03080c00800a60719040c5c2d84120b41c5c1c1d01a11071001c0f030044824001b0361003810040590f4180200c1d000c207030348240c00d103400b070b01c18580100032000850043c401001800c0c3c11100240d481601515103692002940c16010000d1080400c09503111f640c580c0740f007041c181e01c200a1807142c0400e035a41c1040e034407034000035100c10069209040001e48034850601c03141c080c0c808a81c2c0c11034840d0040300e050361518031032200300d9509102c0100710250b880d10020418903090f1401601705105900070400220054001420b2944c0610003801d81000001c5070280d1070030980444052400f500041d0b910340c45000d149240301d507c40c1c850000e0b6407040310a03002e901e01401c60510116021a1100c44105a120581c8001d60300301405280c250b55070707099000011050700d149034007440f6270b08200200400351841000158242c6001c4041e040c04010b14140e01615044c0c100c4083e240c002c043c0f151241e4a074030f401300140103110442a003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 648200332 1250 648199082 648199093
    0x14010e01021501080a1e050d14071a0406050a0e0d18030203190209010b04082802030d0224060a03140a0c0f060305010b07050c240f0901032702090711 66
    0xf04c0c4c2070701290100c001361085488071041281c50000c0004520180c1c006000b0360001440d610800380550040a1107203c0302110600300981d0340c4482107904860040207440c00d07090800c00c400c2021074400d00f980815030a1040040510030306200d07a645030b0070101203080c00310b0303100c2d40086100c5c003032030b44801107900808990400e10754000000d403c48520320124082d104403000446d081e00040c0503202514400b01c018002c40c6000d00c0c040703d4400d0a814080d0100e0000310450000d600e09101c0910301102d280c00900c4441d11904510400b050180410203c1c0d900390018440155220601c2401303c80e0407030310304034001d22000c148c1d81c2071074441e440003049104013002c002200d42c00c03445403404686058a04000302d80e0390707010342100c500c50580e00525540003050068200d2920988400f02e140559012580301c0340e0540d08000242d1150710084010200800c1c1090251f80c1406460700b041080010080c036456001030b80080700c1d424500080c807815500000414062080c20004103003000f20f001c890 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 648201438 1106 648200332 648200339
    0x3022e03021309050a05150d0803130c0e01080705090a060e041b050616020906030304050d060507050712030c0f030b10111203012402060114010e01021501 68
    0xc519031080c070b1001c1034902691080341c0c880c2d641418009601d04040445229603524a50402e00c510742c4c5240d010700041010b816203800401c01c00d54402e054803940f42080001025410024401000f00c0c00000e440b44006201412900700392029900e5441d003440520a544060207203510104121020030000b40e00c0401d9211b10140b05002d0f0f06a07142c855002a0b000e0b481b2031100048011411041815490322809540d0058821070045241c07070f1422011811592540002a146d20b6032000064001400342d03003101ea003a54010301c007100140f1116005001080c40d101d1020024100080d102021030107407007552030024005200100740d98136480304890340c0d0303030300c0010701d01c54044d04100c80e591170400c101030360180100d00c5004001d900f0600707220300c0c0c1140708080c240071940240010080c0c1c3d800100054020042880e040c1414010200140e103080c4004105203102840d400001 = true := by decide +kernel

theorem cover : BRFrame.Cov 648021582 648201438 := by
  have h0 := BRFrame.cov_init 648021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 648021582 ≤ n) (h2 : n < 648201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
