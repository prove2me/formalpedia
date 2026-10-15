-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4180
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:48:02.133144+00:00
-- url     : https://prove2.me/submissions/33858eac-e426-4582-8439-295412e27ba1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 751618705 ≤ n < 751798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 751619955 1250 751618705 751618717
    0x1e0901050d2a06090603061d07030e0304030f0b07050304030921170c010608010506030d031a030607050a020c010201110a030518120a080606030105012c0d0c050123 72
    0x20740c400c256241c01d101d89000300b41030759040c0040d918040300c080c28403941c101507140715140c0410200749010603084d00a01454042d2040700c0341802180d4400d001055103904041e0a20040c1540d60300f18032500320040c402403000d140110340e0040f402e40f82c0c0ca807074503402d803009144100b00038042c024840020350002c0c459049482162452107025070341c000016402c01c031f0300f00040c81035010000c4c003001906440041d1000800300b200802c000d40d5215051400d0702c1c011204654160001c3c0c07000c56045002e64440e906001c00421041520034850001c203290010680f5694003046011031800d4242c3c0c1d04000a4400050038030090114003040300c202c1d242800f40d41c15050905494000050444101e40e2b019407640e85960200c0380d00c020988041c0c020b942c0110b000c140012115400552141030003411203041310030603034919004180710503054420090000c0c0e601144ca03046810001d0558504000c0701189008201400b00300d0700c1c3c4000548600801c8003940329000003c85103840d04203c81066a032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 751621205 1250 751619955 751619959
    0x40e0a0803041514041103070803031b040f080102040509090d093308060a090b0d0303020a170f1905060d02011101060503030c160e010b0d0b0625021e090105 69
    0x28980c1c84500d050b01140300a003001d82655440c00c3d80c895400e26113400380a000340d004a06039101162980c06241c0c44021a00030202c95a00800105520207000e4244c406410390200d540c0d420030b612901d009100399055840004669008a4140628546290700c6038010200c05c1c018050504000d5000e08500c00360304c648000380c11205040a00c0702c1e6100c6036029a0164007803070011b4011203e00203064a0400c1d034840e07000c1e00300ca0201040070426441600c2c880c0d6402804c0002d4643c8940e0b04030081e510032048030082001e250550407100511110303407401a0956118101203203000360032000805000c840e07108038070b8204014008541c54113001d80160035020300c5e0420524400703c41c40317409890654412501840002210340c030113000801e0407003c40c0360b4a400014200d40c0e030085100c580c1800e01508161300410010941c80344000c3d4000e82d403001e07001c3c0200d030928410081c804400b012028441d5801c0c03001c1d05800b011403500d0402051024483d8000d0b039140c00a0310040303045a641406464 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 751622455 1250 751621205 751621207
    0xb100f0e222301150525030809010911120102040e13050c040504150518031b0708070f0b031905010311011e120902060d0e07060e010c1722170606040e0a08 68
    0x1c103100d10401c11030384804410320701d0030f210b030028a80840c042e0f00420010b0300088c00da20080f62401c40f043c01246181a048214005041951010424600e0b10200002000c0d9420040054120b5845881c544541c143c14600e03a541e00346418400d0821003118074981c0709914280030000040d0007050380011201201c0f42c0010141d8842d11190000400000303401842d1001040c080074100507680c1ca50a440030030790542c3c20f9903564584aa5488140c0d01130005100c5802100b0312864246102035584402c0020300441c0314441880b45104651f4280c105035210404600c00b05115604502282a15902001004071144071084001d110740c00407101c031901e007600c1c0d906034419542c03400203440e8211001e80c0d08010300800d1200181c5e80720719611522000ca00c3c1c401e00a0480c1d0701911055800c2904505086510054000500c9840d480130010700d030703881c03500100300380c0c01c00314103156030003805909074800000400c09014901d404c200401c4035104604013081c91081c414041550482594007580b43d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 751623705 1250 751622455 751622489
    0x182114030c1b030c030904060510020601051309020d120f1e05090402040915180c052a1005010618030507030321150f0602010b100f0e222301 62
    0x2980700300c001c0b281c0e649520002c0783c443c40e6048040010400306004450400c0709903503ca080c0101c8406152000015070003480c010401420040001112000b10400014801005900050f44680c2aa4003a604410041000e00011743c000d90120081207803420302c1000344c103030103000101c2c0ca80c15902050130020080b58942441e00c8507015200601817109042c002c11580d4030980f002c1d42940d10442140700303610800030395958524810342d0207191160f99203d02d0201104a050a40c030514900102404200c40d0350740e5009a05020204c08015291408101545013602c0100890600e071045a1031554900081000900025010f400c40e42c1c503050446d8001d038420020307140d132001061040f05560400d284014840310320f0405500782d403d8101c58a9465455200403801c0360b8850000503080100000050070b55401401e008419003414504880c1c6c2c40e44003c0401ca5400c264105054000c81080d80341c9400e001c140508a07a8107001301e40001d81c00d041240d0041c030b9810621032500030343d00844c66 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 751624955 1250 751623705 751623727
    0x23030105272a031501030f2405250e0a030b100b0c0a2603040609020a080111030a1a2209021008070207231201182114030c 54
    0x12000600b418040070b140c0048075100540d0007045240c44941c840d00901c020820181c00ba200a18141c035000040300b487c039a10396803403003032288a901e40701e02c0009239203d41000c1080c0f01c2c06402d100c1d84208816044800030405510900b88458008400303010b540620300c80a91200d2460004403a000648a0015122505108540030244d001302c02d0740c103000108802c03a0707400081c800444a00c00c502c00300200381c94141c81d80220814009041000100b0404240480c0d0310380c1040040500007007208000ca503851080030b084032100d40d1141641040403040120810309417041c0f2425110310342c0d404c05148031050001d20041c0d17030a4004031a400d03819683c8001d441155008850281c1d0241c19104500701d07116024250a100702c4003a40107100e05140414051003204a4180b500201c14900c51100d503140100548034100701c3c0340c105290350b100094010500b10b008a5012903019803840c50718011441c0d00110516030060010f0103005141c0d01905400912100f00e940c486484a0640d07107401c80490 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 751626205 1250 751624955 751624963
    0x1a07020f0904080c06010b0307050301030602071109180f0109030f120b0306040309150c15200d02030f070503040203060f070e1306060207090b0603060f0d0c2303010527 74
    0x201503040180d1800b04800c204100009081104282c822100c00b0ba80c0c507440914507210888444000131001e20041001032600d801034440b041c0b0448545d0409031010010824001048500d00303810942d2492411130000140501800c011500c070090084115a0b06c002d009104c000031031000b04002e8605802108142c6d52001d9078071b0310020159400c0f403c10741070060862117140281d01c2010646c820f50b15129000d049a5a0001d600200ea1000700b0341401a03c00241244060002404240d01d00b12590005403402860720b85070200300141c03a41070070f00c1c4052002c40010a01018441d01b00148070145e540014131b9036002d510031082080715510400c0444070642c83d6030100343c000d80e0103859501c151043e90403171070680b02c00c0d501300c82d1400d585e1103500d0242c4048500d895049030040011030309500304103200c02a03501001d000c0310079021840d50744a52039101741d441104914414520034503075201824004030003001c00c030024030660a00c4075078000300f01080007441c003901100031401440c1da44244 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 751627455 1250 751626205 751626229
    0x140c1b0a05030406080f06030a151509090f0501061a03012303030703020c19123512060f091302150c010504140d02030406080a020702040e010209010809071a0702 71
    0x20340e83c80303e41c0c0d054040c100705c0d000d9500c1003051080d00001021424005408010150402c8480c44186803022600c4003c0103400b540c4d9440b40140e1390007151012250054003c010b11035411240f142105040080c21110b11b074020b007a03a03605c0c6142c0031080a2405050307038191030320504945a110032040401d190001c018014a03018040464400700740b40d0003096000c0c1d1902d0560364444107a085c101c2c006800072080c080c2012603d81c01d00c0707401c0401d412605050101c442c4071103002c4001200c0290441c642260601c92044880001d13190b5035100890107600e82010b010386642c960b0000610001c2d5003038070300604041c0c03804211032400d019569400095406618440e50b441d603205241c0c000c940c0a803404075015130f00480400800900000001a8081ca000e80303a0301540c02c2908202c022207400704064004071500e6020700c20030000d40d80701d115a902d061051000103230340310072400c0050001400107000c00c000750080003040103445c1d0b5480e01c544080e102d00c9540d5517100001e00c000b035a40c503110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 751628705 1250 751627455 751627463
    0x23070621020418090c29180d0f030e0103060308160f02150726041505191110060b0a03091e03030212130c030b0a0e0f0d03140c1b0a 58
    0x801120344080c610f0b88602e088030302a035190405c4a450b1015015526000b649103404804c0610001da0214101c00190110301451200c26440480001c005540900c8100c0244e5103800f440114008154201900c43d628110a003410b004182c5035454207484d0340902c0c4000c0da84484440000f104000301c8403020382c60940d0040c0311901600780d50320714800b0b43d004402d04840d030800f21141400b0340c2e400c001105e0200516466160320385424a4401c03194000309401d03000a100c0280006011811040000491943c45581e0f80c40c680892440c4940351994851070301c03201d03e00c0c083d0b0912100004c9003c9030202c81c1c05040c0896600d040e490403d1012000f403c2040120100c1e580e50000c240d81500101042201c40018142d51380b41d4000301d0303100300d144000007010b2803400001040001c40c20716003a40d000d600c083c0000780750070840310600d040c440e545d0416211031b0840c4101c1c03210705805110300701c08500042c0035440285490071400e103584c030502c220701a4000c022016691001c0e4200464907519602c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 751629955 1250 751628705 751628729
    0xf0c0c051e09071e08040b0402040b03030d0c03020909060609090f070c02030a05070e010e0f06010f0c0f1211030c21040b0c010b09181b031603230706210204 69
    0x5014010301382080d42012000c2c1e01400300407030780490b10405005010700d4001e40911510b403510342c2000b000f400405889a05800180450461880c552242c807a00c0751240c1c07409030b80c804540301000b0100c14000e00e003600c112410b10151203d44c03100303000c00b03500c2414074050320b00e2901c3d0f000065503501d00c3c0c1300000794144610f140d490204080422094200c407a900034400043e602c49100c1a082d1100f201e08074600800000058400c0d849440b110040700c0b954103081c040c070001a1a0f0f4400d0000e03684080c0d681150710007002c4c10b0783d03511821400990625801075030400129460309601c4641c1400c285400000140070b5071486004282150000c0c040480f000740d0300c410080c1a80e01900c04400b840f482042001c00241c440c0c2c00040e0000010303108000a06a80c000110246070054240c21019805108400d04141060000c0c001e440146000700b0480c0740e21600300f500071060001142201030700c0e40160104101858100c00c3c442050b10060300c20702c00c855200742a0b680207000f9540080c42642c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 751631205 1250 751629955 751629961
    0xb04060908010e03030106020a0b070c020901150801090c05040504090c0f030506090124060518041107060f090f02120a06060b0d0e01060303080a150906090c0f0c0c051e09 75
    0x40c21510103011503007070320028029480034018180c4c40780824404c2101581014040c200060210500ea036444900380c1844140c0c01115001700e030710b41c00242c000e840c1c160544c8140921960300f08200500402907a041030040c3c01d0200f000030010b0040e07124040c0a10346a444100400c100300741108041d0203070b0340b042d81c0b00f40d03500d08140341d039803e0558640d820341d407030050000c0c01c0c45030640f402d851000200307007900e20b55440c01c1000c903103990183c581204100745482c04121a65518042d06060207190b20f52903440b000c59003402011111a250345400c410700c0d01c248100001c4072144900c80c841d804170ba08810718482e54a01c2c60411140c000300511080c500100820300a1100002d03002c98004940d00300451814032194900306d603643e0101501103000d0000051001116030880612000b1f042130b6000c82a81d1072040c213042d1246034004c40b000907141c11f58001296400b04080444104030b203815021031845440300241101c96010706800b030000c2409180c200d01444004561a40c00601005c450303103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 751632455 1250 751631205 751631207
    0xc100e0105220b01180b10030609060b03271006060305011a030f01141c11090c07030509060901091e030b150102060604180f08030105040513051005060a0b0406 70
    0x1020442c0c4112042865014030001002020301d822000c5030701000f880c10990034200e8003003003520078101a000720390321440c0d0044c054031055504200820551408622241032041507410368805030009001e12000703200f00700902d440d03911400c50401f150b034840d001610b1441859410300c001500740c01c00c0385040550004034130340d242c0d01ca03034129000c00c40000c0c21502c148503070848500c015164000070303c1d1100010301484441002810314503200405d42108480422031981600326a8030703040d0b41c1e03e03004107080c102078200620314030b51046005211398600092540d0107819070145c80701903800780d0400f06640c42d940e402040000094005907850347e15a1034200052440529940002c9a02c0c6a40b200030407034030100c280308040c41083c1600034103400c0e41c4450510000f850240200610048403103903950110343c04072892400396004400b0155030317605003401e100c1606c03000b90201c0c00085226103d0000301d0780101c4d910b07a005101010108854035400300042e8071140d180c00206c100d03103000400150607 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 751633705 1250 751632455 751632461
    0x120f02150711011d12190308010510020f030f030c1605030d0e0102091e04060f12050114130204050907030c0603020c0f0115050d0c08061003020f030a0213020c100e01 73
    0x103034465208624942d45141c011103810400441110004103030000071401440c02c1403e491300c14044000311400464000010325405641a2051740840d030405c0040c403503803c0ca01c0b0340c0b07103440760307540002c00021007203032030641d0340384518070b900102543c001c00843c080296180846890000d58000e0f099480700d9420560385030707031044024942c002d1806843c00749041044c000d991008000070a42100d0030b81c04a083d1151101a030030065010f9500c44010962289980b2030002030180340c8501c001000e03007840d0440c2121003802c42d450509202c00d00f001088000701c088595007650598020500340c82c0d00c07074201d241109903000107080b88984940840c6850f410707800381090107007100807a09075560350141e55080702d000c400910a406558181801281001d0b07280c2da8055114444e0f154410360f4444409080c0901691025429130340b006080042d880c11800910400d40202d0207440d0020b4241e00052001c4924130b2402c0300581c022510521154042c415051b03040d140d0700e0b0a00521900c1c0c81c2981c02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 751634955 1250 751633705 751633717
    0x260717120604090803011a190e0a08031e070204090f03031e05040215030403050d05011203031a0901260106141206040305070312110712120b010504120f0215 69
    0x2080d0914800a03800d45018020b10000030b400901c4070b455039003880d807008920b2050030301000b000c1004011100c4502c0b2131584400c01c130042c40d036910520b550705000304000c080075540181921340c420311100040074000c0428030807083d1701c0800d180c1e42c0c0e022440814050000143c004d44003d00341443c000a150701038000c040400002c00411500d01540342050742290010b59001c0d4001c1999812403d01d03030400700046400ca8007a0900301e041c00304150000f03064a009820940b150600c44211000f0190103000300d030f08401000345240400c59070040400d44066051145251600b44440c0703a4204010b40305600058002d81d80080c806640c482c0901141c4400100496000740341000440464190100d24203015036850346d0340c03a00c1d008958400b01c8071001408140145243d03a019090006442c600007403a250b817044401019811746014044c1030074407240b42c04c0c0030042c104070b041685030703a020040b40c040d61150908111706104034100010040d00329800250010070f80c3c3ea13800c10144c41e40010b045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 751636205 1250 751634955 751634977
    0x60f030d09080c030304030f06020706150902181804030c060f0e061603020a0804030c02031c0c03020f07260319090905160905040b01110118021c260717 67
    0x2202850f00410b1655034411448060103484031100617400040a9800911109000359408113040d44031040c08103021101d41d021300516a40050b02a00d880c803541c1250381c4400e012038072444002c1c0d10080c820f281001c010802020003410f40312140030803109602001c0ca429040108000c81c0002c06103c581d501829242c01500e6102c14a041c10124400c2c0203c0d495079840d603130f800b111034503035a5050724100882c017022a858001e08010300d100100241003044a030343c850b0303500c141418050802a0420413129603d82e401c0c0c20141051080c00300c4540a00704000352007080e40240382c01e0f090603604502445180cad50704029422103101c9001d902a04032803d8826841c401c00c80d81d12001c4200300c400214042a10118500060411540c0380603445100c14002c1810080004a9801300d06400c4906070b42c3d501d00f406e83c4402c0311000f5420000d1083c043e8410f2040102d00c0400340b41c440da00c03c11400b50101c2902501c8042c0c50851107000000d680040c2d9220340c0c00890100115030640e2984c100402a103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 751637455 1250 751636205 751636213
    0x30e131a010e1e01110c060f03010e060405061c06090b101721090f04110c0706030204081b1503010603050a1416030f020405130b01080906090c09060f030d0908 70
    0x494a49080710403640034001020a40342d82882c02c20040d01c5c0da50f002856420f85020740201c80049031a554024030280100300c4446a803507050066400c86240081c103518000c52510b02003000302e440d000711088103412404003080e04141145000030150480300001080d030902d89041c40081d5034907108050a4a06014104c1c002d0aa070701c0319a503581c8280b002008814510304140e41803415104014031450001800201134090b099022406031503a1103140702003440c0004440e000403109000010140c589861306602c1c0c28903044840d9624044030f07085540780c0c114492510303259640d1064400740c041101e55140d490f580d5840018004080480b40e0320440707806c0c0088018504e500107001c3d886182c20242000300b59441c040102d009108076924811020703420480411507507548407400c800f8a56522011441282c0400018844040030348030204542c40301c0103110040c100450141040407054a484280342c0d078000018181c0207401581039014000ea00392662150380c03020a40041d030f4500d500321 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 751638705 1250 751637455 751637477
    0x60c07091b0f020d0c06020f0a0c1b2607050307080c1f02190c090e0109060b01020c0a0902030601031803020a02011709030f0c1c02151e04030e131a01 66
    0x5484030301d007940605005800c031034130b4058100e028840c00a9080e0040c4401414a03520303c400c003a0513842000440c0101e00101522820440800d40a40c5628017801c0507581181c50706151028238840c1404e008a03007200c0c10481c45503084100300c01c0000b84802000c480989941d007042644640f1a10901d50103242d85100c0ca244000c0440340858060b81264020070700c204405400c000c105d40d02c0e09003102d0640454138005010440742c02083c0d40349540e800000303004d000782e1820404807a1110920360564010240c003018980c1d807184004103c03504510003580d2a03540b01e00481c000c0824144103d900124060103105040c0e0009140d00c04030f02c04c1e25200040c503c0c62501a0060008a07000da10941c401c1191039004411040542000d04210003112014422400901d04c400d0080454000581c44410203078a00442c14400315005540d04e11041c0d022000010780c00c1140600a0003d42030010b503010b0105291503424034035600c184041c0c4100f1000c014900e800e100d422a03a1112400036800001c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 751639955 1250 751638705 751638707
    0x30c01050c0a09080118080c100e030a17060a15020a05010204060503090606030714060c1e0616091401050304030e04060b09030f0c10030905030d0504050303060a09140a0b060c07091b 80
    0x5d01d144a1b0002520000107900e0760f072001c4040d8031110200ca258010303942580c411603c0b030b001c0c0c5000c0700180005503071540c1004c040146074903254883c91207070542076003d020654540c2c05031034046d00d1340d0020404200c26944404e0380f800d050804000c00239803001400180159005d00514000d018040681d01c803911240201551440d0038020f031000000c110b8001c100910f0301100424218020405072803054030400c0c6c0721041009006030400c056085001002014000c54881c0040d241c40303410030804040c00d0540400a07004811052814801c000011500b414041d01c03003141e1440b001001801007a03191145c0a2094110182c018064420111701100f003840103d1100380380308019007082c5051010140807030103465400030a84581c0001c0200c400350745032074000c1e988035070302a400a6550f4280b0074103010505840350300c0b08800d0382c502300c1601c480791110a41d058001020300404203600140b42d00190070792017003401c41c5450b40304840001a4400468015030b00c0c80000c0c281940804500c040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 751641205 1250 751639955 751639961
    0x19090b134b2a17030909250c080409020313030f090e16170a05040b011a12100b0d1a06041809030c0209090a0506090d12050405030c01050c0a090801 65
    0x100c000c04001030000700850703110007030310700d03000340300203214019021962480f1403000c49110110480890700000b44000141c01c00b03400060700020034440b00007001018039111034001d4040d20800c000c0141d0400000140001170050b60083c00c55010115580d08000299030715042c00b0070021404a45144108208140a41c054400700c0781844d000300c80aa071403000c2140c0d442c45a000d42070a010032180d00c8141024400100703445440c03c05000202810241444140c0440c144d103c2d140900086103000003c0030820155014000c0c000c5119200b9161002c0c07070b02d86000c80d600606200540803651841038251900400d000400d8a400c00380b00c004050240034075441030340100c005050b04020081900940c035800020181d00928080101410700c0d0b00040307540c541981c5c5058a81d101e201c03400c0c180081400055041003015006000b100401600a02803441032480100200d564800150074403105000300c1c0e080c42c1070340c0000c00c030a160001c410f0065400004a180005120100c0443c080030144 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 751642455 1250 751641205 751641353
    0xf1403010c02120702040e0a051204030c23090a06030203060a24060e1512010e09061f2705090f0601090902030309040b01030209030d02030319090b13 66
    0x902d06440d241c805e40a100140c00b00c850380341c400307105810080d00461024481984682e04041405d0390b1a45541003400180d80c1c19009601007031901c41801d140d4190422161307500109c207482c402c4181d686d109101d4014421a4030194141c0a1103041120300031043c2c1c80090b0140109904c404512140d8414882d505403d02410003c240c9a81d400b070b00e02d00d45405455429107d5003802440c141c0b00d0798007006a041c00781d103d406220400005d01c801468284803036644400e0841c07601e0444001026045141012441903a603229940701c4001e060005003143c80d2102401d0800600c22800c002c0a4075582e2011a0005146401344a00200d101840d40c010342c0400740d0020000c41c00c042c640300c03c11008110340421541455400c000303218090301d0034030081c16031000907009142c0780e20304803034400d06090070070f190803074403601d0301c0d00034000074848c207050f190841c031004146800c401c1249000c044038441c00e841501d400380c086100851519008841c1c0740401950600306108280401104968411003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 751643705 1250 751642455 751642483
    0xc021210150614040501270f170d140d02040b0c0f060106210f020712030c23191103121f03150e0705040f0204210203100f02040f1403010c02 62
    0x100402c05c190362003100041c1641e20540d00ca519503202c403c11045601d4095031183c030466080e56800c00540da0003c10340e400101c0958040c18a0342e0019000400038080350044480c3d4040115159074410b4047d0b0585010b0005510f0080c3d4580249450559415081141003810b02c030b01800401c1c00703481741d1806580a00140321856100c000300d18410003401001030200d400740d1742071000402040f4040210b5580c0303038058030005050b542e4184002d0607150580040303001c1c03800184280109a018104540c0c191154a24545900c180407000315860051641880e003244404112510007008680c203d23402130b1341c0880341920312a040c885000540704248400303480500d260491300740840054229204900d080420b9854443d160340010b0200c1e50441c490316040780e1b021500340b0180e40c010508440c241c1c000703942000301050380d0f40003d40d03400c9408aa1010a0f48070342200031000c005406a43c041d0a001840e00c481d15110100314000098154104d403180d820444510405800400e0a80040e249 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 751644955 1250 751643705 751643707
    0x40302030d0c032a080313030806040612030c02030106050d051605040504030f11070905070207062309100c15020d0c08010305070501140c010507051314010503070c021210150614 78
    0x44d0342c01d031284007403000a102d00080340800034a40007a440800461280d050003035298040c10b541d0a0040c4500c00c01001c16004925040062015048403c08030f28001d5044c980440d9240b01480800d0142810740e03c850341269482504e24208070b03000c9081d5101090307048402c60743c1c2c0d640300100425030f0700550b0089c0c085039003103880d16507185c0302c1d4050113115001345007100c1c4c0392a030320480201210801c850400040c1c2200300c040c40029404140e40070b00b8a100c442c00c2d0342014012202c0340c114450b01c0021b41c405c910844010001501840c548203074a508403843c107881da0180c002034400f030740c4498814107801c0e10b400504030209004100f114164bd811800a2544c0c1f8106001511142200001240014424032154805280902405114440301d03964070f07445180b100304401000b8040e400c00000a1800320f104e4190780d0703000041e40c0d80003007549040e0148641c1d0380003080c200103003d0181c0040d4003d0554410811905400c40f4204041140000580682e600700c12540884003540d000800c1c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 751646205 1250 751644955 751644977
    0x11011211120405011404062004300f0507050a050d0b0103080c0a1527030813140f010b190b04180612030e010305070302040803092112040302030d0c03 66
    0x207121801c0700e51051080c0e0002a41558500d8040507110080750304850403030b00c0d45080402c0164120b4907244038a4141d031030504084c00e065080021138200441216074041c0c9804101d121940200b8400351150004000040682e250803c16281c042c10701039280240c0c89a4030010340381c01d1003100950a190002c16107880b0fa42103a4880740c40d94400329504006109030100900030807624004030400300c0c1c0d075410011f0280c8400b00b603200c62003d000000c1c41c480110030a4031020a40001c1c90360b51040350413010718000111481c5c40e001560100d00d80a044d48148018082d5145056224000a82c0200c4a240d841142e001c00403d800380d031405140741c1444140700400002000070800c5a1813049032234080b8400d600c5000c40300022222040c01e0b8001061800302c0b80749941c152184035007042161505501d802d0510701035035620305c110400c40303000c3d012600d22240d51100a110b600191030708031094070048144044000760b650040d0009074031030702a280c4445081c1d800740700c0e1003900c2c5625882e181e00c40c1c1c13 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 751647455 1250 751646205 751646227
    0xf1f0602030c0705010503012108130816051c12050f04090209191d04021507030c140c091303110105010f05010318030801050d060207322b050d060311011211 69
    0xd00000f00840e070820080c003c00c1c94070100902f24038040c10814005204005007030554218051140d4401c1e4001c004c41400c1d20408140207041d42c041d17a4000350f0400a4800004080311241f1503041001c1c007000c0e001c6000300d89807103a074004007083c2070102c61280c0100003601d40e070f419200315446420341101c0d8a140b5260304940040500382d0280c001000d542e01c004200b0791300c0c20154081d0341c046001581c01c003014001c200803001130104418540c0c0050500310985004220038410140c480c000441c07034003036003004051080c507542d955528404000d00103942e544403802030010482c01a1070200b41440070281000341c1c00390701304410035055985c20100340d103040b00b413040c810452001603d0142d003c111703402c0400c04108491410540002d4031f1f81c181140c1200c0b111105040c240310744041d0b0031900c42c0500804504404076100085c0b01501807413407454040590f17161081045000d40d01c0d003000000000c0c030280b0070030281d61010a032581480c0c80b200005120444608047c1543c2c09a03007071200d41820 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 751648705 1250 751647455 751647509
    0x506010e10021c031b0801050a0b1804050a0b030703030905310203191118030f07180f0e0307060c050c030a030f0e03070c0302031608060f1f0602030c070501050301 72
    0x1000550a0009444016403402c1800304000c00124000c86c9900b0010407050602030862001000050305c5c06003040d62988103607000d60401c0110320b10683c3ca0b50089101c0c01103503030203624054002005c03aa903c503502d01d0090b00e070002500c1410f04c514082142822400140100b058680c41b11401e60902c0f0b0002203400030080d0000b510001d444403180c08416060070091050580102541040d0764890520041d020380014001c022107009802550404245000004d80e6800703444070031070000300050611824800900c1d818200d0b050181c203090385a03008010110040420700d014002c103000700c000860054071a4451b40040511540c020400c510040d8030030351218082042c0c0a0380031030b03130348800d14a051440e08424000d80b05210110030420451404100104012070340e020400d800c14542820325854000c01046000300d1105040041c00041482e81d8040e5107003908a03101700c502e91180d10083d501c0e0403046150120b88a103220109031507000d482568100c0b040c10a071840c0344d0040701042080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 751649955 1250 751648705 751648753
    0x7030806102f060c090f150f07060605040b0406030b18011508010c1d030c090916030b040b060d020d150b150901080a05041a070207090504060506010e1002 68
    0x80085035800c602c120342c8088415200a40c0d845002c042d418030b10002503003081e030044c26a15400100f08400e540d41c5d104d400941103400d030102c500303000c500d9920585040038030540f842e0891001e00003c1201c02c000207903200c403084d01c0054800700030740300468051104440c2ca034000038005c1a0034000041180c00c4034002009603048190000c030f102c07059a004220a0303103140d041000b443c2d448030505141240e00500c0d2000d140300385074080081202640c0400c1d107501014040500a0b661200041c08442d4200300424201c080000d00301d440503600d0524481d90003013910304854844031742c0d012950301c1c5040301e0b00040c0d0705c4d0000c007000400040ca1380c1d2a01301280081c03940a00c0c40e200c0c401c6c00260741d6403040212141e281c503407185a8515400c1d0005100b007000074000c40199186c0000d00000ca600b6400031001355a00d07541e54284c1e0b48502800340e10f0800280d000500c0242890200800c010103908117901410003a00c9029042c102001082200140416200b0050340514110825428040d8400322 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 751651205 1250 751649955 751649957
    0x20918070c0501020301030f03020c10051801020a0f0f0b0a09020303040b0d230105151905090a09050403120509030703021c0c050321061e010c02012d02070504020703080610 76
    0x40d60785036030340d01c60980c2c00036401500c01d1108000c445041c1601801b09a40d004007c0b20205071800071b03ca809811070050502003103e82c401310820240c0d03a4000c014aa45154000012403008a190314040c0e8100460300001c4502e07014180110b03280094a029005880f40d004025500341406e0030550000c5820030790300710510b0746d10380310040b500b41c0c1e40850326040d4480c1d100c0d40c102c8660402080c4003048949040d8914546010003039a1000c03c0018035000d0810600d280560350740d804c0100280d10b80710907400c2102c4252802c0c2c01c7c07004064100350711100169048a080c4a0396841d00d0002c3c0e203038041c0c00809405038024031180303850320301d6142e60f43e4413402d0f090800010100c06038548130314580020078044071300d548006103c950300d0f0306440035a034044030031900d01000b481c2c0c0f540c010f9242c8500c0d0f00800d06200040b0844000c42e03010303900c1c0080003417403103600482c0704040d858883e410246462080026000310180890241400e0080342c00c01501a110310140b134507404140911030103008800d070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 751652455 1250 751651205 751651217
    0xc0319090302040f1a0604050102120a0311040b0a02011b05160c0801020c0604020301061a0f03040c050d0f0204110f180a0902031f050f09040b070909150e0a02091807 73
    0x40016516841401c503005080d035400141d480100e10701741034541d0080310030340c07080c0702c207110800060b07030300056014240d80000c0c440c0c0c0e2103100088d02503001d01a040700c146803031140881c1c086001844040900781e4802c156009004402d019100c481c0100e2a0740c0343c0500250f4104000c1031210807242d90302800c684901c0003403014540d600049400c80c0c000f0b02030031400f50845001d0205501c0c0074041c00c0042d05421450501c2031058018000c4c1c1d030b1107070044012040102000180c1800f8480e200d0304d008240240c06480448120314040700e20b002d90000485c4142e00d030040c420780d105588019101d13080d07a814202c43c50040280302004102c10120a111703070241182c0c1010070403000d5800954011504408840c00d10010b81e1a42198002e00d50081406039054069501e001c1d40da980d0700030380203a0040e20150450f03c450804841041654116024041c104040131340d1141140000100710ba203a00e6401007103860300c5100c4400d900c50000341a5226140400104103824807500080d001440c5040403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 751653705 1250 751652455 751652459
    0x60a18090c0302040e07030201090503011119230418050628030c030606080d020109020607060216120503070e01110307140a0f06060302100f1e051c051b0c031909 71
    0x10f03064440b40005203d403900101b604004658004e4840e034040e046c102c0081c000300780b00d1a200e480e107000700f00a4040340900f550140300901e000700034402604101060184500d8a042d800c00301300d500500c5820780c11240150170213141c604030700c41c0ca401231600620412103400804e0314483d49401d040d0040c00e0009080000000040c060315141008503c01c481c0400c50501e01a01355040010412110317007964100f090142c0140d80346000c444006600850058990400e11080c0385880c10400004001400e039001e10300a550f0010080d40c0316001c1c0d562004540d141c000011a0103103104c21040035250700c24882030002400c0498006000d10060080302c003440e246498052010f010800d065854659410301442941050019818454964205039203114209440144040c01c2c8812413140c40005080b555910b901c9003040750741d4a03482c3c42c0008003e2042d038103000010030054580c5030b1204040741c0d441c0c0d11aa03080703007910000c029a601450919000b001901e411003000714036502048404200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 751654955 1250 751653705 751653709
    0x10512090a050f1209040213050d0609020a05180109051b21070e09060f010203090402070b090705011e080702010b120a02181302060d0b0301050915060a18090c0302 72
    0x82910451410000344121081410500e090142041102d1a99005003031100040c8003203c0440300c9055040d900181d4542141c0030f04490702c201da0300469403110b40d0301f40d608d083c80840c0d00300e0080c00340200c4e48422486e03950030410400b0800030200004800c074200040080700c945900003540f061030883c407a000c1918940c40300e450341d40000ca08071040c0504401000009645003005070340042281403614080d000703940050300c0980018401882203190110018083c0d1003403041d00c1070740038054415512032030305140810b40d940040b1134521030340c0b0607172400080940c17040c1e0090901350078a41c1e521218200000080b541420b000f1b003641c040d9901d030135803a40b2945400d20108500030703000001e007403005140d104010000702c1d01c1c41c00100c0c07111640c05000018550011b0a5178041e411982c0c03558520036821088050036000c1502d90745940307040f04004c0f40441c0460105400c050035444222556192810400b0f8020140180c0152400500381001015840e03401070b00300d41d00a040c1c6503982523403640 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 751656205 1250 751654955 751654987
    0x50f010503100b120f0303100608220c05030d03091b0e04200613180c02100f1107050606090c0304050a0204051f1e060203041208090d0c0b03040b250e0105 68
    0x840c281702d5800002008445000025140d014101900e40010241081520842400e910440252400204299600400c144101500300420000c3e00b44e460005040d88050010108000d098075008849261100c209a40313498005c1903800c540701200d07041d1500d4458844a8030098500c90304400040101426562540c0150a401d80116141d0a00a00f0940044907079140b56100304465410020076181c02500030601742d40381010610b00107441040c0c404020301030012003001401401001400320f06000e0045001c6200707031001e90b41905c10380c44184600e07806110032280908543c018802c600c0052400d80c1001d504007050300b141c40d01ea107480da030176043c1d81661a4419032308820404407540604c441c480000000b414280055400d0038035204000014292085000303004900000f044580345d918510704000741904242c05540d829100c1c0b414101aa2003a41c0c15580c04074018002800001403181c0910300d4000700d000c0c480f040001720f40548a0455034141035041c004180881c0311013466100c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 751657455 1250 751656205 751656223
    0x10051b0d051905100e0702161d2d06060c060708010302040e070506070b060a03120908100644060411040e070b1804020418050f010503100b12 62
    0x1000018850600800700005040b8005079002082d003080c0070400161080b40001048443d0301d8141ca405545a90b8100d00382028130b00115608000039201007042ea200c03100d40c8100c8001d402060503292100c054141180740c41d560600c80d03001008001e44003000303041e18a0b070b030800070150440d41400c8001807580e09045080343c00c1000a4403d4004006616250140200312401c00015020f40c9080c01c0104403d48145040507000803c00004500141c80380300204000b1038020480038041c1d810614003d142c0c0c030640c403444410b481f440184401e840c507240300e107804907500b1190341401b026812440103004d901c4180305580c00c1ca900324103190028003010204080c0180103011740785901e0140341401549845480f5540220318002410040c030000041c100143e519040311161600225494001000009240720341c1103400498005805080d41b0510700010407048030610a07965119aa94072060b801d109aa906601612407080d03420942e5102c4101080013501103400c01d115001030503d490380d2a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 751658705 1250 751657455 751657477
    0xa15120f300e1f120606031a0103090c030206070506091515010e0a090f0b01080c0c0d0810080703120806010e0a060e010c0b042405091e0f0601060224060310051b 71
    0x15510084c0c000698440c2c0406044542400c120a0039944024034000050b03840c1941456a03590802c014000d42001d18002107900030061030791441c1d04d1601d40d0b1205001d66000c0c1da1880342c04807082203520002d511a00c24428050707034a5080523030800448040007455601d41d0842c04480020403149214061120703450380e0403201080c0303410307280001005400018103c1070a00400e008603100c0c1d120110310307140c0066140c94200d5881d200c580341c801c0180515070040203a17100d40000001041003928200da10024591507401580c0d0303c40c00151003188a460b809640000c03000018020203000316102401c072a01858122a40c07180d5030b031180d00d01101510151030410180c2050f540d190001803480c04002c00890083c0020b04121003440c1e0750b6640e108001002960441c00480140d004200e8596146101c00850b41d0b42d50359040003075120440e20000c01d07000c200120300701521011169049018400190052118140c8100d18900912015041a11084900d0a04e1041c842d506015001c0c0c4291 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 751659955 1250 751658705 751658717
    0x30601060201061418161106090c0a150807180305031c2d1116120f020f0601050630011404090302060a15120f300e1f 52
    0x100f5601c0c581a038201d2030640e00c1560f500503403250000c00746174003503000f2001c004120440f0682c2041030721032082c9800c50813114451101000f048440005800042030800c0d506018599113480306041c0c89480c4079108000f0403c80c0e0042003650703100b02c1c48000c60b8131240e00302404080d142c1d65150308542c4241e002035041e511071629030903201c0e5140702d0008680c03401c400c4e0580100d09040c1d9000c400d540d8100d43d0f01e55550300c4140600070003034030048a0300d03581146108450392042d4504400c0511003a4501c1d40020030400301c903941e07030b400015240401c00801c4000c01c116032a1074200542c50b80518242401480d00c1039015440c00308600042c04800e88032008031029605250314102d425145c0030820784901c0c00c03c5030320000b107a00884d015400444480d004501d0303001d20084031441c213041e03a0100c016900203280920a0040000b21020540c1c81500d0b00107811200130000c0030f900c58490782000030701c64003006141955015410082c401c4a001c0c0110020030314114407840300031500140100480c3c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 751661205 1250 751659955 751659959
    0x50304080601080c15180a0803030703200d0510090213090506030a0803070522120605090a03090b0c0a0b07082703090616140a03080906060d06020304080903060106020106 75
    0x9024040507000d002800001d0001401150000701c1c4803001d4400c40d00b5080c0001100c400b0100d0380c42d00d00c01140780203040d800c7c01d07554558100d5580da10407900c40b07000034900034003450100130600403015000c545031a040e04040244068070018100682040000322200d0000941804540054004504e040c41015182d92400c140caa09a840007041c141c480d802c41d4070b840c40040c681c0416613810101030300d02903840d00401c614031a546290316170a04100e000381c4c0380014901c002040004800d034860702c0240310030703220200c0b5555120340c00c0c070000b0040340000700103003c21402130015100c1a241d800132034144071420b446521800303200781c031004001030301181007000003580044024002c0784107801031002e0360070542d403c54a0713008001450b0722861002600310703200c0e003000001c02051504002004181e01c102c4202c55500d5010031001c402141d20760340007c60190000c1025480b48201030600c508400315a5104c0009520040080399010010300001000f40c4041050b80e0182070740782c00000c0e0a034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 751662455 1250 751661205 751661219
    0xc02220603021e1f0c080d0b041104060224010e0601020a0b2d15010305090708070f061e020a08070206160302101b0e042d02090f040204050d20030307050304 69
    0x380c10540325901c1012040420700006170700800724450030340c202029a845e0100481300f0300207042c2c9814115032241c10201b00c1703941c600a110003402141d20b10307001c880740040b043e5200d99040071081c040c280c421181400402030361240c00d00303041d481041441620302c50411a9241406100151a050342d00050b2007580303242d43da1407001d06400c607803210a032403c980ca0416405105141c400d01141d0400d529540400d0480c80100040000741085e44182d40c0c82075114a152102001248a0000011481c0d0000305064243c0c52403821200c01a81c0645035100003520740d07a50f40d500000b01260803800030840d80c1c03030422440100c19529807003940984802010410302100352559548001d2000c2800c074200c4002a400c040301b241403000c25200441e000d001c400c03032908080c4002160f00340d850052001da450307503075091780241421902200d410181e4440e80007400101c0c001c0b40a02034002152100480c01b0580300358461040c1c0d4024012035121010040c082421600312442c126030350391000c80c0600c08a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 751663705 1250 751662455 751662469
    0x507030b07030e0a030e0a0b1810050408031e0f0f0307030c02010c020703031223070f03060605180d0c090b240301150e0406030804150c02220603021e 66
    0x28680b905014011100c450f042c1c4442e0070080050a000394a40c1c520119100c4020060003000b1010955440e80a001c0d5025a05541d04002d00e2164001010031580180660103032000e41c4ca2141c021403c0024001407452624040ca0b441c0482103400d000180c04030a04800400b0700220002d04035840f8201201c0c05002c2d121001904800e46e418090010210b980c00205001200c0e094940860301241004500300102001c04280d1401c80c1c4a48a40000352080304031503000f00e40999800d14070580001084044a8a42c0502000200204207110584015101c2400c501600a100380c4140380140e5035025450203690080c86400c0d159503280d0300c2e40c0b4050b0090015889402c2804a540c4040d0544503602d2205000750480d8811000b0180f600754440e2518060307411014200300305160301da007091980b07608548601c650941c0c0704909540400c1c4078030b10307a81c885940980842c02c48a501c1c900303c15151003d15800001581d910000001750740c80d0101c0300f408074900309881c02c1a0a45105001d44 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 751664955 1250 751663705 751663711
    0x30501020a09150914060f0906030907150c0b06090411030f070f0902210910060305060f180604020f24190503090c04021806031008010f0c050906030a14040507030b 72
    0x138821905010003081c00400030305c0c1c3d01c40c43d044a8095031042100c05692250140b401c131590403041c00700800c080f06400240e010180c520b401c454116251803088111b40001101e0b41c000c0103400d0000128160f400c10410880d00079108104a0200014150109103070000880708500b1503440220108178400284181d030010b880c100f8001d51806178039200d1401001107a080307131101d00005e400000c100341400d1003005017040f507114050065640d6400c2c850f41d200c0d820341c2e80c003001c90150300104403030410310204c00710003031904409482c003543c1d0b5808001102c0013403145a9084801c2ea58110021000072481c0c00c050510721011039102c890a07500e00703c10001d000e15280900401b001445070a031400114641c0811007140c0150340e824810404001040700e900380a60003200200900a080600044107810340c0c582800800a404144e56500c00f958a808071000110394101b0108a050400a0003540d10a00041001c182c546016540d01005501100c00b40c4d49900480400d00810034007198651f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 751666205 1250 751664955 751664957
    0xf060103060503071d0402011106040f1203090f020114040f06090f0504060807090b0409080a0302070302012a03091704061706010905060d050709150c0303200703050c0304030501020a0915 82
    0x840e0605d4000c40f00d4540704800362407000382032000102168030800d02034000351140816540c841c1172038030300b03081c81c0d01303003803000320b441d4956102121501403083c8140003c0e10342080300c120b0342034010b4005560600404611240c80f130780070040450452a082c81500c0107110940e120101d00340b600b40b42004901098000600c141d08001c41003004036400038683e000c1d1005428006542e5185100007001440700010040c5100030202d05050100e402d40c0c090000140640c009014803551407400c04520002402002e01d0810305c90080100c05200750700075031720700348200c0d143d44030b007606000030303480582007544218002400c000d0058070050f2014001c03034200314282003a02c411418280000d406004000c0c540307507d26a03c1d00003070fa0180c810030328000101b020100d0b0b10f03400c8642c0310000380304100c03545054000c40c0c00c1001c128601741204100c8541d9001d42d442c0c140c00c241e07196404880640c04040210b16a2106000c0480843d20a1004114032507103602c4603043c4e103242c8038482d940400c2c9800994 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 751667455 1250 751666205 751666213
    0x121506020f0723091003050a12080f06090a0207020109090603080c100605011b03050d0609020306030f03030906040f03140a05071202030901090e0a021e0405030f060c22050301050f060103060503 85
    0x10580c0300b03c02107a0402d040440b0020440e1341c68840c000c04480d0140d01c0a070151140203101c1c4188850a0201a4036100603503540c4010b68640b038450088520030b950481d0030402940001e8042c006590141410500c141340c110040c5a4465503801034400030b801c140c52101001400300a1420208019684000380c28020f002080c5441c0020746010000c0e081c9818490082000c4000c0502c680201ca8000d14500410000d81d6200c498401c0250412a210b901034405d25a5a184807003000055a01c04e8102d54000c2000e5a1166a2001d16059143c012028804041c41c0d00c03001004800103012128a035548050329800300d03048c490704900450b040c1c42c055410400c449401c1d0307648a034825040d02c41d01b4050340303400e465020b51075000b84203c3c040c0051882219814802c007a1a01d0010022182e00b1800c48a0100780e04042c5510744600780c5840202600400c0311502001800c4485500111b140f140300c101c0c6c59540006c282503c10490388a019000440c0811400d5030701485208041c020944c020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 751668705 1250 751667455 751667489
    0x3020f1209190b0103020f04060905071e210e16080c0117060d0b09030f0406020304171f0c020102091201021308030a0212090f030109080304050d1e121506020f07 71
    0x2490303560f041c00081d00034418a00c00300d03107544aa4018400502c8030180821007468654002428010800050b484503008000030001d000c0c400c548071600c101d0295030300c03401c0c0c07589050000c00900c9039589034807090013070704184d07900076171602444001801600041d1500f42800d000040a1a2654041c1d81500352040706029040e11480c00300c0451607840000e5498544544a2840c41c6008440c400c00c1c40442c00500803811581c080050000c0350001308030001d4020b10500100e40340d00c1e4034601803e000c0c100d4410030541003220380200c0c101e480c07940001868400c40f5004a0350b00c440280c0c051a0702c0e074001401c1014900c00000400041c0580c01c05103050130401070009440d4406840044401c4030080780c8400c5554a00321091000c10008008000c241024a0b1603400ca0304222000d880d0360148101406c00c01e401070124401c150903034030000a2000c01480d080c2c1d1203041045038003a03100d035910325290364101d9644400001e08001d4005000001c1d001d8010ba15200103074200ca69401580010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 751669955 1250 751668705 751668713
    0x601060509090711010c02150f060d02011d130b09070f0e12011e05180109150f0b1206060f010507021e0d0c26010c0f050a03020f120919 60
    0x203440407040115801c0c036007500c6001c021120892140c80a10980d481c011503501d10540000c0e503051080000c41e80c2c007556545490700d0740b0070850111b5081d5080a040301c01d0800641c81061444e06284640350365000c1d030b001010100764181c1c0300c0103c140e011f503034840b0070242d03d29080b40055803040e4a03240045402d401d20000400f4421600750a5024038160040306055641c02e401504000c0200b030480c0340080c00e4149480090401601c4940a00e64580c4d02520f0421040c001d2a0055401c10704441141603043c4c0ea54006005030310b0100c0b0600e56507a51440755a44241501181140745801000c10741001d034200a18100440700241c1402401c00540340103071205c2c1c0383c40d8400c01c07881016507146001000858458184001c004100c000c4095007c2492810000c0d07184110076500c13002d49002580c107a209007255a80c16610010802d01c2c2514448188558001c0c00078841528000d414420714a800c0402600540540c00f50300c00c1040c200001d0315003c101802c0d10440040044401c08510b0310f07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 751671205 1250 751669955 751669957
    0xa3204020a021f0906050f040c0f0e04080a120507020f0610051f020120071e210306050a0801020306040c05070b0c160c080c030f0d050d05130b0c0307030e06010605 72
    0x143d65074503001411102800d40f05501c1403203041e4000c0018091840e0101503c4280b04003100c0440309a14101404240009031111601c1500c0d1881c1400ca140d0f1641d41744c0c907245400690314042084000346228491482e680507a40c014807594000f0081d143d2038502860602e50010008075100d000d08034100302c03903070342c40060100110703044290f07485160b00d0600890142c0030b450000302e000502e03c210b4020401b1044000c2004500a42908101c00c0d0104030700120301642e4030002e40f0350211134444010310409029002100a16802d000035071650b030f00301203441e0a41a03840030055035800300401406041500941c07920854501d4030510700344480d580c40349041d0000d40184c01c2480c010595902154004c9803080743c45400450340340048d980c6e200b1140d40c03450741c856514001e000720b044c0003001540001d41e0b2040140c283e03e44505080d0008030320360042000030240d002e1040301440b1440403600c500b0481740200100d00c0300503503074600b40c0c1000e41901c000129034051a44110010854203138804 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 751672455 1250 751671205 751671223
    0x6080c032e0f02071a04050616080402040203070c05061014030c0a0b07031b0609210206071d090901060f0b04030c060e0d1a070f08010e0112020a3204020a02 69
    0x1c0001240d1100041d00002401101c000034800c11043c00146400703190002d400784500e00c01e4049681a9035003541c0b40d48107500115011012441c0311022034014a00360b00990340c41511494402c2c11010307103890b501d25203032065620010307081e5584e106001e0303074004411001d203206098000302020f20350003001c02c5048107a442100e9164a000c24000201442035200c00440010f07044441080c14203401d001c2c006104011044030b6010000125082c06d041c4016010303250851034000c0e11507035640f4101626503c0249040b000d20080c00719001c1c0d030359a03d07611128010349903280009201e030300b84185215806095004064000f41c00e0108100081505084206480fa1882c00a02c51840c803404140c4a02411200070700b2044120382011084a20610b424400c0c6020360b29683c051450b1602641e00c84428000d8203007012414006000540601c03d200050364070150181c5040c0d0341d51950a14180c59508200c41840c6042c501a800b4102030080c968030100112421460090304100c0a03684060344 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 751673705 1250 751672455 751672543
    0x9060307032405160f021b100e060c1005010e01030b0a0c05250c17030301092c0a1101032915070501090218010803030c0c03070606080c03 61
    0x325400c0e415400d0704202c041c1c500005040c0b0071424485809441c603180c40c200c2400003007070418401201880007c0b103c841c01c0d20402d0703207074600b8504014000e108171041130f10303400e20101459544103501d5141c0180710f82c1103403001508107158040e10170802e540041c1d0040c2c14000703940d801030000c2001010180d070031031150036002918410301036080c1c0b61030117046020048050025180c01c8091068140f180250b0301c00c45003c40c145840f00089040d43d9441205900e10f40d00a04c0144580040c651000c813019034030008068a0358509200d114000c080503450009940150480c5c504000362889448110710b400d083c240304617009000810003900f90710320304001450300c8801c590070503101d84001ca0035141141c042195500c500e824503d01078250b0b4038040340901c203070042d4010105841d680d001e040e80d02c4031000d54a16100e00d0700c142d90a40080451040303a000400c90880003800c58450a4010100003002d4403541080e1400c041c24401c07003c1d24601055901521008a000781d0031705c1803188589 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 751674955 1250 751673705 751673723
    0x4030203160f0c08030a11031903090501180c031203090f06200a1110060308091e0315010810140c160b07180b0909060603090a15020306010207050906030703 69
    0x20070b040c00000040d0425014284000c8008045480d1802000922150015490380e881180490b00c905581e0300c115466401d601c410f20328000b041c01c1c4a03802c401307507650140c00080b500104413a00c5030303a034001002c1d00300d4280d14000c40820030403000310312032540201c0d00d003402c000b40314181d103a07500e0200000074010031440d40c900303040c6080c1e41d20000e00d0011400201d401921450b4220004d0041000c1076005080341c40307841180c10340c0c80031900600c010b0301d6220702d50b582042c9000302880b10341e1741d48040c0c03001c00043e140300f03203251506c040200800a250300300c410102540f400d0010307400c003900700328062402404c0c007082680c055801c0305415000907900507600c2d139801064100041d03890f101000203000d0348a00d024004e205500130110740d04807040043c02c80900d0303034540340c40d00c00e489512000b40c0c1108003200010228980074004d150300c45094001d84e158800c103603582080702d010001c0104001c0d40d000c403e015107540d04000c02406002c069585406e14240900043e59800482c800280441c2c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 751676205 1250 751674955 751674997
    0x16020102030c01090c0617010b04090e1c0305070306060e1516061401060e010504030c060e06160c06030e0c03060103060504060b1806040f14150f06070c1502010504030203 75
    0x4030810454100345280c000811648100d4a03080450544600c50307140001ca000c403d0451a40002462504071800207540926051624103901c01400648220345403038041e00c01401104645122950580e4003995000121403410380005000c0755060340100080103400c015200c819140c000c80314804031400710b40d181c3c0310b03804107140d03402041521000400f51814080b02c00c80482e9002d10340c0f8141e8046459500030314030041c004489134001c41c400034082400b4104100041c6024540249018002420742c91400c030214800b4001410303d200101c0f04861140d01c1040410b50502c070f00111105443c2c007815500c002000000c1d81e808042c04045d110603581d4000c1002c011690380301075800e450140a6103040010b1000301c81c131000c6c0880300c03240128141022401c00545620501c5c443c03500e50007414a49032240460b40d0700500c2841c51180e04441d2060600d0080d60f5180c014100c0a4458481843e11900b007021a172440d40c181800c0b0015a818031090100094000c42903d40d1003a4802e4070380d4501c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 751677455 1250 751676205 751676207
    0x50a110714121204060f2a0903020d050d0e060f1c0204050406060c03030e06220f14031c0216020607060207120c052b110f06161202030408160201 64
    0x8a960b55255182c8400061410518003002060b01d208030300078841009020f011034144030a44011030081090301c040700d8680b2400d20702c440c1d20043d82000302d240480c400d40d00c4e5408510a00800d441c02d642c19400350380400d141d20781c084e0303109038685001e8a02d02d0038038a41d03211202090150300e2420040c3c2c0c91180c6000c2c404661503040d03900400000380305010341caa56610180090321400ca003900042d0402e401c2c60b100400004496000302d011079000202e02003105003c50350603540300c10864005010842444c0812080c50001340061510b50255581e000d0b03ca01100c01503462001a51280340140176190007840742040c14001140c0664000d65240319918081c8004d1080f0a4000e000111100d0203e0b821030b40700d49918851031181c82111a0748041c1003c0c003030500c1074914005000384c514a0b1542043c1d100e800c0809007460903104451a144103001000d041900c211040c1d840320079040e0500a0312036200f1255200c10110b10001c51950405880c0c92a0314822504200040700341c1c100c41d0821a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 751678705 1250 751677455 751677463
    0x1090b040b03010606081027020a1e0809150906070503091e03040501080a1e0b0319050303040b010e07053004030903020a0504060b0d0e01060503030d0609050a110714 73
    0x50071004008220240c5c40c1c038030191174502c00b42c4d0710042e11031031014089a055820710351040d80c1c090102c03014120103001116072029520501c0c1200030010138a4074400c1120300210599604061610358040e14980020b10b6464100c024072145802d0080304240051150081080c0707070002168a0042e45e40d560301c101e454a270170400c0004119400314101e45008004004c07000d0029100d0036a9a954283c680c0b070b00e08000e94100c9400c0da01e803240600500c1c0222017459212140400c0301909641989810198151101908803029245038100208000c20051101102405020803021100d090709040400038254059920b141c01800b80700040d424140c001d00315107644030507003072020044070b250600c2c00825928044c0302c01c03400381c140000040390030701d00f500800c8141d82603112102e007040c04624071040605003c801d0321180d95660700e0b0105043c0c03010b100401c0540100701006c19003900d80542c41044510003824104903901c0c0c904182259200a000c4520207500311a8851841c21a80051424 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 751679955 1250 751678705 751678721
    0xe090120250c05030a1101260f06040e010c031b08011d060301091e0236180a140606010e010c080703030b06131a04030f080a11031c05100e01090b04 65
    0x4c5445450091000c01a10090f00600d190081c0da03900c048583c034508003c0d00d0504021580000710314100000d15825103118125401700c402031001c61039112800c0c17503d003180c05160f01980000d458110802e204098100049059074a524ac0002a03624151040030f07452040000e5041d80c405420110340c0380d03542500144015504a841180b030f540c030804560028417410306080303005040c01c110303454441c07507a611181c0042c2a0554a880d29429564a07031142a400501900c2804001c18014000318010418128000d00c11221034880b03074134050210345012401400c0d01d0412441c480300c0d039131a99000c3c50944100d0b030b120160540303400704c0f880d050b006001300d004003c1d04460301055030610225080e1940007100d04062201c1502e1644400d525017a118500010741200303a00d11218001801e058000d10740d405035440c0c0380319800e0044d01e00c0c0e82150710410030910700c00b4071002c40c181d500d0034030320600b500150b103180d079807461528105d0404050001413051078543c82d03545505a4030703500ca613004a04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 751681205 1250 751679955 751679959
    0xb030f04050f030a210e0712020406090c0e0108011512020f070204150f0803040806070507030908030a12060506160b06040e071503150f0306020906040e090120250c05 73
    0x38550301c600d6801030200d0590110224425071441740c240214549100783d40c1050f00b818042d050350f50070107031040301025554500700c2c8c00942d00c00c00000c04003007034403401d4803218081d034805070003805060006000b0941a08000340e090400b02132400b0440c2c01c007950014104c100100561554030011140d01d9601420002a402c2810201c5c0840903000019610307040e9102500034000341e81d2101c130281e9072405035000301c113805d40c060001318410030b00a10247c450310340700303183c18081300b034503171000c80e0443d0442909840461400044030003080301c0b81c0281000340c0030030754500d4207080a04044481240f9414801b0b8030003400074000c900c00e03444031341040e0040c045d00001c40c0c80b02c40d5a015090321002c1402c42d02d400180c504468001804582e001a008a58480d03071503820071415a1105c9009500c0310700141e0780201c04000000318445e0384d400c0c1074402c0d0452000007603042d10080b020383c0140ea6490248201c41000c000004500c8100b47c42c1000842d283c1408010701030442c81c000004590581110ba = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 751682455 1250 751681205 751681207
    0x8070c05060f01030b130201090506070503130b030a18082b0c020f010e010b06030408030a021902011a06090105040b0c07080303042306060109170c1c06060509010b030f04050f03 78
    0x3902c80071103959048138810a02841c40e642d5200c011202c8800c2c540c03000740058200c2c42700300f1003440c041015082190098003501e14184a00700c081a64584e940e00c4025101b80100400110348018881d80c3c80708500d01444a2806810f0b0392483d40314031541c8141c2041d0300c00b10b900e24002c0034442242c90000c154510040001200c0c5250195403000c4100d8290210360804c01e0040702d6a1044c051251400c6000e4056401e40e112540e07180e80c1134100824584109509100e000580807000320710040348c00701c2d50000070309045485900c0700040d86401207180103420400c101c40d11a42d0210460702161390240500f500c2d841c41550190400007641d008036541d2101000348418000c3c044110440860752001d2240c0800c614410f140e240c5400721402070108400741410841d20882144007401000e0180941322541c2d07460000bc1c000480880c0045401501c1003415400c0014034818200580001c950030f400940c50310610448a1000501821042d1707014404034003000320400510302030400c0c0201792 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 751683705 1250 751682455 751682461
    0x3030705120606090307120302030c0d091701050919030203040b0a170f011d1e1906050102030708160302030403081908011e090b060f04090c200703020108070c0506 72
    0x5066801c0304510300880c5240e600899107914005088035800c07a80034003e00081850034400c030301c1055507142c003501580405c0002185494050000c00040d04035a2220001e03241881c010034218003e001021045a240405012100d0390000304c900010360b039080b154410070264601242107008942c8021001103012820387c0e04030303800100819082d540618000c4465903043d010070b40300b0000b80f04006802d0031202c01607511408000da100c0c5c0c40703d0000030138100c40803070031078000000c0403c40310b950104081d8031100f814000e40740540401043c091008504202c0d103a140e84e41580309009213450801041e040e03940030580244240c1c2c00075900b20300080c0e02c0f041440089601038070322391000030001d600c4000210b13010501c0302101e40a1509406110501c074140103500740203080c04541d107548100b0034403200760807029010040c4007801e65000c3c00306200045800c0030f0711002c80c6c01d1503184865500e080300d1061940018144088a07024070300111262106e2030300395040044181c01504074090740f420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 751684955 1250 751683705 751683707
    0x306010c060623100c06050a06030212010b100c0503041e05060f0903070608041a0c0c0307140c090108061906052d0f1509060906032403010501060915020c03030307 72
    0x2051041c1810b400030040a50404100003082c120031000d000883c01803400c82011404e02d6001f103500801c2070390000f8849440e500001c14401503130004000603074542c0003641050501c085440795508250508500000303090355410b440e8081da0060200c104618698031004248130040c0d100100800f8105c2942c91a02c3d4008915030f40c484090180207104070b0b00000b548502c82c41c0004d02c01c41c0c00440d43d0950000d007608240410102a0007102000800e01003d80198014401801414401d010722113048524006d2141441407510a682c0f051031004010000034a0200b08598006465615502c012082d0444000205681d820058000700882c50344042c1c4803030001c007141c0082c0940f102008500058003085001d00c1c2d042840b54100320043c080c01c0c1880e2540000d441c803a04002d222600740300c50324001c501c581d00111554560388041a01a250407807050050300d03030821055000740b0072581081070151403120b66119581095101100d0742d484503100744018020504010180c0780d60741044c3e10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 751686205 1250 751684955 751684979
    0x110609120313060504181a090a1409010c05070f0c030503120108210a030e0a0204110703110f0d2a030306090f0608060609100b0a200c0a0b0306010c0606 67
    0x22002c41ca200c2c0c150001c500c1d14040d500307030740c11101c0170b1031a002184400c881042c054a204a0b03c50034407645070109441503035440c2511031245903402e80000e852009110b46808201019000c00c000b6490400303c04010703903110003203c1145801c1442440032212901c4e0040490201d58006030690001180b07101101411070040c070f0494529a08581120614110b1481c2202060f072550901d00c0c030400c44081c4103406500008a440c9040d07041d40d840711040c3e00801d05681038824069101c4c0e40001e201000c2541140804020000e180d00400c0d001408040c04d41d9901412200001442800e00c8180d03458000d184280003503001030482c40403085071500c0c0150240c10640940c400280c01d203c080f01c0061000d1240e4000c60309500c005104949450051183d90703140a402c5207001028a8000300e012940c001c0148003460103582c0384030b241c09010040e6020002c1400c5580165040640040c070b80741e4403084400c0907078041b40c1c403869a985607071006907101540014000c000d2401d0020001d00790358580303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 751687455 1250 751686205 751686217
    0x100615030b03070b0f070209010602150a0e010e030f0a0206090a0c0509100b07030306030302010b010e031002130812070203010506180a11090d05073b1003060f020a0306211106091203 80
    0x30708e2041c81070762194000da0b1914045650260b000b08650005004040c06410000212880f200005080c903010a5800d080d50300c1100002c58428000900103c040d60402c0313129403107090b440142000689c1caa0b00e49907903058500c200c4d4800d240d0040412103400d03003840428000d00714601e4950b47c5a100e4a80a00500b0580c44140c000d540303410440340240d4043c4841c40412030004014060f18039643d064040290403881c1400c410800800001ca030408040024080c08101345c0d40280d121b48503441054290340d0000e040300d000d01d20103a80038002c0403018800e150480c00c150700120700c2440c0c0c06105542c0c0d028141d02d4981c4004441c202c9814418042000819184100d08030b20500841e411140e42e50712180042a515586100030031302d01c0c0510105040e005046120856031266490b00c90001b0340d00c4640044c203150342e00017500141c1c03a40510401000701191546507140e0521075008444209410001612101c0a402c0451680d6030310030407511840f1005004e100d0003103c443c20644c1d203070446 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 751688705 1250 751687455 751687459
    0x3020418050f16021f0e0607020f0c060412120c0606090609050c0307020a0b041509140c03070f0b0d020702091317040f0b07210e0102100615030b03070b0f0702 70
    0x71002c00e152880116070090586441c0c2c000f0025541010720110034082c1c1903003845c00041d990750110f0a82c880510103180030f0b0302550300a00102c0d0841c5000c0e0300f0940c519640c1440795804000c1004a609152600e03200107820030340300d00607402940c1e020f40d0845020407008118500d00080031444101640c01501642e000c4032042080e81d59554401010344011748600c800740e804205030a0010300ca40310f0881c1d015104120007021010340c0e5040d1410f81c1c05841c011a40303400080348100c80c5650820064400c4203088004140d081d01d400101102e007462400ba01c0710341000058201c003071844d00d0301201c43c0030b640605100c0f194582a001241c10040c0004201c070b0600300a104005000410301c00d0fa016601c44103480410246403040c140c480380d2006108030745444032141c05140d881016900500400681c0c0c03568000e442031800020b0402c803903401c8148c2001e14003042400301104040841ca0604cc0300d0a0016400c540500000e28012040c0e101f010501c02c0014034600c0c5041440150100d1071003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 751689955 1250 751688705 751688731
    0x31d07090218150f0304140d050405120607090b16081605070b030c040e0402010c02030a06050402010e03012003460b06070201211401080d021f0c0302041805 69
    0x410100281c1c3c1d548404880700b056001e02a078000f62640c9002980c109100709240d40300003500c2c0c001c060a00140c40c4085000c40c4000ca810000d03410701ea00d48220004240c07029041c140b4094801078220a146d019984a02ea0003284840509907502460a070710394202840e42d486050947d541e14100d1081101114075016215001940081500a0300d001c0d0301380d021041d0400c0d0801100c4841c80d840100305070304200b051100000944c41c03d01424003400d01038000800c00303242c50300001d4200540f9007401c1d4060380c58061400b56901d0222055001c080c0e11004aa9aa03180c00d000c1040c0f8050602c0001c00d84443c903591144680000bc0203001c07010382c004146054038024030009411100741402c0710341c00c15000c1055100543c8180491a001503100c1c00c8000d100c829440b641c1d044480d000d00d489401c0305050b00601202804008a00521250303200410802c0d0049024594580c1950f0507031720001c0d296206004440e010340c0540340908041b0008808001155010394094075050350a0100010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 751691205 1250 751689955 751689997
    0x150a06120b090f010c021b0102010f0f0218031204090902030f030f04080709020a05030703200309030705060a020702030a03050708070519020415061b0c030c0914090f0d031d070902 79
    0xc180500c42d07816045070060040c003e0300c020f054140e807e1041009046568071b9a40c9500c214081c0304610090000050041c0ca070f42e8007480c06107480b0b0310914028406c0d84034110380000e00c40c2c904110f038191070302c001012a1100340b51000c00d00d400300ca1300b2004840e0001007101c003498100203001d0011510024102c40352030703640351900030480c829a05060000303401000000c120701e0107034000300029a0910001c1c02d212842081502c495042503903040b2950300300188000520904101042e0031041d4143c04524108155000981e94080200c2c01001e2040100e045028881594141e460680c0c02600780d0b000500c114540c481c0d02007a10310201d02c520700c0c0c0120300248104000700c007002c0d0b0b20642c482c1100100007002e41031900c3c0b891482100d00317117030070800480091061048000203003560080490203c1c01c8007007041034080010401100e5611003d1001024000002d0b48a2820214240000c03007807940792a0181381141400700d00c00600c5141c00019400380103a0042484214030304400da0912 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 751692455 1250 751691205 751691233
    0x80d02190f140a110f01050618090c09040305070503030109060f2c0c0d0e060124050f03181e060a02090d02040f23010503100905150a06120b09 63
    0x28003821000301c0010400c1102c010382c02282c03070041415880500301451202001e084052401c01a4084142203944500610446003481290f0b20207801c1c12500010a910307200300c51960ba0141507813598442da03220004207090602600480c0c4181b50442c086e41d03a00c0d0384496034040a80254030400b86441281040010054540288652032000c2c55600300c8003c9200c0b10b034038a02c414043d0030302d01d0303002c01003002d003503010a03620035140400b02400c00707090590326240024a5070127801005c040d407601e800e0851100140e1150446960646017005c00782c40380c40724120400458086001e8140a21500100e000400c0b2040801d2001c03814510494040d90f070b64803081c0c0103034019100600d4004c41c54940c500d0051415400003019000079410004840f8140142c4c0a5034201e0504400503902c07400d4014009030505003c1a981d000e120704045c40300c460f13240e461541e9412584242c51020844401040c0c40003000e81040c0000c21652924114000071810204210340c2c09645451092103480c2d4180c20320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 751693705 1250 751692455 751692467
    0xb0f01030c050d0e0c060a091406040302100804060b1003020304121d1c0b0106080403030608010212010504020c070305010204080d02010b0301050f07050a0e0a0f0513092d080d0219 79
    0x1ca1041c1e910300b03003001d0400e014100680300c0c015038458140560030365a1155102d030340141c090b0310402d42d94110070f5031901041205150350740d55101e001d51401c100c00d1003da2140c3c0c03200800d4100600c5d001149a8a9041c60380041c102502c45941c8000800466449941d02d80c01860180c0c4c0503041002c0104a40e840c02c1e070b581a10440300b6200c012496080002c5403810100390620405c5030030841201d803100344d0700c105a02c6000d80010000c28180030a102c107055040c85418060404031000710300d002c000001e00c02c1c1c2e000c0144121440785400050800c0d14100c18006035005540c080001e645543d03c90515a4561614411800040d841c1280c6e1000b90725050003010302500914940058985070b42004032101d03442000d1440078005da00340e034484c5a480d0411548010910101007404181c282030803c00340d80c10f288103881c01a81401c40d41c00201e4041c1c0c142c40f8140c1049200300001915684808000288042018280d4075000c60f080c5807445060300242251a010a4170410b170300d16180c000c0c4d0354 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 751694955 1250 751693705 751693721
    0xf0b0a1503060501031a0f160219051e0102040305061302010203090a0e011d040f080708121e090c03100b031f0501082e0902010905030613050d020c0d150617010b0f0103 74
    0x1104c7d1844012450440745403110003c1413803584141c68240041c0e20000341400300e1413204442036400002040101c003242599006600f0800c0700035490986180c81c0d960f40d0f1600a040303505600040b1504004582c000c204403092044040c2c0070b00c80c0f00d41d9450f9214035480b001d104d4951030500228184070140c0d03969980741d00c2031394443c840403404c5030940c48090454100000440b91580100521034414181c60740951084c0700d0b20400c800c1d01040c4060040180d00081c00b01150307079114406143c001c6d500828508c240042c0280700050422040001a00d0a00f660003920350704078508001403c501d00c42d40103e03041e52140002c540c281c24001c130405041e103008a1140c2c000501c01e4000c0b441c2c030180b07508901009801494400d103025203c400090601c982078400e007181004050860003001014040743e11004040d0000e480841c052001241500c101141d0040c1818845002c0034840d5055900c250050304080410007949042070030407074000c000d00c02c000f5219500100010889601c603010740b40c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 751696205 1250 751694955 751694971
    0x7050d05040c1719170f0f0307020c060a0c0b06040617010b0a14010c06020702030c060a0309060f150315061517090c010914010e22060506070f0b0a1503060501031a 72
    0x200301320b06925030305400030345050b01c01448042000000c4002e18100003411081400a0246136642010000a86800c0e1aa2806030240005002c1c0c06201b0341c00410031641700c1c1c4c1055910300c0315580e000008005201e260018402c17455840428030711010154840d0241071000e540d44030301661030ba00c0900103503040b07520721030024020b4030b42140000d5081d005445020720240031112607026100c00601550020030902c400280d54040a80c14091070380174440e80515045d20400c01a00084c1c80e040005581d400701400300c40d1400021400f9554962010005103140d01355480e429907a00d1004001191b468013001c1d050b4070741c20225040700004145410342000507116406014546009400c00e50b83d800b0215051240d29500010607880388a02500004031284c1c1400011075a1403840048440b242c200a0080c0c9043c4a503900103600c0483d00201c054202c4d800090b0341d500e22410030b000d469000d000c0c207061074601c00d0000c03c025030f40d0803130390680340705000c00d980071213440050428000007203450300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 751697455 1250 751696205 751696243
    0x10806030f031e090a0e040b310c030c0b0903070e150f0111100f0c080415020c1c0c0b09031306050f0f0408070510050c070e07050d05040c17 62
    0x99000e0f003201c215020280d0200026007450105000549501e8580c1d11400e42e0030900700401042240383c9445d142d04c06050b00c010081c2140d0103032400000d01c107846000800881121600c000e100c174402c6508000e41d800b0060580c840c1d11401034184a41101140300d02920030f02d030000c0344074800310b0748c2c180c812040c0110764050791040788204080e210300f8072a4941030022018640c60740303c1d010700018080030f03101034000c1250030329038400310106c60420203400204105041440000355000100c0d14100010070f80141c1c032007000319010b074100b01c074460a03204102c064140d0400f1302a0044201d146040c002c600c40860350707540f105915100d11910520f0070b945580480148001401900030300a03980480c403126007880140445803140f41d01613048420750f41c2c4801010800c5241142c55140301003102d02e04582080d4400035071680d54012401010114000c04000481d03480c8584155030700d408040e0f00600181c10f190400c5140b43c01e05004071050314480e00111039914a002950f800c030103814014035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 751698705 1250 751697455 751697467
    0x180108061f09020a09080c22150b0415020d0e1003050a020d020d0b040e0a150c030b090a0e06011e030303052e18140106050c0f061005010806030f03 65
    0xc0750055a80380d00c6124141c116001c007003801802c2d0320207400082c0d4151903017070105040c401c0719031601c201c0c0c0c3e0401d4820305440c1e4100030360760800000c04803002c016450214110f1580f200440050f20b05812002c400301006c9000039450040220bc2d001901c0780b6002c0c1e076120500004229002d148040f5a00c1d08010303a03d6203a5160382c482c1e4060b56200c42042030050030014080c00800903641700d00003278491a6140c0c00c0290301c80c60326105a98100030820018001d16200b80c0e03d40c0403060740b04400c102225915102001510b020381c2000f455860010841d11480c41c00010748001825462040901c0d0703c54003002264480e920014503280003e040240d1807000d16555040700681401032110716500340d6590a15102d0310807021141c104288102213005841c108541502d040d2000d590002016041c045031241ea00344036000141514a246046669041100301461909a04140741c024034850b050400140303020a100071819a1001d91718100c3c585c50351020140d60310306011200740303650401c0002e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 751699955 1250 751698705 751698721
    0x304080409022d21070e190501170f0105060c0a0f06140a1103060402092e020f0d05190201151e1e14010210050709330806120f030918010806 62
    0x405c0e0310000900d407026503e0030780400b04800860b054606140403880c1401841a980c021110680aa00216811040340382c15171401c0b59050042c4101c9002c0e500000302d252204c0c00030300030142081d810181440050800380382c09001481c1400c0d80002294104010680503c00c0b4060780484100d04500542981c42e003804204c002c1d8880040285d01143c0c0300602c0e24081c900705e1546001d442c00d000d008844074000c0c2d0010b8100050402030081c540c01c46059001c001e030300301c02510100b020001c6c641124040404060303004060b80c902100e080c95442800046000c98030a042041094603601c024180c0d64038201c00030125000b40d0000b902c0107043c9400c0c04810f100504004916005204407000504660b006004540d4159521000640903880602c04a41d0455024482080d4280d0403400c0304d400c1c0d010200b5040c1203004c01010030040d01e001c16803a54038521080320508016056605036070114181690300d600204800c2d00544900d180c900104145180e12412200c00c82d0103891156a41d4071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 751701205 1250 751699955 751700017
    0xa020f061b061e0f01121506050306090d02010c030c050f0c0a08030a0504110607120819020a0c0606060903050a12020307080408010c14031b0304080409022d 69
    0x100408401c03520707610400754010108010b6005a4002e00040d8441084480c402224440104180b04a00c5860010885d148035900311070071141c3c0211001c960720900014000141040307030b1025905100c4c1c1d80074020284d90101c0c14003413415240c7c00030080902617003411360649601030300c40008a01e05000d840c00e08400c6800916030901410261005006141d032801c1998006940c51040700b9942c000704400c020b04400780d061907040c1250081e0400d00700744c0e0b03105d01c1081e050068504102058000ca0424001c281034000c06007818407040d5101e03021450000c207005a1a601943c1040c10a01e00080f494020300c814000e5a40100c0901800c6506880310300089583e00403413000c6210801c4001c012401820150010740f032607200202d05080d44000080c0840003508000d40815008c206000d60848940702c000c07d1400a01041a202c2d51207041c0700b0030070301581e4403441515000066880300c94020a11052184030f00c08640940f00a50307040d034a10902500340f00d20800b2034080034481d60910b80203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 751702455 1250 751701205 751701217
    0x203070f0c1208030f07020105010315020a0c1401090501113f01032405150d020f03030705010507200a061107061506110606030d0f0c1403040303030e0a020f06 70
    0x4003540c00002d0b034400703000c880c0070b4002806540440c000f00620003285020b002490700242c46100901555046480b48170781516029913004205500040070045240100001c49685800403500b400c0b100c1c080f007d09002e0420315008958652905c0105c0900480e02415600e0350810404039000588000c8019591001c2c508854480120156141d0000c59114092a4040c600c1040749600c5008280f80ba0007845518032640303400c2c0d034280805c20400e134034002030400c0c4007101142e441290300f0301400805d1005600d44291034040c080010340c0001d112054100c5405503a1b03d960750103184000d441c43e121a080001c5103000680c102080744d9001c41e0b010342180384c010a000320f803036160041598882040f25850110062500d0180c80c04001c00e41d00003007050803e182d0000a8011031030b004001a1f140c000010251081c452420040308002c4c1c42810041c0703c41d5400300b81031018205010b0300c40c1d0ba03900644401c500181c1010300f06600002c001c601c50790591f80c0608191100c0b11070104208031a0008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 751703705 1250 751702455 751702463
    0x1060e011a13091e0b044a0601030302060c03130b0604110d060602010501060c0f060c1407030c1e03120506240702090a020406020601030f02011e050a110d0203070f 72
    0x164800f14404550f4482c00e013003018090060701040180b440b00074150b800c4440384511641c45e2004020700320841181c401000642003180d1001010aa181c1c5640d241082554099910801c1103c950340000041d0b041c1c145c0e0b01076021074265a80c0d460b004080c903c41114400c880400c0c0e40d4031240043d51f2840a03580107000107001003a04c0220b640e0f0300c685c940041000085141d02da102c104111502842010b01400080c40c0288e481d40213515980501c01c51030400400b0700e0313680d050007980e182c440c103075003001d525040740c66968565007410010301e0300111060a95401c2c0c0055541c11580004040c03442503954581c6030150300b59650002d0200a1000520f05504801c81044106140704146464407141d40307900e200e00d4460b1130700d00620140203001801d0042d198410081440b2081e00015504e0450368007400c4c1d100e51a90034401282c0c40c8039030162712038003000141040300e18150054040c05858400e03a88074407071407040b44041c503900c01c25402d04030b0158008010302004285d110320042042405 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 751704955 1250 751703705 751703737
    0x309020123030a0b120c1e0406080a05060603060f010608060d08040602070e150607020919020301030f02030d2f120d09031103040e13060f0e0c0301060e011a 69
    0x140514401009090150070440d54a00200700203580315544515001403a0603500300c1c29906110300e085640d040184030851298100071080c405060f9071840b00c070140000500144075081e80d401a0740d90318811858100e60601940e030003d8030320300b00054a584680c281e4034100b81c460f4039210068078480f101800090b00a003d45552002140e51100104020300781980100340940c40c0551240b0b4212001c0d04820000c0d040082040d8039503100002d55406540444090099480e241c2d02680d56400342026001018004030001040c003807100781408040b170081d811307640039540030041183c806c08a0301c40814900d49003001e400e0ba00200503a40c000400420044960428038030001c03803115000146082441c80e16081040101607100d40811440c0041d03c00460801e402e010304c0ca0031031480200030f61048401d4000217030503c4407941000b081c01d01001c100b04003217440524200e458504161006000398200740000a008100900346c0d0304aa08000d1074000c06030794826115251343c40090800d8250700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 751706205 1250 751704955 751704977
    0xc0d05030c031b1b0607030c0203130e06010c05010c05090112050f0103110111161a03040503030703051b0307020a03030632030a1e060c080601050702150f131d01031203090201 77
    0x3a40f04102c0c82c0480751100074240d46c43e04000c0201619007458200b021500113003c201d041d90b06655058098884680d0303038082540c0d5440040b82d000d540800003426039800e0241000071241c000e402031032039050130784c0c5401045020715805070a981043d40c2d000c1500354030f280108003040e80002410610b4405140000607202c10440b03a0381762640103650701c0b40e0583c000c00c2c20002c24082c440240174881490481c1c0d411450261105522400000c080b0420305440d0300001d83c401c2101c0c4180303100c00445030001602ca00708800000d668506002c0c04501092510101240070090880d0031030442d8501407030740b14026108240210402c405214007601751003010b071000c4c00581c1d101d403115004008620000c4400c6c1c06410160159152282e0000c18000c000d03042c0b0070140d80c000206c0340c202d030701039400c2c41c00040d01d0022030a030340c4100e00e070312240d1040200303120061702c812100303400c00c54907503000c00e285d44072250070703811207408080c40000d0036028400383c0707021424080d402c92100c0d580141040740c4945 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 751707455 1250 751706205 751706227
    0x27030e2803050f1b06070f0516030b0f070513060516051c0e010504030218190e01021b070501020717030d0204030f120e03030301050d06020409110c0d05030c031b 71
    0x141690022107483d00700c0b90790b640d082002080000746459403c0b032140f19030341d00c540205d80d1138418190007502e003000540455060000070003d0380d18554450b0401001c0c159241082c4a05401c29200148100c10280c0482c10f003521840a842a0941c407080c020160342c40e041c1700303440b1940034040000303283c01c14021610120303200748024064800040103540d074080c03100c1d60003001c070040480c00906000041c0000c0c005a117480c0603c21002080060341007080d10303004843c90420442c400c8010710030341003d1900640c0340c010340103004030244442c03010618422403564161106c4840c02002c0c01680828810008c0351039034a82c1c01c0d81d8140a0050300e241c0007503080310380280c1c0d000350425540c600c00240e0070301c00c1040d00c01c0764040168061604281c0d40c03945e1400079407130744010f202e00380c03280703044030140018082140c2c1114001c041004c0304100c0e2200e0304841d642503400c041048141402012901c3c400c2c80c0c080c0b01180d120b9118030107081d144d55150244007200d4041008010007034001400b9108403c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 751708705 1250 751707455 751707529
    0x9040321150609080709150510030b04050a23190b0d050a0c030b06030c0306040312060e010312030c08070816030e01090f0203010c090501140309011e27030e 69
    0x103001e0a94412071224101901a03145c02e856134401440c042c64402010034100c6144048130039a1411071300c6030702d62031600404a004d0303c116506558054609030600c845007210707500c0014148080f04803000403032600c420304d5108840440f05480c81500184600444082c4c0d035105400e1460010103070b85203a000e03501d5031807038542c1c0103074111a00c0081c501c06209001101030b0b0f941e0f1011080b4000d14507000c174840440d07100d04000d80001c0074020f2980070820f0810045e009071000c0d00170152660300a681d20b05101942c03003040785500340800d180800796500d041c0f2401c034442c030488003615034540ea0380303608019401c0035038010a40c608255550507201100381080c01600b0515009020002040b01035004050841f800c407000c200600c8070884c1c0820a59030030060f0001c1075501030700082d4490fa51a0031950140c00080d04140189400070040f801c0c1481075440908040800400c25040300110905480b0020003000c0160101d0585030802c401481c1030b011f0b6581c041ca0010301c624400c41e45024100d60 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 751709955 1250 751708705 751708709
    0x1e0519030c08010e0105010f140d0303110a020705090903070b1909140a03090609140f0d0606030b04060b030a02010e04020307090816050306060301140415090206030c030708060904032115 82
    0x20b20b94482d00d00e0310740d40d1000d002e07240c0500080055000c0c0b0500d010505020b1543c0c809003180208040c40000e02854000d03884100c2070030703122004595490802c10300039120303443e40c01183e00c2a0328440104d80b180e038001042d03e00950744600700d0f0240743c03944840c01842d154031514034254030340c0310305060340080d540c10b0607203641c0301c1c40000a00911500380f074080e080a91a400040800004074010410700c00e000440c5148c000095480540d66990350703020074000440c048028081ca410b00e1000400c00030401d0485200c1c80c09000e04001e890399502c105601d40420320700207400203601202c4920309151541c020740c1c00001c142820400c540c1e8032403415041504081000c0100da8050742d003001a81018082c40c0c2e07000a040300204109511504401603500000d000074107080b410b9a04000702c062150301801c00740307030000c18058491825410303507046680201c0c2d500c000500707a2004070f82242008002a801540e150300e0322441200316000400f01d107155800e200d03520540310400c4200c2010600d1800700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 751711205 1250 751709955 751709969
    0x32409030906020c090f160203070c15090902040e010303050306030c12030c0f0106080d14160602091f0f0302031b07080a03060605070f1511030a14011e0519030c 71
    0x8580d14040c4044d082940102d034241c05400f2031000c2101c080d003126003095000e01d4034540b2025810021004a28601070a00c0041142c00701c14004030300b59202461020a0462907a1081802500c4491060580c0182c4c494140119151001480080e0007400696030109003d0200c0c1c1c0c1c0c41c08054000342d504502c1038030362040381e04002510040c1c00f00038850040c546422100902c142c515250042c1d9641070000080c008001d4480c400d00b10344804041124a00c86080c0c240c8125102e00303052240c02540070b040329074400c0c00a1130003005a1920005070703020780005a1154002900c100d0800e6019610081c001c48408403040e45200314500b441024109450007081071586841c000180501155034980180701444014480800002c03400c3e5802070f207060780000c0c41c6811b0b200212004002d420740610100d0100d0300482000a1a00194042d01d60340202c0d10102da6540d90301e54202940030542c0409070381c0108800420701840c2080d0078490108a0034401c0f030010756aa13511108112501307070f0000c507 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 751712455 1250 751711205 751711217
    0x20f07060b1306080a080d060e010e01080c040603020102100509030c0d0809010c0804021c0302120406050a090509071b1403030708070e060901050a0e13060609030201200703240903 79
    0x244032810802507268060011140811059040001130759640c60202001456207034009401d0450881a030400001400e007029800c0440d40c594445215440007406129080d00c101040d292051909020310401c030398041e000740030700e0246481c1c240080e02c4000c0540e80c05100400078150701007010011105d06210380d5841103403504259041c00d0035a50104035510030082014240401340c0d03242021a03c58000350b440c10004d4081e9450213a041c111900040001d850001c030f80050165001f80081c044a292a5a0101e20a0311030301000007120341528008001790880c1d80c00b090a031054448210300e94001e000d920b0f0015202c0b0f003007510355842101d2420009200b0700074000a40e811482c11004000c0443d0914103021304980020700a0203008902c90801c40d500030078900c1922801610260307003020040502030983c5650000d8000303c10391100b2130024261180d100e00e400c541200e000e122f40500310281031020310f5a10f440390446920321215050101c98485070480041d035206d1040d009100340c8a503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 751713705 1250 751712455 751712471
    0xb15030702010b090105040507020c01110106030f0c0302090a060803041a0d1a090115021507170103030201020c071202030a170f180f12061810110301050906030a08031504020f0706 79
    0x70004c080b8040e88000d0080e400c103024004156004945d822082c1d5080c82c10098048002d8025400b415440e0f1002e8288800720045d01b0502c08012400030942c0c0c001d454101083d21403031020300403201a88280c407038581041c042803144074011102a9148002c41205606104d8400c1080e4210307610382703918440300f50021603540c2c1c003418403241c414010561900c10041010300200b0294071400091000d0f80c000c030300c19000401180c064002c51001c0396140b592400c040d0307164507001c1c0c000e40c0688204c4100784500000003170000d407060100c20029501130081c2c0518807040d074442000c60414100c0400d814014030000030140c0584000e841d85040340c8009615245c41c1d6030600c0503d10400c1c18550052600a081f002c0700d481c001859600080c954460340803510145100c141401031525081810300c3c18441710940902c50180a14180c0c2c2c1d003160340c084540c5400080699440b60544010306545051000402079007051002500320308000d00007628000300043c9850f0b80743e100107001c541180d910000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 751714955 1250 751713705 751713709
    0x1c050c09040e030304080f03041a040f060b0a1202060703020f0607260408030f0a0605031203040506130f0308070e0a0e0a0c1112030a020706092409030906030b15030702010b 76
    0x81e400182c0c60305000345103942000e8446c1c100c80d200301c200e100b14205001001c6030401c5038924111403002d1004424820b10304091070620380c13401c2107013401d5600f10306216000d222450900401c2c81240e00101222540c03800310303800d00c035003500301d9003050302940510808000c0e1500309102c0300f441075526996100300c101c11001030942c110320300354015140012200c20880080c500000322508405c15107840e140541d1101283d0740a445590007543e014080c0d41500059408542e0107140500d21544c190f07070956542460500c2105800c1001401c090302c1c45050b5800700340281181900180349140c0403a5000280d03002c155080100d600a5545201110401c094444188201420110301e8a8141200c2e0b030b100050541e1050520b811035400b5900001103084d0369a984d048400c940e030300071014401041c16040c891100310b0310000703c040110852403910310700c0c03070355100e0300c220154162502826981010780480041c00714130203854002c1a01001210040407000196110310700a034000f03d814890002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 751716205 1250 751714955 751714961
    0xa12060312020f0d0518120703020a0f03060531060e12190206070905040c03061a0309060a0e0a060e100510090e0c13181505012402060c1c050c0904 65
    0x40c1081c20018144040506c03944091000201c00f0004c54000000c02c1004000030f00f00200b50384029445140054001040300c40003807500110b900a010420131a595074030b41120b944540c00112000003034449d00fa100032507002a5000d0020700800000800d02d400c0b144091420414120120701c1c608082240c604401c1251010310000405202070040d074100084040c18106103801042d200381c1e1a403e6001c205440382d40414000d140d1902d00c00d05000043e101c07207800381d2058490000364002c580003d21011040e00417908081c1142005043c1c3c06500c0e1102c0008180c0c0c190321715514040c1801c99014a4001c0c0a25400340c4101810703103010728030300030068003161100c1d80801015044841452010350316010245d124030614034000c12500f0600142c9002003540c150028100004001041e1549420381c2c003c074103807401c41e161001e0a03041c04000c1d0310b460403880c0308100164000c5c4001004080b80e0707406066070703190340c2e0b4980c0007000070429480140d03041256040e90340700c0301040b449154074141c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 751717455 1250 751716205 751716223
    0xf0f05032502031f0e03030c09010e030604030c02040207030c1a01141512070201061502030c070f030807030e03102906030c0315010c06140604060f0503030a12060312020f 75
    0x10314148440106640800d0b101c920440c1d0080c8000007410b0031a00a40183d008441c00580179410340360380749800c41c0704085980224a0040c0003c103120210792032400e0000d04a800b4542544400c001030400350700b000040d500861046080000d0300070f10600103080051b0035450010007156a00301981050860009296102c1d40944280c512488816002000c04200e80406030030744e104549980d01ca071000d038050a560703406060300c05024003a4142070340c2c0c0840507090000b0044182c840c401d03518148c603440310207030340005000b150f010881000001d000340c404011500e0041c0c2075403107a60695010f0012120b500c0c0e0f8881c544100f41c1d91030a050034103080103506090003228103a0444c00c103030182c4544e6000c010001d0242c8586c00342c01000300c0e0700540206100316840b10082c0f10401d120501d441c224582035a245000f1401d00c100420704515070300c2d04e00c0a64001800450401010100c111111108803026841180c2c1d1144017002280d407411841420f090b458000300aa0540901c205241403600 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 751718705 1250 751717455 751717507
    0x51227012a140105190b030f0a0312060603051603050618010f1724042a08100603030e190f09230f010501200609010515041b08040f0f0503 61
    0x1013001c01000c42c619a0400c4107280300b410380007442c800f82d0000300b0300e003c43c2c0341805105803040c1c4054074205940310a031001042078011007882441d0350355500303606a902c169118a41540003226040d0441c0c803c1d07011550211000b02441041c0040400e083d820303003000c0c0c21005c04494103160900514070420700c21280303080c440000341590001c2c000301c800c440105508840120406102140501030150402c9a1501d1011340822202e01c9013410a856803419105150860003127051a00f0082c0c442d1064070300b03c079010744905e8400b01c2400d00300b2249101d03410700f800e06400d40300707404030350440c0400e080c102900340f030140000d049517094a0740c40c410841e80400414950001c08000406240010712811510b013800c0a282c9000c002001e9152240041400c0c034107481004c040241000054010030301070f00e01c4000b003034000c4142000707200c192a070300001045444007500000c0c01141c420146540e203d0300640d00301c652010180d4071101c101c4203c08082c1d40d00d074000b04290b506041600700c1c205100c441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 751719955 1250 751718705 751718711
    0x110d050d03061d0a02030c07081602010915141309020c06070801050901120f0f12081005010f1d030703020d03080a06050d021305150d0f051227012a1401 67
    0xc0040e040111a000618440707113150048081144024400c06030348140340e02110b1540c481c10120101800c059440324181c0c00a00240c00000c3c8104a05803a035925513000c2c0da40d80c3c400c2481c5140c0c000c040e4840c0d0b040850f0440102e10004450206101800080080e80050102da0414400042c2040b806800c43d031703c00d0598400400034101c01025030b003060b03507000100390003c0c0c48606241d4591460294050291180020900503166005010700d20503d44001440a015242c0004403038090204d0420404a146207452580006a500c030440c5440300041c102d41d01c842e240c3d4017250303402c000b0290803808a840b160a110510071540180c9014003002c0d100540c4803803d90700003400c01003290f1011200295182d01041c03500e000301e404840c0c0d03844068264180380d581071500041e44c24003000d0558081c06030388104001041c41004482200a18841400c00301d0b1003a80040440d203400d4000b141482004070302c400a80310b440140d100162088800d802070243c4609004801000411b0290301d9a45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 751721205 1250 751719955 751719989
    0x3021608010615091508040c180c020f030906040e090322080606031902090a1d030c060c040e060105030709080106090209040f381f0f081e04110d050d0306 68
    0xa0360b0b0100c05102141c1b80a2040d0740300c604141c618548160048102d1a00030103408014111680200d5810b1409600300d540180100d80a1a140d01030040305542c0070408120401100901c01e11864210071043c080e240303414480411074401c81c1e40521242d0005030254410132202009000c900e03440601a000303000c580c280681d541c000b6406401c0001d00c180c00c400045800d103003140e4003140c4001c0c100501d4110001c4c2c054040c6650f5005030b400340000f44580340004140030070110581c1d04840ca0056601071310b0300e5440c01560b1982008001030204803a00c0800034090000740101070080c03401580041e079400c140820700c000c1d0b40e84803911007911740c00d2010403500c803c0c020720207105005440344804800350408034503026206c001c200c02eaa00910460710030303007006004d443c00501d40031541c1f5003142c0c0d409010300503202203c049603d08081c5c111540c202c5200c00e0050800c0d0742c041c0c420381c80108007048080005041d14110381c4151010303030200e011040269018440c46c00504a00c80710514200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 751722455 1250 751721205 751721219
    0x90b0903150720011e0908031614041202011e0e3003090117100e0c091804030908011a0609040603080406050c19050303130302160801061509 62
    0x203007150207940a031142103000900407501c25410020850f80c48001442805503485203180a860010600d1081504030f4019255460080c402c0c00d50480c0c0c425521402c59881c4981c01003841c44440c8500280040654081c40c3c5a03081401880501103017102461400013070b000041160001c0f9102081840006c611810306d84e4016100d040f0301c101c21544409400001c0c400d4044855a40d94940751516050710813105884020018041003942030344d641e40b40d400582c038038158a0b507090340d0700c201c1d103040d00f1410f1012070400070b03007503030304c00000700c00c00b403030100380c4d001251804031001c2044607a0620281070104041c4d02081c81401016804020b20203511003220301c58000007001e448602c0f0340c200040342051170312140c10500080d90090380140d00c4035034450014040313a002d04500b11031030203640c0000460002c42c0741d0281002d07410200541c215030301c59014510700e01003440294258815145204c111195040703000001c0e09001c800800d02625202c3c08156041d81c0c05004814801038960074050b03c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 751723705 1250 751722455 751722463
    0xc090506090319020f060c01050a0c0c03080a022203050a03030e01060819050106030812152d1201050a1a030703050604030f090503030a09082e0b120f0706090b0903 72
    0x810b00f0103010981c0b00c0c9552002495520310800d4564100310040b031fa040c01502c06510092158115a070240100000705104490a01420000401044000700840d50104081d806400e4a000380203003040c420004270501440e0300d00e103a200700c686611500050040643c103000704500851140000e0113044d0400c1c80c00341d103460481050003041c1c0c40070780140e801d000b02500f1500045400014a9544001d51000080e08400850320610120b4040340b81c0b820b1418040030103e07041d0700d4585114070350440c071903181521150f4502c5031a07000e610440c0350700c0c20301d90a101c1c880c042c02400c000000c00220000c1344a28a040c9201c40900c65008142c040010510100f5002e0344540d01d840c01b0880b03111a807200340d54201060304055011710001ca00ba040d100d4004203400c0c00d44140008492104401d001040c5070000980c4c4a1a08000902d842000d581c007560840207000c0001000b800d5425a440d10703d030310b4592201540041940540410005035400c2054980540b20f101d007101d280ca94003401199903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 751724955 1250 751723705 751723723
    0xf080c0d090f15050106021e060a050c0d0f021b0f0607080601020a060c09030209090c030a140a061802041b0503060f01031107031e050406020a0b060a0506030a0c0905060903 76
    0x50310385500315407040040d40d81c2010402c0c3e0307020a0618555040408440090000340a15000b40c0300c0c002d0882c03041c501e400d100058000c1798100030b112503075070200400c0251002074041048900e05000c1214080c3e8180100302c140c030724480c001a2941e0a00005215903140c2018003c1c00d40c004e00a04c030240c920108106502c00c6640c2403400e400c0e03c030000101d1420076000400740040b0302c5c2080015031213601c01c9810084038022500d040d06616021a10794407071101400c09903040c0d0106074024001500235400303211144824040d5002d07802640c83d01c005461861540701490034041c03101c002140750a04c5400c400c50607005030b89108070700c0054050300a1001500d2030348503410314210341c1181c0c0c5c0b29410000b00350348071b0541c0f2074030703203d0600d005460b03d201c00f0100416a80034203000040103214030243d8007211007550080c081a17946440d061702c010b10150480350003400e4440041402c1e140c1500035400781e0300c00e40c4009205180c00307000070180382d20390300a9403088008001ea61340d255000108102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 751726205 1250 751724955 751724977
    0x6150f0e0a230a0606030c05190806061c0506040e06060901060509060720010e0f0a09050414032206081014010c122003090607150902030a120f080c 65
    0x1640c000034218140100302c00600d2503101d42d801c08208a0300305455040036080b034600741c405004c80060088155200e015000300c0045c202018000704241c03612440000d504180058a0b040c178100c80751000d540c1c64a48812400c0c40c0319140c00074050030b81070900c0f80c202040342100242c40242003004c00112510300610901040041c007064100b0300759603040480300d40030742c0003402e014081c0c0300c08087c1d802e280d801c020329408152990b001d400241400c001103020303260010210940303141449010b000900c00a8001d807071180d00e43c5142c0300d030508100003c1240c0800440541000325000700741c000e4007061900100d0421447c030003408000055030308000300755100e12a05070a031520000049600a4085c0c5005c1c103501490381143c0d08203604030038a1940d0020580d04581242c95041e5903c1c0d491042529990f0045010040c030f0300440d00c0e040780c03e0808a0322034404101441240c002a24258013400145d484003401030071422419086028034031142c24030304055007603140c01444003140b4010803141d05 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 751727455 1250 751726205 751726211
    0x307090501051b031615090302120a0c140313060e0f04020a020102070204240902040e0408030603160306020a03052a09060904020c0703030806180106031a04020706150f0e0a 76
    0x103a40d203441040491183c0c5a040202da03100c2030b803a80b00540c5840c0b050001e940c44520300c1003215810030306000b803600f041d8240c2c0041c00040c2c1c80d41c401003c954444c0b40500c003001a4684150300003040c03034840c400d036030001400031510b03200e25000442c0c0c3c80c2503a42c0b09200748404072004032410b858407107a2200c20380d82110010380f07a14550f03106902a10171b0500081d807152502500c0d908440000d02454400d200c2c011040d202e880e101c0136540100d20450188509180000000800040300390000355030002010302500c0c085451900b900d03c0d66015a0000c64103d5004552070505a0345441066407100b491510341d1188510360400c00030100440c5040c5c861001c000801c010f082c1c59080440e1000d5501034070031540c411604541684a1400d404100c00207640400401e9071842c058010145c1c0d04600f0144101c0ca0b403070040c080e001000080d04100d1483c0c40d602d00c402d0103644600c064490f040c080c400214410700ea40300302c50901138440e0000f242d44920b0260510040c000401c1702035010103950800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 751728705 1250 751727455 751727467
    0x8041203063203070803040e150a09140f01030201121a0a030c0e07050703080117120a020a03080906190b040209040c020703060c1d010c03032c06010b030709050105 72
    0x450190026070006581d45284800c0da010640b80c0c0284154610080c900400c8200b4040041540340c5007644192007480d4000d0100b4080d1590f00070070075801601660740c800640034880f0100303007003003469840854282ea072070075491074000d88511002c0e448400712001c1ca03007941c19640040d03d00081c58051503800340d40c03626400c1c0500705242000c4802180102001c620507601d142000c41c01350240601c0710415080c0002c070701000e0183e001c0e80d16096060f01c4d6080c9581c00d08000750016412172003404072a02c01c284480c1c00c980c02d5071000342008042ca5020742102811400d000c1c0a80d0340140070000c42d54800803c00c203042005d0313079080ba001c0001c508045000850340d40094080d000381c800c01540980341580a140303c2d0b40014580040324401c000034441c1c51103400042d0394442001c0d0803415040c0554034840200c2d845683c11200b064801d003400280301502c01510303440c40c40c1120008104031181405081d07454810414140140f03d03840d4582c0c610304c0c06200060030410b072441080c0c1401000300c3c00b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 751729955 1250 751728705 751728707
    0x150e09010605030f0c01030608060129070606060e18160c0c0e070f02060c13030b130c151b08090d0c080f28020d0b13081206120607080412 61
    0x1041c40144401400c40321002420b00480340c40398503020009011915150307000804880114030301e8101c81c0c01300c7c0a0179103521040141010080000e988440700358081000d4400540540b15081c00f1301581d54031076104410203028803020710040d001064810078a01c0800440201c03e1221f12000500c0d45041c09892040c0d00c0c040413030046903000080102521010005825802010701d070b4262456400c44102e515080080403213440313903944001d041711000e03500b400840c41c2c680249130482401c003d0b0401d04140c6440340140c1c1d410640140d101c0c0000140102503199120070040c3c085906a06241d0034010a9a0362084611410651030700882140780306034203010b07200c0700340c0c030081800d0020380d04041c09810b184c54903040104400d00f80504410303c4901c030325108071108c01001c0d9002e032000700c00c8052910b511441c0c40000382503c1200c5540d140c079000084200c1c000d4560712881c41415841820400b0800c207480c4c507001e41c200c0c4680c0c400400c200c1c501d42d00201680d0082d400000d01440031514800c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 751731205 1250 751729955 751729961
    0x2270a020d06170d020706081510210903090812041401141804110f1b03160b0f0703050c0d180803010e060a08060702030a03150503060c040f0504150e0901 68
    0x1c00f10741000c0345524540362421000c5110510155180d00b521002c40c0c64101c2960300d1082914030340c1440d1500c20303d44183e0305100740c0340313642162076043c240260384080201300401d0909086008400743c803103100500705a081088a0084c24050f409446201440480c100050103548690369000503071100c07070700d50744c0d0180c00002e1101c5000400269140c0240c90318038819081400450b00483c54140081003101800c81aa04485155074030319141020040c280c28001d0300800c81c004540c0404c0200481c84510040340700c0c0c01c6440b5034515281450325800c0c001c140e0303000500e442c00385420b03c010000f82522080894150702511f103800290f40024a0240e51011721102005000e00300010010900000000845100e45011105003884a0b1601d040f81d40b55601914040c003da40280402d1002d28026002004140300c414042402259103000092400d501030360440b600c2000000c00b03002d0040343c0d0300b070701000d01015601030003000b803a2844902e840708903101700052100305a011038811f0601790 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 751732455 1250 751731205 751731209
    0xd11030c1b15130f05030303160e03011e1d0105091522060e0c0f09070c11040c0e031e0a2910060f03060518070c0b0705030402270a020d06 61
    0x2e4180da114500320340b10550b100860b025110404082210018851600000300c1e03100c1c540c80c1f110004c20000030241901c01d4010300d032265516540328514100c2081d0000030700801e2000740b10010460408005582300d03084030914000c203099052a08008580d1000501100507080e001d002181e80d03564489400b5140c210342820050082421801d5018043c05400c07046040603241c0644040d6450b44080145058144000740d401009201c00039284c10300810f4010101c0c4e0181075140c807417120510004040352100c030140c0d070129001c5980615107040c2040040040035520168039030704600d02034129035840003407800610b480c0444204600b8a00e030f6101c143c20100d00d42030034100604004a01041600c0d4900810340010165581d00401070301ca805884104c0d60023a0070a034108403160049000803000034800802d0103e11800180050f400312180d61044207180d170f030140c89091500c1040100040101c03c070b4008020610110000d034420880300da000f030040940141d66410146101e0050a655 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 751733705 1250 751732455 751732489
    0x6030b162312010506070b0105120c060d0905010b0d08030a0f1e0f0506010302040f090504030e030d020c0102060612030a0c11030106091d010504050d030b0a170d11030c1b 75
    0x544100007100c003009030800304200c141d6407040ba138950b414404075018070030000e02a0300c0c00c070004215605180c1c4000f0030a000041c161404e074040700021498681c0f220280f450455601d10801c8280107083c82844002482120080300200300e03a1560185400082c0000a0942c0e82d10f00030722402d800303580000c600c2c4049148180460106411610007044c4801840c003130316040000151081d0301c42d100f00c506455244030340201b40c0e814040004018000203008500b4002400c075050104c1d03401300102c1c81e040d4002d9008000d840045400242454400b40c213046c0a40d0b03c0d031002c2c510415000c8203031185070304145400b1407400a40c1c14403030013249500c10080d07055403a09030302041c0480d00382c2000400001d181e109030301c02c240c506072090803160103c03000b030304a810030794030346401c64481d8001d80c040c04402082c01c60200e840c1d0811041012001030318094030303440064540e45260300002c00c0f200742100c18001d14100740d07400c140b168490741d2240505181c040098000510b5030764120f1400c20100c25 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 751734955 1250 751733705 751733747
    0xf06030a150b090406150501090501051e090409080409060b0f09220204060e2b02090703020c0102040924030302190303230103140a030f03020304050f2b0306030b16 72
    0x2801c105e0010711071904150802815001c0c040b5003940101d80b40c1c0304403001a52002d103001e020b10002c80c1c0888850380c40c0420000c0420040c2002e90307070790080805490198044640e21490a0700a2044034203a900180442106102509904c002042a220b00c41c4040d0340e4405070081d01f04050300c41d2002e0034454400c0910228011076443c0d4011200340c400e10050301c6056880703c52500203100300f10070b0700440320801c61812000005050580300d030b40c0c00c0b10031820050306002800e00c94509a0301b19410040c2260359461500c05201d250f40f0111045d072500300031800807030b402c54400135103944000b030303281100803c0400705208062003035111690b100d43c0c80f54040c2030f84d43c0300701c0d4610000384280b0040e00e00700c0d0481d0f1503050854001c5520300405034151100c0c18030410001e02030f406500010800c1d5400e0003030fa0444459454284980054030604058005a200070035544c03080d0011240340f00d000301481c00b10b00340000740d003240c00c01d50445240c00241c1405070300c21408440038200c0fa400702c1503000f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 751736205 1250 751734955 751734961
    0x50403060b03031c0c0f2c1f0c0303060b270613080a02030d02060c0301061d030f0604170405010801030b130f080c070b121611071d0f06030a150b09 65
    0x107045c1c3c0842c0d002000341d524528404042e89048a02c03080c002200d50a00300c01a41813903090300301052511039484080c0110031050030050203030408c02c41c051141d0700821410303022a42019814813031200509801060301d41401c0001180c00240c4032451700340721004070002c0c00d12515a5813502620021004400444005501c806206480e80d445000c120b000c3e00c6001d0000490a00100d119841484488900c60540c2e10340002201c292250000c0954595040360340101603132014400751001d04954802010b1505041c03038201130b085614050210002400d20060125030b900140705811030350820880e58094581c88111039031034501d07400042c9130104a13082c540c1085152005060102d000d503050703410700f0303503510005c100500c566280c8000c03440e401030000b4107203d0a0300c03008201460901e00690314103900303402c0900d040c0e000d400000613030031051a102c030003130840f010480d84071010038a5003509041100120f5903d2500c80002440b02c4546022220050400da0180200b400014500402e0b41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 751737455 1250 751736205 751736257
    0x90c0406090f0b0102010b03030307031a06030c0315030309031522030c030e0405040c26010204170c04182607030f02011404050304050607050304080105041110080106050403060b0303 80
    0x300c0014581da4005040030700c00f400640c010310880034020f4000c2c0155103580c0d1250022030081031001d0340d401c130f81c0d000502205019158003000d10300c00c03410800743d1552070030b02c2d40c45000204048038502d84070740d2080001d0081034802190050001720303101c80d0b18070076840d02d02802c4902042141104214625013042c201031590120340707025014085d072501400800c161041c4415a20121006404681407250401034010f0188144014051100c2a0b0b2501e041c2d03016002d00707a03440781e440611000340c1c00c2000d820040d8144503210380031004503020400d0b0020080c1c041ca01000180d00a8211070340b0181c500a0080c085d6240e11040c40d40d6801282d83e000c5610340504030405c82003500c00103602e0060904140c05c049036803580101c3e0808003d40c1440e250008024259002120840e807600051100041c915002d000b400d00943c401c102c01d240075034106d0701340040781c004100d000041114800042001c640c1080c112b800f40c07500078a0110321400c84034042032840c4210005010f600320a10a001006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 751738705 1250 751737455 751737461
    0xf05010203040b01240e0301140f102408070915081e070903080c010906060e04050f1b152104120e090a05070306030b01080f0d05030c0d05090c040609 66
    0xe81c42102d00d030149903210300940780038001044101061081c6001d110300300e10300541d1b29060382d1710000d0001c0307101c0856030307003803d19004182d40b1900e4112421051101e05041a00381c0c0b03000d811440305500380c0c92010900f01e0310410b4950745072002d20840c4000b007100c072032298031200042d029004046607220300084006010100440306100e1003545601da0210800c0603c0841d401208a40d550fa4091410b603114240c05500c032180d45901590307103504440004015003d00030003000c490006401600d03050400342d00b40002c0e01d400c405c654018015808500c200035a80851081c1e003130342d000107140c1d070700500c42079035100c1c101e40350240ca441c254000408440310211188103e00c219a91440301c000144151612140c1da0001584016100005052a43c055104550242c11403601146880c0d4940b6112040e41c0b00f03030032400686d0807160300300e0007040c0c00304410141c48540e45400d62840c03501261228290181c9050203084d591643d01052494a041101c00c8031284001e1040081990360704c440700007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 751739955 1250 751738705 751738711
    0x20d1e0b0a0c0e0607110a17010905010e070e01030803090a0803091b040612020103020d0204090c02031b070e060405091606020d02010b0901031e24050106110d050d180f05010203 78
    0x4030740c10700d2a9a0b014600c1036882c5100700c00b02030440340c24005181e842d081400c20700d00c032898010070340f10300c00075001c481400304c000d419240500014000c405818561f0a4075040d021103c102c1e40965030812558020040030750450390000f01007512900c0b00807840c0d08001141c0000f0304150004010b015001c03002285a09048461000920304030650409000581d0300c00e01c038108500c105810b0681c0554080d80042060b070300f01c090014a42038450003c44119041c4041c118016480803038155020b03151075019820809022000785106490003509441c11103004017403900994553b000300300344020030400b8003090000002080c0c012038640344c4c025610222040844019820714482e00c1281c108010450b0580390494104d0b210307012081c1c0a8054010000300c1200e42d900b41d03104002e85a010700c40103801c0c4080344a004174940d4541000100361000c00c1c501c04103240c0001006004070740e080001c8030841880702e4004648204c844c13183c00c0c110400d4403806044070140000a80400a0640c01188 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 751741205 1250 751739955 751739971
    0xd0213060f0f0f0518120105040219030203060606070318080607030c14071118040f020907021c0809070b0d09050d05030106050706020d062408060301020903060103020d1e0b 76
    0x161900c01401140e05602c5000060082a0b2143c3e58000e0300d03101d40c004200c105462900205141e8250022890941040c01c0a46d401e075035500602c4110329100c5141d0104c101c030b5101d06146d0b1410740c0c0020340c444c407024181910800000507200c1c209402154051440001020f907180010340d01c0e5050b684411040325a18002031500300c0c2c5048444c010200b9852600044501c942400d21542d83d4415885003582010fa000d83c1c800d5100018451200d00144581d20466640c3e81214591041c0808480c0140540301590001c803080d10100e105201900c0c003c41c4245042046611a0b00c10581010400e03003000c14040000112044240155002010400d03c00c00c01c407102010f20000071105400280502c00005900308001c4c80440c0350360300039181c81e905808000810903591801c900d1800000c140d08100c8035104500320741040d030003030380380e907401103090780250710301185400003944401c0c05000080c480c0015803c40802d200c5005426800084409500c201080c42c0f402c0c40c410340d00c02164120 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 751742455 1250 751741205 751741217
    0x61805010311100e060d27120809030d2d090b06010905090703020a020102160614090c010516111008090601120317151011150108030405011101020d021306 68
    0x19050f42803404043c082e051807940d907154030f0b00e2848200b00c01503001d403c844000c1d6031240201680481100391010300418807950000499a0394a002d1400d8018607000c80c040c04201020003040300004012101e03a0304004800241e13040914403d8a20104203030940c4034120005107540d864005213038414000b00c1c0c094003036041070303544460044410380741502602c1e030007842c0b0301e02081a040c00394024021040e514000503091500300c886100e903491100f48150748540e102c00c1c07114180004006510f400400b0303400980301d104400c3c400a002440343e45e02c909540140984141d003402030301d507501081c0c55401029000e4410b0880300080540d0790945a0303000c24007881d000091104002d820300703180c1507031549490003121810f503401040d421000309100c0e45d2038260403200b40e50307a0718042000400d045079101c40b0a880f405441843c513029510000703038014441d05005100341c1000205a03002c442c400d1814540710b1040e121941d02902884a0700101a17002042c080225111030298000303076000c0341d643c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 751743705 1250 751742455 751742483
    0x10b120916060e0a08011a060d060302042a030605060a12060f0e1b03040f060e0a0f0b0108120702130209031204090204061e091a070f0c050103051008030a0509040618050103 76
    0x3046c204c2e50002c62103043e84c082412403a60b60309201018066800e42c100000850940d25000308003550f030303a40601d8245091500c000d82d0207510030038401840500324981040441d0a03c004545e151141c01803c0702030049800010544226a40007034002d04505100b8006840d5580b04140349408180d46103068a8094422603941410318000d0307030f200c0d0ba08540308804542c69915150005c0010b1410b80d9220300402000c000072505900328091018420708910003150300d00051703141070590707098003400e201c0300070882580540d8600c1c61028802050000041e07803441650700191411000381400c1a0710140480c0014107010f0a502601c21103000d9282e00112182a02d2460314500185000c0307004184d0800c4c00f48228440c5029518009070f11100491505103251503401e032030325000c00304503501c2c0140f81051210b96814050b0a80107000030050460703a40c10110002c2d224051100c0a0b03040020108503c2c001b90390b40d800c107034020b094480c07840f1440c4003002821406014240001c0c0c80807402c501032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 751744955 1250 751743705 751743719
    0xc0717090301230c16020909060a0b04090312020a0e12010b0406050631080f010510142d1309020102010b0f0d0f110a0f150503010b120916060e0a 64
    0x21501c1c0e0007120100403c0701d55208041113405030407000220100e9000d41c041140140c5444a882e8086c605090061800d868804d1040013903560751551140114141140c3c0800280c100c498100540c010810240e10b0f0b03841c0f0341044498250307030070a85600c03042c1d98580414088041d8031070401c0703400c141c80c18000ca540720401e0003414030514581c100040c03089800f140100390386020703880d1410400040c480d08030791381d00d009610385240c801c040006a5910710900030716400e00000b0344003e00035120080c001c074901d000014442403e0342c440701e4844110703840100c000001d15440041c6082c0042000d159908010040402014822022405907180c001c49035800c0c40d00c3c003001c2d503840c4401003d45644c0c0a8580c0e81214080f040c2100300d8200d8443c0501c44003565402c0ca400000d4a0002c0c41c1d403001d030b440c0c03070032034a4007a200c1200c0d41c061120800051118414204c01c891000c1c0030a14442141d454624a01e86048454104080b0745e500350380c4045011680f282030201889800c507050303c85d489e140c3c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 751746205 1250 751744955 751744991
    0x803070f0906092129060d080306010f020a0b010303170f101403031b1507141209100c09090e070e010521120d0c0e010212030c0717090301 61
    0x803003000c105040c90820001090a024020444400300c1e89445039000340c0e02d40fa45100417910013580b0003000b280401409032501c0b00c655101c541141e0501d006126038403804020310001d000f0750304028070344c211f019a441c02045298403540d442083c1100560b940e0600501f20000351441e045142c503644082103049031000602e60003a40d00100c10000140350021140d2a0041c0811032034040c00107200c2203113a07601040f000000045074001800d03054403001e09401040600034421800d0007039801580280e203c0700b42c2900d13001040c1d0162529141c580001151800c0030400ca403031030b443c1c100039060b02e03c1d540c400000001c5030b2065106102d0518070040c44d545419980c0113600c000b0720315034010410391a19032214071041c1c0284101004ca42c1d06030600724140804080138409140d4000345250581000303100b42036888015282c0344850f224a800000d44540b401c0d407464101a2010011504d14200fa034102c50486030b000e0300e8034201c00c41401042029400c540700184c407a51811030200100603030f02c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 751747455 1250 751746205 751746209
    0xa0e040c0e091611070f0906060203160b06040e0d030b0f0d021e040204080a2616260d140a02040b0a030207030504120602070204051f0515160803070f09 67
    0xc2900b1015690a41458018410003003401c08101924a501802034800e0101c0d0303003c1c0641084088a00b41007084207002d80b840342e03104a085500801c006803a030b250940c8040c0c43ca660111991081c1d4803110f0025019010744411101ea80c01180b4059185035015070103100782c510183c4035090101440400c1000321032201d50301941000482c190308a84400d4926072440c51900108014249511003203050320b009004142101c0c21076103081d2084d84c0907030f0003900c00305005450205514001900c0f405400075014400010000b81c40b9400500c200c5668001e84511030100c0d509139503c51112044810142c01007042e40c0d04001d800001107000c4601714000c4805440401045c02e00e0003201520841c02540a90005d60401c10300b1700c00424600c903182003c0c0f003094040e00001d03803981014010407007203038400703022001801c0d180402c0b541482c1c050a100e000310f8104031003110805d80d103e11325040e903100d5030045400d40300121800c00100711388000594001c105c0c0343c1d190703403051000ca43e090b9402d088034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 751748705 1250 751747455 751747459
    0xa230705010506040b13180803040507081501060f0813142a180c04050618040b0a03020307150c0203030406030507142701030e010c091502060f06040518030a0e040c0e 73
    0x303480728461b030700441e0002c452000c1c001405036101000da450b40260750300195000c6800d83c0046004114544e01040042ca0602c191800ca0000794500100580042c1d0791010843c10b03c40101c002510380ca4176402e13903440480d007060321500480201d40c1d0050f02d4106d04044065464043c9140c8180b400c600d00d0b00c1c1d5140380014100d441c0c92043c081824940d0780c401481103058950030840031a1684541016141d030001c10a4808000440d4500f000290741410b101c0318041e00c4c2585040004d070b680019820121151191510000e006100c41151003509406020f5054440013600007174096050340524800c466031303070312004002040594100180306824084e4442d0344924601c010b01d480c0880c030400c135440c0504001070300f2020380f030605003900c0e10f030040c40010489080007003101c01064800b01403d0f81c100d02c007600d01c91922807100905038201500440c015035a80000a104000300d107220012100c2078400c503521590b4054008050078461400c2a004030700f86410303030211600501d841c620904c40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 751749955 1250 751748705 751748719
    0x1719060807080f070e130c030f050c09130b070513050402160309051207062d0c0c050102070f0e1b03040c03020f060702011e02011517060106050f0406050a230705010506040b 76
    0x10b0141d000246c4038400781c190781042c00d40500000090102d4040c08900b441200500046c24655081100d401402000da5007800754904010303000840d08801c0690243c180e0800c1501c03030141918a020840c0c0c51780145030424170000f4241e0a8020400504081034801c0d82c0305600300391100d003032045440c05055052241e5012581c10300c95103014800d40100802480601840805207110040300c0f1110f907001240451039690840b0280015218508080d00003800200100c600e4005495018040e92103040c011100b803a0101d00d000e8a52015800030b10008000c5a0303c82c102802d0a1040651078801280b0800d00b407104e08089040980544084603016110031107100c030309032851400b00045080c2c0104555803168080050f907038412040300038007440480509c140c140c043c1740c40c0c034004040c2c00c100180030044c00359810740b0740f07020f00700c600352000c600c0c00f251101411102a103c140c682c2400c107803104800b40c04c480c51846031101412101e406040240711645400d000d000c210341d10440c445412600b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 751751205 1250 751749955 751749961
    0x3020d060207020102010209150a081609060e0d080a090f05032b0c0507090222050d02120f01020d050603010c0e0f1c0203010e06040b090705011719060807080f070e 72
    0x481c1d8050000140107000151421110400091103002942c82010000901062038800d6562016403154820094400244c03244400c43c000392801d1014410710080005c0e0107004030003a110040b13070300302c91540000060303100c41c001080a443c0452500400c24007608100001550f40f4000901400105011b100b052020780f42d040c8060008400805010510440303144800000f6010807600c001407550300340c0162100c0c6248454003021100b5080e03100e2400c001803050000b13030340b09441860502d40c100c0d000c0c0000200c0f500c009003400c400d03949054455102051405114049800c11031003002c0407002001a00c200b40b40070340c2c5420200100d0364001607000b07203500c034604014600d180c0c00101000050078200e5141d00213800d451108040d032104c1d8100310203000c1004400861541c000c4000c401410305d1b14101400205011401e00d0b82943c05070708400403c0d1203c800d443d80024990325243c003801915214804665a1500c910800c0700500c1140b03917000741000f01041e00000d0711041c65661003952 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 751752455 1250 751751205 751751213
    0x2411070f0b090111070303120b010305010812161e03170906010e09012a08100b0a0e0f19170f0a0f0524040c060804020310050a2712020703020d 63
    0x24101c4040c2c0c506000c15140001a082c40401c900700003540b0031307615100180002503a8200f0f5650707000d002411300d800d040c01030002d820041422010803107000c1095485002807034200c00c3e81c0c0299100644900c0400c4c03072600d4501e0825401201490003600c60040c1e8003102518644500c400f100c02c800ca58005400500c030844200d07445982003103032140045210505026030700d00f002034000a04600d5032454610081e20b079040203860303a01c0008203103600540c81c5401c0c240142880741d50003e40400203030504110341550f07079040940d00442d0241910b61403101d400c001c190f50407504e0184480703681903c1070891491100164000002c0903810180600d00c4003951039140e84000414100e40034060555544401c0c0d8a20204940703a00b11000c40140d03a0810782489003917a20a80c1000301081040400c020140e180066045c0d003290707001c0d40004803581d40d1540b403001041e64412100d0303507100c002c016034400c4112000b821246401407503c41c2c00100c01101c00c0ea9120000e11000307400007007025000c03001c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 751753705 1250 751752455 751752457
    0x6050f060f010f08040809061b0d050a0f030222170606040c0906080c0d0509100c020304050d0201120e060a0b1306080a030c0302010e0304171603020f0d08042411070f0b 74
    0x5c24803440f0b050341840421070020314507401402901450000b2901a403c03210380030458030b600110b55080c00c1c2c2c5440800c00008060401080041045c1a00098084030074035030b200c000e52204030707121071654030251100c4940000543c94100c0c0c242501c40c510100301c484c505840b1b941840300c2e06841c1d03907030078519215041d5000b1800038181103000340180240c0100c0344042c050944101920400342c2141c1d40211035201c1210442c05452046600a1000384999140c40f0500e1150940900f0045103041c1c0038511403025202c20540312406018841c24041c3d031201513006080c03011001c0300d1060248058500310011503101d0f109042c0940c0c400204440864098480303105050301a100200f00c19500203400d0340b9607806a0300111003041c5104510308500010702c01008030f428003140040301d040c5142c000511122460043d24800c25042c40310340b00f0030000c0412240100080c2104188210b070f0507001440d5001d402d00700e8030100d000240000d222680100700c0406460cd1081407040c85400c4c01400c00307003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 751754955 1250 751753705 751753711
    0x414211207111018050a0b0f070915031e09030203090f03120304171b0a020a0b1303030e0612040f050610031a100509042d02030709090f020d06050f060f010f08 70
    0x38240040310a002042041c01040c0302c080c01206500c1e03003814a40e880c80540c0600815503000c1040030541889019110100460144c14078500404d02c0c00c50742140b40b0008903080b480c030340035900c2c103b45203040680100180c030003000b04a600ea001a442c4200f41030b203658204030880c0820108000080c00928a015256249605861990305210040750075801d8131000e20483d103d280e00051101e0210f02c0c00100e420301900d841415a81407140e14a510158605140030080500149080000007078480b04260f5440e502c4400000c01182840e0502c065004650003003510503010350030008241c0035100944204580c0e000380040356103110407101d208250400f03459604980c0d000070000540795100030625000b0350241444c082d407541500c501d4001e4400280103100c4000c45100007401680d408030340b68080312920400030544082524040380380000040009520440f003d0380d81d03051246a51106201d03000300440c940541d2101810000d0340e141303165105001426a641581aa81c072030b104030341d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 751756205 1250 751754955 751754981
    0x7150903080a0305010503100603021f02120406050315030d0c06051302100e01030609060f060825090f05041e0e0a210e10020604142112071110 63
    0x6215450340d41d100d01d95403201015000203900c80300148035500d03007032000d00d03001c1d200140c0c104145451640481c1c0c4c0a012609020550b08040803159a0b4900900c40c020030a081503441607551034680307070058041c2d0000c0c6c5140140d5118401105618180052014903500b00c944445944440540d16207000e03003002402003030301c030300e50741203410058891105a961014543e180e101c055001000010f08031070590b03111001050500804100840340026074005441203840c0c46082543d446c2e210300d41e00c10b000380e0903445c4000112015201c9030307408020241690b002e10600c03011282e43d101000180e610603414038a208254402d94101c031009588501c207184c1000003900e04070410750320386110603102c2c4040341590900f80d06c4041d12050740000ca6000008040303130362450404502c44001d43e100c1004100401c060100043c400da02c0c48200003c104144500d1580140c000300309044202540080c102c40a5140b02000400d5256003e052100d014011140041050640c1c420001015180d8945458 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 751757455 1250 751756205 751756217
    0x2030709080c033d020403060902041a011b08090d030203030103030f020607020d1d03060703021c140403052b0204060306080c010c02060a050d0f090302150c030403080615120f0105040207050715 85
    0x10841c0413540054002140210b4000070407203128018841070301c9c41e50a01900828100c1c0740c01003140e810450b41001c03d03201e0103012540c00d0440c540003600e441080c602e10b5201e015950f24004142e400002941600c1c42540c0b145c558110b02c442c140e0781d03000c042c1c5920700942c0040b071548007003a21841d01d070102e001290b1312200301c0680a40200e420103d068840000103900019440c104070300c42845a07128824203c01005a10340351400803100c0a0068001820040001260010481084c40c0051000c0008400c11040340300c03190707120002d52040c461039001c28202240041c00c0a070116580c0340d01c10041e19100d1454456908001d00c99001404100034000f05002d10441242c0f035208458005501c00b1001840011504000c2d103004204a1101c912065110401900305c00c13402c20b594206030304d4144400340351184000902d0941502e070403902c6da20745c086401901c00340c0b080152401411415210f4405980328024030060b449085005450359114040400c0b8001d54106052011252031402d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 751758705 1250 751757455 751757563
    0x3090905090105010f0816120501020405090a1406150313060f0c0207090f021e0d230610020c0303041403031e12011e0b03040201110102030709080c03 66
    0x98111901074401d00c00981d0f455006001803605007143d2005030a01d400240440180d0400d03003861126280600c03a80418100d05540c20004250103540c06410700070901003403441d14407840c0700101034103456000705004007030101d20541840300350440003013081048545596076202d803201241d9020641200c94a5560300d02100c000315078800c425101c00664050610146412094000d503030920b0840d04019204107c5e588011120103441d610071a40d0010003a01c620038440d02d10018071a81c0d54101005401c20828090b01602c0402184218400c032001c2c2c030b408103005801c03680e80c420408603d0709a03208020a110702a510b00c50302440c110300804480c504083c1109034001c0628021003c5030b116001300e6060003003540138824a01511020040d00d1540c0201c0425100480907441091121003000000c80c0640e407081040f0f03415914401d009641d0f81c141014000c115190a108041550080d03242230301142c0350100e42051500034445148651400c1c40084000107000350f00702c3c100f061941034270 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 751759955 1250 751758705 751758719
    0x14010603021c0c090801050f0106080610030212180d140a1d0d0515070509150906070c0e060301060501020109050622050f0c120a050d0f0c020603101706070f05070309 73
    0x14550110050fa0b14181c40764501217515007584c2e406806040e90300071354001808820b91000f85036522110894074a41c1204900800750000d02c130395000c002e54081e9000800001000440380401c81c49164801c43ea02d0f41c600200032209005210354540c1240030822500d4103061141400484200c00d8080392585070708140002241542d0310300d0104c440d500502850302818081800c1c0300e44c4562641081860582d641d4000b03101e002e504000603d040f0004600c1003140c6c0c44445c143c4000b5075024405003005900ca61092040c5101250245d210358245400402c0c0340d44103016084c607441d1f201004010a8485051b10251080e1038800d461103e1500103409001c03480c104002c0c000860107401030030904490b003050091600320500341d90b0180d4461140400081c0e03000440d8603420b030032890404050101400c086551000c9114065804440881800322104021300e03024101c0340c042c00f0000000c030000d04000d807640001c031101750119003d012540c13070650003a0010b212903840307460a0b100e283c8e12400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 751761205 1250 751759955 751759961
    0x31f0212041505160c06050727140a140409050c1e010201050112080307030c02031b0c040c08100308070f0606030b0402120f120f0d090b0f060414010603021c 69
    0x25042d148140c6665080a6210080c41100d802c40c0455800d00c03480102070b074004e040011034000003441144d4410004103905c2c880e214083e119009031800307110400d501022020404064041c5100e140c0e0100d05170b401031701e030280d114002c840070000c07542c5c1e613481440200001005140c400381c45034000d11440398200e46d81c2d210901c00080c522086441c010f0010000242190300503005041b40c51144a010008148100700780da40c090494680400d075035280000c101c1c1540030790f54025030200400214616202c001040300b80041c0800d640030000781c0300b81d441c122003441c0305580f01c608040a80c031045c004592104020402e2a0040d0110a28a44156140740c00c0311500d07070055030207807000002d000462809000303258207042803100800040740b00f10311690700c0b2900c0444500c00c9220004040368007120b66010f4034088811100e08000301e143d0b500340342903010011150500840911400100b2510f042d100342001040c0102c082d100d6682001b038150000e61020b1030115018481442494002e15680 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 751762455 1250 751761205 751761211
    0x807020f042a02030a1407020409020909011e060b190306030b0c19020a020f120723090a110304030c0311100c020f0309100804021201020a05070c09050402031f0212 72
    0x8010782100740106080803108851104802d000c54100304100e0801310703071002d2442c10f012003c4200c130340d61302ca2500c00103004011018000b500034118000b00218244107600818020310301101504124a29101c440c0440d1440e006a640c05081401640308070b0780c240104504080c10781c01d0006056803240c603072034207140d011917420310300d42000100c2106075224403151204403a9940000c2c0a0000c1d80e81c00241e03502c503200440c038042e03884039030b03503d0a0403410072403031005100c10b03900074000340d0600035004200c03000c911142d800303206d859011982e900c80314450007104030380020b495800c42e02c4e00d6a0440d054600b64030144d0400c2001c03102c41c0419101408085811120001c1c0081c0d49060740f400030b4181096542d0700b42c0700381c1091200105c251a902d4080307124451a15100700159164400510b64162001c60002e0f00c1d0700c04920940c4164002000b040c0e2036018000c02d105907580c07a49008191001201c000f5015001200c0c02001c4409020b190003000c0070145025045c61055002414407040031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 751763705 1250 751762455 751762481
    0xb031627051008070c0206031902071b0e010f06030c030222081002040f0e1b120f0105060a210608100203060a0e0108120a090e070f0314070c0807020f04 67
    0x40030100700a00d08501100411071032814400388910b0309600c050a1140d140c800603014000010002c3c1910249081c09001d2203202d001c00c40d207800060270140b022035104580442c440a8451000c0742d2000c400505d9070495001c00740f104503e600b000d40807005410004424400c3c541c080c0450400b00481c0c8040c5500e060211248036401032510100038903040528403501c1d0100d204100c140035042032000c5030b500f178a0700705d04061140d0b00c1e50700c442d4400702c049619403500140040b03101030080b040c01c00440e02641c448032422842d030b600c410401203540324011180c004140c0d035410781c845140000e2620400c2d841c42150000d0001da60312841030421030602c0d09809802da0000070042c4506d040621034000d401c1051582841c1e60400901c540e4528103408505024400407411032445032107212090083d01d4240200c00d80c41c1483c003405080d10711301508000110b03003440d0701c1544000c120140c0d20b1041c801a95030520b80714054135100459405000280d80084041c2030080c1140c655004407035800c680 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 751764955 1250 751763705 751763777
    0x4090b041401060339120611041706090f0613020f03102301080307120c1403040902120708101e08070f081c0e06160b2403070b0316 58
    0x142c444c2c0c1019500695004c185c00c0070071410510100745060300c40c3c000150700050008808900007410456400b5960021070b01e0072218081000302c0c000460038600442c10031044034400d4040e80c040c00d49031001214141454032841e10500090b2400540c1039600500103410340d015121f036141c00700191110f811404c036800500e4030407601c040c0440144140100340c1351014508210b000e1b900d0340700c215128580c0d00100000c86142e00140a1300780d450301c105019040c100d95a07117603103110b000082d400110000014240480008440d81d00030142103100302001050743c0c611908015801011802e00030301150002101c0001242d40c40c0c0170814000030305030030180b81c1340840c50000ca652409085040098003580700c203400c10800c03600007015104206084a09540300e504058001807103680a5901400150b14a02840307c03940c5d2030380c940015017004c50740036007104000034141030740c80c0642d200c0c21131070110420000306005650020340181c03031014a401c16101c08514981090700c500007200550a101c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 751766205 1250 751764955 751765013
    0xf050a0b010510050306030d0f1101020412020a05060c0d05160b09060f060a030b06042d0606090807080a060209310c0f120c021903180504090b0414010603 68
    0x90651290541c5143c3c82c5401031a614010380440c1d11094007049403028824825026031101c3d000310100d20303440803004000c64130740341c0c3c400c4010904034440e0002e07070040004c80000724032414030400b01c0c3e1b5200b1203d4000c240000d191041200e8903401a9440d59000c6083c0704940b0000d9a1100541d02960000d40180f909080c00e50220004030b00241031540b00740c007252801c200188103485119806078044070000741c81200c0d51030600c481601892004000c1d200034658548401300703503104401f50741803940c032100481e8403020711960301d01d0903000348822548210b41440028000350014800c1d4007016211044d220406c0325080d58007034030145c1800e486005c082141c0420145445044141200ca180401d1044081c0e00b001e01029031f901c0005041030740300cbe045041d4183c0204039220f10464543c0780d0320142e05880c00c0081403060741061460413444140d000040528190003462016508074422845a40300c568132402c506001d03800f42006952035a4000020884d285041c0d030842291400030f020300c2d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 751767455 1250 751766205 751766209
    0x8030906130309090c02100203070f021b030a1e060204060801080d18050603040c1824050a2d09091407290c010908040303020d0e060d0203040f050a0b0105 68
    0x1000100401c140d40703046106030011a61000e040780c00c440501000040c91401c0c010228205050222891039150001080c0a550b5070b00c0a5600d0216405509541e800211000a640c41480c080b02c40740d45940044142070105200c014500b20a010f1900074034004455581c40000307981059000e10007059001c401001407138818030605072400c50518080d04400b8500041207950724107401064086c070f001000140c208051088110b0180050540e2007418201c100250405005900b258190005400d40c4441a10007010410010394400a018051490408103014401d0080d1b001c0c819402c0000703640e10220388007500f9100041c0c1381a400c089002050380c2441110301c0750203031121850350300922017005104d04c0c0708032040001c0a001c42c42081d41d24544240802c070b0245150364481c2d94038101400c02002100c0d0010400c0724403076025240c0310000030205071500400002c4882d0000020040c0c240d1034440b43c1d0003158464403480c0c60030381010781600c4440c90007810752402c482ea11394100041c8058 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 751768705 1250 751767455 751767463
    0x200d050c010b18070215060d1502070b16020d030504080405060708041e0f0509060a03020103050c090405090c180112060b0112020a0c1e030507020432010312030b03030a110712080309 80
    0x648120190030002e4103040c0040342e2380e40303115100504041c141100d07808080010341c04507904941c000101d94141d042221400190701c0540d840c881c0584606a070f0420414040d001c0e030703403250790040040c80c00c02e440c00042c80741c1a403001c4004ca42e075840810000c14400e10422118010305030707034a4888900d608003214070620a4941c2c1205200300c40000810000d0b60b030310030008050301c0d030a2a0201c0c80362100c0d00c1c551f029001e03400240d6801400e040810020107000225a450903200b142d00c1e480d43c2c5060740c0260120b0300203010300010083c1c8a10000301162454105910303011040c5404007a032052a0030380c42c101d030401c50300303040010048800c20301800540074400c0c468000140180c446950030f41d074041c1c510700c10710f20024011070300d41c4400c3c1c42c203400b6a54004504100b181341c2c03500702d6079000c0b20f02c200000300340821074103098810003d0b05600c0c82441440c940480240c001c1d458180400b00a030390320b6031095020f40c580c0c130485c600482c50b0303075149200d54100c2d44190041c9803030b400c00c01406420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 751769955 1250 751768705 751768723
    0xc04090c030e0c010c03180602060402130603020108040314070b13031403010501121a0418060e0601050d0f170a0201020901080c1e0d060e1501200d050c010b180702 72
    0x8150a0400040d40b00c400440d8900144509003070a801105041c601543c840c1c10401c040e20729040164000100c080d00401c0c4940300c0e038070854130210606201c05c600c0003220300d10301010340001d10017000240000e0154244034900074159448a003008070a9031a01180d800854104d8044048010742800705900140c0c180400c3c04d100808034210340c10034000038034003255103003050303070352900d030391b080345107407114207414410803402600a20110f0140c0c1400081031391340d5201110b000380390a445409800006c14014145c84000b052038107000b80319150004600d42d414030507121072200380c8507003032000480001401d10306019000540c40b86048400988030600061083d10350803010040c0c0045c000d112492940d6040700c02c1010794954100c142d80c10003d0009400409200740714406018062803c1508440b10340003d0341c429a8460512650744043d00c0c4039204101c0960000100b1034009001c0d03006081c42d04403ca00016001d0703034190000c0c1000044e08500352912050209000005034144a2480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 751771205 1250 751769955 751769957
    0xf0f0f02090a05010608241305220b010501050901030212010f2c011e1a03040b0c09151b07030602030717040302190c0320040c0e0603060915090c04090c 67
    0x104540c50102c016000d260700a004050003022031102d1f00108a0401001c0c12000c80500f50480304903000e0580c200400050342c0180c03107000105103503250000445402da464a038800010582c592810006440c00c0d0800621a818583c0a01c40124542d10040c0a9030082003200d480e20b444500e00260352080e40c2e16000031524588544005451154210f55000c0c11074802c3d2600003890205104861100143c54210364950b10310402505a26400e0401a600941c0140e412010503202c544601c841d911501c4492a00403094019038000d140d900c2015005880d02041101c8c01585080381050505403540c101310703203640e4040184107405030700002005a60071307102001c6a180c18541c4003c0e40c1e5140540e84001a801c030340401904100ca403080c0c0300001d5622100d0000910f6100b003030141040d20307140080d4019860303d403d840d00144100005c0d403101b10058002461521103505028540c24020320149129170035000180080d15130b1540ca9104000060586440d0f41c05e080c0e000042e030700c0e06002a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 751772455 1250 751771205 751771211
    0xb04110a020712030311030109090c0b07050c12030d06030317060a031e0c050916020607050301060912060b0303130f08120a0e2e02060c03010b090d0f0f0f02090a 71
    0x110352540006100d401d40300741d95210b0f24540e01c5482c04034040d00b492002d82d401c004c1d0100001900c8020303600154136070fa2154400c044c200e500c0301304099650240d058047c04503442540800700030309207203100c0340c42205020190f03403921a0b03050f01e4030282da0041e801140050126200c41241c1d240359440c690704408201c4540c0810b52a68031a415052014861146500e500c500b41c641000440e043c480010708000e8982c44491500003650505c041a0103411340c0540074440001c1c03040c511036002ca9068074608c0e103400745828208045040b1441c034041e42110703072039500e00f1000c44c0c5a60401c060071200290b1020410030b54200707542141c042c039507644600c0c0c3e154018080c0c541440718142c03d44810541c03500d070200d514030940c80041c940c110b00c07108030024803400c4440c0d071440f50045019070030510440d40890300207464420011510784000d200e440c5c42008140004805490000d0f2000183c6002e003150400c10481c6407107080190003141d40844013034000c00c0c2d6070310071810000e42999200204010070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 751773705 1250 751772455 751772467
    0xe121e090105030f1003050a030906120606051e040b16021002030a0507060c180329090d270b04171506040c0c081206010e0d0f03120603080d0b0411 65
    0x42d16601019102c40401301000740043e080c1d0030501c1c0c40300700861300103084a40011140c10040c020300384502981c00040e1f0603a448282c00011030207980c0446900b941c400d46440b032245600b0036003840401c62400a07020030000081c03008880405400c04449000701040340c44e00910410901700700c021410302c25508140010311819803c02c0954110907000340300828181900081140c413802d41c94081580b203008010701109000e8021401c030842c8810151510080d5035055407190541412a040c00d055404a0b01e8901980d1003041c5100c50504e410380300b600c0040c1d411100300c12810035500887c0c1c0c0004007180c03c0200d04121200c03400803101032030260540d0078402e8030206c0d0402000f0141030080b0b03107900002c80c0c220b00c00c140900030300d5008650349884d05d155500e111200b403070a40e10700c1d0009254240035006480c040c500c0c0350b0b070281d10503c4041c2082041d03401741c40500410b0f1200310400da1b40d000004c003198100c80144103440000e000050750301600d800708811a558180c81e407182030340c1403045c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 751774955 1250 751773705 751773707
    0x2010b0a0311041107060507030b0f0301091e1106190801050f060712050d0f0e07080c100305070e040606020609060c04080705040b030109080403051507031b0f02010e121e0901 77
    0x25440c2c144180d8020a0a0216035a0000a4400c03280300801c51484c3c401002401070381503115080480048a49207006400305d42010300341c1e4031344100580034411807040402d841c516161034401035440381c4190032042c2601000252560050b02802114500b160001c03001c0950040c60755001d86021540000040c9124011504500801d1401010001c01c2c800c1201d50394082d00075208224140b16040c0003114110140340081e0040c0d03881840300341304140b8049018000032603030700c241800141805003610031004045026010260565007400421100e40466860314059240a881c40344c004002c2414040c4550340390507001030601410350000e0009010401d03002c101142203803011a404194980300000090040480c603000501150380000c000007004404103d1a049600c0070144000e00c4d0384010056068484404200f0549542e803400000701500515441c07200d1203040c4000030305081701800c0c4d039240020501c0c0044084070081480e00c20700034490211000c0000550303050341001d00c0c002c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 751776205 1250 751774955 751774973
    0x40305010608070b180a0b0307091a040803030c0a0903080d0507020606030a0309150e1c21050a0f1b060501151b06022101230405040314031b0c07050102010b0a03 71
    0x415000032000e4031880019035075800751b00080c02c0c1140c446603a0741845640900079500c584254500502d110b030000e1030b00f0001005840848042070065490740c0d0310b02d40704048a80c0001414020320210302000700128a852010f00080481194005010308001e100030703160200080005100b58440d525060010354400d03140302c125001d400c42001d08a41681c010b40b214000e032046540c0102c0b01e2141d84110380718040d400001039024100010f0004501541461008240b200060101d0001c00520702c6961080520b54108c141526004410800c20081e0f843c01144801c5c003690065191001844840202080156940c00c40d003001d62a200a250756002e501c010f440024100550124000c910001454150202c0e03903403078080d8554640e15230841e21903031100b41814042c00321421507000c03843d00706845050300664043d12010035009500341115400c1e07000034031941e80f002030907100794004580300021b002641904802ba141160500c0002400c40d003100c42a2481806e00040400100d9170b421 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 751777455 1250 751776205 751776217
    0xa0b010c15060e2403030301030f0f020114070501060f060224130c0f0905180a021302091309110a0303050f090607021003051f0b0405092703040305010608070b 70
    0x40d000e08003141007011a18010a0700b40d000c0f40581d00300074100007045806803140100703d0050501080036034052002d00d1703a030f0300090100800d18058103030782e1b00104159102400215205141c01512003c150300c4201d00380d0000b100c03c803407503034482c0c0d02840f0300e40c64005501d000e440f0703a00c010030010b86610100080200b0716003140b01001d40c1480402c42e001e0324040510081900800e0700100195150800500310141d80304200e0030601d001d01280c04144921400c2c00d082070b4107001403c1544458080280501007e146850507650820801589841e20040840340d61159200001c100000b81042052440030212091280500040c1400003030f8018043d900e902180085954030f4808a001042070b920410030081d6000880050701e0007465410b07041103105440714880c1202200d00c039504202145814016080c0400c01032005200d141840c031a003e81c441c0f0103001c3c583e88a5000c0160170503016003c40d41001b503410000701881802402d007d80320041034044014031090340340400284060150f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 751778705 1250 751777455 751777463
    0x403420207171603030b0604060504050f030c0901090f23070c1b0b04151d01050a1b0b01061b050c06090303130806090d09030f0204050c040906080d080a0b010c 70
    0x3184000510825100c0c101030140b18034082540d5004100030060400320400e01240064200344d0790541c91b046c6541a039089070500c0e2aa0b40c01d140c02c103010403642c0e140980c806600346c80b42c000366000c160f4500c800c180c020400e5000000d6103112a80d00841681c0f81070101003a49050149500f82d05620380c0f2030f0f282d1202180c40c02441441031460903420300180392802e0800b10804e014007040b400106c5000740121a201c54152024541030b4905640405c25a403007c18505a000003d8030554040d100800003034955150444841c040540b42c02e041480111083d182109030074010701c01507404c80c0c12460003880c0c140c0d41030410b44056030703980d60301d181e100049401400081400380b4140c400f0000e44040710481c030003003110303a622002956138581d8215a64003582c410900c40048041c010000352098942100031511040700a80902010700f070060301018080000b0000018001014450340000d040c40d0f2000c1c0003000850400106100000303440d050805140c64000c510607a040021100c0450b80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 751779955 1250 751778705 751778707
    0xe1027020913050a0501020d02030709060206040b0708090a06020403150b09010b03010b0d09051b210705120304230405180c13020d0608030309011d061302060f04034202 74
    0x36030f1425a00781610307400020110340c008910318441c1c010b80d4003d5446076125954801203150f581000301e07603801040c0c0d4050a01e00600340410004c40c03040090582c000085030460b25003203a42d036912022a80b1541c02139a03074001f08410300709003d5050040c05180c40342241c0c8002107504010b500c1e42244018400c680031140c0c001240807141d00c13103420100c407241d04041600c060104024039214105030701060581f103000e00c40000c2e074403e80f0140f40001c42e401008000c18143d4100703010701041070502941020a80f005000c0082d038030079040c02d00341034102c1c4158150710a41ca9a402e0200791000505850030000000103500300c0e458002a8000c1c0300c000403102e00403101c02c1030703660000a00c5441c091402181c01c00300c0102c0c81d074000000860044000742d00802002d120104012002c00154040514507003013000841c0b16568003a0015a80e81e000501e0070346041018840400c3d96405030b80200ca507a458180f0392910201c03020700480c0003010005c800d61121912840001102d01c41c882000407081e8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 751781205 1250 751779955 751779991
    0xf030504020d02040204031a162015250507020f0d020f030f0c01110705090708070306260c030109120c050a02030102030c030f0106180b0a02010e10270209 68
    0x541d50680c00c0c440c0350013030000c643c1c803610703820b049000c00315030244100440554004a210309100c00c01001002c8020f41c0d40d230a440c1103500c2ca01d0207007402da0a0b006614840c80303198090b01034442ca5154092900113020301c50ba02140c1b0031000741652104100350a01c0386c1401707501c0240c1c8803080440c00300e010495444030380c41400e00c0010a25400754401540500c04c0d900e401d6420200050050a441c20980300c48402d00b150b401c1c02903994071280545900700034003401003032456000d6074005030040020700b0007003601511280c600b080107a41390800d18080e8003240010101e52010300c901c5c400031100b94004e010030001d948031200c0d01c0103421301c49420010008141c10500401344200c00c42c8540c014020341d80c070700703000305117540310b805c00c6d21040344100c681b400010b0281d00030113203c2030780081c1c0e06c0040071042c0740401d00941034010604100c190b54841c01450104c0c0d40500909441c100080d400054a8804210850500440f4141c00715024409411900565130300c4074942d03802010301d5188140e1074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 751782455 1250 751781205 751781209
    0xf0b03060f0403020604122016050f0a092c07030c06021b0105090f03010e03030f13150f0b10020a0b1605040b2d07051603020603060d02040b060406050705100207030f03050402 77
    0x4078031f405401c2c80c003040700200b0541705c0046002c0f031080954075110140603071104104003000480012f0035600c1103102d5410030580c1c941c0e42165582070b0b00c414080d2a14aa114154003030460b800303a002070310782c004000600800001000c0d0b18042d00451005012034046041c1043c1e05010070010b841c180302d0003140148665807110608981400c2c0034000740702c0490f034030003810f94079001a100c903452007034013200041d0139007000b000c0000a690094051307191401507451b01001000c4568540d01000c0e00c071000400d05480325289601d80f0b003420342c020148410f490602c100c0d00b40e00038050b03542e0700350b840007205039490f8400161010340d1445296107031f80c0c0204514050322180440c0e440c7c1e0f04256500b181e8840219003902a01c2d0544c0110141c800301e640440d83e0310800c9407a804020f500107030510200f01c0030f08000c1003945841b8800717000094124242c0d000109030b071300558400800a030300000c2140c100030b401d107c1110b4200c1049801d50030190a0381e00608480c50f0402c50a007059a01d00018041d5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 751783705 1250 751782455 751782467
    0xf2505070318050a090509010b030102090603040b06010c080f030f072f1e070f090606080c13050339031c05040f09060509090c1f02030405040f0b03060f040302060412 73
    0x2030400800c0300720b000351746804030790141c413007294000303144d5280600311505410103000301d40c18080014041883c655079540c42086001014250760704102c00e06035070b100080c00080c01001c0b100c0005030f00b0b6442e441c2800c44034490300070040c002c6d010003040d02c0032006800010f14941540041c901c3d0500d40340c041c82584286880009402c2c0400803031482c07903405606001040741c40a4690703201d4030106480d1a1110182500c196100d8240040c1c8200000741c010700115001e0444800071a0407040d1242c3d880c13000030701e000350010801c51210b13150003142c140c100121145540301003681900380c50102c0c212001a44907441d08900c00140710390021507035036191081c000c480c041c1c40c00b040307040c3d902c589808900005020901989000d91a01c60106168a600003000e001c0700c880102161801880d401c10040c504d5005901c100540c4011300c00812a680c55003d50007115a803200d0004006031510101440c105000e48880d125500075014400803d50100d042a4465000842498450070041041f100303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 751784955 1250 751783705 751783709
    0x301210803010306051909111c0b070f030e06310b07080402040c02160312210f0c0f0f260708070e0105180904060b06030f2505070318 59
    0x4103a000000100421040703030b00c05801058491070306c0c6507180e00c660421046800296001d402581c0c0c4541c07058003482e142c0350781e0903480d80d00c42c0c40a8056109a9421034410003d460500210b009980400140d55240c4194051000500000d00840c10a5045030144603494800142543e814900403006000c0702800303050a240d01c12000c145e10301d00880e00400c00030081d20300302e200364141009901910310002d000d2024841d02c4000c800240d145a4a004d10104140c103884107210b00201d104402042e443c1c804800e020242d04042421081e02c2690300031a28107903051402e1024600c14140d00c161300040c0407c1c0d078825400c140501803464000b50003500308030401c00000d0f0302c8003070811114a81c02100103004140b00e0302d408909010349001500c2c075011305031021105240c1494604020700d0109119900240220740c0081c2c41030540c40400c000345e00484202e56000001001e000d901c4500e81c3c06c0c50790401c1d41c07000c0704403218002c8200a28a10a440e000f404221803540d114214880280607200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 751786205 1250 751784955 751784963
    0x609090d1209060b030d2327042d1b050a0c0813060518150702090c1e0c061b040e15060d090b0916062102040b0304020f010309020303030121 62
    0x841e03c46d440d0300509118502e110440d02000c0b0741034072a001805041540d000c02c00c900c007540500d2000c140410341000c0034454955214ac1c0714005030b502002049010310308941ca51220916001c607880c07800040d6891403020600c0e0002180002d090750354410180c44684040740b500c2c0c28410100c0c00c5c0044680503000c0503801c4070000c0c07100002c0c40f03500400103200003030207040710416220b500d40c108400c01e01e451160f1110020b0400a82c1c0044c500b40200c40d0b440303c1110380e0282041c03606281420382c00203001c0f0512001c01c00146240380c10030200310060340281c402641d104440000329004425000e240708807000c409a480100380c41a05881c1403210038000640410b0b15882074000d20310160000030419680f43d2031810128a000901248055081d0500728004048928040003129442d894108420800007000d07846800080203000800041c440d4000c480d4481c109401044100c6940704d400d64149440d02074a070b40140c5022040c1c80c11240020840480f1504155040c42003158042000f4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 751787455 1250 751786205 751786213
    0x5130306021224100e010512010b03010602100b03071203030902180a0b03011b0c02011b060906050109050907030305030c1b060103230712080904090b0609090d1209060b03 75
    0x1c0000842c003101a10810b80340d0082d860f40200f10002c0484014a102080e0300001c94603400300c05503000d04c00302d4010ba070061521034544a2600344a0b41641c000b078109118141d4004010000107a04100380084801601c1080240305100030000ea640c03a407c1c03103114100d604200400d010b00d0300a510220710982c01610383c845038043c1d0740f0514076024003103600d2004e46160070310008480c10144a4907008150440c3c2c40d601129030180c080d5010b8010b94022410482c100414504808211940c410740300d200702000308071a403035842e043c005e4450503000b00c210149000c080111480c4000f8401007142d030103050040d41c0f501d511109000c648101201c012200450710311308030624000252003030407a4041d001000803005500000c0680580061400040384d00105007445401c0320349100d0300b4624840d00d0114500030249000c80e0581d01078001c01d941e6803000c00208049420610507140e403000f03d41005d01110707203500030b02400c002c1d041c91141100d140c2c1c502c0303081c081051540c4005403080e002030441d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 751788705 1250 751787455 751787467
    0x180f0c030c02160501020a08070c1203020102030402030c0907020303181603030215010e1014040603020414090607090b0d1109030a080711060717030405012403020a0f150513030602 79
    0x540540781140903040144140c01070140024442d0f00000180d4105902801122501d41c464041c0364020680c16900382e880321000281900d101e4180c1180548260000352302c0703161a00400d070502d940041c40303d01840c6202c0410401c16408800c0365480340c4c80c92118101c103c0e5410f4403900c0c0450005098203c810801c1009c006e0680000760140c03504064038902170940c0c2c0728181443d8140d4151140c855900c0740f4482403010511400a030100f921000c0e200044840c0d03250001003d40d0a11400e0041c101c0e85c040034044240000d000b92a44011701d0300b40886102e2500100c02640c0c403070541c1e18020b4035910f00746840c044440c2421a40701c070788020226a00d40e0424105040c4551007138400f01e03400c50301d801c4c0c4100581001015103540c9a040010304150300c0308650b0304144d41c1e000501c100d42c55581ca5045000f21081c03c02ea00d0491045010740149171400c51060040d003d601c0c3c0c201040c24208600c042010b00c0d844200102060058504151112195100e052580e08140c2006003450300120b01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 751789955 1250 751788705 751788707
    0x3071b02031e0609010b010e060f19030b12070509060103090201020a02030d0302040f150c020d060b040f0c020c0415030627061b05090904022403010801020301030b0916180f0c 77
    0x107010380300b0030010165a4039031111300c0e04900700d800710704c1c50502241050040d20402d00c0d0401c00307003000b80301d030104541c980502c0104016101581200c0b00300800d580e80031003502414501e5941d01e1550000009002036420100000c1d0307500d50040182c0d04045c0c6810244046901c240003640c9580c1d405411a0707004c2140e0600500070350014040c2c1500741544e10000a04000320100511000f10300e0313220300030602095024001080740e802e40035190039460f054102026160b0b4414486180d6007000000342c074442d01440203051640b202d1140c1c0c400c500f408801d441c01d0f9000e0540201700c3c5e5102c4c1d40050b09074018500071002d80d06103800c1c141c40c14001150481400442d4016000c038204520055000202d9038800740c405004140080e600a40c5290001d00107090020390400010071080c0103080954045242404aa201342c1283c44165000b10041040000340703050290412a980060150300e10b40ca245034460040c10f1190f9500c55000014200340c40700151700200c0c040c03410f10800e00507040c903800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 751791205 1250 751789955 751789993
    0x1020c0402030a0905011d0610143c09010501020d08010504090203010e06100e010e012d0b0f0904050c090d060f0b1c050d1107260609070608130803071b0203 69
    0x13003201031f64007600300016084000f44031040c05a4040b1030f03d22118500b81414003214007241c46410310300c910900e6190032030600c0a15480289280c00110a01c1d00005074140035103001c3c180d000a055602c2000c95448454000c1d41c50b07419628203442c00241203034240006070240c41d5551800c400c501404040c441c1d00146254484155244015a21f171140d984245600f0701b21307003d21330910700342d1051300c54030500c201c16001100f400c0341c03e16080c4201034a600000c281607006001d4814400e0300050582c4c914201400f88552050300845002d082031074000218404904e06c440040c03146565081c1149900d40c030ba801a0b01c0c2c620044c0c05042040a003000314140042105402d80b082d220318008600e003a4460503403010f5281c00032001e007413804d240c6198041c40c820a4650b0120b807000001003402c11980070400d09108400100003442c21900d41040030308000c0c00541301c5c4101441e00300012020a221400320b80d00b0602c1c6d8034114983c180700d070039903d9074032015080080d0705014102e59588014080c1c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 751792455 1250 751791205 751791251
    0xd0327080f1b1606050715090804080312100f0b030c120103111f020316050705090a021e0a020c0904030c0f0803060f0319020d02011e03230601020c0402030a090501 72
    0x16085902d8203026080325002041e00b1301c640000108100902e40000c0c0b0f40c41100d0400074808035021170050721569030300c20300c4c0e000360300f06a00035030020035140c4115144585158100a1141c0392000c05414207910140ea10303168000c0031010b00000022036844d02d02c8104070b490280c1200030f045410750312441c00c070b100446030400c150b214100c00084041d81c5441690140c4a10f9a641c004500d0000f19903174000782c018030210242e0303c034000e00798000b4079602c405410b18441e228061005a40780040001280d18108004200840103402d20003902c40c0c44e0001400a0490412640c1c414103903558902255901e180307030710081c822400144a03c041006040103035000c3c1e501100c07050b2140c0039400502d5a601d0341c900302e41c3d070803d5651000c0c80150500c050046805801032401c5806583e103145c440d45810b5883e40395070002603039403410040d082c0440c0f81c00b0604071152031201c1e48500700b12000030354541c00c0c0c42625204030360000118543c51010761100c0c0049034800020300c40c0c034080303100c48a001c00d504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 751793705 1250 751792455 751792507
    0xf0a0b010501031a1504050402030a05041e080403330b0406060c0230251505030a050709050d0b011404021321060501170d0327080f 58
    0x2000007140e50b40c02800751901c1d40820940940103410154204010024400004015a80700700030100345a201c2c0c0c0001c52240005903404503850a00c1d180005001d0072207818080354144075031a0f000081c80c1d250031203040383c1d000050302c4641c0064505946085084004241e00101d10300c600c1d010443c0b1682002200030b030200c41c20001c0340e541e4481038038031740b0403820700a52148200140101c00042040c440c03030080c1d801c44510380410701d500d01c12490101c1070181c0700c0c0200310f0303120400380d4000d14503414405040340031341d80309030740032103030005400750201811003a4010744407400120041d00c588040380c003d040c0245240303030360b0083d42000e020707108081c0034200c42c290000380e045400d41403500032203105c1d0044405459400c2e03c3d180e00d1806540300c12000c01c0d041c01e8001001c201003281401450702801703c4007400c00210300303104907003407410303001c0e034849820b140c02d0800004121151843c14050b130400038152500c40b000350304e08060316215501861612441c0800c40549a0076640040c000000c02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 751794955 1250 751793705 751793723
    0x80105071202191b0602070804031e02010f110f030d06060e0607050d0c03090f09020d050609040b010515041805071101020f030103030c020d060501141e09010e0c0c0f0a 74
    0xd00d00e20040e48644000c03a00000e0401e03a201e4003c80c80b40c0340d0b42d108030704240c40d081c48404890369030710181c1c1c3c86104242c8402c0c20200f01032003070000368071030945055aa10914504001c10b580080c26010781c0d05180b00c05d20844150500142030144400907240f402c1d401070745d0356079000707407068401007001d400780c41c00013889059102128200b800885400b6a0003078000d05003039440c68422184070f040d4050807001c0141c1c60b64005503c0513041c54140c0644180340015031035186079400b890031601c00a0503039204013011390034000850f444c0340141d41500e00607500142054122804106940300701d9001c0303407001d003040e00a0070135071906a0006008642316070f20700c00c1d80010b1841e450309034010a85448501001000100700107400f600c86024a00c0c401b41c106290b0b1134041d12010204d0b5000da02c80010203650b884161054507045000c2c4c5000701000a40d00b41120000021407905101405003000001c01d003004185441244415aa030049a5008031444030507522001c544441240c90200c4000300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 751796205 1250 751794955 751794977
    0x405031908040203120f07080705010903080a021204020f12061f17120a0e09090a1502040f0504050703060510050901090f05010c031206080a080912010e120306040b0a08010507 77
    0x80700322821401641c004006080c003000075001d000d05031340900012400071104100f8031001511500c0036203c40d038000d500000c1d80505a0501914101000f0701c0300d16090720402c110106042d0007802d0350b4215805449603800000800c001c540010079034810011035200758001c0000f022808180301e05c252184889100109940780030401c004a404c40ba000615000071550200f250900005801480702500d030140f114450040410311240c420354941c010340d0000007000040c00112120a10140380c01042140342601e05030064240341d40e41d02650b807095481e03c0105d100071703200386c100714041d04005012031410040840c1c06040e690140750058085950b8090000740c40203042d00d0030040303840613100c40f1500c12181c0d034115502c0c0007103040016001e0f500d41c80440d081c941004030005140c80f548107140e4409030f60040145280c20f200008142c0d0317042c50341c5103003000408180e1210728a1100c07107071520b80c0c0300d4070001000741042c00341440d0404850072001550a01c1500034074044c500c00e0f01c41d18580b003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 751797455 1250 751796205 751796207
    0x3050c0a0f090b070f050c0303031905060a17010e010515180c120708070f030501050a050607140303010b0a03240b030405031e03040b06040c08060d08040b0d0b1f09050904110904050319 81
    0x4041162f1a004c00000701000c0101480550441030380042c00601e01c0c0d00660704c849000c070708031242d00c3d10310445a54440141001c2e070005d07c80e25420440104480c0c254034110700008079120b51030681042c9680e44071001c1030b80300000000342c0d0301c00003035600500d103285020322004086200c112099000926030320901126540603204880c16144054200142c00b42814103000035035200c0e000845071000002c0404504a20620107103000c1c0c460312020765501c0128150003804e40b0001040c05034020701080c039640c25113504417040c1046a4034034404a4032030303a880c180705055014418180030550082c60b032400150100100440c40b0ba0b1090f4690304040d10740380c0610046a15101c035a0740450510700104a2034a807010301044402d2003000b0799481d081d188c0e2491320844c0c0100b00e4001d801c580303d0840a000c1e160014003919103002e1100c01740f81d001c02c844001030000d40c41d4442e00d8042c064440c00305040c008002d80d07140c0608009405422076040a1404a0352503102e5501506078000390075001c4405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 751798561 1106 751797455 751797457
    0xc230a0905070905120304052106040308070809030909040209150a0e160f020604120509031f060504020f1b070e071e03050c0a0f090b070f050c0303 65
    0x642001403010f4862840c030703048584030300102c48090342400000001d490072039504445214a02410040a84000c4204d00c2c0180c0381e40215400c010500d900815500d000b0800c50341c80e0155640c031034291603104e01402142035801100100820058038100c0581a04260007011305428603034220002007404200c0d80c045100c1d0031040c020003805200010340c03840001654249a900900074440007034454600400003043e0040e0020340c0b4041030b00c07034400e840c03082c800901164480d41d001034421204030fa1103550001842d04000700031806003002c1c001d40e4402441110001c2c24034040e010001402290b06841100300d1255400015040741d00d208018014141390f02e4004414104a019010040c0380c01c0503581071501f001f041c0280b071b50b009001c4a81900311440c084444110081d0708444201d115441011244e0012034658103000805c00813038601c500c154107d0b00b410841605058413 = true := by decide +kernel

theorem cover : BRFrame.Cov 751618705 751798561 := by
  have h0 := BRFrame.cov_init 751618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 751618705 ≤ n) (h2 : n < 751798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
