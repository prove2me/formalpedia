-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4779
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:42:10.032987+00:00
-- url     : https://prove2.me/submissions/5a6db887-209c-4434-9df3-96cb7a164ff2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 859352517 ≤ n < 859532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 859353767 1250 859352517 859352521
    0x15040c032408060a2307020303060f0906012f1f0c02010e0613050304090603030f0201050a110409051b03090f0c04020a0c020f150f07031b02060403150b06041d0f 71
    0x1002c0002da10760b00048042c40800c0e10703400c91842003013251036150292641d08088061000c01034000c400741d84107802c00e9401000300c115135410040700d0f140035189180070602c0400d07006000c107030808107035400b1350510855401c0d40c80c8500c0c0f41880c01000906c26000040c1c88c401085501c501401043c40180071440240410496055043e407203800182000034103203056030555042100030303c1528002e00504004010585e03403400d0203413074400b15600c1c10005500e800002100c6440d24030030604c00320019007003282400c1c00c00b110240101170103040c000319182400c215096a01c4148000c502c5000948040c001046100034540d02e40210710011500c41da0044c0080740d0340d036a0101c03902c03511740c2d01110140751030400500414804142980100340381080060101c3e10015118014401c00303200740d8401c40e045010120351102c800103c01c009501200401c01080800c444034290001d1000413500001d02030442c0c1e00203000c1da03000b0780c4140e0707095003091428403483c0e03541030050340c3c0011199400680f40c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 859355017 1250 859353767 859353779
    0xe1203031611120313050c09012d03030915020304080a0c03150e0c010318121e02010221100b030a1401080c0a0911090a090603052a040515040c0324 65
    0x580001441981c0068a0f42c9403401032010810040445c003102034003241c000d503100c1c1c2081c2c007642c2610800180c4028038101c200d1540c9840313071a40c800c2f44c0e0140d0350710904034140001c1c54458042c003280c50701184070a11000c12100c0301404480891445aa12001e4107455442c000200388050060181c0311840d108985c040c1d00004100c041d841042441c0001d201010958141d5000c1070a280c06080080615403040020b9000144ca85412008071102d00d5011074900c1c0490a03071248506480403084000b002507600c080100b841030b001701e400e1402d143d40c1511080003140360340049900254150f103031502003466544407030405000d0912140a40210303c0c0e8080400d110054500c0b84c581010b940c1c1d07040b9070381e2403541e900f40c1d60310700402400b640e07100d50381d01c4041014040b1070100380e600b03009500040410801010b1490800d400c0742da203041605440204200042c10010200119250b002d50320f0900b03a60fa52180c1c0460810507100003e60740a0500754003030340d19004003121200c2080349030074404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 859356267 1250 859355017 859355053
    0xe0705130f0608090a05283c02060417070b030702330711010b060d020c0f070e0115050d09120314010f090515030706020d02060c0708030402010e1203031611 69
    0x4065054107005a415400e840c5000200c00110014154001c00b041c92301c0c0d40b010071041d02119803000f9001140305803c045008400c5071407450000c2d03202000300400c00c059130904001c2c503501d20300001039030082031317480340001a9580708071201e00c0160401005150800203154580d800308072a04403170b81d41e030000381513007040028018210b0b5060001402c03580950072804d4000010b42d8001a042079241d101c0325109102035080424a80041c1c0620003041e0039180001170854101c600c1003681c1103440c3d01c1d00c1215044007204003091010040c1c100014440c890f80740c003500c50394600c110048034034050480e07001800c41303540c4004400101d01e00350041000701c8044c1240c400b0745080f81000102503d4200700006034034442126290540980940052241c1d004035407952009a0754003a13480c075541d155050062807260f021b004055140c1440400c4c050351003200e0010342c1000282035041444440003078bc07071841d001150300f03007a060303000e25220440542c410b03a107090010b0b02c2002040801048292000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 859357517 1250 859356267 859356283
    0x304200136061701150e131808090f0901030308070f0c020a030503120c0703090603091104050906010510020f0604170f0408060f0c0a02070e0705130f0608090a05 71
    0x20366120040101c070701e4400ea00c1d1409100540d20541001560341101400d02a070920712034144040c90300001801e54080d03440c8500740d940c555a24080c22a000c4101f0501c135405d03c41c992400d664515100c8506070407608410b901c10301520125469a0b0040300308009030a0310460070303008086460041001030f410040701c5400c030029062100c101902440c084070801c4005401a5211a0412000052100110003000070081e007074681a65541d407000484010b01c62090002c0c00201c21745000c1119071f02c2507004401d01071098030107c0207031641c18000380656805641102e00c6030080c4004000c54a130402da0300062840300e001070842904948461901c4450013400070301755003011141e692440c0d008808650070300502007079464a41e0384901c51983c0e04d44040310201038800d1100c000c16032182c0d203c0e0030341d040e0030820340c020f1500c80d0401c004001411000303040d000501006100d100b0419031024165000b030520612888051403600c2c1d4020001d03e00548641e140b07801030a00000403820200c1c40c85 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 859358767 1250 859357517 859357547
    0x41a030402040b03010c1d19030f060b1002030406050d0209040c020d0807020c0f0f0301020403020d030306090b0108091f0f180c060905151e03090d0906081012150203040803042001 79
    0x44059847d200100708035440315410105542c4901c81c1c08820050001d070b20364191802003030100101085030301440650000c05152901580c0305010070040140710740000c3c001000709240150030008e40d400458150b4416100d45c07801360300207a100240542d8822541075208050380700905060b2104008076500201801405028000b0b83d9103c148545003501168010740c0d01500c1c0b681181c4090030018020003144c015074100c14201102103903c1e41c0314050803405121082d003d0625010301c540d119004603c0514800c40c9180c6600021540040b544681c00ca45400450165404049450940d004a181d508140148460303000c09202c02e032503864404000c08201c00515581e0207451540400c42d503042c82d00c40f003403507400004101101401144180310303600303182c07140c0343e005440d000245ca40341e00845560036080000441000031010b01070304c030320030300e0300990f4000441c505040078001641c0c8100d0f0181c5120000005003c100180500500901d81c405030001d4035840311900001c02100340c0754484 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 859360017 1250 859358767 859358807
    0x81902032b06080a1b080a15050603070e010602010f05060604030804121106030c090103181e23010b01020f01020f0702101e11010b0102010504021f0203041a030402040b03010c 77
    0x1001d040340c1d1180028114240803607494045520784011001d0f0007001c01c5040404130400040d4404001980c600a1a03000507a800100000c0b20400c005040080031542e043c800e45800103654003254140342e018100d40d500102d4081e21744049003040d80d5000c0c1c01030303000e99008c002c02c0012440c400c0944041e1107001040100e020f04900f0480508050b5064580d0703c01000030600c41418000340003004103030000c2c0c0b001d000d0500d0040030b4a034070030b004840107400c50124600d00c038030f00000680087e280d40c0c807610b1070107002006e40004100c43c1020010000c450f80d5601d180b5010f668040150b501540d580000a40c9066040100c4000030b004901000340284402d140341003003140201d8002c0100c2070049411055007102c4c15000f40981818410703442c4c1540703841c0d0440850352060149511580d00580f0a140781802c04040d0b01d0582131444840302140001e11021031201c0c528400001032840440766152641410b00412048840c0d6015043c80b90f8581107513203c500d5005010022207100000c0b107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 859361267 1250 859360017 859360087
    0x336090903090e16270308030702030d0e2b020d0e04020c16050103060914010312051606050415020304110d05031b060f060301020702031504110a0308190203 69
    0x2035a00c81499040b18440301c00000c10002e540d01c0c4c00e0a08031200e480750383e503500403d6600300e800c1c892044601250015607110340042c40400c003840001c54004520b84100ca182c5070304d038035201048509054100e1540c0d040160100284d0340440508804041d1002628a00907070f05900070756100c4d1025a204140280c0c0c06040c0c455a1b01d590590b942c104941003941d210110f01c1484041c1d500c424090706010905e080c40108404040d88114003003514000c1034000300344d00315203600911001012003001000810401e00c200703248588100c91205120300c0e004903003810f00e480c102402403544040c50901c14414410040400c074094034500c1c0d0960305031050b424014003400c0c054110b208003e40002222011260030811040014440b0f21402d072100d2207041540310074041500b41d1240f03e0019515074401c500d12641c0a16243c0d206030050720900c854040100004046015490319900550b020213001c40c000541c420307039030155022030381540f000c0d51405848290849095001900340110900d103080c1e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 859362517 1250 859361267 859361273
    0x4080604110105360f010534050a0b0c0f0d09020301090611070620040909020120160f0b0306090a090203060c12181209120627070e190207020d03360909 67
    0xb234103002d401d000ca09448901c42c500e0030015543c01580b9011144501c039100010b0701c0310810700c155036a0080f102000303403500f1303a845800e0014044481c0141e034155039030310b581c0001451038428800c00708101c0684640310b49040c10004102c43e400354044055000041c000c030204440c1c1000c4509803940b0344000112205a4001210040b040340c8504035551222103844030704460004841811907010038145540540b01d5441c0400c0d00b4440c0f01e505011103041c00420010702e85446243da00020340c01000440c014640c0009140c05010340e03140340441e41c00204070280d0391070311104640c0078200075a006d0811030044040b540c4d440f031500d40b4015241020900d9440e655a005060180516580440381c8605104813500c1c145010b00d000303a0080380a032041c0320320042011031502e00b15031800c80c40d8842e42c0d9954075110000014541c0d03031030415908104542c010307501c25081080c1603010b907945031031010b83c42a103615501d41402c1c00c1d030003900f100c01411480d003255500c2c410941b0145040881c02100501d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 859363767 1250 859362517 859362577
    0x1050d06020d15091d030a031e0603060b1e1f02120706150509010311130e100c120b0d080a020a021507031404080604110105360f0105 59
    0x3145103450315003402c000c00075a002ca003458030240d0708004400c00c100700002c60107040c00203814179401d8450b001032040c6100940a0303804404c44410f1640140f0a440200510071f0864003590021500d95649001303021480c103000c054048090800b44043c0700c0f03401c00e0350020b01390303a1900b451540d502c01c00311054a1551710070302c003c54421506010032038540d400d61504030003504078078291809100003040005024070f01520407504aa401015200a41101b102480020200d04c950003071f02945074001240e0b0141d0410151000400c4100002030903c3d0040008208403c0c4111551450b81803116030059a65000711910322240c2c894a1580e5820000d02c0981c1491201d00c0c01940c41004410416281c100500003020501d10a80d074004000020464000c158013507400b903400d080e03000300d00103000144030407803080000c00c05060a83c02c100c52810f00403110500003010305e011891042a0741d8110001c101d20640a08003143c2c0d4114007202035000a0050040c220b20012000c050f0701c40c000c60800751 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 859365017 1250 859363767 859363777
    0x90307110a0b1c0f05040b15011704110109091b050d0e0a140610060807050d0e0105010920090108060607060f111803010519020c0708061008100b0901050d0602 70
    0x4080b140340c81d1102490b10068a072203140392800000d08000559074080214824a882254001000100754070380000012040c0480c00d038190621940d007081001106541d140c05200d140305402051000c0d0300c0d81d00041600c0142d03480304400904051410448d00e00c9000c6c80c6000c1d404a2426903103400a400118010740360400400b0064045e502d04d010901c12142c00d00858800560200c48040c0c030f4110812840e0303440b61140b400000c031480c001c07a56942c031a000628416800d000b01041b5201c0e512103142c00c40d07000b179001035809a51003d182c040c0116241424200e00125a4130300d00300f80300c0e8000a042c003400140594881e40c40010346004101055200003014810202d0400c0500c8500c1e241640651086080120b0141400c078892094501400707090b100d030003a49928400d20b04030000360380180d004107092045074060494041181d2000300320045c4245d00b880c04074030116181221660174100080700b52a006800d01c200c29500752215003100d070445209a41581d00f038192820988024050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 859366267 1250 859365017 859365029
    0x90f0b06070303020408160305060109020d020c0106170c060f192003071a091e030d180303050c030709120f150506090a060e0a0906090b07050403051005090307110a 72
    0x1001c5842810302d03500d03501400c241c03100041181c80040c60412040c0201201c0d02c0b0050103688054014048400b150700501100c0b141d801001d424041000411400e503030b229005442d001d9141c0d911421021020451000c00c030005481451a1541f0402081d590b0303c21080b0070903441c60b07605c00300c0020910805400e01c81c1e014500580c0000d56545c01200d480c0d0303000507010f0310030f03404d07000395000d110000d018041d010710740d144000d00d912452000c82c26510400055019624002030050040095041c001d5200494074402200382503000c900d0050f003240d074090450881079600303104000344250003981c0c14090320300c0800003005119007031034041c41c0700110500c0100102010102d10f0000f604e25040540264000c440c030421544c0d82000c0364080303442e18425070008450f12008180004441d6020b07202301340c014800400c0e4004c0f182c0380e00030880000c0c1e80c03204c0003034800202001804003e0100440c0a28101c50a00c80d50402c8000195280603140d00036101c0d22061349189000d0b61010384520017894 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 859367517 1250 859366267 859366279
    0xa02030607030c0f030204141302190908010e010e2e0c0f1d15030604090215130f0e06130f2c211602180702010b0a05060301090f0b 58
    0x180c5848002d000d403440c4071441e000b0965458006103028042d000b6201918101c01c04882950b80c02020000b00c500102040c0e8500765007001007140b028616410601c4200254882d0403529203080c800c603003141d601c00000c642c1d60740352a0750061400000300e2608401041c00d543c407202c90311020040014a400c56440e020340600e040074030300c000ca411603c440c03205821925220828601d02c410750511841c400c01c030a0340108a003642c0300324901032070f000c0c542107071011340001440740980d03000c111080280061011034050109039910310004404181001d403800c0d0400068191416020801d00270000e0f00a6110388ae48a00700520b800780c5900540025140360410300c0030401c501d119800c145044021900c0002c2c0403c6199510351002504507070744184035501140609003024024100e8002c0c1c11440741241411000501513681c40e0045058100b644900020604013581c0190840358070007500e034010034401c541000180d440c042568110307500c0900202da215030014200c002800d640c130156502c50 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 859368767 1250 859367517 859367521
    0x50d020a030902010e120d030f0b0d061e0e15070c0b01170115050a12051f0212090d120506150d0c09050a18091718030606120318030a020306 62
    0x56855040b9080c190b0003130725500b132540c0c0c0007014803441d0b000c110340903000b03039212030f00da0b00ea25840381d8400d00c42815520f0b000694070300d0722400140150300b4000c080d600f0316100c101e44981050101a4800c03098682c060821001f05181400c6803502390303254049034034060480019209074014414030344203a5020641501c15a150102a5904800c030001c4c01c4156181002148028072107034100010307604000d0a01000c5882c100410704007400c100003c882501500d05c5040c0300750310303904070204203c0b204c0070056241d0714201c44001903e00c0052154000350701c28031540c02416009040c0410a00542c030001c21542c0e03520020079105031805134510854140047e43c1a401520b541c8109030b481a980e8422400c1a90b84003041003400481c000d00100703480000052200e81c2c071030350202d286540b14000310203220700e018222060680020702d010600d003042c40700302141894284180e56014404035510b00d400340c0d10100607607480c003912184914441d00c50f401c0703042a079810080b070251994010111010342c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 859370017 1250 859368767 859368787
    0x80310080a051f0218061e0309010905161413060f08060604050108010501030b0a0c120f150803160f0501060312050c120306062505190507090204080a12050d02 70
    0x3070304040b450500d01016140500c2d10703c501c01e00890308415000403000920343c484c0402c01406504c07c81c80c803640740e4549410240301c1e10340c0c200034510030242c000c000150700c4082e01b400c60070014060a03104102d8483c00003444960300001174a880c404041e2a60420349040d084101c00a1025800108800705016000a041d4070001445446510305603024481640d0700c90120b0300b643d170301303000041050003c00700041802205030301c140d40c22840392804222000d0b0820440c01150841d030701030418192556080400e8100041c180340013000044000c51402900c644145d00101102e0f00091078220300c0d5042d84240a825040100915000720142d00d091504603009055580014213030b005601580030703003102c488041d0381072700d11404005c1c120915107a00203c008080850101d40d10300e445071038150280200b02d00b004002d1045c5448102282c840040c1d081039032405074190b02043d4039a004000900081c0d201043c06049594850210941400c1d030400a0300c0f940110f5107015442e91010408080c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 859371267 1250 859370017 859370023
    0x906110a0813140303130506070f210305070f0509040b0a030206040b04150f3f0501140a0f150903081204060b0609010207050f0f1203040911070c03080310080a05 71
    0x215000c400072036440390700f00400e00da101c2c0240c8040501031030380000200003034281040140304180c858082540034445940c0c40850f0400c08020660f40d01d00850a00d015040e010310420b900f114441c2818804400d001c000248184680f081d158041da0721105840300e03c1d101d403442e0b4400303180d000f04056196510342c0c1d04090250414420040b40000b240c984486190140840c905080d80365a0f500e0402081c124a040904204188601038804d002240340f11030f841c881841d00c1589014400821154507107440c040340091214049845408040001c00000d045d40d0501421204041c5200c40440d0b0043e1059a074400c507940050305a40000650040200320049240e01c2241700b980208038981c003940c1405114014519840c1c05a80401d02c01d00c145e01d4091025900360308020401d02c9007858007404551a42990f4002d9441d030380c070115040c45803100307900500322a074444c48009400c002c41904e540700324580c1d500c0007600905000000c5244101da140c1200c015148880454800040900c3c05551b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 859372517 1250 859371267 859371269
    0x1b1809010203071404140904171b010f112205030706030f0c052a07091a1011030a270611010b0906030a0204050a180308190501060906110a0813 63
    0x2001030041c0f46010700c1e1100080c19079040d00e051240203044069200280465028050720545400c203274115580241c2d45904010810b01c10b0412040700100c458116150948103155825000c841c00c2c0030030400a48083c10a40d0300c0c00011080300c89008203040c0141246608d541c1016405001c0c854001c100c8903019000500b440b02c0003601005404100b1404a8081c011100710746424800f503030841c0075440180c01408102c0600a059803006e5545100000071205190344004040000382c5103000c080c94030411054246d040c504040361681c076550341c1e40b41c5a01c2001a01402d00142198014288a9030040588010756445100c01071030784400c8064031802d081c44c89100c00d503003420601b1801303042c48100705010f024058014481c0000a500b0880604001007000701c103140d40d4440c0c1080030300740b0342d4040320181c02500e4601c900d0074850600c2410000e01200e0054050920004110447e801300c1c5100499146240000a05104092250805880716005403c1c600d020888401410031420010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 859373767 1250 859372517 859372531
    0x80406021b0604030305090406082e0905030306090406150b0c0c0409170a170408040e0f060102062701090506060a050d02030319050f0a0c030e0405091b1809010203 72
    0x524100c0007800500c1907003100c5035449400081c18882000020b026901034160050020004281c40392941d643e5454051044a044030313400984501c0ac06416041d210f54800e4010003406101c205540e4903420f40d0381c4406007115016003041d400060920940c1e030320452201c1905145d400703465696120740c0406403c8100d00408038000d1030411034031850703d403143d4405075a001c1250a1710480d804600c442c0c60300300201c02001d100c0c0050039250702070410b0341c0d0580b0481c03044015545441c1800c9110000d00001080e201c1e15100d41002e010f180c1c0e0300000d04c2c80c3e10004070500c0d1f05840420503803451040391200c000301c0c4c0c150308109808003040800300340d8074481c40c0151512808159202c0410000710f85070100650036070401c00806800c4140c20349109c034103240a040641c5800c9a001005025900503600080040c6142d442c0d0010154418039a840101040b9070905c05c0f8200112910b88480004680c4405000c9076410100242c842c05646e922680711501c4000003031801c50b46080c080c3d40111054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 859375017 1250 859373767 859373773
    0x209090a0c0e040b090d0c02010f0e0d0501150501080f010e060604170c040c051317011803020706030c1d010e190f0806090703080f030405070306020c162907110d08040602 75
    0x60301c001d00012103222080899882a00c0c642e00c92300155131118856491f2020403106420003401038889082d8020414822000024000320201d00145403100541142d0304009041060082090750741e58030301c0c103507908500b146c500354560400158a80c8240e41c8000a42512a20302150b145408034414400040c20b40d020300803d50403000c215414842e011802c42511034000c4284090325900d2203081c141c04410000052000c1444907001f4800c1304142c04030016404440140070301035040c01200c800403018108201883c81140c0125401d0b181e00e10083e04115500038942041d5540c600c0d004a1300d480d8134a40c0000c42e4441001040c440018050105144608800300d01180740c001070100840f5000f603169401d04820909100341588040c10540d0340c0c0c81105004070124901d03100400f60f040e00c2400800c1a84080c01a08001c40c005612079104c102d00c034100034841400000c04141d01d072051100e03032a0744824618010703d01d43c3c20200c029801c44151030321107080002040091007592500d40072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 859376267 1250 859375017 859375021
    0xf061d01060905031b03280314070c051002100e03040303080105030d020304061b080310050f030a0b07031107080310030b0a0510030f050f150610051201030209090a0c0e040b 76
    0x603501602e05104180d0154020410808000e0607002e588441c28002800da440000300a044218800c4034103410400001c07021803007108140c0c000f040c8071814455410b1980c205000f40d12100164041441841c2c001e020200803c10034078801c1c41271240401c5064010030440480d485040c2c0e90382c225001c124049105a4004a018a00010b00704010521b0358000d514150a00e2003c50301d203480150101d010400840e90303c0300243c401405503210b01e10b08160800401c1c40d01c0200480005c13804240340c0203822060055010172400c9480325803206241c02c0104404041921005036840b40e40005851880048144611003c2840c0e80d40304403405062204140c0e100c81c03038060100c1d4010703240120500c2c0141010400560041d0120382054010030076070b0b2600c0f061140560414012a01c7e070701403110078108210803880c0c120a400140c1c5008d20348541001c0d09034800c1c0315540018000a40702c0c98005001800010f400c01074020040e9020041c8150603656113141c2c8100705098400b100c4075102840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 859377517 1250 859376267 859376279
    0xc040f06050901210f0605070813031d0a091407030501171c05090d0506010f08070605041a090a0806010e0a020307021009060b1509090a150b0a030f061d01 68
    0x950041d94001400000b203a4a4044000101d030303040c040484100d510807030030402146400345840312050040c1000300c1c0c42c0c941240024404035004000c0c8003040d800e086810301003540070030b4000b038050816a03043c090a0011000038804040d80d07001c041081d0401085261904030610014000c05050720280032690301d48000d0812070034000c03545017040d404403d84e112080c3d12540003611006990601a260050000200e01440c004800540d015400440100410880c10004400402610300904a8182456801850b62003980b14090034160260304015094004c08101c0301c0c03198000f81070b1003d013a510554141c0b290b509104043e060b480e002c0001303004055900840340700f008141c1c00341404e0318582441c1002400c400b4401d276107440c1d83d542e100e045a01d44c84c044800c0040014000c54543c0300d031400300405008000c0c4802c0c0500d0034401c42c4110740300710030000c0080e16148621145c0725034202c201100203001c101e00c80e05400d070920301c00094030820340100404c0780e0b60108000c02644c0e2591 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 859378767 1250 859377517 859377521
    0x1707141f051e0c0114010b03100302090c04090c021e01090b070305040c0e010b0c06130b0103080706020d0c08191109330309100b030316050f0703050c040f 68
    0x1103800c0c004034950061039800d118500a0000e02c214810400e81207150540008075500045242c0216a540c0e00302c1e40d144c1c202646000c1c1c01810b076901c6842c9540382a203d443d88080381803100a0043c000341000c038198008070310580d000340088400c200318160440100070343d980550000c80c800c840000c8240038900806005802070300c1c0d0032401d0407103561a000005ca00421000301309952800c110783c00482c08042c40080c560082020014058890b440350800c20b041031400b074155070740c03010080c5501c00012011800b407070440e60445c0c80c00e61110103034107045020303116186450310410316060300f4040c0b898104903814003490240b100b0703046102c81000c0d220212004080c2491100c50280003c0b403032132400b1740d008000b40d42a5202c0350740020040090f143c0100c1c0800c16049420004810004070150405c8408882207541c0014410294035001282c4c80f8424024402040c3c01c6182402083c0031003040051000900c00049400703880d40c0382804d42d101c80740d40e01c003607218600f030824050441f42c441c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 859380017 1250 859378767 859378789
    0x70308010b032520030415031b200109060c0f031a1c02030318010e030d080c07060b0306041b090e120c010e031b1005091510170714 58
    0x72070144101c001c64414219a5074850382082c0401280c1315400c86002d080c000d1038070f419140da03030040d03031281d08110b001205c480681c001c103402c041c540758081c82c11003039000031401120400d0401a075088414041e1040d01c0308041444c0c1c0c610342c01d240c0d1490401c401175000f403501800d00e555113460400d01039011001c1d10b000b1080d00202c1000d4500d914074500e006ca032a071102c60851142802c8030325031640824110340001e6094031021000da00c4814480d600901c50a40281d001c070701410010310b0302c2201509152000c1c1054940c0c1c00041801d904100d0344c4d82c84118031004c010b040312610700c3d203441c1c40050751405103180744180544200002e0440c000e0701511034028210310207080c0102030340009900582000314a450150348076488051070b00c800b40000d041c0440d010031034561003064040000d26001c40700145460040c580b00c01c00c006c251010404030030708030000c244800617482d030a100421290403a00300c0101c00e56040c60442900200082070000c0311050141840070703041560400404405d6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 859381267 1250 859380017 859380031
    0x1107090b04200c1911010e03030d11040e15010c03030b0a0b040e0604110a0f0c021f0203030901060806060108130c0306060b071b030506180709020301031a060a0621140903070308010b03 81
    0x24a0700d514942c1c0d1f005100e01010780c100902100c5c18128100800f60596120800021094500081c1440030314490711446a0103000443d00c000a2410400020b014480120010f01003541d600921111640d481e0941001004400c001c0b6854a0f141c203c05000740360181d0300035106e2468008802003400041c0d0a4074803d100340d8a5010008080c40c0e810395045000c8a4200c0c1d0140038450081c02948440c1220b180004180e8003c0d52245010a1440d00311807a40d00305000c903a121408101c440da920041da02d030300001c503607034224041c1c1091500403136500315500020403040c20300001040703484580d0090229180103d00d0049006184400a0328806a601002c0c0c800c1d0401c100080700524103902400c041c202e900120b48009544039111812a00207800848000c41c1e0f80c1d01e55103014150002e50f43c0c02071000c41d4048079071440c01c000a000000d5162400b0442660929001c80030701c10341e4885480881d920561900d1480c014800c2a12944102d4049002c2825040049101d800b0541038900c07400d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 859382517 1250 859381267 859381283
    0x490516080402100509040e0109030c1b0806061c05060c13050f0f0105030919030c14010213031e021302070b0709120b040f1a01090b011107090b04200c19 67
    0x3e58508100d500e6848445120b8029444d954000098a0244600c451040c06035450091180031464a400300c60b0202840071000015582d09008480000c28142c0d00440d01700e8507503014403003070b0698550b005583c0001800f503001e81000c0010610044000b041150502c12118210a07160400c00002081e291102a002042c2c86110a0194020002182c104000034102d070102c0074107284007103c0c3c0049c10421000070700c070314201000f0424114244001b408a41c2c1c001d6081104204a06e0008200344c48054180a003a646036103100309040b04c04080f65402401e00c640c0034500002d118065030101908486940119001403800b61007030011000f41c0d0980365005072404682e84515021001c0500b0a40c1c800340075001c210006a5005a00c850007609944241101e40c98102d04800301c455007803100b814040c4c01040e0009030400419044c0544102c400c0000340d040388039022800400c800b01a012104003c48000c1202680b010083d0145042440455160a000c1205591064612000180014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 859383767 1250 859382517 859382539
    0x100215041e08070f03030b120a111306060818010605030a03030509031603020607030c1103040512010e0d050d0e0c090439030314490516080402 63
    0x18010900d101a2140107103003503000552544800c911a80300502c100c40821204181000b05038060003007410b0b840c0c040340c50040d241c0b140092181c403052514401000c41900f0260a44642d590f0441ca04090a04c214100300c165101e0601524a840035616603454129258000503145030500403003050710000340c0902040740859600358080c0c00c02904001c4140001e01695803480400400582c406009074014000c83c14502d0002c2e084600800301d007801c0203001103207100441c100000320340445500303461109881080d0304403140102078000340d0340003038012081c2e165a080d80c030502070008040c0e011400c020500b10025542e994081c20120f05401064400003c0c0219200706e85c864801c0800f0310b16802c520142e404407288206c6c80d03a1101400b520030f01c0082c002d01d5840191640003640180c00070349408442800c8032400c1c0c2900c6194001050f51300c080701400c407040c2c8003160200070440d440f007103401001c82c0c003640541001c4a40c8044241c0740740303003007110364416813180c0c0c0540c0e00903224076812 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 859385017 1250 859383767 859383773
    0x17031209030c06040b01140d030e060a050409050711100e06060d030c0f15110304020d020d030c170d1b0e040b0415030b1803030c040504051b0a0e10021504 68
    0x800200a500080c0015202d044080c00b1080c4560310503074100a040d030401000c4c0c22201c41d2001001d000d02c510101920000380c00200d040200306003154001c2d224800400116480d1069400140c0f8040c20001030291380390b040035040146201c0c0006468594111546641c01c698207004014250391140022622034189800e15645241c0245000040440182c032000c13540c035000341040301c4040f1405400101c0d81e56501c6030703d1500020b035a5243c0ba604040d000240c0798000c40360060b12903000c41d00481c003054066201e0758002c2c1d9200440340310340740b00702c5001d0310755407c02c40c9010319150030400c40307003409941d0032000000c050881e00c0303c444440700785060000030320b03401000c00c0d00180c0e1a101c202341c0c00200b00c914801075200d5000740030a0300c0d06080300d10504040090340c07000f0758000d0080c042c0201040d0251819244203641c0007640d50344144054115030710701d542d42c5040910005103140c1a5500080c00c0e1032408090300e81d5400814a07050403a03403240d00c100c032604517800d00d0001c1400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 859386267 1250 859385017 859385047
    0x3110f10020a080d0f02122202010c020427050a060c210507021e0f0c0d03050d18121d0a1a1c0c02150604021309090501141503071703 59
    0x80c41d11135041c001001d610f5403803440b0807640a4181455003842e0071b01002040b141c0382c20078802d038040b0000303a03018401c0c107540081c0500340300303400091040b61640e0071020074804170714058004c5e010650800340103111a040c955107607a4907120584202d07040044a2040710b0040c007480e96444d102c40300c1d00b01c0d18a10521100000d01001d00b5810440c000c0d0541c0901100e00a2980f41401803d0005440702008000070745240c48001000d490048040204440100350000c040d107120007a200d0002c101c400000c9a4080d0842d0254802040000d880800200042d44100000c8101900c0a003546094005404100d0341007a948994201e43d5141c0d9181030440c4904ca010b814402d140c4010300b503201410100d070a040d0b03a600ca04420040e4800603c146e1803454449540d034000005403011442c2410144569880c40f001c0d0190002054844021000300300d02580310040c50300b40700c410b500ca2401d112103040700c61540022420311901c2400000718401c200403030703183c1000c0400c00041d0700d00800e254403194 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 859387517 1250 859386267 859386277
    0x1180504110a0b040e0a0b09130507120b06041a0303031f0e0702030703020d1e0f0224070908150106110f0307080909090309030d05180a03110f10020a08 67
    0x200100032601044040c2c072000b01d000e0160048090707071030300e8500348911500072032801082c07020410304041d078101d00398071242c00054000040300e010040c4802d140c10007901e006070756440fa03001c450b0329074003041c01d10400b0f0f1040b80c02480200c8040c8110088200c3c40310010100c0d400a5505401c10400315840442100794020086170240d40a00c44907940c2024284152003112000d000d6000066003000b05a4113100d503804e140481d00308407000c41c080321300c40114105c0c40c298103001c0c04140000c1300c4c1494020084460001c030300b40060a81013000e0f5000440300354003940c40e0b0000c20301d5600d02180344580411034081001011100744c10aa103040710072102d945c0c004008201501440f0300000121b80103100a00c0200c0c05803d9072aa10140f080c10310001d598010300030f1400ba00300340052103140c3e401042d8108142000e18100e5100e810715034141d040d011444078010b03403020014030000f00b0080e0020740842010700489500c00c80000d0b040a003c1c103080b0f460000d07030040c1c0252400ea00021000c8015003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 859388767 1250 859387517 859387523
    0x1081801061703030702190b06010f090e0a0912020714060306010302090603041a0c040303051b011d0619020405060703120b0a0806060306010f0815061206012c01180504 74
    0x12610715030307403012041c09002034503011550741c20000c00c009580d50100300060300300150034141c2d40c010303000751100d168130240581198100084d989140c10640d1240d000500a08450001c4a807942001e1850700c1c0240f80c010403c4030038815020804040c2400456104215003100b84198400b00c0e040341004a598001009141415400d01c501c005548481015601c00c0740b041c81c072002c0700b0035070040318008850010002440200100001d10009034844265030420403110303c10072103030303840081c1c80f8007500c820401100c0d003031040c04540c4640031001880c1809040c0c26444022032403080c0300c81c101648183d00480d030700288104401d5001034030032440030404010b118800214802d80d0b03c0041c4941c1c0d801c2e8454421a40701d20140001841c080c0b000c5c0e0700510003412461542840e04801d10344488246e074418109666840c002625500d45c550030600d0f03903c0541c01d41d00030750385820100203a150044100508a4002003002411b03000740b0010740e068070f41c0120702c484000d5502c500e6401a1a004000b2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 859390017 1250 859388767 859388771
    0xd0f031503050a150e06241f0c0611030601021c0912080c0d210e0a0503040b0310080109031706040e0d030614010318030e06040e0a0504170901081801 66
    0x301c1d42c2404000402c52103041c0c04031905004c1c4e0340d80e2007510001c2c1c1a10407103800100520103405900304401c001892000e440b40004842c030f00004050310390148404480c0c5515075103d60410390b005014208107803040104115611451112080c41e000231110280075070701040c010080411250902e003140c03035142c94000065502c640701700b5100b1505010032a2071240100b8002e58800060010312030040131881c085910082030101c80310a4805a00c254400344d9407a8890001c410091180303400f590380010817207903101d949100702e43c199801254141300300c0041c600d000c0764184042c091014600d405903991010307044901c00a190000002d044241d019585e100103a01c450001d014000348140300703882c0040c006140c1050450300707805003810710f4101071070900d541c0c80030400b0300c800041490f05450982c244c580e140c000300b4014441c07904200400700c050404c10101e2801604414425485401480300c80081282e05400354000d20243e103000c0744245000030100f540d103001aa122140d90400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 859391267 1250 859390017 859390019
    0x80705030a08031008101505030c150a11011503110a0b0703140d0f09020a0902042702070c0f0305102310090c0c170702060d0f09022e020d0f0315 64
    0x68185030041b1500e0070160aa1182030144c40400004035440c0102001d90140c400c17a044080002e0501c1c02101c400c007a003040115208004c544070b0004480c500c1d51101c02001511503000c042c2d580b00140340720441e0f4000181c41c6000742e0f401c11079114812508806001801c15250740d07000c5c0e0380c0710100c141501440d1414052082c416519026000c89441140400101410301d0b00501806003490740001d050140100300811a0340420380f41c8102580701c404090780189044803070240079100710355024203080c8c40c0c0c1c5030100750801708242d20000c81c6d100d40102e070400000b0020000a40d0040200c060248030584090020710014213611a444000318200f230500c0390310751040108868903248060000b80c800c491040c20058926250b540f01010003070b0050803d001d5038000344141c815001040310194480c400350000480503004035175202d60003072142c060318607081c003c4501c5008051203090b11000d40c641101c0c1150020031085014107150760b8140402d94100700c1600038099141c6500418007007224 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 859392517 1250 859391267 859391279
    0x11040c050720010c1a1609120209040602040e0907080118030906210c02011e0908190c061a100f080105060f0c010c02070f090c05070311010b030a05010b010306080705030a080310 78
    0x100c174502c44240483c08000a061450f4140c00420900709250140b14040741c0620a07081848001030602d030707040794403d04682d00c91409a01a0086034490b04007650b01c2010b11107141004036804050b118080020002e6404254103c0e03014480c514025000c245030340c106102042c440d880c03030103040308160307144890314041420715011110043c040d680140d40d0f48140c540e602c002e250010200880203101407100845e5030302e0f00d2542d40300701c2e80d00b2000001a00c042d00241401082c1c100c001580008003003007181e0110340c4503202c00e1a00c2d140740748100580d80898140502a04e02000c4112495940366010380c242024088640c0c40311350035205104043c030081c00314020074010b010140c0c80980c050440503103040104594569140c00000c2c2050400c007034810955804826210305e9601841c2c003011601560303024030300502104200c1038143c002c1c50703036a20a00005401440c0d68080070f83c3c0402c10340b0b40d60b40c20151a03d00c41d02400c0e5242e080761600b0f20109040c00081c540200341c800e29401d21a41d164 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 859393767 1250 859392517 859392533
    0x40506010c1205091e09010e090a08120714030f04020603090a0c031211030a12110c24011e0306051f0806040c0b0424140711040c050720010c 62
    0x108000b800240700040090302401d00080205401007114030050880d011000000c01400050045c0c08140500000181c10381c50108100717150b00703070040170543e5613544420240d0042d8004542c4800480c8031554004810710310b44080368402c8801206200d2103031070315030802103a070340040e1005045105284100d000314110740d40d544000c520410103111080c10f0664098440704030100b20303420641040c0091000903410003031508000040b235100142858190804c3e902034000c80440582034032030042d100700781724070000b0280103d1807403420700291607a0b10b500c840300d2038810b00c42c0706401c80c03110581000004c40b540c00254000342c04580700e9030500500d0700c5020f41c200c01c6500c402c20a41c850421320080c0452118180040d10841d03d0b040c1c0782600b04142c05118070460300e0b810303950b805100c603c0c0c000175125070316501040d50159070311a134500607800c2111a4110207440d080c400c03441c00216100c0076008504440600d50300201c0c101903050035040c40c0c40201c0c161078020703060000e0500c6010020301c6075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 859395017 1250 859393767 859393793
    0xc1b090f06050103112b09030302032502030a051308010e03030f060a0302010e060a0207030818040b04150308070507260c01021204150302090907020102070213060e06040506010c 78
    0x141000100c1504005061058403059400541071501c4c04081403a4591242d0440d50500c610000070100074041c580405051518008030070340d8540b42541740d03000c155040d0011400741d0808210884400041c900d098a58071071941c041015074400c204008070103024902030011407405902582120342d039800604d081d100b642c0c1c0c5158940d000003007003080840550184036000308050384d212801c141140d002030174001d0202d03482c134030904000c0380c46180207108000840165600c44c1700c0f203071500c0991081194200d01c40300d03c01c4c80f950030300780703156114185445400e0b8a51000d10500d41c607503245031503060040e4040902074a441c05540b80c00308081c5042007040b80313030224407602c2c0c1d80b83c090a070041504003a8200e02181c11500001d6050050082040c1070398140c178010108001c1103512400280c00030300c90703541003a404c84224003c00440079010340c0507200060080d10780810445807808004102c407081c1c01000719180d00403001c104a405c0640c00780e42d0100c010705158a040e1156100c0200743c0c018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 859396267 1250 859395017 859395029
    0x150a0f09090b0a061401200706080910090c05060c0709060e040b0a020a1409041416080708071e0507020402070c140d0b04060e070b03040302010f0606080103120c1b 72
    0x40c1c428020070400c06000e2164001003201e400c0100d0750804149940c128514040c0e681005481c1802e61003010140703204440c8203070400700300c4644595078030014000c404100d80c2a042d6004403a01c1d50450f0303401e40140404507610503400e15001b41400f0400110303810402c0c2071442882425404100000580f04102c064000b03030140e0880383c6003a24101c20440b200924600e212070041c440b00944c030f070308801c1041c044c10b1207030601a241c8038050089001803007444034000c001d0b4600002d00c10602410340c9008000a0030b40d50f03104580e5101401035518240c180c40310300000d481c074101c6d030524000c103000d00c0303c006007d0710300a0701d0840f840e000503040c4d07048400250781800c0120020840d04c1190007400030112004c1c0c0d1800110340c0c50f80c9410803c07603402000035003125280d0000120801c014003880f03025003026001603803203007040c1c28001e0082c400d020305800303131901c1c204010034007601955030f0a04a9074000001040d072888045c0440b11200308200c1228005a801402030b68100c036061002d014241c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 859397517 1250 859396267 859396271
    0x303070605100305160801060b04030f0b060103020c0307060209040e060105030a030e1807030506040b030613110f040903050706050f1302040c030b0603130b16170411040f09060e0c0603150a0f09 85
    0x20403c6c100d1821201542c1c08014020b03800c01040000804400300c0703490071504401000059541c110060f000391180344c80342c4195010010b43d03442009a9640039108060007034604220903060400340680da004e081c020301c1d616900561000c00004e100d121103c0e48181d020f046112602066002c170840b452060b40c02d180401e4503801046240c0c24036114088011a0440c010071442c2000c580344030b490b16041c0b0000d400703580d17013601c3d0403020740b15031420300d520b8400034000b0800d500c0a030600a283d500400002c450407420040030902c0303010f00386031381c41c01550103a502441c1e029440d0f08100080103078030408000d15440d000812202d9444002552084079071910000d05180c543c0350100c1c0445000300b40000445952110030003440e07002ca2810313028040d15048088988070790502c9000120100251680b00341000c0c1b60070b1050a0319045895458072901e01440340842c001ca41c00d0b252501c42880039001030701400020b00417a207059070f00000003009822100c000f612810f0008401145401c0401000d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 859398767 1250 859397517 859397519
    0x6051f02190b06010809070e22050d171008120a0e0a080601180e030d020f130605070614040312020d090203250b030c0a0c06110c0703051b030307060510030516 70
    0x150b0084402c507807086d8101c025004c00d81c1800c01050411a0140031000200580384140000c000c04c1c0110b014000c1d000b0040307887d08004141c0040100c111413951660440f06070000c83c00d01d0007803c0300c65080e9080c0c0310240c50b00d0400104290401d401c4403c0a400700400103d00320180d03125011002c000d0310710f440103040d107581842c4101504c0e61081ca00c04001e18580241c503505800040241c0b0014845503502680d41c0c1c0440c0100781d00c0c0c1c0202c80c0101c00f0344441030800030312031350014001c18860b44582c609203c803852005040c91404c1c02180d02a003c0b44845640b4850007080d80d00078042800700e00c90025540f0019001700303140040b40301100218202116080f01c0e45200e600c0c8440044c40b02e04041072540c603000d0910482406401221018003000d038a4503010000c058014155940101a241d500d600d00003c0c0159100c0f06444140d50700e0007002d24004000c2da0301c04108601c03040107001540b0702003c6581e240300a20700142010200e800b1481c000c40001d800f84502d410714640d040c0d00614803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 859400017 1250 859398767 859398769
    0x1009140106050d0c14220c111b0f06040f0602031306080f15130c110c0301180303050c0904020705011e0c0c02130e0a080712021903030e0a0203031b1006051f02190b06 73
    0x5030300b41107071110359010004503909027081c0704880d10781801c01e450a030b041316030410210f0380c00e000b20f41001c400760300a4074002c01d016500002601800c030200003610452079070b0303c2c800d0302c025200780e40c004060340300a00011004518610210140d00001c0c1c68010959072201081c1c085540030318a9000060b203101e424000f10714108444072031800e04600030010140ca0a50030542c0104084008042c0340d03d40d00000c400c1c10306d43c0c090783e40c01d000290080d5603400183c9400c5008007429880c4540a00401c02d06c0240b40341e0300d10980c3e940b880c0ea6140c0f5650710b0065001c02444800e0043c440390072507241c03c00d0100b4401e082c4a071940280c86002043d40b21031041c90031030702e07003260700300d045085500c04503a0103002c11401172401c1143c0e8041c100003038040c0002c2d0200e42428404c0783d000e50580300004200d00d0001e9034040803c0c19238001d2003520b1889041000200c283c40251203690761056026046d00118080c6d00038180501d01103004030350060b100707105000002c040e2044103a0304002018104801 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 859401267 1250 859400017 859400027
    0x1012060506040518130b0403050405010215091002160c061808010b06070807051501171b1509060d1802011d01170601021009140106050d0c14220c 64
    0x90201162024102803d01c000b040e400c03c058200040200d0141002c560039003c3c588503545090780040700803190781b8290602400c81d41c000d224250040c0302d02c1811202940070704421502820000c400740c1030074500304c91860003a4100d940c004504940313103080d04002410307600000c0c00420998030788400c24074405074843c1040314076030f20442446e41000c100852035507800d4115012130758082d54085d01c405040c100a4540030b2108012a0000903590011518546001c6500001d45651003140c030028890b13036801c152840c146030600e800080010340c0302c5090070458041c01c0111409400c4a05103154460745009991700e1151807008000c640e800340d000e55a004184003d691020240045440c00c802c1c0020541a001c0d409035070700220104c08294280e20900000326038070302c802c2d07040c0b00400c40341c10328079a100003007400b20320307150310300031303000905040c1260704e400311582000059540d1840c1240c41d000789464404001d07804202e408045400040c11038201110120440c1d002550340c1c17900401400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 859402517 1250 859401267 859401269
    0x603061815190f0302150f0304060e010f09051921050d1404021804060612150e0706092306070809090709080c1201230f070c0c1e0302101206 62
    0x100d40324103030010f108100d00d542c2614212030b41611710459518000346030401c1802820640001544000180302c1408825002902c3c111001c03c000c008400800504004a90a6101c000d0a60300312041c483c20004802110b0440359028a003081c080700404400b80c0b84580005c02c00c20b000c00d8000c211010344010314402d081c186050b001c1101000d0078190000f8030102000c0c03070030341d007000c0c4c605002401300605030700400c00621901001c07040025480c46c201030804043e540c5801203030f1800e030704020b840e82c0026007941210300545822802c00d00344008004a40c00d49085000c034402d45d0304812441d070700d500c0020f104e6140103124554403184540200b004c11800039000c074040006266040c0420070010950340c51200b0b044030825001c001840409000d400220030254110a0071400b410380b00d9484e041d52441001c4c050805807143d41c500d10242d400c101c5501c00540b20750b85c404803d114201100e074014440c0d11000c00084901c83e52031b80040c2d0010b00e4600b42400040023500c40c2e40745c00c0110b000f044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 859403767 1250 859402517 859402549
    0x10b0a03240905060103052e0b040b10270b3703020a0f0201060303090909110910051002010207050a0215091e01020d02191e120f1205070207050603061815 68
    0x2041c1c4030320708c840c1c02c1c44840d00240c42d0f41d107103030307501c900042d5a6a140d0140968403800307421f000121110300d0016000700c14100100c101980395060603c1251400400c030016a030407107070414285803541d0050214a01c546c080b06a062241c002d40100c18500400e45002c50181c075540075a4946002e47d005201c418200089429a0306049081c8000307900004e07210242c8181400c0001c500c10740b4100000d55418840e08070b500641c07902c0510101c140610406026600142c80001c0c08a4803400c00701e080b88161707440900141c11245a400040c13900030b801d500310890081c102130401c0311110000309000e4954282840001c01081c82e90070359601030040941c3e0031000d001070000e10850000c559a00d00c06401c3c010488202c0e030801d0b8000301d40850040142d0341e04102e6041c0c6824504902a0541e110a407202010070b0314011701806020b43d60003000d101c4c050590190105510304421b00125800140c0082d07406403902d03040f008a0b408080340e0300c1c801c004000444401c104441c0c02e1111b2100041302003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 859405017 1250 859403767 859403803
    0x12c04241427120a0e06030a0c02010501051c06090c05041d06061c0602090d0c080f01050a020408030a0c021c06090c0501050a1704060b0d0b0402010305010503010b0a0324090506010305 81
    0x40410b00c4400324180c0050152207040550728924407004554021220141039030010002c818041e00000c0c590100d414000f01c0d03002045217980318402c01c090006e41900000c001c02206e88454002034094000f644200d00c9a60f41d12002ca46803c000340580b0301710910003075000c181181480001c40100b00854000c001981e00385480212400340c002c0304411628007070720882d00080c640b007058030f810f107001e0307003441d001100c06030b100d030b150f501403a15001c4400c1421220740c240000f0640710003c80c07084604581150008524001c10281d06480102c820301c1c0584c0d001c600c020700c40100011051904103001e1250f00b001031120360038501102030100c00d40150741044011300c0303000c1070150843c0c5004d032004141c2440f03556070368a52500c9409080740c0e6907070a4104109120f00401c000e008a4807074000d80c03007601c0501a580e00c82d0141401c0300c4102c0815507010310100010800f0070b102c0c86031600c01144030211550f242510800c10000c0d2900c030041211250301a1004000380f18060042000242c010501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 859406267 1250 859405017 859405081
    0x90c0305270c0103150f080307050c0f01050a03050709032001110105060901062001020a11100b1f0c0501020f03040302100c0e10030e0f06012c042414 66
    0x1c0c25660b400404900c0d8113141c1e072145008144400034034035500a1459110007100640c0301c4031065100d802c00c550483d03d0b8821f6501d030010900d404c030103003850404180e65207401c0001410b8210060f0201034403110500c116500040081448100d5441007640c103541007244100890000402d000702e083d400303a8840c0d01d0402441200e0fa60310b48142c2c1100c50520702100382c0243c9070108030080c50310b82c200143d0b9602c0001c496003220b401c80c0f03040c000d0401c900103a80a8540c2e070350200055031030226109510130300c15540c04031200c5041482c43d110120600e44444911200d55176035089a01c910356281c0d625801108000c02c166040007400c0a00c8400c000902ca00c07034030100d0103094825000074682c4125803005074400b050f8401c0d4040108030740381038103c075034001c40c0001c5903445010038011408100168811070342806400f1310040040d100505100f001c1d90780b0350f211225000e00081044c1a01c0700400c9103c04003c40d2030040302d00184000010070340c542000c0e41b02928208282c049011a411041c02c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 859407517 1250 859406267 859406341
    0x908041d010b18210c01030e0a0b010603050c0717040801050606120703050402060904020d09020109052b050a0210030f05060907020604030804050c120f010624030e010204090c0305 79
    0x1060f80c4080055050b0030040760b6503400000c206506004880220340703d050f144944d544c500144150703d9801c02e0300c0400407040d0f41b001c001d032103450030580034011845803c01004410303c03a49c03100341c0c0020020000360924108c0d42e03a102c00b9909040c0c400b904000046002c2c0500d58080c0f1803241c0088040716441c2c60070b98040640540381e1401001c403030904d5500c42c00202951030365412070343c2c00c2c08020300866482c3e01d01080301d001000074202c168002803070120045040d0a00c40d061824490340d40003021212a0382d14403a00c482205942c0c100c8050262200d004011385030301c81100980b00c06903c000c143c4200b010f40f1001100e038010403191166110030300340254681c0100e8420740058162605895a070b5540c2401e920b0101103c00a5400101c1c1460003c900b44004ca08914048010402800641e03682e541e90405074048980300850604040348500c801c0d8025803000c2402c1001c4c0c40054245036035401c002d41159036a508407004245c4410420a11110070940d0301c10017941e1025803603210101103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 859408767 1250 859407517 859407539
    0x3160c050907231b1b06090109090908040801050115120c0503040f0f150c12090b0c1c050c0c0f01050f1b04030213091a06030c01051c0908041d01 64
    0x300c0784114010003580000a5002d0f94084409500d5030540000d101003640c2480f5607038404250310300000f900001d00c2502d4602c0c041044a804003c141c0d229225641890907480c010f11226030200c071803100820001800c1a030078040c20740200070000c2a50520303a07000e18040c1450101c610311140c030502e0160342c40000741d0402c0680e9041504140329400c48501c503d0181a2882c0340c510207400e4001802107900e0186540c0c0044019101c142c3d0380400300510b0050080640746001401440c01002d440001c607991604005031075215102a917110348414545400c0381200c50070740704101d44070341c0020184a091002c00c030a15008041f0402082a881d011090484a240103441c40f00341c080003540c40c00c20340e11410b0950f40556001484c40020480303c041c610009d101c0311008035080b440c1d49c2031000003016a0032400e13103c0c00d00600030f8100950b20740011031340340d480410381e148102460044010140c0e00e5106000a491090080f41d81d114108440410034241940d440d010f1880b5040050100c1c05040d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 859410017 1250 859408767 859408787
    0x1140903040302100f1b05012c03030f06011e020601050901050d0302060a051b0c160b0c03090603270c03120a09051c0807061a0f03060f040c050303160c050907 70
    0x162074107130300e007101817942203450b001510b44884130707109200084818040190700c420303000700003240d03032005242d44001d40c12420079180030038040c107030010700c00500b02c82d82807442e559100e0414500843c400c20b410070b0910942c0115590384005134081c00051000c5d01300648100d001d40001c40d1058410b801554001b50b541d82e0040208410341c0d1500d001c00d1818004001600128056804450300d4099000e501c071754503561a0005500e008030305d41c0c00100742000200b03c9214280840c051417920710703054140640381e40050100308198950600e4103640e001c440100c1c0003602906009445240f0241040500c4c1440102c40f02003002070405c4081c11154000c07818408032181511159150340480e05810451426014044e10b00d000000c2c080b010441030b5848055920340c54904401c07500821024020000c3d4403505ca1fa4065100d00c0114800880708144103610030b104594412507541c565000ca41144c000c401035084158000c1c000004101d100000c0c24041c20040d030707032170115140c00c0c0310040c03101d070380 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 859411267 1250 859410017 859410049
    0x403030b0603190c051914191805192d080c09070f0c11180f09010609060b0403020f0d05030423031b01110f01151401030b0f13021b01140903040302 65
    0x10002894640c0c1c7c0307031181540d0340d800d4460200514155201d0010b007401c0c464100d225040040510003166030300c0c001d0708114041e13032208903100d000c50501024980921100c211604140e101200071244002c910406902414481c40501411090101480b800500c050300c19024091321765141d0301b07201e500c881d40c610f21a40140c40780c070207160034030301140d04011480c0824174a0201801040a420240165603009824410082102503581c1c1058800c071084c5004508900318100010009898105040e4026483c0148006040d01f503d40e102da141d58007660040c0c034540b51072520004000d8284145d4450800d003a0301405c02444540b40743c000d0114403407215410b011498030001d006250803c024080204000c0003040200f21a603840840303038038248141d020001f07420007490000d521a0107014050030001e8611400e9404072000c004102080124031035803294213001291a0350640103006100040600c00000c0350124102c60f84103040c0300902030205a4400c000800041e00c23944100c1ca00740e04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 859412517 1250 859411267 859411277
    0x3010b12030f2203050f0601083c0a0b07110109120c03020a05010c0503190c09181e060509130f08030414030316020d0e180403030b0603190c0519 64
    0xf42c3c0a228001c5a20b9241e40c04800c0e80c104102108102000402c0305944035914125044c1d0380e40e580a25964082e601c0620015060f00140484400d00c000c070183c035801c80c40c410346000000514130780c1c2d2511400c21421f842d004404401d100000e030304030040240c0045c4440081c881c0c030006071100368002d000200c4420030003d42048141c10305109012020080390301200920000c3c18901e0002c080760003c1c1c4c0d8896070007509a140f01030061841c41503030390108040d290440c9103490412540d11011880d201c0161240d11145441c1e00881c1c0c07480b03054a40c0c0d050650002c1c0c128240010b001041d1030041840e03154454450003c804a030300040c1e1311000c5648004460b5aa6031545041e0f60003d0300d41e80340c0c1420344004030502400000d0114480b44d40d02c1d40ba0300b1030f0203100c0c0c0b0000c112050069244810b80103409a81d804000c0d00c00d0101c010703801802030401040400800e070100b440b0350b0080700d4564002ca00d41c82480e0f82c141f0a4080d0521400c002d290088c10560780e00a0b151100b140c8000d283c003401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 859413767 1250 859412517 859412527
    0x1060b091e06120403031a030a0b07140f04030c0503010605130504380f01061407060b150c07060c030818070b0c0a0525180b0a120203010b12030f 64
    0x1007148140c03007180d510040c1c40c0316240d581e040c8034058120420b40701100404c0c01d05c00c0500c80758160311383c1c00304910780041c000c040b004000d0b1100b802041014003240e0801c16284441c428410b06140200f011424640050790358a242d821309074004440e40d0040342c42641001010400366a40c2c825500c0440c91031100000d071611545000b241e80507041c8080c0380e906c80140d2080c40c5510403a02065041c004102e201031180d5a106504401c50a09000e81c2020519100c0031030703100e048000140521603c00d000000d81001080f000131403441e04c00c001d4003d090000214a04103203428414080104000c0c1029010003005607406030815400402c2405000307003595103221031705000c011172001410f040480556524554032642e23140d045007101542c20307109044840840880c11100f0441a08444002e412080d060807e06421100c07024141c0e40034030789900442d0307125036070407004500400002440800c0c900c1c0d00e00c10b040c00d5581815a40e4480c0c070484080030610f800c0803040350b56801005142540d52 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 859415017 1250 859413767 859413799
    0x2161a0c0a021003140a1103130f0209041412041527060306080118170912030307083c13140709050603060709030b10080a030807030e01060b09 63
    0x201c0da1503076029510207040a0301070708558040e80f10392003481407501c1c0340c0e21075500c0a5941080d47c0391034071800098042000001c04480d600384046181328800c1c001d0340f82c0300140c3e4001038842c00041d80c06441c4840d02126040d8405010000465541b05404825007003900d000c1740118502c02010074242440b900504445203070a100740c00c218184190f80300410303a0307a142d01c0000c00030300d881c1c0a221815880d00d00194465414800d4540030036030320010a0b1540c0312081c07091103c0c0d42040c000e80b50800c58071811940c04030f0090014510a144c00d030b0300c0c24094904150007140c80c50b14901c0c101c0f07150003100c1001300032003000002695148108600b10000e80c0b104004203011b0386e5031070300141c0595908040746051042c003190941c111408140b0601960302c9000406407189000d89015007c50a403400800c0040c51440d1120b900040068010715003e07a548061418000c0d80201103001903045800c228010340c02d481607200c1d03409888000c1100505001a82c400d07880f0304030009105070011104e0141c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 859416267 1250 859415017 859415023
    0x432060103120918060f0605040302060301050424120b1005090406091104020408070510020127060b040f0e0706050f041a090d1a0106031a091509010f050102161a0c 72
    0xb001202807000180302c203004ea481c024480c0703001b40340c040c0d1380345d50000031140e00c583c050310242d81d002004185140d00c1c10301000001d00441c0601260116155861420300300c807005000014148580700e0240c082084c03800074504100281200600c000d841c0c6c042c0329584548841e030b0f03801644514001900c031000e0822070641d10703505400e95840b50002030b012604180100300c0f1411038506031000c48410340098001da00745e03400800503000342c0d6111480c510b505c06c8007000102c01e1a004520010b9809401400700d0295000b601d50548465110b01c0c00d4041d101d03007001900010503403403902c181007074a140112421071040388560039401d40c4000004c0310b1001e410048511900005182c410800441d03e400701b40341802c0044200c90200c2c1e4000020744034081d000d00c8960075031903c0b070343d100303c981c203010410fa180d00035100da0303d0000c10242091240c1c5811000c2406891180d12100030070345010002490300b80b603500202040410b041040000c1d2114048050b0034407940e620081c1c440c8030400003149 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 859417517 1250 859416267 859416269
    0xf010b0c1608070501021005060d0206072603180a0203062d07110607021216080d1d120705030403030e01050c0607080f090309010e01121404320601031209 68
    0x908041c000604401c00140201c2290403e070252400c0b10440c6d10b004084481c00c59000e07400014021807a001803829000812107107100f41844801e881c2c40d01c002c0100350780700c0c0c5502002c40400105204020700240ca46052100300321300200310440b01c55022030780b611000780c2800c2d418412600604d4441c1c81c0400081c40c210407034140d0484030b00e010340d070090001881e0b081c45e00142c0034100106000034408038000003400750340400a854a108000c501e00b20140d680c0007078880560502ca001000c0b80540102080400301c044c2c07180581c1a0442282d0a0911b1420100c03007040e02041680d0010341d003c03003590101d0b5010b04100d01c0300c01840c001070390039105084c140d0031207014134403c0001b80c0c0d4202290038001e8508410042c410358480010b1640c0740b003901e41c0c80b13000c07540741721156080790310a2941150241c220a40802c060f440302c0500d002c6070b142602c00311414031300b440c40003524007210034003400f038031083c2044c3c941c1c801c450380300c03043c3c6401d0180030140009042d503200f04203182c003440c4c2100c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 859418767 1250 859417517 859417543
    0x20130504050a1e0b130b100f031502220f21021009081603030816021e071503020301031106090d0f0f08030f0712060b041701111c060b030f010b0c 64
    0xe035041c1781009003500b244c050200c0881d8580119404200d00c12690a0340300166020341e0782070040241140c48a034030314034040c419580300e107408000c403070804000c603a101ca031a0345175901411015424800303c002c0008650f000300994441d2650303034400c0350030002914005180c0641e401004a4070418044584080d2a000380007140304200540d180d00a0140380b4504481c001d40e10715050380c6405c9200d58001c207024a41900503444604c07400d03040c052170040030100300c800c030045860456640f4510885c0502d040c440703901096001c4010402d1100242041010f8070080758400c1c038054100f000200002c40c2c0e9030780508071103100b800c803508019a1610040740190003090f07290303da182551a20780d44e544120380c04c800107410351114582d108041d000382002d50396103a001034242418038034020391580581d00c10041d9903485015031041100c40f8030090040d0315600c0c407450188001440420192101c81d0301044103203008104010200a818280701c0c155038140d00e034a031b603d2540714816031070961800001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 859420017 1250 859418767 859418783
    0x39131a0f251a0702190204020306120d0903030215010602030a08090a0f0f060f0c02062805010e012903060d0f0b070f0e060702030d0e03030720130504050a1e 69
    0x9007050022081100100320b1489070038501964610b0b00c101e072a8101c0098441c8925180e03182d0b80014507194004c0e5500010185c2150307081c042d031511031482c3c01c0c134820086020580219013801403680c1032040328521100c4508820855140080003541c2c0e01c15030410314200020303880070503802d03c004d0224082081d003022401d0710b8120181001c00c00000071501c00c46015240070800817855a05018079805400340c0d0300030741110303618550141d10a80811031812100d040500070700012407010310429002c2c0528107512001e540c180007031582000800d04014070901c1d914a0720344400c42c08a0704483d404401940c000d1000311440c0752040100d40c40b0603004001600a108001c1401e5208c0600d4490b9582560b8118040020f10705210051040600c003a4140e0030044c445150342d80681c00b4040e5444015049030b20b440706a84a5041e0b228124910701480c0c1c6006c40e031048146001c3c4002075201d11144802c0200d800d003941d4495036031302c41800051155510303111040d22160912441101140c1001075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 859421267 1250 859420017 859420087
    0xd081807060e04180b0c1e0406050d060602061009021b12030106030b01050f07030315090903080603060c0408120918010e010303020715020d0807110102220e0f39131a0f 74
    0x2002d80ad03908083e0047c0c2e0b41900c1c1110000d40381c3c0c40011518001c1ca0b440030720034406401d00d5810000317036000c4107040828802d10000c4914502d008c012590103002411195601c1354100b0000805564403001490f041200500540b0320118140048403582c40c1e2500b800941400c000503012070158440d13100803946443d02c0350b50703018507800c00c80d501d1103040120309403038059860f40d140c039080340503e00440340a1b5200380407010001c4050b600a169100b4000c0c8023107015805031500902c0c59100b40c00c001c6588981d000104109a0104040f10181036140482d03141101c244000039550154410500c082058000103d0842805110755001000c0c02400075035461900c03c603540c03072406a455034404842081c010000d100c92074003603003900030074075400c02c0d0b0182e803100450541c2c941c52080c4041d0a500324080b0207441720302c107102096108004070b00059107400e0708010740c003c00d00d1654082c03840d113035800c4a403010100700c80e800c50b155100ba800c021a1280441c0340340c0c0603004141d8880c0b05034480b0741c8403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 859422517 1250 859421267 859421279
    0xa020904050115050301061401110102071407060806220c17090d0206090c06041e0b04090c1106010510052d0c070b09030d081807060e04180b0c1e04 65
    0x30b1080d40f00071544103000c065607201894201c0c1e22030b12034510b01d031040b0004060ba56104150024203022040009820505a502e0b01518007140f42c2c0d4081c40e5901440c41045065081442258861000c8400ba01010340a55503110b21410340070b16500d10326640e648400c40319014030280c514801036042c03158100d1a080800580d2011540c640380c0140c0328000028081150028000110800280038581450b1401350085003403c40d55510000816000202003850450900600300a04c003046010070140e4000034003500c02d00783c1340030080d580e4114200501603074a0f1140320b00303107030140d9241c00e96585002c00ca0802a84a6a000c0c806820740c03010100082000054045d003032441c05441a00c5980f542e551a06056200e44c0d01c4041c1c050700096001802c450252822903841039030035900d034044071081000710b81402000c0c0c10150100f19942801001801d21384100104e01d46804034000214000f929640746003000140a00228040001d80c00311106003541d2640c151046800303625103864540d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 859423767 1250 859422517 859422521
    0xf040f020d0534031a250c1a040c03230102130302010f02030703090e0a0b0907090303090807120b060420070b1b030610020c2d010302030106051b0a0209040501 70
    0x10740b00c03200c501070004011060006401001c41782d0046003000c1403203c0761511142208010008509021103c1c044500c10441c08401c100d4079a0b65610401c901e05203203020300000e908001c48000400d84201000005041c0c5a10f00c41a06e80200e549100c4011902100686030385000151402e075002081c1003102c0050222181e041e28400d07210382c0d41c18100303980c0403a0f40307019100e005000101841c0d0304211782c40442030303d5900280b001d50082070072910400031403140442a41c18038001080c1c500b0801c140360744190074901030b2102c032024014091400c101d0b282d80c40b4118070054001d00e515800f060040c1d031140e2199080d540c01007803840d44622241400c81e21900200016220301c4c072050001180c1e17001700e03145d56035040942051541140c0700e000500801f003a004c1c1000d001e41c455800c07203000b00da607280101c51405018940542d605a42c403203120b031286404074540b505140c0144014024141c000d41614041204050760804520440714150b10308004801c010350864105007d00c41445419 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 859425017 1250 859423767 859423813
    0xc0d060b1507020a0803090904060b01050d0603080c160b090105091207080d1d011d0a210311030403051e0703060515100e100c050f010501140a0e0f040f020d05 70
    0x700c441302105580d90404a8803840b50410007a03008400d600050000f0f0401e13070100369444010316025040c02c0312010640b0843d00c4c260401d60f1b0b02c0c04042203a180084040101500ea80180a6401a241d1804000c40080e000d031448081c10701030301180d40c0c11141c032403040186440b0580700441d40029654505240c4601d000d20a40000400c00d1900c1085620007003082040400d069440c4900e025400c19032545071240d141c1e206500c2082c41c400080c00c80d840207501a80c0e2305036031008113150001840c01420020729034407450303001c0e0014402040851000300d0310440d1005044461040c80c8009054241040301c5034100410051501003030210f1848000c01180128000385d400c0303901007804031026210034910307484190b800004849121100c1344116a041c80441c416021981d030980001c1d075036404e40300260801f0b44840c4001400c0d030542d1809540d101c006100d0b00c180c1e07110500f040d200501e8081c200070000340030300240304c600204546620945403925900134082e43e00007944081050b00c1120b00d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 859426267 1250 859425017 859425019
    0x20a0305071205090604030e0103020c15090c0915010c0c081009033b010e1206100b0309060a150905040b060a060207060e0409060b100503011d04050c0d060b150702 72
    0x8942d6448500076451081500030b00c0d296000b004542d5840e1360403a90203000074030380380c1003680a008050751180c7c20489200701e420f0550b49054913140c00d11116140001880c65a84900640300c1840b501c080071010782d0050120a00c1c000c1107120550906034860392080c1e120361014030400c0c0c1034090540c0503500c0b008555220390345100e06605a4807502903088400c07803000f0003c1d480f20340441e00f0481c4007182103620084c181007403c03011001000003020b840410302440d80b5070b003200040005003061002e0384401f40601d000c00c241141807504510380e881c10020300b0241c01960381c4040b80b0300d0340114840f1070020850080144150314041c94011058042600d040780a00e5480c400800c0c420700120b4614155540d65031140d0b00d000c4d00c0340c200400b424140700d00365607c0e5581d0468203803548130a03e03510580c140da5100c241d03032940f4002103c0141441c0c0c00451141c5107258080c40000350b40031071201c042c59000c44450400011506101000303003800c8080303590040c20340c038000003000c200201500c46580 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 859427517 1250 859426267 859426277
    0x30a020306010807180e06241503010509100f120c031401091716150e0607021b150a080907170703020f030102031b0c071802070b070f20030d020a030507 67
    0x90804040e0058801c121028001a002200041c85190303c0e00d4074240c07480b1a034001c00d848445223001082c10f40c1c81c484508a5100c03000001404070342003003443c0300e80203800d01410420181c90540b802d40e600d000c2c0d0142c1604000701301d441034140100c1e03005c00805550070041585003c0d081c42101ca000702810030044540c4004a580318129900400949820750588203120300d0404590b529401086c04444801036940e40c0e07110380c001c001d101005218810740194000300308400b2600609610b0065000820303104101d80039000341030444032001c1e54090001414010640e884007600241031208c0d079080a40440c2a1151002d0030040004990b000c50f80280d43c4030007041c0e401c0c0c0505d420b0784400c69442004d61444d00c04690f05903c0000100003031b0800708180c40003c1d03100c10820005400090740b40040d40e40200b081410311801c128259003181c0c45041400000c00035120140081c848110141c1c9106009000b001054609200b03c0b100018000340440da19007498001400410041d2a03440010f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 859428767 1250 859427517 859427549
    0x40e0405030f16140f07050409020103180303020a0908010b0a0302040903261e09060103080a05120a0b12010c0f08361624141204030210140a0506030a020306010807 72
    0x9030000c1030080b4454035000c046c02155007800180300282041000481c105951208242004168604494207862196030003581c3c400403031000030708403040c40d00005101d925210300c0c070f8a03d42d2400445011203a054801240700159410180c1d440784011003900300504aa071000c00c42c3c40004d001c0305109203d5100400031540456081103548481102c0a440b2548203000600c042500500036104010952802620b0101e003241d1020b0604800d0b1802140d00d92561046d01140c58260500c01c25580e502008002d2584800c4006000086c2c20b0481410f02220740701092030b100c181601d268a000854120003102e041d1918683c000d03080220050f011030086500e1001104407018420007220348074401d4844105d10900759200e6115416103010a018901c1d040759101c04414002c2e050b100316108840c422440e05060107130404001040d02c442c044c1c5084010031510700c01e45406034028040c611300060a94a4001003890304614100c0603506201f24000090310100000e180003d6442c0040541802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 859430017 1250 859428767 859428803
    0x9050303030f1609050109170a080c030a020715021e0c030d170106080115050a0207091a090a0c0c081608120a0b09040b04260d0b09010b03010b040e0405030f16 70
    0x1000c05d014090000e29910004c00030441d035944120140410402a10320b00105551000302c40c3c2d100c11a44501c40c0c00c04203951400507010f1245c138000b4400c132000d442e1240048032009480e207003210580c40310b840320540342310154002000700348468903001e421580c02d201c4402005d0300c00002c80c0c590351403902c2244008512544940320385e5040759102c1307585101c0141e01c0442600d4540010a12604500c100140090003242500071714501c08071304840c00300312802c1e10090140d042c0c402045001c01a04280900d12225442898103c0d440d130403840362501c6407040311150010101e40d080240202c5401300b110803080d40c0306090b80f4020800d52204126102c200000c0c0704c5120011103000e40143c280b54002408601030070a000384028250360082c0648015a100b02183e400216030400c4803070343c80320085000d003031031701c04240500300c03066080b42158501a42104184601c3c0500e01d000c0180402041c01c2250403c02d94400d20800515591190310400410007190940d00054541c8002481c1001d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 859431267 1250 859430017 859430027
    0xe0907020f01020c0330040f06090b0c120a05150105090307030203010606081e01050102030f09240c011d030712200105100e2502122d1602040504020109050303030f16 73
    0x10903846c10215905a4550701d4580c542c01e5101003d80e81e6941380c51a090000d000e064040b8403a042501c0959194182040c01e1808680300801c140c2c611840c001c24030042c28050006108080341c01d191096a44811b500400e003032508035440250590700f00b04000c81e0458006500c00d100301202c100c41001d1706014841d14403000028854a809a0810404150300c248050000c1200c614050403181900074a803885110307175040c06c00250b100f0200410602031819082c0544203070141c2d0784c90706800c1c0314143c0c40030586900c50300e400200f6010143c02003200e034030702074040d030803204441c0349a4200c20403042403524064002222f41c8800350650400104000303100e1401d8074010380c0d8a61000101000046494007059801140902035101d1100d015a003242404000c103002c00c1d030a40d00100c00000c81b000103c0700a181811000065003d2040b1542d017070b2058042d502c40d5804a602041e2600c484c00140e42850702030b000300da014040042084049007102015130b0050001402480c403403c40c803141118 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 859432517 1250 859431267 859431337
    0xb030604080904150b07060b0102011b0219050c03030c10050a020a1209020a091a03070f230109050d0f0b1005150d0f0203041212020a0e0907020f01020c03 68
    0x2820082c0010310060402d0340c0b0080d002894038544090040e1690b4000420341c20001c3c00b2240c25484003030001d0103503428000c0c480c1403030021060f121154114180a9200c000c141d03007141240c502441038805000c01080414400c20024054a40d03880e05144441c2c1c0b200e450640205455007001f001c18190030b690b02c21030721100742c959912a00c40303130a8181d0b0005414410002d85e4004440c00011445203c5c0d44105013580800300c518480d0711b041002498100b01031503210403901c040841041100e09000005005000a08604ca9140000c1000161044c6c4c143e600f0003504891300030103ca00300840009513a60182c0109861a91555055030901d00940e9600030180c200d142c03200209031185100303001d8110705240620204140f01c20b1402c41c000c0fa0821070301503031101181110303a5103854100c0d40f20f100840c8000740552a0907658907002c3c00603880080c005005003c00800101c000f4800d210800c800300c0081c000303554420954008031b969411603d51a00d05c0c00818070510001ca41c4030107040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 859433767 1250 859432517 859432523
    0x70804060c0e0907030b030c13151401050901050c070f0b0703110c061b07033315120203101b02010609021e130308070b15030a020f221a03010b030604 66
    0x14a156882e054105d0280018080241d054450606800001d80d20b094040d00780744400100020001003687d41c0e40c240030b200ba0701c06440f00b5801044580030303980c0902210303260542800d1007960b604015049034a40407140e440340b8103020f4094008502d00a6407401043c07168003941d91010911005021152104100d0342c607070340d10040c200107c04450310044a807002d1548000185c88919aa80d00c0b0740d50b11100c5c1075990b181e0110f8241c3c88454031201c1101c3c007884a2140b91080015a02006002261800b10701480c0c85440a41c0310b03181c110356081100030b0810f09152014000c0348c2c04004d501c0c290b1001c54644001550a124020503010b040d8800d58181c0c100c01200c105040c281c8000301ca800e0351000e082211000800c1901202240031140101161881000a007034a443c044880003a20382007400118401d400151409025a64580c40c4403e200000c03501301003514400038601c80c1c070542c9111400241400c210191300c004184403081c2009001c141c00a01408200c80101a00e55500300e0f401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 859435017 1250 859433767 859433779
    0x6090601260a02041e03020319150908090616111002210903071e120818010e030708010e100e06130303060b040305031e0c0c0d1109070804060c0e 64
    0x2841491115081090b0090060b001c014509619600e40c0a40b103007555050310007900803030b40b00708118202040042541c08994080c0c91078001641e4440c2122180528207480c940c1c0c40e01004018084000100c0d040480001c100c0e5640d04405070045010b80c96004003520200307034054202e072550905040520110300b0070780c05000d00c03004c049100d01032100f04481502c10003500380f10072103103a1410070207803001d132000f00c106400e4010208904100d85196800004000414040e5103000640c0042911100c40501807441c000c50815001202c0a145440c86240c1c540f1504074006103509040d40614103071200381c02030b54072080c2201c0c00c030f40540b0400d595041c1154406000200c2c00014880e00031100c1d803292030f0104030160b40e40e003420340c16001074100b079800c1e41000940c0590704000c0c105107001182e40314404d50811000e90007940d00c0706441c07461b060088134070310046030410181402c40d844002c801000340445042071000180000001c44084034071318a00700b005808a40100c50011400000800c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 859436267 1250 859435017 859435067
    0x30f1f0509010e031b06010605070c05060d0b22051f031410020409020414030a02060f070204020c030a03061e0e040f2105030601031a09060108090a1a06090601 70
    0x402801094001c0000116558801200c03403407050a000a2108011154441c600b9840e5588180d0400300c040c0d000c01c2c18402d0400003140001c480d0b040e15001c0ba0000c4603d01d032070b1a01580c2140152019481842e400b220310880d1049003c0d182038042e181e00da090340c00b0401c9540e0030681c0158603039031180400841840b101c00b0000103403446840106020741d0021b49500711201c0303a0a00c1640c0054000025241e000b080a20000801e614840c070303880c00c118000c000020464002c00c0b070310f00c00c05800100780f400000d070007010364a40c1c2d01201d09804030310046998600790700c400200240058000d8600044602d00fa090075001c2d500c4c941001c0d43d400c0c1075066184d1700d599995660001e100303942158004100c80c0321030450a4003111498401c20a6102c0d941e0b20b01e0b103078000601721184641150110150460510441d803624007030f45034000d8003030800c04865151000410300d44000550002d203000f84018180311081c0500c482140100c01c280d030803240d02c0e141c1c0c5d0019150410300c03801c020042007050358 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 859437517 1250 859436267 859436323
    0xf030207110909031e1b0a170904090c03080910081005010c030e2805100909090305120705040f05040b030607030f020409090309051806011209020627030f 68
    0x11110340c01103165400c40f071174440901412111540c201000c402d40c0170f00030a420900c0960b403200040c050654202501c1d01c03c03d07a07910f00741101e01140005420802c0403a22450a0300d83ea2f0195040582003045505010350700d141c041d403150b01c03010095000781519a01404007500035000c02d4010316042801c4031403a424140111a4100f00840641c20030aa00903040c9170781d10350640c1c3c2440c8800b040100601c0b0a50085083c2003010241c1c03205000b0356000000c80795031a4080c4104003a40c1da00040400c000083c1c0c10f044645000724180051006c824006010f90250418000c104440c101c3d0001320406607207004001c1110350394640c06400d81c00410000d1008da01c41d134400c0e045407030720507401820a61250145800c5901da12000c40110b04500400e01051802c90000070b82c0a01e82c08440040b403525600080c8002d0b010440082902d844010507011941d465082d5103004070302d25502214400b4012808190210f100080360080c0150010070000303d02c003040340101c9920580c00c405160410318 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 859438767 1250 859437517 859437529
    0x6050d1e0f080901080916050909030d0e030c0f011802010315080f0708250b0705010906020307031d06100b13181b02070609180f0504050d0f03020711 66
    0xd21603448003980d0002440020090080503004a000c0c0ca8010b403560448000500f0303540c4094922502a0b101c11403c08124040c082034a050395429514510182c0398000c0161960007104030b020305090420400040c26000000a005411888000ca40c01521102c40039401c03586411443c0b044080d004403040c016502a400c1117540b95004000d454401e6a1102d019042101006c850074560700000c00800c00316030304004a4617202510302003e40d0f00501141e00c0c5400c001d8034030035495407480214140d02030203001e6007e01d00494100703106564902e461b4030018000e1600120184d42c1d001c07060007101c0020030009295206000c0000b00c990900c1c1002c441114503000305c0507441c00d8508402010544c55016807421400303031044030b804035001c500e04106920070b11503075504c03c08561180c0010452207070b0000142c003c6404810080c22a80c000400312000f0340030032010182403504003000c1c00100000003030700103044019541d446a1101213601e045040c3d200d0018094262152000410050701d002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 859440017 1250 859438767 859438793
    0xd09061a091006050301062a060507030b09060631060e0108010803031612060b070501020d0509190204090305091018080705090402060c0715180b0705100b010e0a0807150306050d 78
    0x12941250099040c114100f1400d60b15001c40309d0f01e444d14144043d0a03018021160010b40807500c0403202d1420380302003911800744005020400766030b081c4071680440303020000d1100b943c04003281e17500b1946900780501180340b409035460009010200004080c040842030724010004115003e900d585480000c4501d01800e00017600420b07940d2800084911400c4002c0403510321074000075885102c2c08072204100c1c0d90052007213060790401040c0c240c010300040b01070181e940c1e044900196006550030308031070500036400c0441e0410014800540c0254100c070388a8403200c09501c180507965214406941ca507041d81c811983c2000340700c07000c9030041c50110080c04600510000b02c44002e541c0b60340c0201c82100d4820000046904140d680d100034100d41d8500b40501042200546440400d44c4d4450395084480240c82405075601400d151581c03084421091205000384004586500c4185080c0c03191100c1c4130380c401041881d81c0d00b8010500902520b0100c4100800050b21040d164440322001505 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 859441267 1250 859440017 859440047
    0x1050924090a030501060503011107030207060302030403170112020f0105190e0334080307020604051201141e0f040c03021003020405090c071e0b0a020d09061a09100605030106 77
    0x40c0701445094840c000400c000b0b50151002040c150b1400060600711a81c0400c9844d0210b070400c0b42001207500024010200e4000d4540140e403a80c1d14202100d2402154051585c0d804660000050b40b101442e8202a207a000b1144100d0483e9946c0041d1010b109101ca106428010031030056070040c000c0710800d0081c00090191540e4160100660010040b40081401210006048100700e1500646090007810031000210314040040c2c0024140380070f00d100c1c05104502c11480310b40c0d04002900840484140a031200241d400d00d403e40001105130b80c258074442c3d26612001580185005181c1c901480d040411449403034119024010100001e48211060640070000060705403507519015114140c60044240c854040746084d40032201c16a0b4894071071240048000b01040d08620b9030354100302c40c03402c010b9407090301080310b20203801e1003080036144c01c0ca08020507028041803006261107500032180e244255079070066001d81e441c0745004a400242d4240300511109000e08110340d00884 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 859442517 1250 859441267 859441339
    0x12d0512010603050414120d180c0305061504060b120c070c081c1815091a21090303160905030a03021006090e0307020d0c030f08030411010509 63
    0x125900e040c9002000070707800000060baa034810070090040301c20882000030b0004029020b0030704d06d40d0211180f4002e4040c3d01c03901d50381d00c05545110300b45075911070001d654010305989009079281015034403020121201c081c421840340a0000a1803d0321880c001d882c0311010082c108026100040354a01d0f00801c18813046508000320f07400329000e0440000180601c2000f8103800e42e02150540d201c1001346954010f00c10030001d60111420000342c80303415200c01c0c006d24a080005480102ca1991056200e0302820b01e081d00e440c0d5041c0c084c540203105e20a103c44620700c00c02c030b410240615161701294081c40503007043c03020400001c0f0700c28a00d00900e010340b910505094882001a0a060740c40c0c0c4e04401607071043d00ca400480707000c1e0103a80001c0040d660100081081c00e18029100d00c60400003d00c5252007000d50342c10400301031078241c0a507400c031104c3c5060030590325024410354026a0103840102d960b5071100d007198441c0040b01c01c000c4010300350f041180c99010014500c207041010b03150a4034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 859443767 1250 859442517 859442527
    0x2090a09020406050603010b18010f0813020316080714010e1011100606030f29010c06060b04031406060f0a090c0c120f170610050a05090d140c012d05 66
    0x10381c5c2d43c006140a044007040e030654170b4401d030844040840081300f45034180f002c1c3c0f100c3d05000b82e40000a403540445541c02403148110b8610000e800c01160350009141d018002c1c0c4007240020740020302e00f00b6034007131502c60b0795000014001901ca00622198403035000108000d65a0024031810f0541b40761101141101d510311070801282040e10b4140d001800043d555440c049510300b00c0d40186148060280000c22043d0003d00c0c0b010290400740c050749050003e410300040410449038081c200904440e03001d40d0312a0384924050800741c404840961191048101151142c42c2c18242151300d054002c280c2c4100601d0828981c02400942000300f0130f00c1085100040803a051401c1002c500b602c554440811081095000d000c1010414000f09054120700800206480f603032540030300100141081a102c00031802c04071105d201d404c0d038198100c10003510f01e10070410240580c00d40f800404041c2e81c0304050140c011152a0003519a0010120a825020790951210f01d46601480101d00d80540b601d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 859445017 1250 859443767 859443769
    0x120c1608270415141311030405070f21060e060f090706020309150318030c011437061a0a0201200421240501050a0302090a0902040605 59
    0x9070020014120951110300114149900d081000000100c0c121010048201da1a00b410480c0215005001000c1090b116a20741540d0317942c40034000880041c0203020030111140218003640003540c00704c0c1c0f0352099110100b60740c05101d82a80075107070840c1c1a42e40244400c1030b0202c01c184107840690b0351582e50300740103240e00c0341408594803582c080c80c80c0300b140307080444040d45451100e90020045410503c10042240c0d0341908249100058014160f05d940380c2e5581018507000c20f0000010510000034000c07450801900710040d40b100e206007500382c965072040c410014020005196090715000f01a04444400d01c04250080da10030758030000d01c0d60744820b0600340144a100180c0744e00c02001c2030101411398240070301c04001280140940302540075429090b07040c0510b0094034445110085985201000b98075180d0000e42c00140b615510b048030003031305400e090b00c0c0e0a0100014205000401c6605280801c10200c0703074050070080302561144c04603c000d100f040348c200d9005807100400515 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 859446267 1250 859445017 859445033
    0x3012f030c040815011e0b160218070309060b0901050906040509430b071103010f0207060207051e0a060f0603050a051b180105040c11010204060e010212120c16 70
    0x1413080d20403a50b0501d50418640d08246141c490701356585482007002440b20310020000d0303400002405440070324442d070702d10000e441d140101d017010100078030b46420407022903456000701c0450b600036070041044944000034400c030340308240600c64114403290082421401c0c103030300c010f41c0329052200f610030b000c1d0000e407080e4400c600e590000140420600b041c4140726a441c07412010342c041c00b03403004415840c051101101c0d029024001c1d209444c0c2e0300042050fa18203402c1000b40181390b800c21980d81000e03190000c02504541410b9407240308110000c0d26070202100481c100c5040f034fd0003811004407035038410000d00704840f54180c0440e110440080040c3c3c0c20050b10a80911403406852501d50f52074a90000740807106006116070310a045620010340704061440c1980c1007568003050b00414100306682c441c03901a4103450649c4000303400950141e10406524465100b42c1c2500c900e0348200c03000034200d004e03216042c4034820012002c18401080907004054a400010401c1a41d0410f2b45031800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 859447517 1250 859446267 859446283
    0xb0406060806153f030903030a031d0f060a090c030b0a1d0a1707081309020a0f080402031c2106061419080604020c03040b070203012f030c0408 63
    0x2c0c180c05100030060500e841112048100320581040444c07540340d0010350007841510f051801c1181c00d0702c4411505400900c200c4100c0380c0050200c0b5a0f80d881043d00500030020309182145001110009030400704010502c08512901c4400a00040d01d448420100811842c041100d038103040c144000001490010502c0c4614860f0300001002d43c03100022504914219280c1c68050b0499552a00051a50b00b2541a40f5100031000c0e070b110482850310403d80d220b82d004e9020b03a0500d611000858100f03a80081450000b1a0348a10790902c0c428016688004140c0780254076800141c040381142804440c500b06e000c07920b10f4200c0c1c2c20040b500c82107038111540041108515200c0c84140a610b81110340703101c502c001028114a00701000d480c20321400c210a2200c130810000d00b02113074890341e4580580340190400740903030b030365076075900749000b42c07a0f001000072800b950802d03900b0410361040801c0008446007040000303841c00e01003d035100c015400240a0115000240008250401e04100c415 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 859448767 1250 859447517 859447531
    0x3040e0a0203101d0c130909060f1a090a0c05091c1209180e031b06063607021e060f010522020c030c031909080703030c0b0406060806 59
    0x590364103201c034042900002c550041ca20401c0d5140d203291036442110f00031517216011113900f0307032030311003d424600b024692a8030591215051031000c0d01403105c5c603809414103070130343c40d0104804210204070107440c40495000343e07401075540c00010070326102ca0b00203010540d50751500c2481c100780d8000140c1d6269a6000001000841c8400b0138100510080341410307015081c00d000402030314254800303026898111214808548490140c800703642c00700300b81c400000c0da048110b8400c4070307881800d0380d80d24801c659041c49180c45411551034414100d500040c03501c414180c9482178070a11506c8103141102806040442c8642480700009c400d41200c0f80701e0800c180c1028017550b042c41c2c40b40e81003689060304504d10460301417919404040709003980f14000070b500300d00980c40e0080443c0d040d06601417140c4191050000140c1b0000d41403440d001d440c18616a41c03580083c06468240107660f6100c14000100070078060203044010401845071a54001d00c0342d4404076140d512514410305002003035443c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 859450017 1250 859448767 859448771
    0x310030c0b18040e071502010e1c0e06030403230a080609060603010504200c0304080f010c14030a0207050a0b06010215130201050f2101090606051c0e03040e0a 70
    0x6108101491002900510018030080e05141c6400c0c021500000550b880e98451540c954440d030b0360080c18044080105003074400006004d0f141100603001c1c0c00e1821104495004840ba82c050304000c60504450700c60701544c1700c40301c2d80056030522005a2006d482a002e001c1400d0001d02100360405010607901800c00315a91030356500f801c00b03003503840d01400941c4544001420450180c4500d070560341151011140400d1000054100c9000900c001a0801405c2c60024421040200010040c022500e41030110769030044264100b40c225454058071000060303441c595180f480007080d0180da00b01c81101d40042c030b401134503a5103d251100a00080b10040200c030100800c40d80c041c84480c000a4038502007448034500300c0c4206540324001d07100241402408503c41c02c89041002c01e4170400000704000441d016800c20144540101c248208030701d45081020100e0703101d03c40e4041d50b40c408040401d00c0483c00e58040fa603005446100c0c20040c2d244414000001d418400e410003d004a0b8040c0c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 859451267 1250 859450017 859450019
    0x120e030a09090b0d1506030503030c120f0408030703020a050d1d160e310515010510020d0f020c06040e0118020301060c0b07030212041101030507112109060310 70
    0x10300001c00503403203050614a0010180003685509000b07941c113a90210710440c211800440602c014000b13600003512a110110812841424880091a071402d016103020055a180c1032280d2840e902110000c0c1629024004504101c1c001d4010300081c1844e8100703d8148000c031042182243e0b0041d0303040001105690120f80c0c1d085051004039001c43c40305000714082800c00d015041c1d14007014008416410001c9034210046401c40c0f283e400e0f07901040800e05801e0018145581da901e2030710040090354100701c00024a61400e4030190707001c40a00c0e0061300c1004401d58040e20b00140e6258030b2010350040340684801a17075000c00400c080d28240c03045031815410000b124424000b1780c107500034135610410050040f55000140800940e601244285c041d0380c51140813406801126103c840c0e81d01d448041c001004091801030540c98820f076400c00a40e600e055007191703138051800080065411540e6242c6e1201900b50f092000000742544c468940040500803800c2503104503004649000140700c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 859452517 1250 859451267 859451287
    0x303090605011e0b13091410080d0905010c0f060f1a0301020a020c0d030e0301181a070816032403020a0e040b0612010b0d120908060f0115120e03 64
    0x2141d180508080050a83c0b10b0f038840c05122801d43d5107000d41d01d40d008011404080c210400d6030007502406070810b0030302004804041402859109941880c0c800d480c0070004500040005114042694070343d84014a0601c1c05005640c5c00110007401d40c1e03040190181d88001ca0201e004450010100a4000980c0c04009150034454007110303201d24480d03401040200c401c2c542c00107841445901c02c07900107456100c1c62a00b03680d074441026045415500b0180504c41441c407443e1204401e0307000303100c0d0120400d9400504071000e44100c0300000884d26041c00304000415031600107a100105080018481c2c2a119002c405041c410020222080100f0828811030501d900c14000600e00094914800e0a140d03843c3c048400f40140031901840c483d000e0544900002d4000345443d140141c0100d980c040745007840c000f030070142e221550214402c5d0000003418100000c980b0b101e194022040400c5908125103e400006210301260420481c128a0750001899200740851007013a8001940d81d9403200c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 859453767 1250 859452517 859452521
    0xc1103100c02060a0b0102070e070305090f0d23090a03060c0201091a010503070f030506010e13150c030e07030308010306050901090b01060c02090c091f090f060923060a0c17030403030906 82
    0x380d174103045400c4043c081008455001c00725800c8841c03402c0215440e030320b04400e0742c6011a8070b01e0303404031417040c2440380c006907400030034542e26600b4031068580a425074084112944c41190341d1503400070310300710040003c2b8240b940000c2d0a11100e1002141041c040d441f4000322000003010b640e0f45030742110040000c0d1400300140d50052034400380d02040716240d030b02c0e029143c440511420b004929a68005038044070002c00311420b95034813640040c00b01004180120050000f034070500301203440c00d04160502040000c01008503a80b550b00c0c0e4005a08581d2000c1c054800039107070036035940d00d0304680400507001604d514007a20565980150390040b070300401c1000380c00a842030003180010003519187d034454801102040044035091400e0908503402252a01d100342d00c18901c810039040b000c280c00b80c0c00030701c440898801d246000103480034506e41c032582c4d00140c58182c2d40000204841122a40a40d01c2c2c3d444036401100a04203001c00b0114141345a4000c40d000c5001980c1e445113007041100c94 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 859455017 1250 859453767 859453781
    0x31e090a0305100f0513060c05040b0f18040b0f0f060403080703120b010306120f0f1407051302040b07032601030609030215060a061d040f020a110d0c1103100c02060a 73
    0x1500c811701140c10151503407080b18a054901030101c1c0d4540b09800507190240007150002d16003c0040e030303a15504c0300b404038029000544500b0740d58847c00201c50061405005200f46203500034103031140340300105c0c00c00c10200100d000e460b400500510000010950f00c1c0043d03c00c0d207000741c98070002c00c0000c08490049031210740400d03060601d0a0820f2201c89100d2180c2c0f84210781c400c06220341c0790750f2810803070100c92a500e0020030044824941d03c40e045004180001100c0d400d5075510900c040c440c40303010a034003840c0150140c0e50004d11a100c00710780b09000c07495040382901030324030104480d81e1680c3e540207400d80003a04c5240d11201c05504255040205814100c0110f501c552141020400a0010060303842040304001108135411071010160403070280c1810014800c0025004041566019400011694003c501e0080c460b552840d000719402c4900c07034055440084500150b41d940e100d801c104c1150310740511440700340c0c40034011240b042d544070090940080120b0b15040d16443c003a6046 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 859456267 1250 859455017 859455041
    0x708060a09050c1005070f110a1a1615060605091201020306100e011b14060c0307020c13020904050411040614090a3207030501050111031e090a030510 66
    0x7034268040c0c040ba201141c1a5040541103d15041d00c45812208940f2405000e001038074541d44140b448041100342480d5100d99001038406141069854820b031410001109205030110810840c000c200d130300c440704a88116118000d000803010584c40c95508a44035600107a0211740c0000b00000245040c0078482c40c1e007040c040c001c0d0324524040011842191184c0509024060355580b81003060307000c0c0c40d2065035040420714030f032526070183c00c0070307100845d00c4050031091380140b501007001c001aa6003240c1c441c14960300100340c0d0955800500c00c28600708220388020690034003482201e40d545001c0c49010f64002c1d50f2402170112a00108011500d03581e0240780c500c41114018401034403880c850f41d610480081001840c08036403c3c000f44001d01050340205802ca4401041d4804200c04500a0007501507540800150380c0700c200550711066a809031001d9a130060051407210031500352080c0e810602c1d0380c41c0328240344145020400c000a11b810460301d9070000d581100c082805886481d0040f04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 859457517 1250 859456267 859456271
    0x3170c0408060c0918060a0801091505063001110d0b031501052103040306020703080a060915033201020403030e06120c070507120602090108130503180d0609050708060a 74
    0x40d200043d05400000a01c0b1182d170310540002403155541e00d121500914070307034000380554a01071030000d0ba4003038011040306220345401c010441c41d080248848141a0400e00071004d05800f8629204100c00001c04a486940d200c025038494070014502400000401a101084808050b0100743c10111692500c8130391003941c00c01040595118051803c040c0d03924495011440d14000c00c180c150302c19900060415400001c140f4101540300c041c580c450f8101c070408015040d02e61010800780c645045d032005c0c42c44109030080c00401c648041441841c0074908000140400c00600603c42800c0c5030856411a5400f0404105068000c0804000e103e003c8603401d00c0c2c0300c21450420100b40300a011004410000f107507420400c403003048a800902407043e000d092020f00c500c0c118000e0b51000d00d0046c0010800c001050074016001c81e02c1a1040c0c0c001d001c1c50400e008a0126001c0d03940521b645c1c1c1d4000a000704046c049080e0344120480240a50068200c0c9810301d8405880c5c580041c00b221341c000c1c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 859458767 1250 859457517 859457527
    0x18060f070c0f0311010c0b070507020a0b0313021305070f051c0c021c0305131202071805010311091509060312040914010b0c1906330b0c060a0903170c0408060c 70
    0x11801250154408d030300741482e0b61124031a001044407a8a185c0004000701c0d0000144110004101080c2c940d10784221103810354014800c0d640d005440c42030343e900c400b1601c0c600d100384141d4011009840034194242ca4000036104e040d029406640c4c03070180090146e00701c13480100301ca116820209144412a007024011802d21a40401d1144041c02010f0001440c104041441782d00c04e00c0410002e02c000c210b4000300920080c0c600b0010a020321007210303c0c281c840342104440c10315281441c801e5950b20316200002004405112a500c1c00401041d494051062000c16010040010708042c00d240003000030345003201c1d0b40c40041000103810010f10607500740300302d61183c00e00189a281c0d10499040902020b07800b40341000103011182d00c1c07101c02080405103900c0340d4001c0342e003215981400c0010070043d190703151740c49409840760b400e4903040c68102800203400b075800384d04603005c801d02c45d00d08600d844a25644500c90540203840140800c100020200040442008000c0e0002e0844030070320300d06 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 859460017 1250 859458767 859458773
    0x609042307020c03060f0c0c120c0d080103030807120f09030206060901050108090d030207050705040e0102090328020f03280b06090c0d0f1b0e04060b18060f070c0f0311010c 76
    0x1d0700002e00d051020919400081c0166107851f041c2c4c5c02d01580c000c00c40e011540303c0405080c5641010f4010b154030301c903c004565801d84900b2203d812250142c0b0780721403588500b60102e0350717600e00b18102c5400300d440b0203a0a044060621803203c4181c06030780a0100c50910100300003000b00103900143c10010304c00c4c140407200d180820724103014041030a0051741c41c0350901c1c00508000050380300b5540300d4075083c025000c110042d00245400d40307007102500d5070240356807940c1910f400c44210390041400c50820250050500d80c0440e000002d009044070000000034a410128000c3e68041084154402c8a0182040036580c40c903508213030111400052460107a2040255000760203047d9203460b1500003030a054100d03503003d1206000001c140ca840d600c880c1c4070252500d26241c0900303000703518140002401c43c100358103a4800e911030040f1643d6990021003000510f8000c0c002c501d94a00c0204441000502c031944140c0040c0072802040000524604100d100350003c001d0726030601c0210341b201800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 859461267 1250 859460017 859460023
    0x150304080f03040c030c030b07030507020d12020a02030405190e0c0a0206040618020a090519060312180b040305060117161517040b181b040b0609042307020c03 70
    0x18041c1d07600c140079141da0740d605140a18001070351014040b40707055074011007030008901d403162041c490717520305000d15120341c00c04980e2030506650344400100e03030b0002880f00d103040d80c0050101e0006407048904240d11100080c950074000581500c003031020040401c40040c0c03414000740e011811803407041c1410a4114043e480c1c00c0018002003520340d807a001d29031050442c810000c00107030080d14219007292100e010f94002c2c001034415690005400301803442041403802604140c9600c51104007441051100a0340d600a440e4485604601140b4020641c0046100038200441c040ca004041361751404094000206020400c1c2009420503c0b2184c03240040b000d02d802201c0c42d190142d24840c00201c0100c0f40007118025407401c8030407141c00d100911904400882c06803124802a0107214040f200c8aa039806054044815140d104000c8040078501a4440380091001401d1030703140142440006044801814095144031380902d22290055003036201e090f03101e005400144a621060000295 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 859462517 1250 859461267 859461277
    0x106050a12020705060906100f05010e040c020309130c03110301062c03010c200607021507030b040c0206190e07050d0510050403090e0703020a0906111c090515030408 73
    0x80c40703100c00340ca142038881541100c507699046030a913413150901d04000d540b5201c0c2a00c54112603140c807807020910800b4002540110741d0143c40d80680e030300401d418000503244420b01003096000a0008807490303141e0488200710000000000034080f80700540190807a0b0000341442150101880144171498100700000480d00d119142d83c0d901d42036203403619854208182c8281d42550805076890041604014105803400081041000e4060310140d00d035543c0d1011100000168489101041c0c1400300c402d001da0404854a00412100c5644020a0648420180090060384144c04104204034245080e8010041900c0103000441040c0d90f020350741c2515010302071242802002550070803204000201900c082c0e101c091046c0d203480d050140241040703101c1c0301c00c600d8281002a0a0520900c2240e040d0800394603404210b03410601d08480540d840711a0030b045200d100b0440e4060220101e00304048402c503030312081c20a05100c14007003003601354200c440120300c003442800005180081991 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 859463767 1250 859462517 859462537
    0x2030a270302010507050709392f030f070b06040b010504090c0225050a1202011704050a050604121805030712020a0f060e120d0e0f04150e04060b09010605 68
    0xf5107170b203060700b85981890403a46c0030101a41c82c08480c001c00f8007809440580e2a500c1c410a41041e10840c00c100211584003203090b000511203016a181000c101200f0306040d204245c8820b03070410103010341d0340c0f955200d4a180e000c00f080200f6130400f000100200d10303900200584080c0610620000040c04e0b41c0214003441034095140d8401d22941c6100f0040641c48900364503455105590720074408044054a003e5503000355450000070400354a581c4448900d1a0b060b5100007a900d000e11400754403d00180003158907010700420071011900402c0b24038083e900600c2c1c288040992518064000580381e1100b45100340034007003c025a5a000c03440c00100c0c0c910800510700c401c510710000c0d1300c4130a0341c3c001e030341c0d4140c40c0c0c00041049a8007010403414104107942e20107141c0c48845001d917858000c1b042c41c0d00040c0e100701c2d0030401810401198002c088002e88042407000e003941c04200050007a8002c0e9204481c140100001e0003124010307400242c2064a4000195040c03a00090842c07007001440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 859465017 1250 859463767 859463777
    0x724020c0d17120a15080312151201020a080906100305031c0204120803090601050f0306041518050a1e03050415020705041a13061518120302030a27030201 68
    0x408008281c0104a8116003d0404241c3d407524244030858018000200c00c0840d04c2c469010110790010004210b0341305800c1c92105103000c1d07444190705e0000300000c1f014103401441c034401d4020002000d00143c11503049a884e01105031600c0d580c602d1034018014000854588800ca0400100e03074044101c98034007000b041c0d102c4001c83d1820580020f44210b6104000b641800350715401848034020144d4050101c0320b00352401ca1341d80d1010040320340304103094240d158115034046400210074075507007207400b0b12240000c00e0300741202020002a00d0340300c205448540107404007004002444c602a82000c07850202150b07900110746004000c0d006a00a00040e600c00d00314101c0c04034020401c840003498024410f05c0280c1c2c840d440d00f81e03081d0250041a014500c0030f0b1340c21041030094010041a0341401b89680c00341c0b0002501241c41076800f01d05c0c000106a0343d070b00442c8804495034510b078500d010740c00035541c0300e4a06600905901c060104071020704154402ca0011158100705d40007260340900e40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 859466267 1250 859465017 859465043
    0xf030118090f140f12270901080a1502030601140307020a06110705010b18180c030304090209040b030708191110091505040e040f05101b11062a0c0724020c0d 69
    0x401b860b640c03940b003925804013140000041e803160028003820760900c5103404804100002ca142c000340e00080e9101c03404210912810b81050480c032000d1640040340e0310403141e000b5080d8861508075040a20301c42d054400008810061020074010040a80303016680302051645031742200c011400c01402403000e4880b0808002007e5404204075200703007400409495070380380c0d242c00440095000400d07143c011410501985820f02d03010030000b08450700000a05403040d200049224848030541c01100c00c003140d90711610664954540310700d1070780955141d0706121400c040100440204070090714081101c10082403095411301c00b003540d04558400030001400c01245006030605011341004281e41d880c101800f08101c44504800031848100c0d21100c41d03901158000035290311084500c0180004804070b807400720007040d10700754002040004010b0516081c6501c490078071030142e2120390341d51030440007540320104070517400c10320746241c1c002895400341d032002080861034400c001038027098280718 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 859467517 1250 859466267 859466317
    0x1030f020d08220509061c06050621010c08220206160506040308010513090515040203010615031406270c0904140118020f030118090f140f12 62
    0x680c0d50380054141c0d030f65240c5040c9126849140c1c141e21030648202029070106080741003440d00c2034030304030909081011012003511440042d001c0680400d82100a9020b400c01007800c40c1840800000d82e0000070500c5000b50b50700401c02c1002905002e00020300c00c507400c0303401e1445070980e61055416502e80e9265502402080b80300c4200d25800381c01400784508001c00c00d603103c0c036068161002103940802e0001e065030540c0c2210700c40040204241e224000340010f034003201045590003840200042401912060a481000b504012900100351503d880d004a03062280d00c00743d0100c02911345080c0381800b20510b8a94007104800310310154010004281401c0e01c48080f034011810141061200260700e103801a10844248280c4680781d413000711070380112410340200c5414a00e16042141140d0800c2d0424031101c14189880c01071030743c0d1700366103c00a000708049241c458020400107101b68410929a4101241e005102c0450703040221180080107039401600e000501410f240925140020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 859468767 1250 859467517 859467533
    0x1009030c060203010311030f010c050703030b030708160608070c0b0f0a060f14040510080c130e06011401030b010903020109090b12012c060c040303050d0f0c1805060301030f020d 78
    0x40989603600000000c0240301c1c1e05111b401c11010117a04603001400400b08680c22600d44c820742000281c410440740380460b1183c2c00c5045003d00040c15a11559501c540701c40c03904440000d1440c0c0d0b50061001003219607003200c980c940c00001d509119603040415034611070361041c01008820140804008552070142030790044000c0d002d092005c00465071a00c140c4a00d0041501e50b00b44207504050002d404010f81d61505412602d40e0301c001c01c030300c1061800304003482c2c418080600b105a50f03924821102c0e4070030040300b0300030200f1100314400e0040e042c0004007900c1100d00882c2c148400c0120820050b40d00103021011a841c4100010780c021a440001e03100303540101d030081d000d40c00c0c044440981c0070340d04140d0f143c07000b65280c1140301e415082e032038a889660803650005060028003007080803e004c2e60050440e803081d0100001c800080b6203002044810a4208000003240214101d4602d119020b401010300422920242190b26613075403201000c15964001380202c20440c06841000025 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 859470017 1250 859468767 859468787
    0x2010b040e060a110c07050402030714220602011401051207030803150913050a1101051b0a02120304140f190b0309010f060302130506010908030f0310050f03100903 72
    0x204240700c911220304420b541d0303502c262000d400561500000701d0300004800e044662480d10080a41480303171a080800c4000d410003001e403001d001e1030140c0c140114441c000240b02030b403044842d0b80c481107030300300700c480549500d074100c202135a150000c1094414101400141129000c40d502c06100400106040c00d00f0220b500041010101000348110340c200050380c2030a2140c20b803100045075503000c507840c80038850008050f0541d000b40400101041003030718409280c44060500310711b0880c184081c0d0414515004050049400000e84581103181446d100c01d030019100d0000c5040038101400040c040c8a861052482006c010072084080d4030744500c03048100c650265500c01e025036810740056164802c0b502d9090715442d2041c3d048800300d66100d60419070390041c15800c5c070307004041c203103070006d000161003107050141b8000005400d107010801003400e82c1e19140d10381c2e180d0a21203000c1c0e07800e20b80c0341c10042c8206003121119803641c8000030103102600c4042e50107d00945c203400c0c140d4100041d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 859471267 1250 859470017 859470019
    0x6180702100c03020d050903070305041518030803150603100e1308041509082a1f0e09010807030f08070c0915050f0d11060904060830040b04031202010b 67
    0x4201107400b225415038050709203902400401c0c01541e403000c003183d03124810140001c01207035003403100748160141e0100c0b111031114141812004c0c1040366540c8038096000f607008a031580c40000400004400b046802201a403068910314110f0500003034514120f069405100c0262414800140301500c00d60003544040750020180d40d40c0781d450b05141005115200b0304003020440c0d076030000810100001e55122071145450a031041c40c0e008120045122808035079141d8848603c0c0714000d0064072803605a8242455a141c10300d00752041c000340015068142d0009242e500010f1082001c209040c11418005030f1207841d40b6610001d518100144490580064142034902040d00d0f00e20486440319000f80c7d0030440c2c000c03241400340c404005000041e4100146404951a808141c07800c8c481d01421440100a0000c680d043d10b88907058a45101d0f11861410200380070092100c201910328041100c00703c226400e407038a4188000855240f01d50f00c00148294a242640c4174101d2007903011112082c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 859472517 1250 859471267 859471271
    0xb01140402161a1b03061e090109061a0c030a080705040807080a02090c1306050c0c0924010206010b0703050a170901051602030a0e091308030c0a020c06030618070210 73
    0x203443c1003e8032915501c0c040d00414484040104216038100302410040d000c0141049246503038000c00e00c001400c401880b4440e81a00ca5590011981d413032840300d01900d003880002901c1464a0040d03900c046203680c0000e19000100964032000b140841120031403481401c00380340c541c944040840b404d119a0740803140d240214580820400c6021450002d500e00840b0041740c540c80b4020011082d11071645102d0316039120700420400940140c01401203429240103544000005002140c24000300b142c0740a001c1e03820f00c81038054910800c030001c2c100700081c4000c00a9604100300003405100b2500b029040c00404198001140c1c49403840c00182440c80c840843c135418500c079080d000c0e1405964200305002e074518801c000d548004181c030f0540e1503e54400107460b07400f2003402000b41003c0c100c50400c518440484021501c0000114010848021903d13600d01052074002c2c00c00303c80d00c207007038860141002440780a6641d01d0403041d04a03d10601441c803030300c0713005090380750800c400503200781e082c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 859473767 1250 859472517 859472557
    0xa110a02060c18090103120f031a010f2f0d0f12091506080d020705011d040e070b0406050d0507081b0901120f0207030e0f030a2a0f0815040b01140402 66
    0x7c480e06403140540801d8685070b0524449401c194181c0c0c5482a40c042c1404451100c20b1103984118080c0410210900b03103040c4211218061400c04070685d50272803040c4030741442480000e101003006821580591403c030405400d145001801428180028a5001c2d01c80c8184400c8c00000c80d054040303032007030031010031080740d540300413075183e000a42500000d4021100c00045950140005109420076034580c0910600c14200b040010503080100c100c2c0d9109050707000c9540c4000c000107001520241e181c1a40310701e00e50034050196030b00244a0320800040c102801000c64180c0316860061200d02019901c840003080102c038070308001d0710030f4031080b402c3c0068a07040d110345034000e042150280c0d5070285040708006c14400f094440010903a056444150030101140042551541d08811401c0d440d50b60f1007501e00e650114845ca4200328103050700709408100e082c0003000071034520200c15000d01414500380e10351500c8803e0501c28140b070511030800c420712594890341150030804402920b0390400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 859475017 1250 859473767 859473773
    0x60103030206310c061d090c13051503011502120f07081201140321070308041e0506270a03080603070f030b0f1e1b07020301050901050a110a02060c18090103 69
    0xc1d6507030b0722605006c1544503002c00420590120001c0d059000a4404075807900d400c484001c15620800107424803c20b0204003040a6684a540c90710001003800c881d138aa50418561940d04243d0311010800d41d03010b00740701c80000d00c0d64030690340c024000d40724841d00d8020500701025507104090002110b00880d030004030704103842c21101d003a00302e015003c44c0d00e00c0480d08000c035070180c20400c0045420905004800009103c6c25503a03238024414660280c07020a01e0280750a2008901c4042301c4541004c030070040e00c0d01d8084880a00000782c40303805c06000404e8691a5140e460441c03001d400c1000c55070009260740c41c10050b240040c080b449011503416500e0600490514003a0390150300d40d00c0c00030204541e144a001030f41203402c20303c00d201904d5103400a03e45241d0042c0d002c25600440140b001d040541d6082c4109440750300c3c01000030030740e031030100001000c1344c20922010079868014842031a225a00149c03031030303200318025440b903620380d9068000703101d03820400800e50740300303030704400100030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 859476267 1250 859475017 859475033
    0xd020406091506110a0506041103031b0a02031603081227030d0501060306051c030e06030f060906060c07140d0c0308130509251809091406010303020631 67
    0x441d40f0700daa91204006021030026160050024080d02e65400800482e000c6070400f40508041c42c401422240f07402100c5000b0311050724004074800954011103448001d40c20180180c0c1044001c0c03141c3c0c07480d6542903079a584210700a0a502040c04100100011015240d1034440104103010103a4068522040307000340366203501c0340e421f0304501811f04000240c1030b8020b0181d841916401040f81d0301040ba5850819603ca1040c101681000404038a1a1407611050000c501403662140420000c3c5009811b0280b40c1101500d06409020100700c09840c84001060030404d4900174200300204500d2080020020802f201014211403d907000010412110798002c2160043c412140c44110b91b43e002080150701e0b08032070f0f11a103c181035214410707511000c030000d2034020490401c2c0b445580c0d205032044450405070420f441481c2d6420b4128180000c10904050040302c0400400d8590305641e4000c0d1904806011484001000e20b0300c2e0072015401d045003041e400c0c01c5500207598003503e0604140b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 859477517 1250 859476267 859476269
    0xc07020307091103040201270303171008030f13080d02060907080c01120b01031401030803070210090812191a090c2701090504050405010603140a0b04020d0204060915 73
    0x4801d10800c04009100103007402076011204541400500310350300c1e0340054880c4038102200200c0300702800740b01f061000f441610080a98040d546101108900c1c0c00180f00981d03019011550a070041c180812002400104440200e81c003421900c1d200e044100301d020f0b00d000d9580110b091809079042c0324051aa0000720740380720385440c40403180e40c41e41c1d4a110fa51078186c0c541c0c60500164600f01c94841107800ca070001007280b4018900000e04420200654014000c280c2044454500010500a01d154100a03203500036040710000c1000c400e85554080040c416090401d02100080000403c4010725110800c080482d00800b80041341c8240803481100000d800b44074131a656010209146544580998816103285058010035100004104010103145d283e11350400c400f5480c0031409403214010380340190710920000c205281140380c920380e80345644040d400c160f4080042440822101d0140642141c0c0555503801104168004100901040d8000032007107802c100100d5040380c1d80306e403800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 859478767 1250 859477517 859477519
    0xd200106080c091006080f1504051008060108030f1b0316060203090115180b1309060902040b040b03060415090b070216060504060203040509092103101d040b100e0c0702 74
    0x200c43c1c4e40c0d80200d41c02620903036000b40e10011700d00200290020b501020547c0d00045402e44250b441c04200780002c0680c2d00440701c2070b800300d00e0340504124015003081294050580100550f0810360201001c1d00c0303500540035040307809943c0d411022080c1600380102ca4151500b40c4003500201e1850500c43c000c1d62081c1c13001d0841351f00e07000580341c2e095083c01440701a204081050190f0031204c0b41001c2c0078150028050380d02c040416090024600f071449102d08030783c4150307000f150521450041008584000003050f00481c1041501c094550f40030038040d921941c454005500e03240b00d43d4800c2c009141b02c0d82d00800610718402484985034000032001100315040a000c0d41c0252104070407502d5010b5842102c0240e4002e00c0300307200e1441d01c038103400e03444000d00084881401c0d161800c03020b00c0d0584a030302101034200005115420046100c060094810304070503103011103045e210b410080700000c0000d001c540c0070b040440c1030001c204034940c00409039441024000e0500001c012841e0f03006000413 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 859480017 1250 859478767 859478779
    0x90501141005060711060c0c1309030e03030310151205250e0603070309050312070528050d0c0309140c040c030902101803080f0d1107050d200106080c 66
    0x6892609808441c00681d1054400049034051170038009a0340040d21040300324091a201000580c442c07140c04495146a0b001c00301c0c0e007400c2c5007000b5140c0b08050165a0180e00200100500050100704c01c80456440d03403901d0700e4015603440304950303000310310805210322410182807100c1300004094442c104c2e01d241101c070a041c4104a01503489200343c042060700080140001920036020358041980360380100d003628984809a020030340e4598044844a01090011810900049042010095000c1690000c99114159003000f070400d019004010603010f849100066000b4880e80240b02c080b80e2000c4401c1c000c080740140c0640b1030b100c064140d40114a081090b41c1607510030b01a00a42640141010035a4503100b01c04560045c50310003100702c00d01342504000005100c2c41700400301c00b62040201398444940700c501c1019950400d40d1601558020f12070030340461004100d00c1c810940c142403105003800c008243c20b980e1000092544015441d040e4000380c5200007141c0300003a244200e0304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 859481267 1250 859480017 859480019
    0x1207030e100e0d060b04090f140105010509010e040b0a06080319122003091504110f0d0b0a0c0e180a0605101205130f080c1203091f0905011410 63
    0x802c4645650201045520203003000e44840400c0ea01e500c030110310900074201049106094a4680c1302c142c540208035980d900410031545500002c4c400d090240100326006402540b42010a00b1040c03806000900341c8d0301e02a0100d2030301c0910383c2c0040020280a020b43e41c84812012110082c98070340e001040c0414a040048103003200707948030b017020800d00d240c100d0040704481803a488441d0001400f841c4544580071000c125a020b003d1800d108622440d1100c1c231820340e940a000319405080e0166014101210107440010035010350f07154019074a0707400241c00241400c048488607080c071a40e507041680030800e030007078407082c60f5500d101c0c04211105000340f80d9100c1c144025504072000130070009620303113241444e000d01d50300415003080500340319054101c4680c507148452440c6400c11581154005605108040c007882505034802c045000241036161180d00c454640040368045401040101080c29800c0d4550f406001c145800030000c028548001c040b00c0b20101e01943c02d0b188085860f18 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 859482517 1250 859481267 859481299
    0xc0302120c0a08030405010f0612050705030a020a14010c02190e090a1a07091d0403170103050c010c081b03030405100605010f120b1002010c09120b0c0c1207030e 71
    0x3040729107154900d0020030041c600381e01c0d440c10a03000075000301c5240d500d440c0081410031040c0600005094228128800c29109142c55440c10005600c024000c0e00000c80e070304090307920b1142120894110740c180c000360900c801c004030350141c00544000d6003c5006101d07004420310511941d02503400c61303442e503800d94850000842e80e50740120340007000c204003212240f10f24201042007580040d2513040c20000240c903045003000e40c3d110070f1171b444c0002049100f048141035200701e401415034003040b0068141c0d4110380f2620b464140e10000f25051002441a600821100c40204e41c81e044425138581d010031002d030a203a840b40e00c1030798150b90b0381c81000724196516280d40710f02011528161107981d140c0c203840c0029030ba051700304a407480d101d41c1c2e501084403050b16a5110845172000e25030000810b03034002d4902500720a0b458000c18110b1001e040400000381da00b220b0326810100d101409a1a0f0340e00c00c2003d0b14144203c0740070680f0a002040318800c1640180c041c040300c0e502115040b0302800d4450b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 859483767 1250 859482517 859482553
    0x8030a060605031918060f0b0f0607050a02060f0906041d18032b050702060103290c070f0c0305070503150c45090609060612130b04030c0302 62
    0x51003421380da0b04484030741d00a842c426480140e680c411224610303910507090311500211030101008100341c1d42c0312142000149003540001d07650f00d10446110f070404c502c41e00c40c0d5590303500509000303000d0000015148821b00451041d00d20102000305060764440d100d440c140d8000225660103e170f05130366200450050700c801702135548800d000800450522214044036905034164501d201510040318082007494105030003202e2040700160024116545945454154181d058402d88588090403c4184003880348008180d000030310744c08145d84814650500d504c44400e900001001d140c1340c0f010000c10803001040c40f10840e1000ca080d0381e80a1015001c0d1a4203807411101502020000c10044454031901c0c0303651181c1c086c0c8213805240280c44e555a44010b082410303040400d00c04c15240407c454034022000e039a001c0c0c400c2d506481c2c03a045c0000417036982d0051100001c0c0c011412400215030030401d940701c030505500600c4615860401d0301700a00b4070009181c00b9070041c0690540108980806 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 859485017 1250 859483767 859483771
    0xb0705100e1c0e150406081009110d02030c121810200c010f02040902040f1e030f1b0605090102010f1e091502030108010e0715080105061602030a08030a06060503 71
    0x4611503402c000340004085030246500c1c0440d41d80314016040c0c4000f00d41030040500083c00181e22a40e60a0400500b5940a10f096a0010302c10504180b070ba45449280c00007540c0e2001c04015015031241c582c683c0310900ca000e000a540d40b018129020800c28118420085680051007c10f880c03910304920122015180c1c43c1e01d0144030803420212440c00d5011302d070001c240c0089403a00018a10100c014000c0513070740281e00c400b803a80d4001c242071180761440445c01c4024180001940054048002680d0b0145000e1101610350a065075100d4117024088000c0d1401c1011003146d0326509456510150490b0030a041e05801903107000400304121007540300780c91007010b4414000c0d80400450300c0700002340c0b03000481140d040f0300303c4801181d19000b40c0041c6028040703900011941055840c40c3e20f10300240b65204070040141c0e4610300c2d03040c0350042400e40c195681501c80d19605c00c4950914401d08036107003402034140c815002040c0a00a005004c1e600aa01055003402503aa0300c8404032901d000c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 859486267 1250 859485017 859485043
    0x3030d0b1005031006080a0209040f1d06042003150a020a0e060a0233010807051807080c16120c0b071706040b120724080705070611040b0705100e 64
    0x80e044d01130090902a00f0f05540c0f0804050002d8584008070b800701d015514051481d11082d030702c4c0c03c0121241c844e5131040c801e00d540610300a0009103056251880b900d09002d07032100f41c4504440e8584aa6201400034094103042c02504030001d08241c0c02400080d48213504144c00116001c0301500d00707140283c01c0740d0107480564010010500504800c032046e200140a0180c50300702e81256616224424804900074421070002d00f201030300c0c00d014000600481c2e01c035580381c0d815000400000c5a00251034981080e110100c2648501440900c15030700c03400010040c02c508c000844109159600c841e01c00c00740340c40790519004940304c900c001d44243c5112560603c1c1b03510351600040c40e50810380d000c1030355048001d041400c02000741070002d0501c651a000443c4400c2000c0c010f00000040780c0051014209610701401c0c6443c00a00c000c1060090400c000d1840751124803000a182c500c03000d540c05001d84000d25692409039280440d980d0001c200e4840321103090006a850304a00030a0307030095414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 859487517 1250 859486267 859486291
    0x6050a1b1a150a1403031219060b19020303130b1b042603040b0a1404052101051b0a1101200703030e0a02090f04050a0b070f2003041701020903030d0b100503 69
    0x20a40b8107021800340d000b05040c1c03400741a6608c41a68129500600d00180141c2d40110b68801002c6049444245060071050540d4810400e0040d0b115081c0c0004c060075410030210000c44e240c411a4040c05a6030254802e04220040b50201e000500482d254100d004503500c0001e50b9002a6442c64680c001c611405250a4040c0f002c00784050049202103841c01410319800c3c50aa00c84001402502d02c5240200903903031000c50030510100c0c05d101d15038020b0b0440712581c110b03010780c26000e009441042000400c01000c50074a4500b5202500003030405903500d481042c0c25020f080f1003045940100c0020350000e410031071098601136001c01c03400c400540203407100001c0d40d10044102c1d41300707801400c200d0711442099604c0000c10800000c890140c985641c41c050524190b8400500d108404400415045142e0078404400b5030004111421115880704485120340010466402402001d07023180d0107010006040c0c000c4400e03907109038800c800c202c950350400214001c00300c0781400211031310f081c010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 859488767 1250 859487517 859487527
    0x101e03050d0c150207050304061107031221050403020d0215090d05210c04090c1b0213060806161b0302030f0d180b04030906050a1b1a150a140303 64
    0xa21902c0c1c400300c441d01500105080c1e10070f080e41c1d041283e0051200f550680c00c0400d05020b880c1c0c1c450628100401503070004c1c500d160030740e29a4564009800c2074441440030440440a02c40074032404603c400c180e2181c101301501e458100a07444c0d4907161003940050090388016200300b00381007061801001000d00400308885041802d03541d03607104202503030402c141500400107681d00e0300b1515114803103c9204a848900e08038400041e00d160b101810140003d4100e888094044002d4108100f501140c07440c0c40050085d5000c002025079800c00e60103401120308000c002001c11009141c101141e50300c00882440c0c4c1c080300c0c50b403240e40c03010040050308200075080952031800050a1800c064000009400010f40250f0070341c40800f83c801c49402c1d0b8140c0800062503080803240000f400d0382c5c20018030b80540d80000500c82100d0b4403003070796281c00f00c80f0181d050001803801c0b20084403148013004c0300fa040c003c81c3d00c003502440c04c5805104825004010442b4100c214088031110000f038004c41c200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 859490017 1250 859488767 859488793
    0x1020d05040f03080d0608030d060f050607050c041d03040b070c0501030c090605071a090a02040b011d12030d18060513031418150d0510030b072006101e0305 69
    0x40c1d408070042c40b200a8a6100107e0400307000d00040c032620240c09000952103103001c41c9206440a07a901143c4180c0040c000000440d8002c281001c04082c1168001030840007841811040c40f108084464244008200402d01d40c0c0c201c401400b550380100207030001c00355a0b400460503103440740204000a1200d000820103203000324060010584a0f404220f00000500003a51500e80d048980030201e910050311b00055052510500d800d000007846c040102c21450042d8503401c0013040d07000b601030000c0b01002c12000c0300900039030341030b401041c1d002d0000b041c2120311900c2400c0480710a8580c1841d11001c548807010203085407280d168141c64003051604042101e40ca00e800c40c508490300b411501002c45c940d5950820801328605403548000e4840c0480c00300c840842d8401460700c5041c0d00b42d61402c5c00824980c1081e00e522004074035050300301960048402503000c1400300c03078040c03d1041c1c40c203002c040d88003005044181d40a40c02d6000e60510034030480801d401e280c3c800a845600040c0d804851 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 859491267 1250 859490017 859490033
    0x160305010f0b1207030b090c1909050f1228020a0b04050d08090f03060906100f0302060714070b030915131109060a180b0307080a05120a1106070e01020d05040f03 71
    0x101c41005e00f800540140c3c6000800d900c00401c4030107819030200007075400c18010814820314542074503440c0c2a40c5843c01c01c0046200c407a1000c00842c4514249000c501d412201040304d0324902105805002c0c0804071048181508498000102e100d09580301010038142560f50a9404440000340701481054440e15400e90703c0d0710004005800c00b94610806182e030711f04101090040c0d00d85d200525051400c0341c140007003441d0341d800000d0f0302c0305408420009680c071741c4142c074400c540180c1c0b01c0c03400108096110786032800036446880c03104808400c0090281d0301190140c2d01c0152017110b807000e41d40e01040da4840d1700b00d000d00141200c1c0701921081940c10b01c0381c051a0721500207402149500d40701c01c04840e81700d0b00c9803903405c920343d102c0c65140e9950a0031301000b001401828014521810b041c0c3d149030f100c41300301d41c00450403c000b05514160920512400340c0301140c400c16500d8a00b80a84008c0052200216290240c802e602c00d0a00d4980302c0e1003282c048804800e15001d80e6400c40e82c440c44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 859492517 1250 859491267 859491271
    0x230c0706030e120d020f0c01090f03020606030d0203090405101a040501030f29010306170309100c150c020a02040c05070204200d050a02070221190b010527160305010f0b12 75
    0x10301c03044c011f0888601c42449040c1e0814000d001541ca10003035464020b241a10003030607035000b42c014100c20420b80b5000401d9481c2e00b01c0854010400395240c80910380b14049a501205020012640049034500a00014000d42d07100b03980030720030380700a01c0c8188240c2e1125840e0701c0d4001e00e040c0c0a101a40441d0a4114103554140b401058070b0b0740e136024984130843d8002200503d50400111504c091074042c4c269400c280745400c2503502c8044980b107049030360303401300001c500042c0c0f102040d00e840c91081c4002e03c00140e00400c1003000c80d005540c01019038110800c124029440e01c2d1a490b405940e02031890081007681c05414036080c410281080078020140101c05201e8017030104000590310950323806410301000e205050020f202c500c43c070740740900400303043c04000c820010004c0480c1d501074909064803402d6034040516410960311180680400c2c1c018001d0111141c01c1c070414a0001842d2180c65a441d43d09002c280d0b2a008040f1810089103c1c0c01c2030001c0800c9803030002100424015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 859493767 1250 859492517 859492537
    0x509030708010c0306090b09010b030c130302092503050907120c0b0f0307080f07200f07060806100e0307060f0c12030605120a030906230c0706030e120d02 68
    0x1991a55a041c080d425036160750b8600c07000ca41c0300c0005202d101d040744645100e07408125400350155141206000c507910016040d2807094200095124090f01d548000380c008503400f600c80c0110b45080446000f880380f5614072054190076111522030300c0c03446400b400d401034440c07038064480d581c84c040b8000d03404160300100308c840180c072080c00100c000c43c1c10082d2840240410784980e40f481e15a00040103000020807110000c22180107000010b0790101440c1445086003d01d4404001d0000d03017180340c0149207100821500c61383c800410071650220304140038110640d0815908000201c00350313030b4120b00d81200c541651010b03d00700542440755044081d205020300703100b00264000c0e00e40c1c02c5407070b6581d40e200c404262a06020041c40c00e04240000e08400c000c1c0207440c41110729135009044003181e00c0b0b44010402446c0040d2070a1200d01c841c005444400d00c84966907001d071411403500e4001c1c6210303480c082403810b10f810032688804a05400c8148003400d107103240c8090b910350a0002d401c102118 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 859495017 1250 859493767 859493773
    0x718060b031611070b0f030c071e110f0105190e0a030b041502070b0411030124030212161e0f180e010c050a0809030c0d05030a0e0c060901050903 64
    0x3030203004140046009280c129031408051903400c00103010210001101d488580c0030480400c07900200750b06488103800340714503283d5603480d07008a0300c8281c011500c000d002c40c45081c40c0030424461213200301440d00d00c203509070394940c40d0f89402c0025046003840740d240072a404000301030800300003000905240240e030518002c00100780e004200303101c040b034204640d00381c0f4400501081c03226068444000c002c2c1c080c01035240113101d9442c82000080500700600030074810079150410340d02900720544100c0d0001451000c11102c81c0348000300851403000f64021040c4180ca0a6070381d801180190a51400c1164a00410300d846a01d50310f1095082c440f2070000c0c0000d601181c240380c2c0400810050035440c06260f2115040c040d204110b4050225107100e0380e140c01d1300880343c1908070b025078038404918141a02c3e2a902e00082e24203503c5024415592402500740d81d500c400e40010240d40214900a0100721500140300039a54440e07607a81c100c2d900000500502c0000d41c850002802c142c5070150907 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 859496267 1250 859495017 859495019
    0x9031602010c020a0b0f0a0315060c021e09090114060d05070e0411040f0e1b1003020d18140607080f010302060708070c06050d0c03020418053c1305071806 68
    0x5c12110b640040080c0c038007190001901280c42030340360240e0002030789000521145103181c020301130800340605100034000d070704109400400b40d244a002084102006d0800c2c900c500d40040300e9402000480518007002d542440800c1e0700381014400e50035825805002040d41074108540045802c000800803200c41a61051510054a0f00d00071202c507030801a1012400610030301015041a5415480c2107100d968030040003520360355149a09124a058207006903610903c1e4054400b514000c1009601d840d0388c000c40904010300645040c065240701c00c166815521a030713008803030004044d030301390741c06065050041c40503290050041024034401c00c1003924000781030b82c4164440861740d1140010032000324855101e40074a000c3d0b14030190451400718505410150030301406108410180c0c0801e54420004d00c0b00c1d202c000200601680c3d03406078940903001da0310054040d803030312032480c81000c80f910003181801d02c51a19aa402d90390000c0078101c802d0904914519801c034001e1000c048640709c0c0701c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 859497517 1250 859496267 859496279
    0x1d090f01110324030d030b1903050a05010510082119090e070f09171f090204110712112406040e0f060a0c050904020406050d0509031602010c020a 64
    0x801c141e11a107241880301d89a192000c28841003030250741c80181c20781c0c081448203849a801180e042250f6110b81030004000c83c03480046406101200450f052401c24541c004c0b00b0b00400041ca400384500c260000d124654640088034148906132203800c401e903000b02108100007540c4d180d04030351000e480c0c401604143c3e42205203990203010024860104620840c1400070507141c014640c1e008400d403c000340c1d001c0708080001c0032400e003031046000385914000c1c6807640b03643c01e208035104222101062007441005941c0140113024208080b0700ca07515002c08280101004ae041e540616003051b080c1401951003502503c0704500354646101c02c0c01500600485154214581c1440041e6803e04d20810324160081c4011110b07010071207801039102c117103400e6134001c00013001584801e540c240030a14407120130080d80d05001b00055594881e00109000c070303800c0c1d4481c001d00418003408134240801d07298008059100e1040e440b600072041c1c07400c101500594001c1c099565102c4c030240070f502d54666211 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 859498767 1250 859497517 859497521
    0xa050a090c180b03070f031107020d0218010312080703060e0105100c02031f0e062e03050601120501141b0715090807030807080f06310e0d091d090f01 66
    0x2c0c0285a020f040801480a0a58800004903203094282403c000d0030307150f81d02001d0180280c0b6030091241303001402000071500d400c5140322a00f94a440e802d00c05585078039160f10940c016604001c0084da01400240b00389100c0d000301412a5002d8810000e1350b401c000a02042146000740e440074010f05004000058800b0007071003192031820504030a10b4000303010441d06944500304c000b0320b664010014019500000300b00302028841001c160019511942c0d04400700c03800c80e60000c0c00c180164000020944d0700f80c080084800e1061000304905d0010300c5810060725000c3e11030800c48250b01000c0320210b1601c40c01019014041c0c0d05c14440c459070b4071a50300c15218602e0b001c550407040403518508044d0010b251a82000fa030b81000b00440c03900300c6420103071724002842d5901c20021081e100e0500d00c002d1040160f0004d040001c10038003e19546118082c201c0c02c0d0040580c1e204501d43c032525184070b0750640003600c10800c5e101e040058510b060590340140070780744c56514080c1300b5019550040074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 859500017 1250 859498767 859498769
    0x2060720030913020a180506030703240303020a0b0702060720030403020301111b0304180504020d1b0305060702031206040b0103140403031e05130f0309050a0b07110a050a090c18 78
    0x202c4405a40d171440400b000f0101203005144c085201040017060200b6070301c800603640c1c01150b61400184003c032035607003a0541d441305060000c145a603000040245540442c2d05080b13180203002820341a214101d0880c0e42e880c086800c40002166914502d05110300c44015400011140080380c1c00c0c41c0c1c070780d00041e08450305078034003000d5030400048488042894170080c0051080400240d1b08051130800300001c420008801e25101c19a00d000203811541c3c1c040051140c140c018903508001901c2201d601840a10341c041500c0a100d4500052100d610010450750120002881c0c01c0076920b81c4130600000d000c06440d440d0506440752080000f8450000c0710500c101e010303230344c042082d051102c84068043e55441140000c2401c1200704140c113010b00107104106030b406049504080420708049030382c440983c01040d481903030306500054028511014115090080014a281e06002800c005031241d80c3d10425400c032401103010000d410315684800c024010508210b03c900c203800070b0300c01d610005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 859501267 1250 859500017 859500049
    0x506090606070f020f21160b0a05030a05060a0909060b1203131205010e010513110406060c2901180e0615010f14042c060f060703030f020309010c020607020607200309 73
    0x40d491f2552811014109006098040c540c030310b090520540142584001014030881a440b0000300b0304039103543c18000c0c0103002d00c07a01088102c1041c5400405080d6611046201d0f19034514509018a03001c02100c8040d074a581d1941c2d42185000700350103901448400a4400b0f541c1d4116100c2242428061240708030640f10340521044198074042c03014840052006000702d00d844000c1c0a81600409000161500b00038203800c09480c51a100102009000006552100030030000601c0f003620000c0251189440c5814410921000b02c120b968500880703160340601140610350000d540903580071a00d408440c580081026045055242a944941c3c000410403565007900c070840c0080141080e230081381684150070742d04020000034100f81e40008024410a8000360007800c26009501c400c0441fa20744009545a00c0d01a0405008011403030303070540580102c03000a07525510120b01d4520a0010b519003062040040c00e0100c85503010712640d50707142c8000c1043c00526550348000850300a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 859502517 1250 859501267 859501273
    0x15010b1902010f060306090203060c0304050d081504060603021b0303151c0c120212030a09051009030b19060f080d0507031103030907080f0304060509090720010506090606070f020f21 80
    0x43d445c0705151030180012f1410220312418414030000550102c3c80c0203000b110b0385400810358540c140c0d90091024000d030300d02da0103031034001300003250340d01074028062170741810860303104490103030440988910040754020000503025240f03c2151400c110703040301d031010090346048401d0300c1c0d42d14503040c292950400741e92001d0500c0d100f8218500200a40291030022002c0d50900d4402c00d40582510343d5030190610031404001c3d08606144a43c61500055401a9188200703040885003982d030500c00b484545c503000c0c04c060340030409540301c03800710040300d11580081602a000600446443d00603407011030400210805854800c007040003e103001e2400c6d04040c240c42441c02424500d400d041040000b0260014002000b0444c2c01c002641e40040098031220310b6a56010340449900380b03414061030140507100d54014840005504ca9817091105030741040c02d64884000300145070050600007131a07280a02114801410408851a060440901500400b01c00c04d21071884402d040d0410940c1a4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 859503767 1250 859502517 859502531
    0x9040c1e081f030f0b06031c0905031606200106030f080c010b0306010b1b1c170901090b0c0c011103090309090c070b1f08150915010b1902010f060306 66
    0x40c00300d0740b82044840c61010075000e09491a0b035075080d145808a4090b01550400d00016103c2e02c0500001700f58508480d82d680a1020f103040c0a002d12120340203090003803080039400c00024107038501850554860f501c90349940e0903003041b07141d001e40c9628a400955501e8140010004403100d240340c920600c00c042031912150744440c95821900b520011078820361000c00100099500c4a0451f5008070310307501066120042000d113245000d42910310961862004490401f1095103d030150480b03032070901d9081c42d1170b140c401c3c5d03d0f800c1c0da0484074050090301402000c14041a4900d000303004240120002240d26031145040d0340d0690000c072103168150f040003682804034640501000d0380038a03c01c898a040131140e4070385a9404000400103509010300c04650706100717003060f1450008041020031185110041d20101581003000c4d00d090020f0b116440e02c80361003104400c1c9140c1603440c0702010b1410320315a008501c41411003403017484255540d548100c500103007107008081c0074601490000c0b03100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 859505017 1250 859503767 859503781
    0x905120d0f0b010e060d0207052401061404211b0f0f140f120a05010c030e06090d0320040f0501020d08042a0506070b0601080109020f09040c1e08 64
    0x6180000260000341d85040080101c981e00300707004502d0341000b80c40040e150810860008028815114050300310710803030326203c02d909101c0f40c0700e4030b140141c924103101c82c4e6030b504d074152038282c0758841040310040c0c02d02c414132280100d608004016818103d8022072074041351603040744c05580c0e0030519100a40004207001e60f8000010100003014402c2200c00000c0c41c0400201c80c018002009900c00c244030030b10aa215918403005041104201c001e603030800c092860b1481c001d04050000d100030a00b4600c00001060340455458840c1d10b948019001500c5180400c9004011026000d22095045190800715920020203030025100101d8460382203400d06001a10f003c440350517100c1003250400801c00000c000f000c030318800014880007210304c40700002521071078042903044160803035008600c8100388002110000c0c0038407000e0722184800c4e62603a200300f042e4860f0f8000030302580310070460482c40c0d0500781e02c0320b60440c54502d0800141a20b00754002a085607400c100340c0024406002c1c0402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 859506267 1250 859505017 859505021
    0x10b0a170f15010e0307050603090708070602010509010c1b0303050403092601060e07090e06031033050a031b0801090b0405070605090f090a0f2c06040305090d03030905120d 76
    0xc542c2d0b0900b825403030070a514000a0395144540156800340d040070020890f00070040183c0c001805034038003580c1b0920788840c002802000100c03640c110f60340c00c0903001010075000741c0e1451303210444a501f01803926481d840540180001500c11000c0040040000038208090900d044082e080d0150743c2440382c1e1100e210b142034400e65005400300d5402201440031207034002240604484040d110440d0580c0c51000007810281420b16030784003103007014038500c0c1c9000c8180382d0902c50800b0214105071080310030369400410301140121b58109100040a0010504500c5003103c94001030050103030181e2291a15825138000807022203698041100740002c012041c03084102801e800d00c0e10a041600b010b0000e440c00e551241c070a4090401c030000b15205446c0c0c1d410606c01042d807120305000d084c4840e008101400c6e5601c49900807070800b1008000f81d0400815014041c0740c140d5102400c00d100c0c1002c1254100d80104224141540c40202c000000c1c0b0900c9034942001c6103243c440d45a803000c0300c0c0d03001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 859507517 1250 859506267 859506301
    0x50d21050601020a150e030307030f050f07081306090f03020d09080a080405042f0309011103090303010e06010c05011a10020f0a08160b0103060b190e010b0a170f 71
    0x21918200410484140d03400203c2e0249550002140c0900d582848400780040c03401e00c201e01c1c03407030000000308441140c0580280c01c01c2808060304003e5540c609000303602c3c011040e00d4580020381e1040124803024001442c40c07201e140943c2001500000590350352104046408040b400b58200100b20280c103a048000b4400802d20840038000c200d8065403054550300c55030049c0d0344207130741c1c1d0003428807400c0c02511480c044402104c01ba120880240044545940049515040c998204035200501403003100642c0c0c01044e00400450543c1d00b0000d8040318000e0041c40d15042140c1d0078041004181c007406201140310740550001b11060a950070712204080325403e8009560242400c031000b0b00c0000f0341031415070b81060b06030303448110070810488011110345020348955203510002c400c3c440164850040c2100443d50362850403000785003030801c650680b050118003441d80c03004100c2d0601400040c1040f00862800d000400407046803000e44140944040740c01070080001c2059500d01c00001f05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 859508767 1250 859507517 859507577
    0x90b01140d020f07230f0a1b080115030605060a05010e0f01032004030507150c11010917030319050f13320c040608030412050a020d03020a03080c0a080c16050d 70
    0x4205065904141540c0d0700c7c0d6008014217054600031210000e03696125044050a03180f4000e1141481800015402d4501c0303020942d80240b07401c002c600c040c41e01202960032114103031680075054100300c0802c403211070407040d4141419162010454009001101402040c82c6400c602e600d450460030710624148440c0c0040f54808420803502c0355850300002c0000c480c41d4030007002ca5044403800c0040301c4180865000f04000010003100010b4220b0201c051072190294072070410b246800c00c03c001054030b40640303403001c6100050000c25214206101d510328614041c00c800034500f41a240780400380000d900317444210180a1100500036a4280000c112111044605011413400d050446403248a54030031258804100c4201c002082401d01c03035040c1468000700401807110f980c0c03d0194540307218580032800120031200286500c4910001e8402862480c2e96000031652050f0105003150301c040c841d103044003006401c080c001041000101c140e0f80c807a554011401103504021b100008600000d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 859510017 1250 859508767 859508773
    0x60f03170708070b06030f0d05040806130309051323010305100b03030a180b0d06150c030e0d02041d1c030605090c030c0715060f090b01140d020f0723 66
    0x7007400b00c0e07503540c103a60034603800015083c2103031540d000103468a40d10214081d002e02840624101c2240c10001400403030b0540410b590250b507d010903484169011600180881c1c401345c8240490300b08880381090480f07003050006040072441a101c110a050f4204e10600c50044000500030441c0a1040d6001b04020240c1840f00d07000315800643c807405469460800c0241d00d0070010445100006041e00500d02408401d995128840000015116030702034000d00d583e280074040e107e24407943c00350825030f4045d500e00b07081c18011010022503090f0039405030782c000d880b4002d000c06002c2301030002d150b20b20000300810383c18165011030300460b18944074a03001c4c10300e080c2080003c0d840d1031410b15030000c03040c010280e40341d0300e00440403d107000c2c45c1d030060101e1424030900858003003158002016141050085942e9541d01c41c80c0c5010b4503550550180080c514940402c0341d488041c02070101d18446810150030206880c06569003a04288c4050300c0f1002c40440d02107203884225440c060b100908009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 859511267 1250 859510017 859510027
    0xc161502032a010906090606061701030c26030a02101a09040f051608061f0b0d0902010e100507020f060a0503041101020c04050c09280306150504060f0317 68
    0x28041c4080200702941030019a102006142c902d0a5005488160340070400700000003050401c1d9000f403000380980808500c050018000b001e1003500103e040700c2c9e02c4406104210b0410304030a41e21900c0343d0f645034444070030b05001041d031385090000c2c00c0711141a82c000e000717001030001401c1c140d5060f04a607400700071540803510401e032070b442042903010307410420bc07a0405101d03181c040d183c6101810074907049008440080350861004c130700140903407035142524a802c401e000011100b883c180c403070032102000c06c00c9001024541604a00d0b07005005040507902e400c801004103034002072142d0300300c0003d0400a8001d04500d4080d19900760380c1402c1d507001e810901040d0005c0c0003440040c01c00752412810408080306a1b100708007002d2103040c090700600c03031070600a6510069401030541c051140c1500c502007000364800301420040c0c000c07207040e040e036110318545440009069409c24141010407044010559071658003c00c4028294034034119110b030b142d42000c507403c0070306014a034242042001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 859512517 1250 859511267 859511287
    0x91e110904020c10060e040302010b030d0512041104020d2c07181e020a030b01022802060c06161404030b01030b0a020c0a08090f0301200f0c16150203 66
    0x362a000030301074800603a15440c04a000c3d01e40040080700d42c038070504000c00030440d5403c0c4054079000324480d40091201d02e1400b0105511010100b801000142042c480540030404e48050b0a0b003043c040d1061150b00400c0c14040340503039111501040303004e500d413520b805603849060205a883c04111401c2d21040248441c0940c03940e16603c100c56100e00c11400c1d02c0408a40c81c1d1180849085d65588030400d042103080040113504914545000729142c007840030b40c65400130030503500c40340c14071480d0b568600044081109051002c20300f603030802d506010032041084100500740c041c3c203910400c00001c0582d450000d1203162000f07200c201e809810700c01000080d001c5840f81e41565400352590280da0340b840ca02030003d009007010f2420034403880492005000121004003c114002d80380302c0060780d8014141801c0c1c4120710001c40040c00e001001c0c0f84942e246c80c01620101c6e04004406103030140d0060241e2400e580034000c00000030101804000c0e0455901c1041c101039102c0c00a03500b0040720f11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 859513767 1250 859512517 859512551
    0xf020307080a0503280605040614030d080a243b0403030e1501090b15030c0c07120b330d060605061605070509010305191704091e 57
    0x1480d410184407021000c0303003040d4020325411071703034010790722884001c1c000d8060008040d007200e2003003601903490840d0104400204203a010309004000d002000e004000c0d03c0120fa00c10303030040041624070b545000111a4500d402d903002003000a060394840c51030305141e581c075031100407981c50303042d0a1480880007252071003105032007201d03009005118001c3d5880c1c0c1029005000d24202459940c0240e103046407458050b890395605031850300350204881020076003844070a0340f000400c801d45601c148002058546600014040204d9050984000c01c0d640c45071406003810011701164040c180108200428060024140d481d40140c80c40c80107481c2c0402d44a60344000011400c2e004410b460340303210034072500e504224010b01019000307a940b00d602042244102d05144000c1700c0500905038000341a10f070103000306068a030020050052036080030001d03c00b100100c0c030111040410706500b03680902816010b0802050503503400726100c0c2c0392040300f1402000d80322084000606d13107644250071107801 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 859515017 1250 859513767 859513777
    0x2150d060f0509090d0210150b031f141c08040506190201050907031101230d020c0f2d010e01020f030604050a090c0b13090c020a1a010e0a0c0c060903030c0f02030708 73
    0x11500041d18400e5810310340c1034032328a803c004201540007080c401c0c81c11880300c00351082c0800b00702004c072850b2500c02d51a038021040561a900c2401e9510034003000042110140f103651191200f076103000d81c2c0e9000300ba11600195025540d00d07a1649099141940a00403079501407100b80251009c51305682d50030001341e103110340b079038100401e00c007203031311590405002d4440f03130480340d08425101c2c400315a890340070394071800a100550240c100289148203002a0001c407402c81c0c51002c3c184190000d0703116005010000d942c0c1c85035922840302840c101028401012035485003050306690f0b1500f0410b00080d03410280030b001e00c01c0d21300701c03185c0c1c0462071035400030007502d0780220000d54600038451000c001c04200d400c03540895284c520075105076900002c0e0b00800c2d5109041c000108000000e00c0c42000609110710751240e0b10070300c0020085c9055a0024000c1c45150405805419042c0c5030b00d0200d8401000c110f021075034a4280340c0700c0390b03002942c4080d8410548021446c000980c0c0e84c50171b041c014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 859516267 1250 859515017 859515043
    0x815030715030b0904050c1908070b031e162c01440c0412030f0302070506070305010e010807210c030b090109030806040207020d02150d060f0509090d02 67
    0x40219007078010380c8250070092650200030b0004038142014204651200540707a20035118001c10946070004c286080103590031640000301601c1d902d0301e03200c03403030707889070303c0101000415040900c2c1100000102c8a409010303500c24440c0000c402c820348000380c208403101705400103403218a107150300c04410300100040d901c1001e203004441400001401ca2100c000704200000c50746501983c04000e050100044500c3c034044c0c6001078568a600020349001c1c89503010301500c603890012080301082c040c10750090081d60500d00145080c040381c030784508000d0280c0d031141c0029120f600400544410402e110301500400d005021200e14110388241480c201c01e120750741d2580304074612424868180a400020354002c54032006526107103010741c0c0244a51a011400300b070410011030600e003450b100340d03070044d0340c080c00d400d505152a40800040700020b6030300a84a800c20402c1503030140460041c540107080704850001c0c102c2c244420009003002c020300c00035490b0701c507425842c2256070005000680c405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 859517517 1250 859516267 859516289
    0x9061212121404051c02150907030614060a06020c030307110d08120718050d02091f06030603021c080f0a02070306020f0309150609011401030f060303020d08150307 72
    0x1400240030341c0c424588594156010307151410070082c10303201c0e464903840f503840b61040d1409810a0690041c80c1d15100b64000c0050b44580080810f48084004d00c981140c510401c507580142d590303452400b0b85200000300da43d150000014071066091861210014061900240c44aa802d000200c0e5803030042c040041c005d019491210199038403043d003042c031455000210582c0d43d03a11000388201c403500603500e120010b440800403104411010041806030b471340050802103c0c4c180e680030080c0100d00540001240f500742290300035070309405000c4400800198402042107461401008110712944801a0185081d001c10000049801044400d0305010040b00794583e414400b04901c0d101454000802041c400940035070000000409184910001012078406802e5041d6070000040e040d9521a006500e0b1801845180c106007080000c806040c07400003100240c0b910300800b40c502c268002e4025810140201010580c86040c140e40a50204020383c410340608000c00c0d5110ba0611400c48420 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 859518767 1250 859517517 859517543
    0xa0c122d0b0a060512010806160f02150103290f010611102a0e01020a03050d0b0603160f05030415050402060f22140904140f0d08060109090612 63
    0x85050307120080300c0c40041e1000c040740d61650000b40a50344280307540240b1009090000500301c0000440f90301c00c03020000c0c085030310b400e00c00313040d40d4040c03041d2840001d41c090002c504466041252245000303600a07030347c05883c0100035441094a40712840c000811031003c50400848034403051050f81160f00c41c0c1303802c541d07401e045048203003400c19101c03200c00d0950401400d1031511070208800206101c6960b00b02c40003030f00d80f010540b0290380322081940540c0011240700c011038020806080305640111000c200070b0b528100040c80c0d43d004440c0c00f00142e07c105007162000c0c0c1e0085404800c83c490f03042440c9541825194000c2c0c00c14118040070503d03803110300080854490000340d60b0025404001c03d507e5141400c511031820300990001c1c04019050000004d004040ca1502c841d00e03280500616404e071110346400d100780d24502060080340c803a80302d05007000d2008104550001c043c1c0d95903075005040000005011002c07c0e03004403600d6041c44401c1c030500300030a11035500180e008005c4039042d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 859520017 1250 859518767 859518851
    0x9030201081909080f07050c010521100801060b0c011b080c0d180503071506050d1716120e060901200109021c11060f190c05060a0c12 59
    0x83c08900320014481c0c131021502440c035280a01c06010b0440c49681a50103840001004440d6809400b403018a100c0011001c0282c01001400b020f0304641103a04442c08240c40301d69136803c2d5280c683c400a2000400254100c45503400c0c8944444845c0c00307000c2020400318a20018026a009040c140103400c0c00180407a5002203035001c107084e02d1804420103241c0540742002030f202d80203884241d800d90019134600c001e0007a180f0440007038401c010140176003078003140c13510355509400002e40304089a08000c040d4200c0300104807201820300c40d4034607401d0b42429610007803251609460280c0a581c080c4410340b82aa00007020703407001c60020315044070340e01200380514054403281401940102c4420980e40000100604202c01c942c000d50448510700b096000f031104a104941c10b400f003d1405100e10342c508002a18003c2450085261000080380c1585906007050401d03104540e1041c1c0d2050126400ba41100509017200c1003010f08018002c0c001144c6c08411140d8250740c80d001880700004411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 859521267 1250 859520017 859520021
    0x60a06050a1803081207080c0301150207090f0e10050103020f04090618080408010c02070305100506180a050105010815030601050f0a0801050405010203250f05070804170106090c090302010819 84
    0xd892010303035550b88059a82c1000d440d41e50150710304817002d40c042c2c0005161180600070040c007a801c110380981c035503803a1500d0007100e092040304d8102103008203600000c01786283d010707800303204040401c00240c0b0700b07078110001d18100c3c1041440c840702e41020010001740c1d035540750061407048255004203c440782e42c0b0f05140108a00201071401c0852480c0f00310510503814050405c1c3c0e9021402000050104d0506990701c458600c0010040d5002e12400069028a03400c05500400080c21f082c15903024020104c011290480d43c00d031045030344d600104480e40c1d0100e94560801882802c0045e540b14080219440d03102c14050f060140280103003410480d11403c0c038000051030340304002c000782e00300752a225000c1d41c002e50300c0740e140b0b0f250000b9528100006490b5001a080b054480300c0e40c60701400f4050300c40703070495003080e07a84040500c4006518403001348a82016084c8500009030b070740c00e0007440c200701c52004c01c0d40c804010440f4418001030340c00401e116004075811000c91a072144503410300780 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 859522517 1250 859521267 859521287
    0x70f02150304060902010201290d1b03050c090a0501051e01090b0a02011d0c0102060a05070504030204060314010614030a0b06040b04020c06091218040903140307051809060a06050a 79
    0x25060380000c104030500c51154001c00da050320076030090040c3e8042c1300740744075401c0301d00f4492019690300700140c450070715014024541091041020840341c002003000320503c46101c6d4410749050f007001d0313180105450200740441d446400c0300404c00c550750414010500704061456058a000a03905040300203078083c030f5403d40144a0750705400d580c8c88480d28024060200000250041215a5020030101030f000c500b5002310038045c1c0c01001aa9204184c0d200035045c0584140c0a01c10300708000310168589020315405140219401c4981c80c1c644003c480c00c542d01580880c41e501c01c1180d40c211241c5c0c0114110004580040d100700c0039031644000100205418200c40f507205100042d40358a194012950034850003032803007900c688504809689481f4802d488070044000e400309003443c1c0a1601c0e50002c440340c0c0c02441c0200c44020042c414207005d91007516094086a40070440c101e2207556644002c00c0c05200b0b94a80304241800008a5046a44c50044170180500456103191440c8510f070b01c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 859523767 1250 859522517 859522549
    0x203070f0612060b0313230604060903080601020105010b0f0d1d160e09030d110910090f0b120723030a020711010206060a0b090604030803091b0d08070f02 68
    0x30514658801d0007030400d0400041c0901458242000002c0703181c03030002902d00c9020a0403d000c41703088280c3c1c480b08180001302064001c10175104040c0c01e0b0140070004076102d54031800000500b00000d007405000c00740000e003440e04683c108801484848030f05410b9410340009001c2d9252030748144000c1030054040b022601c2c83e002c030340203070035a12564000740c2c51901c1030140b50b214215039202d800c54441d020302115444107e0380100400100036089622070007a1181000210b8102100390700003400107141250301c9400940c1c290b00a1126841400e0200000c01d0b231040c1c128548820360f14002d000b070400030b010030203100ca441c031000f60340880c01e1002c00d00d040e04144101d580b4074001d02d100d1300a41001d08107440079031086603042d2080d400064513030301940f4010030030507080741f416a558400385c0c888404550800003c1c8000070018070a603001c1d5000e208480c000d4094541601031610092a0307100c92140306440d0100d184005c5004a01101d48a5400c090442d040c1c400074004103c190907131030141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 859525017 1250 859523767 859523789
    0x20c03070606090501051e0906040f1e0b012d05130b0309011d060a2004090516021f0c170705120a0c0e010e0a0302030105043e0d020307 60
    0x8012040e40042e003514100c038000c0000c0d90721601800050424a10101d044011302809140703507161000303100d548140002d10101d07250003e088440159900314003104907000c95030b00c251006900c14042c40d081c400082c81c02241c2e0008600606140c1034601002041c0188035007c030440c054490000c4036040d0010b08450a036040d500e40c0e01807001e038070032a5451a55460038030203a15541c1d00f015144040883d101c010201600da580d095001400000d17044d0038440ca4581d441c003001d00050004d80700808031140300082610303003040c90180d100240040c0a085402c003403031509007200300c0c0e0802c0100c40c40071000011610390440c0143c45841c9158540b0714400c003401c0410950703d034820020886a010400d1a01c150f032611b0110780c00f51204080b2104c042685421400440d5105154240c465200281404500742c0e40790046803c580c4262429104c45203061501d0380d04a011b5098110082180507442049010005140c4848038400640c0d511403c9421035080655800300030b07010141041c0702e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 859526267 1250 859525017 859525027
    0x2030c030f0f0c040612030f021e0a03020f01020304020901031b03150608010b030c1c0303020405060703030c021209090f0402011e050315010c050c0f03030d090f03030b1e060a0201020c03 82
    0x20103a03491490482e442d02c140b24100121a203403d00380110011a920712040400c00360031968291341980000c08910308501c60b01c403020041211850010010004000180008a459041c02410108080c0d01101035a004005000041e1641c080080c11250003046514000108a490154000155001a013018441e8540070008405640300c10100e94000e0020010303503003003000303058441c1e80303680c50300d54072544803000307035041e1402c0310501003000d840380c40d00604e0f040d00c8100040312500900d0051300082c0c3d031542c60301c0484d5010070040e41c00c021800821800c140c0c4481c001107828000400c0010b015485601103411a401103100c1d803644040708856190301c40d184400103120b60803c903100448010014a00d114039400390000c0c42200d5005000f400c0d40300409024401030b000100440b42d01403208102900d5400c0052080301c1d180f41c414550f1010b0f507400d80c00e0040c19038031110825403280c0c0d0320000602507600c3c011011802c14806844540e2104202c5030103a009018022100c000c0d4000062 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 859527517 1250 859526267 859526293
    0x7031208101212030e0111040902091005070f031d030d020c1908030f0f1903021309050126100e150f0106050313060603150506130e0a0201050702030c03 67
    0x15150312031803001070303920045036460082d40b0810088100c003078111032016810707031000e5100c0e41015400051610010580c820404822a900d502940c0302502190303011404022510b0300c03842150100d400c034a0085d080c07142c59220540307003405400700282446000701c140b000703100100c041110000b200400391814160000c4010751101d40c1da040043c42806542004d076001a040941d280c02d80b00c10400840c01c04500d540c400001c0d0f48105400491400d007484984200c0c0040b52490482000a9802588070240151068403840c2181c020002d19030074940188099021071104004030541d1002a01000380c5224106051100e0900c0c00384400b414084011314114001038004803084643c87d030b44985960320000c021113170400303020708030024a003000821207062502d08013100e01d5003c1d1300c00258040e601d9492080c60346503101e08240e059100c00c200246464000d0544404841c0c240050103040360050100782c4808407140300905220003c070b01141991000c014078000b84002400320781c141c0e000c443d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 859528767 1250 859527517 859527527
    0x3090c0411030a050f130f11030d05040905090a0201081f081c0e0603040c0506130e07121407080106030216080d05041211030a200d050901020706020105040b0f09070312 74
    0x182d200c41d4007030916004c0380440217800301584c40790030000300310010942140c1d0782d44409103d690040c0d502010302201015269818003c0c0081260681c8500c1e0b52036203016108010381b403004002e1100b0350801c1c0c0d0b501e00540d0300054155400400881c020088081c45942c1e240306030035a0f00310030391620481c2210b44140031000780100001415480b00e824020016040000c5d42c8821600141889a203030000c00036810701001401683c40005c0c41c00a8064556101d00803040c4100e66030300004001e0b541c000f4a8520612990354408140d125201d5240303415580680b01841c180b04040405500140c84000105070000e034400042e402085580d03101140c034121030141070203840545480400c20b074644046806555200034035190b540c0590b003403030076540e01916212031500070481d00948014220078989014440b40050100c0384e110190cc07903e030080024504000d070341158095a15000c24031000c00c9000b104a03070b1041e4000810762081e80d6040f03107181080d400e584014802d03404100c00c101501e8100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 859530017 1250 859528767 859528771
    0x2070b071e0c0906180216240c090e010815010509070203211806100b070606050306090a0303150609180e03071110050a1205060a080304091a1906030203090c041103 72
    0x1801030765690307000c64017488124410301387d01040c0404003105520009150040b000540310f55185081a01075200f440d00e070a075290780b07c41c000040d08000b803d105003810369100711b0150248030020050506d00ca181c0502415060040c5441000850009808a03200f00101ea40c020407084501c1c0c1038035003280740c1120b07440003950030200c0e044a000e840c00a00c0c40001d0524417030300404042c40c6209141480c3c1c1f22490f880f240c0c06641030b9407901d4021032a5281089824000c184c4180200b11005042c01c0060490789001c1c070b01200c00c040c0c031004020a41c0d01c644d440c010350300c1d40b0a48240120300d042280000300000da6aa61007404007080c0d201c02e22801080b04512203009503901c084071103800d030084600e80300340540072000c14a02401508100c849501c1641c0c00b0307001a00112950351142e901c2482c1d608181c4c00304100d5501c42615440300852032003c01c114031070030b865442508902c01d40c4256051554042c2c0001c142c1d012001071102442082180700c0094007034010088a40544080380803a401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 859531267 1250 859530017 859530029
    0x41d011515020c03030409110d1404060f150e0c1909091802220f020d020a0306120807020919052e0f12030908010212090d02070b071e0c0906 62
    0x408520655418008190088141c3d002000b8615041c244003d00008110940440b00040c0b014051120400f90070310172441044084005540e252505103001c0c0c00b681c110000c080c2200d41040e02088800d90704804110540310142c0c03400a1603510f44400c04900d010b81d526021580b801014825207107904581e086040e90916002070040490140741c1800820768070900030b41040c032070410303c007102c102c5840108403501350b0040821440c0701034503508281d810a0402c0340070164001007003181617405210301e800810a21611551840d12502c40325428041d0583c043d004d40c200900003075601c0310381d01d1140c0381d00c2a0361108200c2800c080c020301d00e00200000740c1418001406e50180449400402d20340c0458002c034501040785030a02d03045138009441010700320180720b803030400420b0404086c000b8145c00d41002c0708400c660702d07001d0041071800842c1c1c0c100078107542204000b030081c00c2542c0200c414040e003005907441999000f071000e140020700e048000e018012200c0c004680110f0381d4001c10100c1780 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 859532374 1107 859531267 859531289
    0xe09010608060a051210020319050c070b090114010306111e18152205030d0f021002130e04050307020d0809011e050702041d0115 57
    0xa811803004660030741c00704061400c20f00000001004e040f030b1640b440899402c0700d1a151b80c040074000d14540d8000000486080d411000246501d0100c43e040003a440d01d00ea440429403c44241103400841640116800784014000c812220766201e0644180340d1840d540d1034010040207c02114044092285800001d000314110950b0400c0f5905155580c0c014900710032907a80071900e8a1041c038140307140e0208d81c0b41d82d0051716103002c80c2000c0051141e140c4407403045a482d4644c0300560611805030b00c103170801c0d4005602050720303015400304e0b07413403005d200c000100381d000e040210012440186000c1004088121185800c28010001e80b45044110b8010410112090303900761581980041c80760190b50b0300c40d882d2a03900040740010003c03c03240c41c10081c811b00c42c1c0e00f40684900c0d00d400d0074201c0b05607011014480350b0000700003000100c448180c840c5a0b44c81c2c0748140c0700690 = true := by decide +kernel

theorem cover : BRFrame.Cov 859352517 859532374 := by
  have h0 := BRFrame.cov_init 859352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 859352517 ≤ n) (h2 : n < 859532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
