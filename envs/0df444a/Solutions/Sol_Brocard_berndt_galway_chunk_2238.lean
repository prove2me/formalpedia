-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2238
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:05:08.398112+00:00
-- url     : https://prove2.me/submissions/b7655ea0-4920-4bb2-a583-52e74dc2d09a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 402338129 ≤ n < 402517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 402339379 1250 402338129 402338171
    0x603060605151215030a15020901080f07080412030906150503060f0114150f1209061503060c130f03060e06070302040501020a170f1c11030f0112051504110103 70
    0x1440b000c091940c0e50b510058404c90030011038843c1c06010b982c104200003103c060321a103409128800058403942d40c8000184000002006421035964890034091403030342041042c0d601507404003021000590f072540480180c00400300c001c00041c100014100b1341c1e1007030030351101542d10980845581d6034800744c0c5240c07112400c0c4108060885c6140200032281000340c480071002140440603440d0125000215449a00100c1c903000c2405c1c8450600080c40c1d000cbc80071680119164014084801040b40040c1e01c3e0500035000c90342d2038000060345840c80068408160040010040706002c0c140d980c10a9000303040031003000031840c0105800a101e1502078404d0345c01fa0313007044c2c0c0144412403283d81c0d44500110391030800c6164450030b114440e8440d04c010010700c184007241a0340c4c0002440d01d948030090341e1341c200c25500210011f004110f0384011100c80a411500c40103001300300d41c082ca00300340f41485240030402c200444180100070921440103013a01d030416080e0b90400180788000c000c500c4180e9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 402340629 1250 402339379 402339397
    0xd0911030c150c011b0302030402030c030105160c051203010605030f09061303110c0303030711010b060412080d09051c02063405091002010e0d140304080d0906060306060515 76
    0xc421410700280b09803900c0900070b50940f800c00003074007100f41c02140c84061920282400040e8000003040118141400400c1c1840c03000c0d8000c1c021420804040010402c2c0c010800342040000d51168060180810010300910540c804880d42d070750f1507240c01459940100d449286c100451000700c0c4980400080041c030407600b03400750507990b0009640494035400740c005011680d01c90741c510011560b409000541c010440b9454022400190120890a480c4c01d0034406200311002d0200300054134920035098016a841603e85030780380c040c0c0109400800902c4030160903441040130203088624664407540340851140c08a40750360343c44000c0b82e0f00d82940c910030140c1c11224502140122082c0070ba003406102114100142002c103054081200740b903030300b118080180e45604840040e05401e00c9a54002031081c5420052060340240d0040d00e0711018000511a010004100e101504258032000c06940e20030b206200b003943c1c9080403c040c3c242401071500c2403400b062a400000c2d8004210b0700368403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 402341879 1250 402340629 402340639
    0x8030c030a030203090109020306090705011d0306060105090102160b030a0501120f02060c070b0d060303080705041d06280801050a09020a05151603031506030e1504080408030d0911030c 81
    0x7081e00e90850103500050809050ba41d02c0b803400c0401a40c0030300046101d1144c0800034410360b45000b0004214016241039004a400c07840c10401243d01d0206943e03a01400c04e0800a5a0702c0c0a000101c1ca072442c0010350015940e2501e0780880c03100d400c60300540c0590101002803019980b50468520000d20010707000344409601222000182040c0014200700a080c50607200d0040d07640c0c20740c0b1280d900404420310030641c0c4207424010150003c05440d0090b0701450060305013070a010303112009045588110000512040010305e2a44c2c44001805900c10501b007245a1351a17107103d1000c20103914000c40c80c495007030074001145c000c0b040c450156825001040000350a1a14050000700c3c0a030394042d40d5607550400c000780c03002940c41c404040c00d80c401d5500080501c0d200a51681900c03a0390040c00c101402d00100741103083c00051071018401125440964540703440c54442014030565200d072a1600000c1031550f02c010940d4050644107001d4004800c07218100c4080545594004443d15484 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 402343129 1250 402341879 402341887
    0x230c04021c050901150303120c0c0305040b1315050a020709200912060f01030615030c030b191b0305150d20210c040908030105040b1503040506070908030c03 69
    0x100c1581e8010a4011843c400005101e03080c0a40054642c19660015000310b01111803041d121b006900c110400b0058030300d08809103a0703050394001d00341c0c440d0780300340c0c0c41c8030002250347d00c0540c540d41c03070703280003821074181107543d103003421501401c0c542200700383c4005070191000010b014062400b070007206001e400800700d4243c140100302105500015103407908481c0b00c01c0002c03c04e520400c48a8085d4103400040314540d03140d0b240440949002c1c001c40101e03a00e607041c1c02c10001d50310500c1703c002d076603100e111401503503604130039a03034141000c2000c802d2440c01e00795116071102050340a40b080c255550b505004070b0355241031684140a0010045402c0903040d00c0c1e600c00300360711030b200500900025262003003a8440c2c5000600f00516500038101d40e80d41c0d007074804840c41003046888c4411a0580d402e00c10310172141c890020728001481000d00840d156030f140c50407641d030440a520b02803001811243c0b681001d0070000d581382e40881e0b827840469003440020070180c500000343c91001209800a601d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 402344379 1250 402343129 402343177
    0x50702030a0c06060f0e0f0702151306090203101b030504050307020111030d05012408040201080106080601050705070807210f0210110109150f06080601030b13230c0402 74
    0x100b03900300e0a003a11004d903a14400b0a1029900c014a0001c10342d48001e0ba165040402c1c0c403c0240701c0c058401c40039540521045900f0003035450718984d00c501c0640e4205c1e803261207414200060503500000030b48c5400b90b0308982059041d1540310710b0301c45645500900418414042c280c00300e803026940034201e644180042c90066120700d03809a141403030306040d41d05200310389000308203480081c1c1040e21414211000c20b0901d000344001084940380360310302540d19080c1500043c1c010341060044600b0409240c00040c4241d00031400c4600c4290311200b200c08503941d891440361a142c440c0541d104101d082c0c412624906000314520000fa900460071440c000841d0b1700304003040e038064510000b0b010480b11202c0313400c403080c498118624021181a0500003034824000d0407201030b441011482490958140402040041c0407415a540701c02081801e4841d00d6101841520b0000000c224400d9a440303417159803000074003003224007101001c48204450140400003070307009150f84643c034004a1a45104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 402345629 1250 402344379 402344387
    0xf0e07050112020f0c0d030b01021006060519030b0d0302030306120d0203030a05060301060b0f1801210f14130c1d060405100b13030308090303010e01050d050c031605090a050702030a 80
    0x2840441401a00d0b00d440c0c1c00f05c24090609030301c0d1000f640803035030b6140340e000503503014081e14690006030102000054284140940607001d044466505040b07400c00061044c2c0c0298829008024010030501c8000340c1403500a540341c0c42116618080c4142605075812020001041d0200aa10b82c010b942559070b80c0e1103203030017080020822981592214000940381c04000c000f06500da40030406140d4400010b2080000c0740d4104010703904000d040c0507016888844d2620500b411203480300041060f040c064444806490a80032010f803c849010511108483c1e61840c0c001040c4910f4908613020b0740d820280542560004054402540b00170009030507203040d9105030b80c0010341d501194146500e405920009400c0b860107241c0301b460094090003417682040103540c0c000d111100440c0755604050610214a00c107102d0140100e8280c244101040070034032000d81c03641005001c456852142c804400d103580b40c07030320405000e0003000c0c1c0402c081c82198012640711b01c0305500203528200001d01c0841b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 402346879 1250 402345629 402345637
    0x3030302360f090114310c17010807060507050c060d060509130c06110a0b0103050102032a071101050409020a080114090609070807180b0a022802010e040b030609010f0e0705011202 79
    0x14902c2c9008805480e1185660b42c2404030309140c1003400200002c010001401c1084c1105002070848d121000401802d400061a42c099450a140040c2c0350040c91030113500e8031004640c01584200d001c1403840311100d05922050840b601201c0d0352040e91102003408a0300003141c0d2001d011402c00901c01c2c0710950180c50340e407407402c0e0075008591031010641c850550b03404007a04101c4030750350000184180c5040080400d82564271a440a1403042d55140d64811188074a06006000c10b880409684e0268005c4081d50014000c0c50025951140e020000800c1d02c5c02c02d001d81c0c441d50003000d0a12040d4240145600e20030140a400d120030340d103ca0b54191031000c002040e080400019005510070100c01424690003481c80d00e42042e2240300f00c3ea0040e05014400303404c81c03140700448202c15070f010440070310340b285a0340a0070304210398020400410041c00c610007080d505842500e09000041d80154000440380c001c1520400502d180e8041c101d4480030f0900c00c0600250907186c03906029203440e4010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 402348129 1250 402346879 402346909
    0xe06060a0c02060304031e0e0a0e060607120207030b070c02030d0c080f120103110904031b0615060507110303030907182a02060c03070903030302360f090114 69
    0x240c124107001e900041683e8400c441c100c00241d18000490101c440d184820341605510b41003004141403101e002c90210803c0d881030b18010762501300403c0441c0c640f4000c40e1030042c0c01082e001d85450003124060340c0d807001d03807108840805071000050489031003128903c8600c2d5000700034080f01c90107403000311450452044142c071a050100020822203200c00000c0102007010481c020456266083c00d0039690b0400307007987d00030b50b1107800f00f00000740d2250500840e1010b54054064800082c00d28000405d481500c0149204030540040b80203034200000d010114032440780707540034a071800241a16070005444610050f44140d800741720740b020703501620700e01003188400004c0800041d01c1f4840702c0500250200362404109502ca103020364144031659000e281801e607217103141000e0f50000d0200d801c0f0301c400340402d640801c00e0465402c031900130110103814030142c009146600352100b80b440c1010b440c60b910442e00d06511002600f45840410f0485890842c00e8403206055814401459680386c6a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 402349379 1250 402348129 402348137
    0x8030a090b18041a12030702012703021003061401030b0609150c0105041112010b031906091a06012a02061e2205041a22050c0904060b040e06060a 64
    0x1070a951502c91348140041d1200103695148902d00c000240710f0f030480ca01803d0307580c82c1c00801500c00540d800290241c030402c00b408415070201041156040b0060007500300075408090414bd4804040d03040e0001d5094810300340d024804003d0701d0005400300d4014001d00c2e600400c0511a1011030324100c1d0b40c0802305008440b005240c24680c0d0282e90840708200c2301140c42103c0340c600b60381e860508107940c030708401d0306000810044983d000060356521041c0c83c8045031248010b40b9404200b101d8111300b4400d580003031007a110581d444244501034108888090010300d44e011100304284481c01012843c1e40000601c0c10140840d40030700032258001e41006c10008034042040c489400241c00900b0050354958001c1c03010342c410740075034082003816441148602e05042c40c140c111002e80314103c07d11030701100c20750352580000c403011900200d2002d82c004400c1c5000c08025080000314002c05030001c04070760400c440d545404007044a4040d500407031054501160005005080c100024613100c2c1681c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 402350629 1250 402349379 402349417
    0x10504050a0b0403031b080301030803040311010e0604050c0d170f1219061208030f07030f15031a0c030a2304080c0606120d0302070f0b0c0a020708030a090b 69
    0x30204084611561005002040c0024100203241d40b03c090a00f4084280903010350400c5151291802404180009880c43c3c9001000c201014014102c50098800c504000c0c0151200c0700b56103a15408100c50961340c501500b100c10b450380c6000403100300030b203511034030032032081c4090300800c2d6aa4000040082807681b0801081101d5182c041d10300d27102c0c28202d40c8021401d50400b12100c144c2e402544145004c00f030711208031002407045e6042d80d0380840368842280c01c0c0e0769561821009041d040700011010f525001850400c0031700341ca02d113001e49004070041a0705408075045a84564003c450140b40507034284042005142d00c0d0b0403001c4440a9541003080c0946c002e80442104101560b00311110400007c0076224580c09022030f65004c039044441d400c0030078400300100c0c7c440440d03019072800c050f80007441404201d44e540c2a540f803580c00c04640621494002c4041d20030741d01034000a8058400d0000c00540f6100c00411112500340d80d94441c0700d940e141906030001d5400c0030356402c0c51412503038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 402351879 1250 402350629 402350639
    0x5011a07110a03141b030a080414040f060807081c020d11031210030302011d0304092a0305090723121011091503100e090f01020c060708010509040b070e010504 70
    0x4641c90b805001c0701c40c06411400102c02e0a0305c0e0300000307000001d00903004204082d0202d490b0f0b109950803252141c484540018980001074010701c1100c0600058601d418404100410700264140c25140b00c101200d0143c0c01503c42800c2c0184111031600041e4402840c06410500c917040040044191074102c90500441110742c23807101f03004485203038107030591102c1001810b0742402615a0f211009602802001ca0424203640702d101f0340c082c005100e51500001c0e1003403400c00d01107600013608540766400c400031403c030007006401d0940b51103142d84070b19600401c0540c0e0310200400c1c07900002440841c280810010320a40e242c500084042c00d005090000142603031500501080800750f0b003c03150b99240000c20481031512a20150003001020b00030001d02d0126812083c05640010407190801d41d1881c40c0030b4503182600803448440e50001c1041070000750005025401503400e80c5510040ea0f8940e004d01c03d80706030445010f8030b03032000345010490141c040c0b0341c80c103184141858064501a2a6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 402353129 1250 402351879 402351893
    0x609061b07140108070c03090e130b0a0c03050f0712360303290d110307140307060c211b080403140706200307020406081005011a07110a03 61
    0xb030340711485030341e8141c1d0500c01540e40100c82035807201040c24840d0b034040241c0c0b00148850164081c92420030b0140c008a02e55002e0300c085124110392000031920301d45450314410015118001002c408a81800c022890a010440b0504c0c45608142e580c15407403806003180f1f0000d0502d5034100300208914840041b180e041c94441362000c0c01e00321309140c040e44120301c1c00404a03a0b00e04090049404105c04100b5559041144201291405ca80c0f881140c074950906000b0f003003c52202c20303454810b0311400075220741e8003468108081c0e0220199081550345900540da4080b004030001d05111003081302184005910f0b0b00319414020078a41208210b41142c10340782d88004080068a1208001c60704000304001c94900491b140780d40f002078004546007000141c01b003510842c007006024540002200c1d0100f08000b690355164000300140b00305940c0d000b445031550844010544042c0c00c1000100350048024806003203403a01c080c2e01480c01d400340c0c6070100300348810103c03180d1112000c200007000c5040c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 402354379 1250 402353129 402353143
    0x307021302160213020c0f1c050d0609020c1c02030703080109090c03051915060f1208090603010f0503010b0307050609120a06052d060d0b06031903030b0310020403020609061b 77
    0x1131400c01a9501d00780101c40d841c0404100c416190350b84800c000131100c080e6040b48004190417801d0041e12440c440c840c0101400031600004030481c8081500801250005010b0100d0342d0000064109121552422600ca204210025021501c00b0004205003400c40d0300c0129400d020b003078034500d1151a981c44500707004e86138900100300c841d00380c003090500c807118610b240a606e400348108542072030320114900e001110302c24084440d804ca0f4481052105000c122001150000d190980e80c1da12502103041c11401800780030300a41c0303010981c02090400007400c20076114001c28542c01c201440040052031702d81c100310540640545801c0d01e00043e01c170b004003401100d00f80c01610402d5901d228200440740081900b0449140c04001c0c010725444102030101d0080d0040400b030710a80e29000442e2170501401c100200980d421074440040c185c1c941c0c00700d210400204c094840300300344407202ca0164040c0e40030280d4000002c01c400507542c41e24900401440c5103038032001e580e00d2040f0078618141a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 402355629 1250 402354379 402354409
    0xe0a05010605100804030518271b0c07030314070b040f20210a02030102073f050325080a200d020a0c0c030b0106021507020d080709050a03030e030105070203070213021602 75
    0x210001401046179007011021030641e0006d4ac264104146641c601d5500c030941d11001c2c0500807000080e4010034018400c81e40282e400c4084002141000d02d03050507111172915040e14651000c601078401031540348042e00b07801c50300400c00c074801070b03c620010580c04816903080030b462150100340340050304c080c005400c07568003542c10b240c1003080c3e40c0040e258032094400c03038901d134103447c5400340d0710540b841800810864103803400c02d44a41d241002c00911514544004480300c0541260303070000f0754801400c0d4400d00f04403109104100414554040c8180811400708a001007440b00c0100039000c0e5014090a000614122803842000e45550a080d00c447e04151498242d520040c0601ca0701023240c03400b10603071007081034214074050170000e40720150b81c100802000300c0400460800c40c86021100040d0038020001c0e194142d407850083e041d44808018140294203200000705902d0021081d83c0380c640d000703402110000c00405151000354404020500700808500309140903031202e08240d14660 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 402356879 1250 402355629 402355699
    0xf030e0d0e10050f0703122912120703080a1b0203070606061409040c03110a05041a0a090b0309100c080114150d0b040e0a05010605100804030518 64
    0xd1007641440003099018858009102c000c10401e43e0600515007100c90583d01403802c0714142c03501e84014070251504101201c02140c030600750403403940c032515000501c420200c81401202044641250703c440503642100c194120500c81c42e030209006a8015900c0078103400c0002c2d50b040322441401680795182c4035000140c0c80860301c40c04100580c402d0340e01900382402c11072081c0c240503545074810300c11890958010780c0c40d242d26101c030030b010350440340c10361864224458440c0350b081c50042007508284240751450502a4454901034004e80c101d4061616a9851003041d41c2440110b01d055071010b03140079501d00c00e240340108103514038820b0700e1991603541d0b1240900d51601140b00200303011001024428550030707982c402440201400c8071020301140c00e02141d00c10f89040045d000307101010001140f0301803803c80c2001c000c0103601c1039064813021200b0b4400c40070902d00c1102c052104950040208401b00600710380650807041c6d03d2140b82000b0301c080c41c415a8010f0144448203401d4205e2205 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 402358129 1250 402356879 402356897
    0xa05060601090b090a0504020a0302070215030a2703050c1608010606140c0c040b0a09140a0c05030c03060d02062101080f01020702012307050604080a0206160206070f030e0d 76
    0x6076a00030032003002030110910560410750040002030300601e00b0310070f20740b19035030000306000214000e0b015501450340040100070f8101c0301da0380700d121503802118440242840d141030b00c0c150544060300740c0c03140c44010328480d0382d80c09c4603070b000d88140c0e0002905503080d2084801d000039040b162a841800342001800100f141407914402900342220052400d800b00030038840c44071200400039554007460707412103008c50000c001802107072030100c0c10307000000d0381402c012080d8169101e12100c0390007008100307030401107a00108000c444a00042d10702e03854007501000030a0309407400c1e05031040c2890000b424240717822440c010000c51107118801404400c0d93f0b607030040002280a00801015200c184002e624003005c60340020138481030701205c03480c0100c14105065126141030240c41400b58000b046030094200303400c3c2400190464103481c00144a1440000c038000d100d0218111640c64680040c011500c4042003a5400d41035a10204101a542e18031400c0d0b401d030402c903400d1050802e0b1189910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 402359379 1250 402358129 402358141
    0x2090c0702010f0e0622051017010905061305040812130303060b092809020f040806010b04150e040e03030114090a11043003030b011704170702030f0a0506 68
    0x9942092a906000f1345030034a07005901c0703420440d0803141800c500c04403080607400c075403a0034428681009410400d4414404512908024103210341414100441d07110380c0e031848104103565088640f41d0300102c403041d100006400c107400c166009449140c6042c01c180c0041070300802808112000c5001c10b04100d5418103140e054450300300a40803201c5003603e070803040c9010030f0712100700e4274180c9190f00140306a00c149030320360401c4101404c0c5020043d0741c2c40c154040d5810b2650080d0283c168a40a640000240d480c007132001c8408840c00300300b42c5001c44141620a50341145216021030708140c81e01c62070b2100d03050520066001e400e5440e60300060114a42c24401148001017801e102c2e18944035003c10601c0c140e206072421901c019401140440d0001c541d40c81408600b8800480c00350850181c0301007680542080040c5042a41c50310203003482001d442060203130a41e00074208020708248001d01c00074043c0280740c80c40c0094101c9040d1503000004629004104800380c80980040d424804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 402360629 1250 402359379 402359387
    0x902090708010e0c0d0e0f07081501141224160c0c1401180801021224061303020901170c09010e0f07090803120a060807060c1103030702090c070201 65
    0x508000d0501d840a070943c1041020f40e203030303640a841c6896144000c01c003048182520380001030602c0b05207040e660701a42c256039061392031490340554105030040400680d056030503001503504a49500c0c074100c01460810080c84030100c094840c1600360b008003585140401e61150714004580d050781c01c028020f00e40039610301c140226000785801080440c400403404296599611415141031034803e4003801d116800503604408421104400d00c1e40340311002800d43c0040d800342400808001090500c0e5942002d80c184100040e129034486560099001c4141d0510074054003001720707010344510b4069120380018800f49001d034407048102088c0c2c0c41d80f0302500000c0c0840d10325504c0a8a0840080d410207804102121005004500800c010b20020701c0d400d100300c101034002c11404054903901d0003202c0040500403012100c042d1054105100000e40c02000180c000403514640e444800c0c404807992420070064104442a501d0b00c401c0c42054003682e6200c14180c001c80100000c641d85203400d10000d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 402361879 1250 402360629 402360631
    0xc0303030f090c05060307050c10140601050405031005060f03010f1a15030c0304030302091305060a0e07051204080408060c1e0a0905042a0207030201120c1e0c15090209 74
    0x845980d041458800003d000d54400c0c400b900c8044401075107a1b0390b9104100c0d0103000b8114100018130550038284d0001c5100e0380650098442140c1030b1507565681801501d151242d441825055030010b1400e0345000a150312050b08a0801400740807034071034100002e42920f40d10001003403410390340c11070560920008603562000d510240e6280306602e0201c0821401400014824511418000001020076107c0d0b070407135143c103a0081a000054062892100040c0ba08450440c050010048040f80d02e4100d101c0c898030805030750343c4141c0303040301e151070280302108064003c589800c81400041000d0800b4080b4610880090041035183d15071100351802141c114124101506e04c1000101c030550703800410b010a86109a42c0410300d03a031011054400d429441c515040304004400c0c0c51400140d020035a201243c1c000d83c0c030b42c40f0704000102044200e400a0000602040a003a600c00c41c4900c5280300e460300d04900c0c201031100d259180c94142c40702c074540c1d10b4211070b140c0d210080b904601d003d00c910303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 402363129 1250 402361879 402361901
    0x1a0a0c1704080712080a0807031107080405040b03010915090201120c0206070f0f0c06092a14060c0d0e011701080109060e0f06010b090f030f01050601090e090a02040203180a0c030303 80
    0xb28000c80f20503103545e5136500c285840d52041040800004050601940000c42206804003c46907034490b0703400d14410300e420a0050074803507410309035400c50310328050107003414403508808200000d15043c0d40c03203c010042c50b1012814809008405440e01c1c0c1c0a100300300c6c0261141c0c02030b100f94946410001e058565505c200d60500c04107a501c4030795180c2c01002440460b078040b20000703840189040281480054913508010000112400700c1d5481000c03613000d04a40d4900300406071080c3d0541004a5402102c550601e04d0f40903a4002c0c1c92903102d580b54a10340b10041c1403000400c00205580c01e0302120982001041d80c0d1294030045c10043c813442414410070303040c40900301404003410015120341c81841018002d00300480d541c9841d40d20680d843d110a00010201e4440c42450030700c480c0600b100f220841d01080303900000103284035200c3c00e158811030400005d403030b070031006a00700802900060b01d40082c0e04080035004229074402c12810381c02c0c9016034200711042c0d2035441c009040e02d044000d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 402364379 1250 402363129 402363149
    0x80d0c030605011715130e0a03090f0e1b160c081203160e030c03101e0c08040807030207050907021c020309010228050d0801080c03071a0a0c17040807 66
    0x46040c4130300d104018030780c0104010410306003184a41c00041d10030f840074803c1c1c10a1a01d0021a101c495034009032450586d4800e0301d800e0141030751040348078080d50141c81840340070f844000004111166907080c0074075450743c0b580c440c1d0034910080c00001d89140504000c88507036080601c244200351040252161021003018860702d903180041d151031103400100455000d018940c000514030740c0c0c013402180c054200190840704d504160313001d11000f03005565101070503a00c0f40304040b490150b1034054941521465254000b080d00c41e5984c0c085241d010030000d50031802081000f00d01c0d5a90456581d01442c41a0f004041c5207841080b0b9104480c003403481e40c002d540c810401c010a40e600490381800000440b00c40c0200c01465191810012104900c000c2550041d003821240c01c0b50443c00c1541601d01c1001250701c94001c90301410380e2804640501064001d0100191400190540050250003420710301115010050783c0c503010f8000e85140c80140c10076001c80d003031081e2a02081032000030241904 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 402365629 1250 402364379 402364397
    0x171c060515090d030905030607050d0f0b150304140607050712090609050d0204140703090c0b070206030f0a0207020409030305060111160b2508040e060904110418080d0c03060501 78
    0x20740114580324003030b581030040d21004060b00c02d160150084a00030000682500d05030714215000811940c042031280310107515100c2d402c2115601442640310b0f00c08040d101c65100501107007404c0d282d4000800403500c6c0100c0a0280100d01d005101c201d01504058541913181c3c0c110f4034006030181a086598000c10220740410042c43d50301105070000c980c029540c0044c0e8129034004500603003604036416070403850f820280207802c3e82c90b9002520440c01000d14881ea03039114141039005214000c40130350302c00030510100346e455401806041e00b11924001c01031410b40c4540c041010340305000710982c0032a44d10000c0081c2541c00c149586015020100a450314800c00d4202000703800140c02803594420300850b94020301035803100e0040660b440c440c803c1c1507021b000d1030100c0181d4442c1c0a050440e01100001c2130044c1040c2410501456000b24a00340344500306003400000d050800055622210020f405c00c0803900a60003003000d049d040d1404103511000260240a603440359024074104681c080d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 402366879 1250 402365629 402365659
    0x110408030a1e170c160f0b1501110c010f1704060915060302011407020d050601080d02011118040f1b0507050c0f03060a05070903081909080303061804171c0605 70
    0x1002066021440105140d125a051480748552041e2840001c211a40c00c0c40c071700c0c1c00c1c400280b8840f807240b640f4408c2e42610588142c0110340400d07002e459400f065104100c0b544856014880d281d410705401c0c03a05000203c0c41c610191525841a40c0580f0400e03526540b1205012140300700149051002d50148000c40c07460303000900203a01c0f100703203203000d4034040340c15400c65951070803014030542c004044542c10358464031000d4032000340b0048040950b1070a4945640004803030f0a440c1142808803014640540311000d21002d800e10403540c041e025a10f80701c1c2c02c407205c105602c20303040811a680c0c90b5100c000c03d2401501e0b002c40029540d100302c1c054a00f401042d41c0006502c0e80c428210540417880e41c8998400b52130442185c0c00c01001e0720000700c1e881c610014a60000451040c96907200a41701d80d5903500540c03a44000d03500e194111486074160300c540c80c0342c504030340d810511402d01110f002069948207070186e041540848000300004d081035058400601425024080445520700e00c00310071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 402368129 1250 402366879 402366917
    0xa0e03130506031b13090c0c02010c02120a0b131a060609060706020702030303040f110d0209131104050c0a0212040e0103020d02030a0b0c0307090e010506030a110408030a1e 76
    0xa200d81c61080d0300000006003410819818900c48543c8240465259999070301d545503c40c90364000e8015503441d20b1040305189200e2010040b1076601070310b0340000002e982d0280107515081c8096410b49108141e02980011000320800748104103401c41100100030610700b01c400c1e40c808452030000c0c50090001d1020300c2c1d481c08102d692554040718040c0d80c41c90241740580c007a000c0c0c95170180d4180804401c10044c0716400c09083c101512039107842c114071081e0f800f040320611081300d0282d0010000c3c0000340030302d001c100905207050f00600e4490529510240014140c400c01c440c2c07500c80d40c0000c100029203d8041105040c002241036a141c01d15043c007503180c5c419801403001034420820f405000341951001d0201c20034041c1c00c405040c04a20300884010100c2d4010b03168800000c5804d080061000e4040c5d0856050310780040c5010b00e145c4600754060040c3c040d00c0b444400500040000246510701000200342c5509691a103060035958500011440580605a80107010290b03521500708506 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 402369379 1250 402368129 402368167
    0x50c0910020c03121312020a0308070f0b0c0a0c1518080403020a171b150a0810080304030f060e1f050a140118051b130503010506100c03030e03071203050a0e03 70
    0x90186d803c0101c0ca580005816000c00c1d920140100c100007601100b4032030400c450501481c09809000041e4407135844061030b034070450000350001020103c00310002404421046e8078900c031448040381d100340341c0103a8607031a032881004803003041d0005420002c5040c2403180400820010740c1d07408aa0007041c100e1030300c40f41a8090420081090f103000c04103a03031007d000111030403403210f81644031300f40e8020103000d4090546000e4100451b0410010b212080003040b502602c0c0d111503c51036142282c1c3d01da0000d00440010f49209002d60140144602c1c040c01381404810b190950105180c01c080020008640b518021074116161080060184944034003150140b29210306002985070740b15016421003031103040300501c00144c0041c500d80000f641100a42c244e6408600811203a182c0c0320401580b00000500c0c8000300d2058041100032a000754403041500c0b048005407072400b18103641d150008071001c40f5140c0803071394440500c89840400c3c40384220342d02d1f00c04000c0d4549610140e52808502c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 402370629 1250 402369379 402369389
    0xd0f1d0a110d060c050d0605270c160803040b01090903050f07060605041503140c09010b0a0c050d0903031107080619020c010e060f100e0109050c0910020c031213 71
    0x106000002600b41c54150700001481e41043c0b08000820310340c0c1e402003807540901c403550441402d000300415545009007100f0005447c2d03040300c06080d0b101030719400d0181f05c0100041c001c01e2040c480590303031040035070f4045032451081c85000c2c0d0701c1c42c091a14550070041a08962240b13803500f46100006900802100e403c03c0e4619409611000d15140c614081d20030758002582003410707c07103069101501005a172003981d129240000407218848481e60340c4024020307509500c407003040c0040200c3c5030450024900c004040c5009401e0742c4c050745401d450110340305048000142c0b5581d04000303240e07020050742451441c07000580003c51070003c40b550b540d240a08640e504030b4400341510010b0640354100c2d009580000028080c442c144c203440e0b82c4992040702c982c42c001c125440044c40d41d03090b01040078192009100528600d908103980140200320040100072018410400551265a1131160182e901c101d98006e00e220081c8000341070916102c1c004914240744c05114039400a01c1c00d94041c02503036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 402371879 1250 402370629 402370643
    0x219060e09090a14071a030f15360919020f2107081e030f0703090b1314040c02030d321b07030806091005060d0f1d0a 52
    0x20b00c5840c0c42e207042c084a988004d08140c0e00c41155a0450302c003054001c03c0321140c500b05045011400d8100d915480112501c5496102c1d0400041a1071214044400f41450203040760302c203113034a40c4401c0c2070318040b00180e081e24030400740c3c403131018100c031060542d004e0740b10009031070840d40e04881850100e070052002846001010071070f4025484000380015031201301001d142c50b00180448181d2541e400d80110b000d035004212401c1c1640c4043c9a0f03042a041003d0b0055240415500100c109a00118800c80c202f140c0c1c1d440004140180700042c06801081310614800b4034500350030100c00042401800340283d09008000054580100c19264503a50303004020603004101400460840a500140b850311300c1c02110b0694a50b0720200414810070110020928003440204019554014800c000b000030720841c0c0043c146040100310207402c00c0305824041b82c002e440e28001140784d0401d0140120850303940c042c4129500d11801003c0343c006442d20900180c032511025107443d1095031801420b40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 402373129 1250 402371879 402371881
    0x5121213060e0a03030921050403150b0a030302160503011e020d06030206220b0313030f0905040f090506132315010303080114030106061d060409020d05040219060e09 73
    0x807002a800030074410b031035202519210102440c0141c01401e40309015100710021000203801c1c20008282810380c0c1c2656150541071510f10b964004a22460b2080b071038580d911150103402c561201905500070b140b1a0700601100c101e0220014001c204661056119038100608881880440c5244c2030006444120140c1d41d603001c80c02031000f6141680c0004c1d0000710014580e6050000c0ca1110401015115005001d0380d40c1c0c0d1803031041600058039101c1d9108801141c5000007401909001220880d90510306100c640e240d0004049400c0318070a0100c0079104c4141d00100032041c404668005594510581440c41e15210110f1102d09501d035907999240c00513010b4000c150400021640044640c2c60408640e10b918000305050000e00c2000b90496403032040c0c101c18038042c090201a9002c5a0703e003004400100400721921186480c55a04030904000100d04440280010025940806404529402c05106000e41803e000d502941c47d41270b9034800f8020341da400140c0100030030341141e0f25521 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 402374379 1250 402373129 402373133
    0xe2508010605030705074b031b02180903040602010b040207050c2215091a010f0806210105060109120c0902070804050301051e1f030b04030504030b1305121213 70
    0x2031280c201e41c070401c0301c07003002190061f4640b00480040301d08030080c81000744107000d0301c0ea081d40e294281c0002408a180348038000d41c1103090080c00ca864600080082d400b810340101d5000b0480401d641c2d801b207541002074248907564090107001c5128006640451411509445003602c821005010740c0c03042049030401c40c4035a1188480c82098880c48008104580055400610482481c402c1201607401c00d041c1d055811070801c5101429541038450040310151800212a04d003801045543d22203c03e00d1800c01002900200c0280c0c0b09042000158608200002500310171503a4006483c0c2510180c00d20001142e00796400b04581c104500541c07256114030b040d100030301070303500805e8140d8078120401c00380040c0d51800702c0171500410401c3e54681c0718002401800308070f1b142c1802170075541c0342040000031074206020b50702900a281c0142020380b03980c0c8101200c3c2d01920300d2030740c145100480100307001050140840c2809407074a1a8607290844c1030311800d0050040c45042c0701e000320586541 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 402375629 1250 402374379 402374393
    0x403020c061306080f0112060c09080f0c120f0703060506030c04020c01051b1306082d010e0601020601031104020c01060312050d18030206060d06060e250801060503070507 75
    0x100300402540d100e81542120780c103041002d2040c00d00084035640811184001c68144505032102c100903151380c41c14503200e610141a09160010401800810010b0011003e000c0d00b00309200440150003010716181c1002510180041e0420840c3c00040c0144c601c8040000c4d00303011640e0000d80414241e0f28400042d00f0031031050455a085800007035069005501948a03a2107400001500181003072800c07a05040da000d16421040d41040c080c40500a00703000302480369100d4580a070010841c0e101d000c0c044603c1032640b00481c7c00143d000018041b0407101608254002002e1005110542c903507250725000c0e203007103d4818000d550004005001d54420741043c000b0f590040d62103010561004d00c000c0c43c0da03003e01b03003154035071385402444c104107680c849000b8002034041d802859a038480004000000300004012a4115903075500005c1d0554900240c510444610b4500c00241741000d0181e98203407602103100e810050004018000550054140ea40080031803401e80e40340c424070b19040d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 402376879 1250 402375629 402375643
    0x414060405011e14030f19050402100c05010207020a0f050a060503060901030f02030a0209010e090717100203131b090e0604050d05030c040803120a14040510051306020a030903030e0705010512040302 87
    0x110300300d40004104281106d01d680c50f5400b4010440700c030712401c540c1203064000c8030f000750341c02503100100412810381140b1402002503081d000c0d8000610741983c5900080302d1003a184d12091640322100f10400c91480d0800c1c2c0d003c000c0030781d0b042562840c980980054140310050000400b00009a900c9406546040101d100344030f07400f030032079103082d40c4230562070340422804c0307441200e603203d500300204580d200082000b030010f034200000c1071f401c0c1d03e4294850280d0030060024203d000c0c0380d0480700c0420300b00c03e25202d601400c140030844280c10103660505590f5044006000c941c0a001403000041c000140c0d15490040751a043c1d44075142c4c1200044180700d60b82c050300251001003901490008400740190040e40d510404202002418000e00003004040344c010b07140744c00c034890008035103409810540e80304956004030101a451070307581c13404a81199824400003580e40125104154040c4241007001011070010a403851030140000c180d0f1040f58040343c0e4110040c4080390806008010030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 402378129 1250 402376879 402376907
    0xf1104060c063206120d091401140403060b0310052203030e101d0109030203040918020d030c0c21060e070f08060f07030204060c02041a090106050414060405011e 71
    0x30980910807011110f0000c0e80c2030302c4d641c0c030440b03100e800224105400142402d15450075200c4020540c80c20580c410140e03e0000b0b603034103000c0d0f20b0000f0714003003c0d5180280091446040001a003001d400d050515200c507003404610981e2a203414855940c9008102da02ca0710990101c4003101440c40c51300b1406061900c00c11425442030f0340b07a40070b419450303411845001d405c01004075800b03500c0d8040c150a9451422003c0c001d60000c02003800711940b0394000001148054000c24040b040a901040d040c45001360240c0c001181c000550003040b510f492a0b800920b4024600800034200e0340116451822007800184445c0c0d03070b011010f107c00418040c1c0c0c401007050036041e0252680c1c90130b0423a2146001c4070b06180e604040000503880901034420b0300c09503520780d030318140d051003030303a00b0700000f45200003485802c0c0d070000201840665661800300c0c06040740340d8030781e0f40f20343c0360142c0107d8803030740140454481e5005000611860740d10101d03036000c5004030b4605040100e80d400d0241e91007a000009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 402379379 1250 402378129 402378191
    0x702010e0913050c03010b0a0e1005180f06010c0507060509130e060106020f01090c0b161b060f0309260c030708280c1b1205010f1104060c06 62
    0x810902e0100080d030301c1000703401181660f20400c3c0712801c0508980004608507440f040c141401e01203e230303030104001c0d44000b486204008050f02c643c000b0350302c11444042d54075104400c104001c82c2c0e10041c80c1594002d00c0138248450b50045681d15542c980b031740c500420041010201c1d44510a0f6542c00c104044450440001c201001001020940b1181d00f40180390252113000303194030f1200707014410820741e250010044c600300c0d42043c400880355440004103c010418500d101070208912a41d0504845c001c412801c210601e0040050002c01e280c000d018189494054501c0c08a0990a070005400c2d0817551000c09800c00a02c2040f240c0c004c8494140d141d11000ca40541008252030050584620030381c9000911000d500f1101410b00d0202d00710710016203505680c10003c0c8110b2021156440313040d103d4040d0715106c110825961610032825a941d0391100304120030350003107206105515640d80c031050701d054145800545801003444004010a0759100720001c420f0340482d02c545480d0384900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 402380629 1250 402379379 402379381
    0xb0d110d020d050709081c03020c100504031101111207051b0c1306150c03020c030a0c0f1a040329010608060301052206050a0e1c02010501080601030f080702010e09 72
    0xd88000a4200c1d0040d540000c0c900004580c079140583e115000300c4d114100141883d810745021005400b40814100040c10740030320850a0202051000c00d4052085007000611032800c1d0500400c1040300d07074090704036a450720605481641d50442103a40c1c0ca0304d005120842500c540a080710980708220400742c2e21000707a440d8401e0031501190411019108440e58405680348202c100101c551a1040c908480c081755142e101c0c80e07000703e01c50702c500c0d802401501c3e4115900d01c0400d04000142e1021940c14541181c2408400070700140403020707003555103e00e0220b070780001c1951003074415402f000e0844480a41c9194044901c904005564103414030303901c0d1603503540d81c0003605115058a0780380c420b50800c00007c10f102014100e0b0030b01800f1152020241c40300c29207504008200142900d1906900e4114445000d241044402c41000106441510743e2520380002421140b06070030800d51504460010004103920303c8050852940101c80c0359650300042c40161158914804103581001c1108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 402381879 1250 402380629 402380647
    0x10e150307120f0204050f040510030203241530010f0504121404050f0a050607120f0305040b0106050d0e1e07080703081b120304050a0303060602160b0d11 68
    0x44000c2089020340041031000450149a1500740d0103140140d079003000101c0700ca247d441c80e060b00042c2e080a01001c401c2c188030340b42e0f004a41030035043c602c2c141c0680301a075030120300e614600c1707980c9a1080030508032011072208a000103000d03450402007480d10758145120021040d2403281c041206010a43c004c0140460388800c0c50b0140000320303003e17075030103c030104003000b898000c400303541c05030300b880d21b03500d140601381030821945841510385107810005a0101142c2600c40388010840c0902038288000d050900c510300801800c00b41c40c00c8820141040184030008070340a14141c196061400c1540c1c40d840c100350b824000f040c54043c404250f12810303581ca44481e511201d0642d046502106039086a0307210000d103561441c0a200060a5000c10230400700903036a41c48500703070315000342016182c0c0503040c4400400a50010355083e250354000c51510b0040641521600000380464000382103014880382401a08960038464480203134000100c070724180542da4400c60f03080168404054503082c1c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 402383129 1250 402381879 402381887
    0x1804021804030c17030f0f0703020c010203131e0c030204090623010503060907080709020708070506010e090c010f08041b05150c0106050607170d15240e0f010e150307 73
    0x1d41d83c2560084681e8229407100c1c004402142e104080b106101d0b41c0c15150445541e1341000000c10030001c15609100c101a086006e00055010700350788a044240700c0018100b56810391510388483d41840201d004035000690080d80100840390115000a0b14403c40e08018026100d8019a2000b55000d1210b03502865100c1610718143c0e4010760440c0c410340d64192945a9480c0350380126916540600420041800160000c4c01514403d4450b1070130402240c3c0d07030910340b80017078100c80004041c6408219001d0400c100c0104a8802440c244140900c0b001026000c03401c0984007814801c10380b403101100e8104031812100415015008442103030224841c021503401841c0c21044950820710000303000c1c0381c000290b54515030000078240500112a000904a500407180700c0f1006803502c1d4042e0780000100c0420000b000c0030380118100c07a41885620510030070052a01041c4010405a00d40300d80351000c140f00984000e003042d441e64400003001131074008a14200303031054100081000711880e44 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 402384379 1250 402383129 402383147
    0x60f091e050603120c0a0b07050406230301050d0c0b0315090124050a03240501080f0c0d020c0304030f0c030b0f07050a080705130b18060405180402180403 68
    0x40c0426240180a0000e20900303a80d01a00c0c600e078140e020300da8008070320b0b9402c0010404010240c04807050760b202659030041c0c107a0222040c0c0c02144022900304842500044582d008210b500c103080c0e50356088044504d4a40010700a05000c1d00e5924040700404c4440b5080001808000d00c1064492411001c2c101701c103066000003d0088140c48000101094603201540c036074080790710b030310b00600c0b088601103d142d0010b900803000c0540f2000d0080b0400310300c0345405080c0301501d40603000c16003400009040e0301c8019043c80c0f00d03010f003002044580da0391501624400c4403140c0e400359803003000ea19034074610b00440d00040c0031648103440c03200c10024140741200c104d0788500b9040c1361554614180142d0300d1011110338010604c01c10448040901c80d503030480d441072a604200307080c08030079040d25003240100c4e0886503d4090002e8500c100201030800240c00c0f940403a6007074502405c0a010840d0720040500e03482c075424200000c20210341e1800c041100340e03941e10500391320303501d011f040080c00011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 402385629 1250 402384379 402384401
    0x10e0604090b09071e05060307030b01021c020a2a060f14030f1017030a1209080304050d1119020d03210902010e01050c0616050f0403050303060a14130c03060f09 71
    0x2008540c5d0b003200c000d2200d0100440303030010006815a0355849040d005010040c1c1c0190441c0206a000c0d900602100c07500c0414144c158024180c0184500d008203942c5120b80f004440e0407200030641d500030140400388416100c0c10701d80348001405400007a103007041160301d04041500048100300300503031580d07210b511807101d5603900702c9176035a143c5070006148810700444000b0342042150039513440c06150100c0200320341d940002082c9250791a50300080c3c006031021503441e08040604440e40d03510100c00342400440f9406401e61883c1420180741c200703140c500c001e010b1003a01c0a01c406150041403100000110b041c143d0b80e0110a004800004100802c800ca02007110050340c4c518a521a10540300c0c80070107503004010946a216040002072400c1c10380c6010030600708400304c2003400d83d8004d8401107128400854072418505d0402411400d2600459000c4801a1500a40f0760b18240600700c0150000f10004101460f1841100a09070380d0b0850000301400210001c0c40d40100ea02500800e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 402386879 1250 402385629 402385649
    0xf0f06010c02010201152315180310090302030d05060916030e0c150408161a280c03030501150503010320042306040e06060f060d140f0c12010e0604090b0907 69
    0x1c03000e004101e181070b0403089030b08d46d2040c1844625a815402070103210141c400404450913a0710b4104000190344540c107080700180c0001c5402c80040b615400b034642c101c401160326a425250207541c10484841d5249490700700b54651003d00c040c3c590a22900d4000c1034068030b440d19240c01c0c040c00a0099215101d620b0407031043c0001003015600c02c42c000b80682d00302c000030b09901054100380041d1504000d11041c0e0800303100302e5200b25082d0b0354200784540192501c400c0304065035420040e00300c0b08140d125406124042c44800002c6521000b100d064942c0803140301e1b9001e00744190020300752010030f580d981041ca0120350003090b645244002007000c404851040e49070f5070302414030050707440c043d0720000c00340c4c824008582c1e40d180444410f9031010001d0101401d05915060380025500202c00c000717940c440c09c205000310101c00030210f90f80f0186a0300c03450315160400c10b4411180c001485180c1039007400300d01081559032242c00100405400000310141402c01110030341e1600d00d90721500d5906 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 402388129 1250 402386879 402386939
    0x9170d230405151902010c050304112d0406050d121b12090e070f0e01030b03100908030a06060507080301050d1a190c0207050a03110120070e0f0f06010c0201020115 72
    0x745c814050081c0c1100c00f0340c0e6140c02c5481c5e03642e40382c401d245c0d854a031940c0f00d040c0e030003550032242032883c01c10b03403482c02d98043c80e65000008050008542c09d40d0403c500810154901c40045210a84032401484140c0b40081c425003aa03640b003251107855010040120312000901019250b0104510b005c0d9000034509082e03640350044140c4004004421a401141612642c0140c47d07001e13503c009a1464050706980c03401d03d01440f440f088855600d4204d542007004010b0241d807900074440c06001d0005410030520300341003901c80110358081482024490700000303841900f00404100304c034141c25003e06844165040100041c140c40a64002c0780c4920303072a0000c000c4100b80300040003001c841021340000754040c00d584030b400041b1220f24080781848401205040c075502c1440005071205081c00c0684441424050b10514110010f4406501e041501052007452440801d242e500720b502400c0009080e001440140c0c05000003248001c00c0001d86080000c071201d0051040032007603403a01d84d10b049 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 402389379 1250 402388129 402388177
    0x30f09011523010c11090a0609020a17100303080a091a04080c15060a06111606050a0801090504020f01081b03090d0e0405040b2406030709170d23040515 67
    0xb500107040c4000d80010807185c021040741c1032500074150000300b10040800d02c41d84400614060380d00c58100c0714001480e001459986c038805000c81c03034020043c0b01140c403a25185840080c03d86201400340e507a500d940354080c500300010424843c1031740b41b16102c88007852406041c40270440d00b0405c10a0507600480d00180100d40742905010312403400103100d1040c59042c00b8040303e4007040d030300d8401c070b0354440d00704803504580c0c417041020300030029955410f0b40d0701d5480c0802400002c040e801a001542007005120043e0340d0f2141c60a0310000c2803a00d6101c660740d0a0040c59002c944481065259200105000d4265404a8040e03e2901540c0310040b80e00640c1c001d0100b02e680445000c0c156a00724800700c1c5490b030b2203841d000307801701c098801d00d0b0121150100042442d482074a03070b000440d00100040001540074402c0381c0517889003101400720104580c0c0b01500e45400c10103082503000e4140940c18040070b01c48182d1303010f002c0140414805503080d8020381016400320320000c0030a01940c00d6942 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 402390629 1250 402389379 402389387
    0x1701060f06080f090a0b0a09020301061a0406020d09030807080304030e190906081501050d1401050a1a0f0114030613020c0303060405092a010507050f0a0201120902010203030f0901152301 82
    0x41700c41d48002002c1d029038400b240e02c030090001c0728040380c0c1035413904000240c0302528030000310548200e070440c6603154541940640391074020011002844507100080020440e6403094400458010100990b284d07510714040301e0303401920742d0701c6900150807100800c00c0c482d1008403c069822403101041003e03201c4d80c2055a41d580d840070b55903501440c40050104c0d0400c1004684500d200310902903500816640a0703081d140115034038080950703240b200c114442242c86d00d07480c40300019035140c20352111507030008140b110401507070764400c800000401c40380c0c0c450865406240414502c215202c0402101352034580c0d01c1501c210744a941418041198a0008a6201300b078000691b80c08034607060109801700c20801c10000c0794140001800600f020039800d0004d200034008580c050710b070b040110b20001d420f0150305500710402c0ba11705000f10f00140d0f0000112034003d11603c40390400c0d90b0360f680d10180940040324010025204041000036a2540c1c12010705d8900101c5010b50003103100380004407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 402391879 1250 402390629 402390643
    0x20703020a2921041101020d0e0d0b0711030c01020d0b1f030c2a03020d020d05090906030111070c031509150e01060f06090608100f1701060f06080f09 66
    0x4a001060703141c1c10703500010a94014a000008143d0107802d500030340d0840701092004540944890b051000510140e42c0d042c0101d108030034441c24070001d251840008aa441e41d82c244e002006081d11a01003502c0900507040703002c203180c080c411170303545103007482907075020390007454842040a09050721994185440d00520081e010041895010660b1300f085c00c802504910036060248049041010b004418165440e803070f06403a40c4800c00032502c2403070000c0c03414190900303100464201100e884120b65101e003c41d603d40c8021aa54441512440002401014842c0701e070040004c1c0051418108a03046461071b048071b020b6110514440c50307418000c000c1d40c1e505a0700410043c3c5c40e000c01d2505045c01d50260704103246c400300006007943c0303c000381080b2005030341018003c03034000b440800409038041175882c0d005d40a518081061840c184e0303000101c1c0f04a024000c0000200b8059104d1258258000c80051425246a078501c9a03030b03070750184c1040310a0359142074042120000800c0d1000005000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 402393129 1250 402391879 402391919
    0x9050c1203090904060b06030c04060e0d020303031b0c0d0e0909070b040902030403050c0d0201020d15031703070203070606090b0a090e0a1407090f0203070e010807050304080310080d020703020a 85
    0x181d450044680100100c0040c01007003101d4140e541c20504046803210380c003461007000f2080025503540e082c014013900403882c000c0098800d06c1100f9814006032004030940341c101e115a0341705410312201e0703502c0a07014054a00c2c4546d0340e1040181c2c5004850b8008140340da01c010580c1d00781d50707680f1001d0020344c0314071181c00b03003c4041204000400006800c0d03401180d00a0080c6403490038070064541003403c0c4407003018010b0050303401240300c0081d4091481042d0000b510702e00050005455903a801a21f030329044c8856001907400301c00200308078000e108680e100da0340084200f000720f846420190040070446030041c0908681c2d4030110f021050344c4112118210100000c059131240b03540c7c2d40a4000315030080c81d205004203c030004844a140c007030107007140365030800075881c0e140c41e001c020001c3c0c00c2104500d04203c00f1a0900c102660084100ea03005604410015526035440300c0441d84045158032405161055001c0d801074964049044c9065074800c03520710000705e580e00d01c00c5240755100050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 402394379 1250 402393129 402393133
    0x615020624030a060915020c060c0a020f030316020d03021c09030e0a08061806060a0603020c010b091314011a1207050a0b030405160b0a0509030a1509050c12 69
    0x101c0d44862041400000018000d0142200d0650410100307003040c2101604030350880e2140d01250400041180078164100c0c6000110b0910105040310b41da5402c0c003034a5031581c00000690840320130b2081c400c0c0e003400c90424013140e640b42050074802034050351801c0707608010700451503180b41a5101c3d000b01c2d112491480d110400c90548504034000034030300034400b182840445182222552500d41d4907a00510344074000c1d1040e4500012031031500c164424241c07200e508901e0070000581e861340000f0080e5441d51800503101c0c0300e041015801003401e005140ea011900303204012505c1c01640c6182c480611408000c0c2c0500c003500c064030300780c4003e901c03207140d03050350b07040c18802d103003014070083d8003071040541250040c0f60741300081220055590069031800d01c0c0002004140a41041b044c0413644c01442c036180e02e07600d8107031460b025009100c02e5004000d000681d00f03070700760f6040140745c04481d0055a9010100c42c56011300c030040034442d1040b1520300451040f44800d207000c0c20082c2643e051100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 402395629 1250 402394379 402394381
    0x2090a272001052205091006090f030b01060c06110f0306030d020105070e010c03122406050306311410060903020a150908030c030a080105060913051302060d090606150206 75
    0xc132441d648020703c4008048046103280000341503660310105070240040c1c400864900c0d007800401450480c094202e1012120055000c01c00a420050300b2411100d41d4038000b8901d8a03a0b00d40380c0d0150050412250090f00c0100d017041c0b860140000450044408a0407200030a82c4038105074241c800407900203010401d80101442c05500403030080001c0c038817900d80070041142c030300d1000c404c94441006070b80504004201d00c01c0200403418661000d440681041c030300b5440c0800002e04200b040c20648045550007807091907a140540449400071382c1191414072906c00c440d0b680040c0c0ca20200c4104050807404080040d60b00d000c1c500c03070404d13a90040d02903402d282c1080c1502c0c0c03058004c84c2e928400c2243c80400022441014006410007900c2d080141d541d440c0070020040c900c100c180c221b588942000c00c0310a1792070340c6d00301440c4032181130b0400214065032401d407a08002c003180f0344040d4121400191034407003180c00c1d91040c603d0300e00c0b84004201641d190000030080e0602c044840380541d100c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 402396879 1250 402395629 402395647
    0x60402010809100f0902010f020a1502070611030a0f060512060c0a02160e0f0109050919020102071203090807090509030a1211040303051207050f0702090a27200105 72
    0x141000381d2012000c0210b07101e00340e00d040000300700d40c558011248000c3d60342d1021750856074026180007a10110784014045c0300b0203038455120740300515038105102d55000803684200316007038101c0c041d190340131050300da00e0f860680704540241020400140300d4520784400401d0b6032506000460354916098020403a80d40d500305100701551207084480c00390301c10400030340c2556400f40c8180b005440000015a55407c0030180010101410b0b040100d40e2410038082040d403010000c1d000e00b0440480d803c0000d0700741030f800140d0406489400540555042022010a042c0c100101804580080040351076507941c2d4074144013150703030943d0240d50b80e81040001da4601c9114000b500d4541d4540d41c03002641c40900765090a00f0f42c0582d008030085040800e2a00c4e400b0000e15045510000c0c509040e45040d00820390b8141501c10b190b4002d01c9521a0310115080181c2d50f440110480c0c0c40302c40b4000c501c80c0319041001c03070b0302400d5000c41d445030302c4115548246030394002c05480080180c4400341800241 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 402398129 1250 402396879 402396887
    0x60a15062001021614010b1509210c0307090e0d081504051503011d121c05011205070b16020d060f0903030506010e0906090a0e030403080c07141206040201 68
    0x246104000008140c041c902080c28401030030b0340715129031281c8034010280780400050014001940361a45003039041e445a885445e800c191220a1640381643c9001e0030340024020302c0301144201c101d034404d401e0340356841c4000a01d14000344084048400003990781d4800d500703640060140110540200c010340034240d01464145801807410248009803205007000f060846104440421040180c0c8510001070b00703003072003401c1460304080c48003101400c1e207001055640503001010007405070700180d01d00e07110510b840e50303a1010b1034924050040d540d41300e40141c11042d08041c02c0e03c550068003400295000c0d201d0803240c101105404c2c035005076a240d02044209800c10710103035401b0340c84241351111000075118003c8040d12175103002035581081d000040c03031150600c0c80140141c11510900c041680d4821503950f100304640c1e0007081d140c060707101203030440c06198001072501070046044100c0140100d030310815115940c8540c4400001c4a040140c940803245c0550030350741011011801552003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 402399379 1250 402398129 402398147
    0x6152c100e18010207030302180f010e060306010c0209040813060513060c06020d1404140102070f02040e12040906090b060901120908091c17030c040e10051011060a1506 74
    0x242d4034126150b05005030646080ea8032048007100026070000302c444d221210000c150240520a0710b10741c0c01c1041c102e00182800249108492044402100040650303101d80e81500c61207038081c001001a040918201101d5004a524901c1d00f0010f0074020541c1d0f88500c0c00d40e210012040f045424a51400b0000d0700c036915a28030a03980d098003040000b06202c8203000b001650004510498001d00d49810604003504081c0c20142442e40100b02e040042218041d076240c4482e01100e0019122209802076480c121021114161400010800060010240cce000c00c0131565442c030b05100540070107040244511500152501080039031411500e00c003101d921808080e071046200c1d615005a9600144c400c61080900014451a030103d000c200501c1a41d8a01100781c3e0490a60441c104200700c88401d020b5406403810010242c2c00044140300c0e000c070000000c040161045500c2501c0540041806008801007001c074031401000c1444a0305921072101c590f803451a14001207030500710125280c0003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 402400629 1250 402399379 402399391
    0x604090b010b0d06241403011d151f020d0305010506160611030108030901090f060e15040306050f060f01140f0c0f010e0f0d0801140103020706152c100e 67
    0x2a45480114000d90318541144c050f010402d80c4517002c0c00d6290004040032211404c580e0010414801003200d28100c0403c58841c2e155441400c91690381d0561841d0003a40300d130f0382d003540b08008140c1c42c040301c0e0096000851510f03c9a081d52441e4481036015410b5610a115240c0c00c06420490480001220310074041c5592040d000881c00707101500c40c0034075030340007a003003a40e8507080007415458035078104601400400d800031a08142c103107040409001c5101c02c201960007500705140110124142600320340241d6401b000800241c03d01c0d81a61900315800c503101c0d03005140e033350300e01c8a29600914400b840110494101843c140d880300c0071030b406400c071400304c1c400c900c41c3d200d0150042d03200303000360701c01060000d00500007400c004400501d09840b2440f00414845900018481c4980010110003100310a08000da990406460710000802e02007200243c0007522030790215290950886070340d014400c441d420401007250701c0503048484001e0f9080e024821054900708030f503008412809078060 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 402401879 1250 402400629 402400631
    0x10509090a0f050708010f080c0604030303020705120d06090b031c05090409020d050a0b0f2a0d02180907020102090102030714120c010f11040302030c010c21170604090b010b0d 77
    0x7000c07003608180c0f4001c1c0da000d00807505517801032140120080301e850080108400030821070f80640045800e6102e6804041c0404d03400260001c240081040303108507a026184c0c501d540c65010483d040d00414407401f505408500b4800d010301c151074002a02c000c403544460b001012030740c11180a031040c1d8403150103582c0151300d0700200d0700580d0f141010700c592540200060882c5000c2464074940482c070081c400c1041d420070000348188003066034402d00034000070a03400719040000c03203202c3d021400b031100c91502c268000100011016004180c404010800341e4001c0869142c0300d005900340d01075696100d0044c0e0007070043c2c001084800c0300610258658804ad1103040d410341c00d000c1d5143e405040c1c0000365a44480d1019009401441500d041d800d05c1d001c40340c10310b425580060b07102c0707803540d000b18108111075114006002c0b182140c0c4013108903242000c0d14100c0700740b0010b4100301c0704d40301f0341400500d1940043d01d9030905001e02c076450fa0744140b203107442c0c0c0e013811803100e401c0e000307620a90a01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 402403129 1250 402401879 402401891
    0x504060501032322050f06101a031b04030f02010e0f150906090409030f14070b0109020309280201030609090512070503070b0a061403120910110115170309010509090a 73
    0x5030040300360350380015000d10080c100541d40070205c1b900e41070018044407450441d410040200d4212821406401d444448400e56251124079511595101380719640010000000e400010084503102c903081d598801e03240c00203040d60761340400094a80c8220319076048070640d52100542c1210b1801042d50329801011213040400c1000410221844070500310b01003981651404c03011a00513075100400394404040324580801a5502c080c00b20b0117102c1d44185a4010000c12107c50081c03000890b50740d000440c0402561400032180703140001c0020580c04130b07103064008640c64071103028040a59401c40020000355031501c1590074142d0140384140d4041c002407100e03074001740007051039038002c0700b1444020407032505140fa1540c08082c6440d803180710340c3c08022104c000c006100141d81c01041c00b124180c05a0398004030a69242e040032000711015460680507541c801c0c0301d4070200c2c00707541d110301070508119184400c80b83c0d24802c0c10442030219000f0702030041180303400314100b540704003000004900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 402404379 1250 402403129 402403171
    0x10020d020c061e0108010b060702090a0b10050d0b04050c040b0901051e090909010b0f011107050405040b15030d090b0901090803030403272304021207020705040605010323 75
    0x101001515000501403601420f0a400408001000d000d000c00200810186208100041d89440b0f0208001c1c05010320030001035507000c0e0340d4001c0110070380207460301da104802c901c8010010351048402200c03503131400c030301c0305090700741841403500c118203a2019a21701030410b0706040c41368100c864030b1410041d007005480f01c4044c80079a5440e500002c43d881c1500c6a54060030040807550042c80c90403681c0c0340641200260355040c1a41000b0318082c203000340c6280c07450103040d00744210398120640013820581804108550481500c4c4038816031440c83c05c130880c03000d00b01620340b414a90200005007112b0b43c248000302010000b000c1d503c1050415051099640e58640d0464104030303004d9005c0f40d10f0b0121001d41da6054400500070003160b0b01d902050500b030140c2d84006c1941c40301c29036501c7c005c2c442020840d0300c0741c1e1304442d00b0200303540051000d85000d030b200a40d0b07021240241ca00507030400b080016194083c0c029031490b4107821156513850008198544820000100790020903908800c22041e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 402405629 1250 402404379 402404383
    0x90606080717070501170a0c021905150705070209040b060103060312030b18240f1c1509030e0d0312060605070b01050d05071211150406030c080910020d020c 69
    0x100800b0400081080c5104803199141030204941c0541e0500c03400614010314000a013421a9002140c2c440000b20482801d0080b890f00f4004030030b90346250b420b80c44080601030700041c5403910003000b00f141c06050781c030008100c80c18018204000d401030b0844000c2400110040c520f00e0f40144185000204103130743e82c580c1c0081850342181c140c00b09503600fa000a1904210b210407168800707820701048a810310075403a62400b114100640104064501401c3c0342e41d0fa11800c9a02041c0014111040088610000d913002161448121411003044220074040000c500406a8a90705500c40030425440300c010b0003008600c0c00011410849404800a240d820912640001e015182d0300c00303440f1611803400461143c0103800c1a4441d0340d4508401000440003d9160180c1c0d22800134061a0410741c0f0b02446002e1001c3c5110b40e100c00c6110340d013290016160040c0044500b250350038084a84a850b056034a12800e03150b10321a074010120704003130f20502e078006100c818660300d001490480351080c428 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 402406879 1250 402405629 402405643
    0x281a09092404110405012303010b1203030106090801050403020a1112011a10030629070b040f020f0409050705120f0f031e0f16020402070f0b04020103050907030b0a09060608 76
    0x10841d59041041c0402e20a0032656820142015036007000a94103104000d4000a50001505000c0c0340e90300b0506001d440a4000d000701c24405000b509080104601041e103035002401b401000601c1d21400048903501402a540903a8040e0050100003050b038541c1001155a051400c0e048003a1455078036690303009100e040700d00f00560740c0c0c01526980400070408540041d000410405007032034000d015243ca02c500307000f400851203120902c54919880c4e15001070142c2c440241400810108000900c05462418090140300300c40039014403c6983c204002c442e0145006001603000b24402d218608202d0100c03020f14441d94100da40e0192610005464601c0c1201d0010440e0004124184048400240101401140c8504c45e06200c3c5101da604258000d24101c98100010085003000b503440d01e50403583e08039044031103a4018249801c04500c104415a001c0340002e180400168901d4808115581900e80c80701d03610080362150041030024000c2c82c80f00b40c0b0b0980d52502d001910141c104910 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 402408129 1250 402406879 402406933
    0xb0f12010b01020105060102071d090f0d030b0a0f0b090405061c06061a04061d06090406030b040b0f07020c01030e030d060312031a010801260303281a0909 68
    0x4a0002041d000090968030054481e13410743d4084071041c000003c90300c400e0300500c8140443d28070303160f450f03040741840c01c018000215401d0141780000b582061f810740240061010560383d200d00b980d500c1440d0880e821052091144400091107091441e02c2c1940000d174006d580205505640364442184014001c00f02c44100c80705035607403408100c0101c0c404004c0f85c20101c00002281090325101000d03100724a0f08820651901d5902e92040655507001d0558803e188041c1c4108a03003030320303460304403600d02080c0c800352039841d81400001d140702c809400b41885130303100e6409451011500343c0158090038510010240d02d000a000d0305c0603100d04c1d4851640214050401d000c98903415140140495500242620344484c02c042c0010440c1d8101308a103046a144681d800b4009105c0092a10400104218008a03010000c14000403480c4d1160315084410f030300310f44104c095841c0400030101d035035440308a040c00603645150110f61800104807a07104050200356040c903144040c0a51601a405842c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 402409379 1250 402408129 402408131
    0x405010801022104121404031203020a0e03010c1d13020f071e050703020d030c0606090b0a0e06090a020f040e070c0b0112020d0b090102040b03100e1006050d0b0f1201 73
    0x451112900d8246180f00325200700010300034509117921914020301350880041c0034480910381902c41040c042c0e04440c000c2d038011004001ca07100080d0300402952008180d4000220307040c0e80103903d0328040c41510b005450b90386032100c49090000420041d00c682d0300342a6444a241075201400000500041890602265035240d46480038a4841617040072426001c0c85141e015210344001040040c401d0b064a404031445005040c482c80c04440b02c241c0c61500500b4039080450018002d102038205104030401202d044c1300c2240c980071038900e0104100c9805921562a00100350307038070311075801040440045010f0515164481c9500580752030195402800151140321880c144080e10040074058200301c0c01082c208031030381c1c00041e80c2c0d1245050203040d5010300800f081c4c5800d008d6041b1030042010203101600e13481c01060803040b0250b40d2292810180c03180c00019995031094003d00700359001d80c0c58007402e01c64141e00ca5801080c03044450b40c2c2100f8035240d4004c180c1d81d040e608100306861400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 402410629 1250 402409379 402409387
    0x50c0726010e0d170f060d2103090210050a050313020d0804030809090a0c08150102010b040c02060f0a110f0703030609050408130605181306030b090d021221040302010902040501080102 81
    0x82c0080200303c8502504030004130001c14040c1c100c6001c200c090700018226000c00064049050804208220090081c801f030120304403075400b02e070160480c03007415000322115800e42d00c0c14181520188100c00e07030380000850410000b004541b18001d6100c3d1a80003414000c80341e0010395031100f14ad842038009692800d000b0aa4168510380030b0341e541c0c1e100545c08018404000700c401c000d4040c50001c1c02c80d180900401449502c507900c02d41c00351100e101c0003030080c410000c2d0010f010303440e80c00684052100d0b0808900207000800a80100c1c21083d100780d50052501d0080d400d441d035135401000c2c08401b01602d0301c0c400907194000e07014940c0114060f000881d80c4206880c06042c0c0454180e000c28207108042c400443c00307020100c001341405409403148244184102201001007080d03820041030000300c0020300c14aa03900084440310f0202c2a021120a04458020034100b40142d081c1c40c0905403074090800b106d45400540326070064400d0001007807903403084c1d000409840c6c0981250085a50100d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 402411879 1250 402410629 402410653
    0x2130e10030c0321050a050702010509120105160806030d140a050c030a092301050306010c110d0305132709031106190b010516020609060d15060f050c0726010e 70
    0x2007544c4600f540d443c10520701e4861203540c080c0040c09204c00103414828003054035134480d2525000c3c03100c0382400b032008005501c0d001c5062801c1d0403105030f0140016101100003940c1e4200016007090058264880c60f070607074000d11800c103444e0f1047c888802045002e1101d001d0050b020005031030b0b546a140c0360311180d5820101e004101c0002c00003513500e001e0031000040f070542d0b04501100e400c001d007031034000c1e0040210b05008841030503d019094210740c060404c2c6092540c4a400351200034000181134a44036601c081c0c100402e98442100c03072042c50074413000d1280b4881c07544805201446400c2041c20466800700f501c0c20301100301c034011031002e032803080420181c07107520860700c1020f004d0801324200070403c0004c01c0ba201c60108020300501d800101924242d503401c081da1498000d602c418000030005080400c0241c11621400021401c07003280d11080502540036545208601c03c0107040e414900100c03ea1005401e480007082c0d010441e0720f511080e0000c1c0a050281c0415200406e801e84d922 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 402413129 1250 402411879 402411923
    0x4090f050a0c0510020d0e0111010204030f080406180e01090b041b0903120f0819060e04080d11070213240609030b01051f110c1e0906010302130e10030c03 68
    0x24030101411500043e46101b02603400850006980c21b0a103084d4444034074003125980203115940014002410000e02e0720100542b0400070701c1626070701d59840b0301445d540d819494011459000d00c80d0f40920020040c08540d045510100003050003d0020130503000d60801c04c0a00000a00c0304000070744411070500910002d103000c5040415240303000826020301c44001070222038080d1402c01c80700d001c6c1c071050700d040410740c020703001038001c0e00350817121402d240c070785902d0592151003030800d020708001d0f041e601400d0312020b446400c1c1e005080e00d004001c240031400e000704402d0400d48150b9802090044428604142d880c02408540d1101c00c00b050840c2002c94450405900140c46601074142904c08011000110345481d12036040000d601c0c143d01c1c5006003090710081e40503410a9a2603400c41140b01c201c5402603805030b06580704440b0351a100c0044003a4840c540b03c4a2403200d00c0c520420000c0e10300c413000c2ea80400040d10035420a5240e6640c008a68103a03402561402d03100c51481c240c000709 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 402414379 1250 402413129 402413149
    0x911070c0e040b180a0809060d02040e0106113d02041e050f01020307020108070908030d0b09070804020603010b1602030a1a010b04031a070507020a080102030702010b0402031504090f050a0c05 84
    0x20f2445040310b8603421851554840401000824032000407c04240d01e44415041d0382d0354581031182507455a8486c00604200c0c10300344203001c0003031103650811107152800b203400c001001600c2c400d10814919146c1d0704079407000700b0300c8110060b0f0f07102c089060526110320141015181145500440c8415400c13a0300224540e6080140309400450710b1551903a00002254031540e42030801c100e0595500c0001e44804840b0340c80750f00c542c0130020303c2000780d081c0c4e40d006015900d02150700340840d4450340c104541e039070740132180290410000c1006200c01080740024005420305422031607000b200741d501003420308100e0407040700c50200d4440d14550181007600400d014150f894041d9060602c2c5032038007140f151000403201143c180160204410f18450001c40d0840c98001c2e01e00c00e00d1583d90700d2041d0007980126400f0005500c0c00b0215216403402c0d000301c80c000c41d0061660490551a41304110092450203c22075001e0140d40c1108000b4401b80882c00e00b860040c0101c070f4485d4604000c1c0000044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 402415629 1250 402414379 402414391
    0xa08010b1201020c0c0f06070b0f10081f021b071829091302060c060403020115030305090f06160b04051009030518120714190e010911070c0e040b 64
    0x10060004d5a0041000500c5600c40d0000b244c549400c40154004604140300e4100b0181404c0190310030480d04202c049100c60040c00c92809441d1039079034400781c0a0301c072306000106045507409407000190002030750b0058040c1000d224032010f000e5400c88142441d09059a1140c402181c07a035403030082d501c1e0b02d40b144e8401446003082d2005290001036500610380d041103000c600c1510f180003c1031041400301a00210039a01511041d910481018083e64a0000b12801c600540c00c0101100484180600901c03c580d0325031101801e10b4500810040025a4103109130340104051050f000c110f4410703605254003e00550603180c1c00d00b000c1c1441ca0810806ca4090b0040b24180034000f40043c2d40902181e40406071128018030784400e02000420100c041075094000303100d00307140890a02800310880b841c00034115a1200301d9844000341c0307074201e0350510a4403c9409601d0040200405039000200d6010720041c041d40340c10030b641e940c41c4281c0c50680000246400c14800c00c0104814184600d802c00c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 402416879 1250 402415629 402415631
    0xa0c0c060513090e010b1e0907020705030a02010c050316080a030b040203060d02221506030b030601031a09100f05011805090c0f040e0a11030d05030115030e0a020a08010b1201 77
    0x1c40c60003030702c0c01400ca51040c440382e0f642c1d0349500c5002d500d00b98005c0551041c018600034074102d83d161690348001d030300c1c000944523003c8440843c4110b800010f500c0100c40015001d80041e00a03500150b60303400012505403418081007243d94011602c01302d04280042c03082c90030540f1881c007001c0040c22142e2226100303018074030400a1100661f0342c884201c020071360444102031000c030b10310001d00c0c250071141c05100c803070b6052002041f08614010034080a0b6001035400b003110b60881c07401c059885400b0700c400f4003840b40010015039281c010039215580302402604403911702400740c1104040b1103042c8801100156540d0050200410010840b810200004014000303400c00c016140c0c1c84c4c5003000304481c803400d0100d0480050303880740c1d08150740c516814003d03201503400908040f140203518541c0c0a101e03020b6800b8412107076000c1d04c1580d068030243c40016584420040040d0001c00030806224100d03c158450070005a480c14400c1d0054010300001182c451690740174007540d10603d80c1456211303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 402418129 1250 402416879 402416887
    0xa2d050306011221051e1c0209120c0d0b071b030c030f030c0905010f030603170405210325050a031205070203120c1e0a03020c0c060a1b06020f0a0c0c0605 68
    0x25a20000391948111b8070f0b101d03503021101032160803a0b684a91582401914104001440c00f1481ca0b4081c1022140649001c0d41d2220481111034480365080e41190340281001a03a4001c02c00740e110541c1e0048440c06c01418000c1c1c0103146803461a8550000c4001407107001c102c20415600003641100d40600c0d0800b446810a91307034000d00148014012203040200103a407022045200743c200d10011030b008800c0c81d2000d001000c810050381e1242c015107020f0251054205a01110b020566200c400041d01640c14000f0040d4414103a1658040900c0002c00708840000481c40904c1100f140c03622a890350071a1924500d40701094542c028280742c00e6400138000c080200e454980942d07441170701902055994084a03250b03200c0c0989400c48071440010108001c140550142c2c02031035400404000c80d054120b25004000d15489148114000141c0741200c070010507010540c0d2100042c41910054204a08114160480d4021410000004640e95031074800d04c6840c0c06100003904c1176240403894 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 402419379 1250 402418129 402418193
    0x6070503130515030a0e01060b070f0203010b0907080f0a091a0435030912040e042d0204021602040e0c0108010e1509040303090c06030f0b0a2d0503060112 68
    0x903000c000c100440c6191101c10781c18420346e00f903200340080d0980c82c0c3d6003910341c01907081900d440034901108034040c0d031a0128402c1285000c0d401d107071046c07086030340d8460290795041503550000ad004d080041895141c506010000d03400850303885035000003043e9a490741c5001d0500c0d401c0013002003803004842c00c05038580103418604110b604441040d550a0340d030340e92035000f2420300c5c040d000c084407d0303421404100401c2c0c2c1024410042d004600500c018198403c8084030300b01040020b8500c0ca00c14400400c2d0000141495006091200612a011000e1085c960045829034104024105954101c0240406030750303045070906002d007540700004860740c64030b903155081c0c01d90b0101007039124451100c00502014400e030404080e295200144190b415a1064040c01a00d00030100d0380c00b00d410800d44c121541070003500d0714115001d4000c1c0301c070900b04003410641c2c052140800f00600ca000c0420118080e142004914001d080d1503540b80040320b507600700184444a4800c507000019021031000f89 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 402420629 1250 402419379 402419419
    0x1203091b030302060a181a07020f120405011103090a170d020c03030702010804171201060306171c0c0b010803190c050d080604020c190318210501020405060705031305 73
    0x15200d05c0c0c10b64001170744c0e844411000c14200302c10400500d500c10710500d100003d0010b00342540200b00079002c80303050001c0d0f0384086440b0034106980d1140d2040c244420000c640c4104500036800c401d01c8103503442c00c2c08203404900c0c4d000e140d030844400c926058248011001c020006500306656174409462607490520000c3d0b200c0c8507030040681004004800b240601007480c3c0d281540101da0707400d081c3d88482c81c0d450702580990912034000802c0c0751810018485c0c0c0e65041103031090000c5806000e00c90414a101740303218481d00f00c40c41c03c2110308504240001c9048845902a003490070095480e84101429852a950107403004010030903402c4041000540006801000c14020709080125940300c0012600034051190f11200611410500000706081600f14404481c026605d0000716090880082e450320154420503107040d414841050b102004201d071a4082407081c4000340c0f605603140c0000e4242e0304002001c0c2e030b994000260581e05950f0f641501002443c0076a0010000c40322240d480f1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 402421879 1250 402420629 402420631
    0x6050d2f030d0e0f01140313230c0301150803220b0c0c1003021926070c030801060206010609060503040602070c0303021510030b01090f0603020a0b0405030f0601050916020a1203091b03030206 84
    0x508c4002440e105601007101c1c00020700700038a8010103602050b215a00c0b41e6039200006054680a54030703112050050b02c038030030510f0040d01c51074401903162002300d1000d019000c04c45860007580e071580130404102c042003000180040030480c1c0c010200b48094000708000800384411140505204104124540c4803514100c0d0001c0348500b80480a0b41030300103401c04001d540c00609041600180c1007002154112240b595000d0082d560b40b5001d81e00d0b008183d0b40c0342004e0041c00040b030081001000b40620070402541d006101c2c2c8005420494181c0c2c03031685071180354100b1009600002e8100c0d00340044039602c698005c0000030034100c014038503242c0b03680c101810300491010544420200312540001c3c9c200000440c0d010b04040d2101d96610311240041d0000d0240902c00d0095004c201d01089000070303400d050311001800c0b5142078440016070070f0b9400780d07901e02400390f01541c0d01e220080b640c44010020b5050031502c0209034030340c0714601360018004035203009580071007003203050003c60f40c001512 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 402423129 1250 402421879 402421891
    0x201091b1a130b0f2d16021203070c05030d0309030801031106070f06020a02010f150e04020a080d0305060f030d0f0305151201020d06050d2f030d0e0f011403 69
    0x2690b103048044407500d944016400c00412180e0006401c03144020030001050051584200b1241d1080003080900241c00049954001c5080c18014403405408103400c035807109100402040440a0010165056401c4008103075071482c401c00c1300300620f003403e011062614aa500d02040310398582d80d00541140010f01000e0b02480300160454410780f601d10858070002c0c0c11580d20030052a40b4505034019510200c20b5000550070002510404030141c090070845190703002d001902c06050055540711400c1c010816680160098000609401e046c44000d4a591880d0b4000c0351034030701801400f1842c160148480d00a6000c00100c244040e4002150f020004803898007040c0f9485828a0403c02e500c00048950301041c610b811614445c030540c000c10214100b071400780038040d918020402104030511014124a21a03541c18240e03080002c0703d9001c4089660b4069092540c850111749020208e05091010585079580c030340041c034080392040c07034002e42440d00d4590700b943c0d41c00c0c9648500005e8a9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 402424379 1250 402423129 402423179
    0x50d11030d1403070e0a0504020c280803060d02010309020d1101020d0804030f0f120c09030606050604060c030806060d1814010b01020c060702180f0f06030a1109060103090803070201091b 82
    0x10480315541b42e0440500030303c00200103541307401030400643d0315803c0702c0034100c0501440320f0202c541201500e001e150060381143c000c5003107640e00820701181744007515040741015a640394103801130360344519411440740502000b442c010885000a840e0000c2c0380c0b03680d41444002c004020001350300401500d1250741307030f10b840b00d04412200f070190340c00c00b040404144401d00b8081400081c95001e00b18000b2a80211010300019aaa4083c8541407055006000005100310302e9036001c2405600041e41020b4080d21191801d0a81e442010071501d03000b0b451540d100d81da841803010300104505a00c07070003244600030080081990000b0303541c0c0c01c89812042c001c490214002c4199600c0440b0710003850142c0c949a0040d141500e1001100e100c120384c8001c000c00e00c000402e0581c00d002803c0d1404c144d00c0f592580441c201c10040164116009001904040d160300700100060b141d2340146014035480d400104905c03590740350420981c1c42d54111310a4242000d10100003140506014110001003500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 402425629 1250 402424379 402424397
    0x2091f0b090f0d03200f0105060d08041208090a030609020906010f0e0d0804031202300306040e10060303031508010b0a0302090718140a0e0402010c1b050d11030d140307 74
    0x80d054600b0980c1101412045c066044692a5443c01040e1807001000d620002c001da5501d450411402c6045000042c5c0454410312080c8881242c50440880c068005d29403142042c1414002407400c80036a04200c0782542c40346100c0c01181440307100d0700d0704a84c09003414a50642e01d82030051501c5e401490051140c0d500010081c01d00c280a002c541c0a180c00460100c4144c09252020b995001c040c00c2c900e1642400c44e8142c0000290087d80000d00070072401070500c0e40d121001040050702e01018410700f5805440140014203034648240e800440c46602c010495840e1810304803800519540800140d03418202490f08035542c8800c0710b815654110b45588490300c1e10f8030206c0304250347d0320900d00c85518009011074641604d10485c89241c00031030312440050f8840414207e101c10a850080c040b0b84042071010028030b60890580d00c9400c864800104207549000152800b9041603003905d4030780856003958230a00b8280f2510741d4000380c90604080c0060300c059000c10600c0001c10180411071401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 402426879 1250 402425629 402425633
    0x4540b1806010c050a0b040b0c03010b0405040207060216050114010f120602070501060f180f020a0203191103040e01090605030d021002180604060f092301051602091f0b090f0d 77
    0x501542500f54100341103501d10300c0c092600c1e10281d0b105803000d0700d078141100c0c006045032880000304c82c1600c842503181400d0502e421b0a110182d00403a01c215030094003803007035101c01c211191040d8081405200046010000180000780d01c0d80e041c1c104841e02c98500e00c0c01e100c201003030540c103a0500c1d0b01100040c0d40d4003507030402034014200c81d00100080c0024040c0010091080d40905c0c0014103c2c044c100400795040010004911a414100002da007050000b018110b45a42619040c0099800d0041c032900f40b28402c1d90442c2d111780c0010704804071900c0180060b0245100300030141c80160001d190084100c90065900c400002d100c0b42041d800041034000915032201142e5107540142901e512551195400790044882004210000d04200c50001d0760010000000000201081d10811304407420001110305501c66506402d050220914070300058450f075503203a2203142801d44418485118040055a8803065402001521814001c004480c0d45518041c410074200300c621703007109a024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 402428129 1250 402426879 402426887
    0xc040c030c1407150507050a0f0507110907020109230f0105060a030213090b150102010f140105060a02010212070903030f0c02010e060a020c090a0c0306081204540b180601 75
    0x684c485045508081c10b106481c0c0d0442c0142400703401d0750711030010000110900711030714014241c010b84801c1c0d51091030007041c281940d1294018903d4800810300100390744840390b00034400603a04141c0c60f07002100c031492600c107000c0343c00c6901c16100240300030700f405000503600326250700000e0310522080c40b8020701b84809070f0000c4400c0d540401180014505980c40c6170081020302e03d0740c0d003d5400c0290041c8250858828040e840c7c08441c9000d015900f490148815030300100c0050303007590740c204a81140c880b82501c84510a520998801c5d00c3d082c11032400412001ca0070b440300c4284074076000030200607030708052110010390060b11600c1d190180b42e4007c0b480c00ca80307000358030b8004501d501804803080058101212111080d01c0c140415a0b030b80d103d0565a042e000c2010080300003e01091042d0481c1c1c50f00c01c0c2140001840407130842d0701c456000d074048110703010b6201400b000c0140c403a000755030302e0206a010101050b4100001c003441d0010880d90001c0554181c0501900c40002d0803580c02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 402429379 1250 402428129 402428153
    0xf051515040e07351005030312190617030408070605040b0304080906070b0403030e0f03040308070b2a0711010f0c060f1d010902090f0402100806210c040c030c1407 72
    0x108030300c1e80c42004000120851102d07810340e0b1038134102c5c1c0c2081001c02c2c5030900004580e0300e4a00c10384882e046590b21071001c0b0010313680c0052089050348666000400782d000d8010200034000d030001079540c4525101e5418540030340c0d94090300038440184020404e49500c0c605507948113800601460b07448903610b00144130342c800c2150003000316000c0800d000501d42c2c1039001c40d1840b2006411282e1181952030001ea50340141e02c00102550400c01848001503000e520407900a4010031a1032808289400c17540c840c0c054180082805502c0442c00009101001d03080064030b07a004c1c2420801110400d900501802c8202c1c00a8280d5413200090200040079030310844030078140d51640c0351012040f02074a4040c24030107405038840c8002d000841c0040b000c1d5a1803601556000303020000000101ca010f0b20551001070070540c0c068410441ca40111a00c100035440620801d0054115641d0070400c00c81181d404540180400d4a0800c444804503080a000d8071480c1100d02d1190b218486854081d204101d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 402430629 1250 402429379 402429437
    0x612010c140a02031c020c1612020f03010207080f1309060e070503042414010b090913051f06030506130c06120917190c23010f051515040e07 62
    0xe504000c5c80480b030000d40c0588248820881900c540c001128007448091110b0b0041d000c0422014404400515182494008005c0041e00142c1007540a0b01c5c0d201807074200300306040011400080c1c02c0c24601104000301d001c1c03d0004801c02a19080c10703c000e0000300020f241d80140003000001c68140f0941e60300c1000e01c40c4159401d40ca40d0050f079010700000d088005056101c004c405400400c068180c10151002c4d000d02502d0610b00e51b83d201200411b01000d440162214000c8000c0c00c001300f00c025407886683c2d203184601140311403662415a1a0a000510314240402c61090900000b400c09014200322459440d0002000039001501001406002c038001c05804900e6401740c0300d46220760240c0111003920100640403811503400340d8010748481402846261201c024401c021903200101c02c411485400000d0922030900b10a01242c4050740c4603943c9c413041e0042d4059919180100301250302d0880200d0381010f15260500800050140106090152401614002152100300d00301240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 402431879 1250 402430629 402430657
    0x30601030804051009051f0507050d030501180203060d080d0617060a0501081f0203040f0b0906061e01050316140a0f09140d0b10090e060612010c140a0203 68
    0x1503901c1ca403081095000c2e100b6035020301500e81c1c10350704443c00b0f1410a021104083c00301c9406da1003503000c144e182118020103006001062080c0000705108000002c42c4070740c01e0310000750950404040000e040c8010281642c0745004008214072034846005000c980c940c040c4a490315440070440d0b100181803070360051041c01a000c5522000a4800942c0700c2c042c20500200700641d989a82c83c50340c4560f410715250505040500c0c220100405030b500845c2d009008001401d0315079016982c801801006403105404c540c401030912038140f4104840b0300c1c00f41000d1503001c0129480c4400a0010300008142d0342c42031070f440f6500c0e8078150044000c0841c1d00558100141e032100340700c10103070100320520961000202030500104046500860a628120000b000d089072890245c0d9148039100c07004200448d0154011070001d405d0155010f003981c201c00e40409049545801c40074401c06034408421100345030305110030b00c00f400b03420490741300c1007a5000c60702c290381300c400b900c00384d28600c1411b1041002d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 402433129 1250 402431879 402431881
    0x9220e0102070803180f0706050f0913021c05010f033815031504080c1f0c180302060f03040602090613080c040e0c04150f060c1407031109150306 64
    0x120080303000711720070f400344100e00740c1407010804110356421350080050601d6001c4d21081c020300d4001c0010345008000c40c041c00780b900543c500440c107540c2a0302c0c108a500c80d0082400100c00201590300d21403c0c11140e0704000c0c41d0b1420601c0034a0589600c4050180d20f00d40248400b040c45000b003542400c015086e442c902c081ca0b40c3c01c550200c820848204040303880a0503500800e2402148182c40c0f680c21074244500c545443d00c0b02e9000e54071410742880c0030322800c50950f041240b0b00b4503041402c110a5000500d403030315540050442030301c5160b02243c11114910500041c4d40e508141d0704c1545085c84003d0701c941d110310b0040c00034410000841e600c95000b11341d00d0b50550762400d04c0c00c142d9a01101f9650014480c009100a5408000e140c03411030300301951130700301c80c1029802000812006d80b000030000b41e50307a100000024564010000041c003010003442072108440340c1e011800494402810314901d9030b10749200b03004403015614890f507005030102d1503d94081c1e0b50070410341001401d841035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 402434379 1250 402433129 402433133
    0x251103090339030a03031a030f1f02030903181309060b010f020c030a0b070905041b08011d01030308040309050909010912030b0102070b0a030221150609220e010207 72
    0x207485441802d04040400e9a403140c81c803050700100080550728050000c200c0e0400702d55090b4041c195900510b40384144403400381d955642e007000301d07040342c00d40200a01a0580204100382400c0c0e19804003140e0a030040080c4541c04400008580c100d4148039500047e58807444c0014000030301d0940002460340c1400a4141404103580c01894040c109827103070043c03030301034006c260b8964000380c0302640d040c0c003c00c81c6c0f1404284600c20180d440190f5260451005880d5800141202e09003c04c10b04011404203007400c0f070715041041c0c507015100c1c080b6074981c0e0142c0c152b09003502c410140402010861a403010504050040801d080130b094003c0804850380f6103002418000d11820800f51501c81001c40003c460f240244210341000c201039000e0966641070041c04207041c1d005400c0001050784c2000380d010003196445040079985810307c1c0d1505203003040c01031080c0c1c0e1004c81c1601d620503082040500550781c0d40541c0b81c082c118131112070a900c1c20102c4103000003804810510207455000083c0801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 402435629 1250 402434379 402434413
    0x70f03030906020c1c14010e01021b0c0a030803150604030210050c1e1506030f2505060f0d050612070b090a08030702010819150b0408062511030903 65
    0x10680b0302030341c200d8000310344460030410f15043c3c16005850014601c01100c0109181e6090703814220850000811307030301030030228582240d010040b01e0203803d14074041010921010700188a17641c204480c51722030300d411a140c5860fa4400603000d9001001500100003c0c3e41b20f44007601c00440e001000b02d20140702c00ca901401a900c034100d450018000c0c0e280d030320201075481c074012035900c0380303203004180b00b82e180000021002d1010308a0740c0d1500c900f00c200c820050003009100e40034082c9102031410408000b001c005a00959000140b00ea0030034824012803002900581e490a02000008207898a030400824080780c2054080ca50b540910321000c01c0a91f110001810141815200881d03810313551801e480d1079002d100300c000d00090090001c103062042030068000500302481001500c101d201d10030083d440381c0eaa203c0b40745400041002c00c9900c00902641d540903400c500a0303c406039000035481010492080d415060000e8108942140d40c800c005980b138500029049880032450882e00d06 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 402436879 1250 402435629 402435647
    0x1305060712080a0e0c0d081b01090b0114032a0a0306060807050301020f030606031f0801060302011e080402060c100e0615010c050307030503060f06070605040506010f030302030714070f0303 83
    0x20001c02d916401150381c1c03005503c01c229910001802800d02c440300d54040101d60b10075150155840d6078103101c200815681c00e0000c998030134002c400000c0b242518604500140416444525003d01c01c600704402620040b40c5c05014a03000b81d0b101c4620717a0141d1640e290a510b51007403d0300300791400c0c004410448aa400401031310071a004a80303180751b0350400c16090784100241d03291005000e00c0842d000d030600c80081d54000b62640820a071340600d40131041e66000d096400009582e468040c20025942c1001810460104080881040e00380245001c2c00c9414082c000074094400081c112111400c20f000c001d00e01741c103400301488500c0c1e501c06019942c07082a90801c44810b032040b45010b07030f5809541300070b01c016404409181406080d48058800c4d0300f005100a41244000d1081130301b076a162001821280d21840c0005058180350070490324010051b00f004115802d00b6505101103a000821b4810043d4004202c1e0b05070000d000135141410490751040c4500c0020400210415800c58250 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 402438129 1250 402436879 402436913
    0xe100905010b090310020c0321040c0608040818150417100207051b010905130c080105040605130b130504050a0b070e010c1112030307030e0c100206060613050607 71
    0x61240d662a0311890445200d000300781d541c181d011170007101600c2800c1d0003a108440e408810340707040a1000010b00d40298462040201480600080208100d43c0c22025405090309162400c49460103980380643c40c032500c40c80300f84162800002e840c95554544028404158400d0145d459a80d20b4024500c0c880c8071501c10b68081c0030750b1080300c40381e5000b8801d0f2014140c0201c01003407605045c05903c513503100c01041960410541d8000464180c0f2500f00f050021006110001000c032603480004110b80c9046e00824072480c10b11904009270707901c0e47c0c00c41c0010340540100007401c00c1d60b000080d6500a400c21004101c82c144010002406004984401182c0c0651502d4180c1c0e0b41d141001c0340c02d9000f0381c2242d0302140b81241200080b50518608041408016242030b1324800703130740e085a10f943c10850700a00080c0d11068061074104052006100c20780041e980110114885c0401070b4645030000c103c54003440d0b021812224141042c00c0620080402416065403210315007007451403d2880510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 402439379 1250 402438129 402438131
    0x30803270d030506060f0a1803080720041a0f0a050301230c090306040b06040914030a03110c0c0d05160b0a030507180b031b0f0903010b01080c120c040e1009 69
    0x130501d0408074101d40405100e80f0f00c907483c0005000c070658010845c19400a20082000000320000341c3c43c030000c0c103145010f10340402c68001241d821072120b18a0390702541c007640c281b441b50180d13251101c400c91031200040b9801000c80308040301166141c6010f5001541c95801c0400d15100214042c004624148030074000c10949d5623815644201841881c00f0190075910910008002c40c4102c40050b40244000740302140100c511b403904001d031100c000f01000c4c1130300005074076100e581e0948603040810354030710045410041c5650385644c842c080310300e045015038030302d0103281c5c00c201007130080200a1482807141051603440e2100c12b20540c00c06045c1c880424a004041741c040c0d405001054000641da01030240c4a9003010046000c81d0000707040107000440e4101c880b14600c003100d0250a0b12201c9901d00c07030300e0313900ba00201030a450b100d44509042c42403000a0007440000013003154400b550300d00400344551580300c1d80300040e108076484200d005000c0e4040c010014140e9015404407080110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 402440629 1250 402439379 402439381
    0x7060e190b0c250309121703130b0a0b0a06030e100905012a090f080d1110060e0603240103030c03020c1003020309060603030f2512020708011107020a030803270d0305 73
    0x842c891070062000405003240e40047c9075003c401884000660303020039504d100c0b420395a500d40e0341410620003914a45903480d181c61039043d40c0d00381a00c60b18028150740c6818000701081c80e01e0262114855a6140f040d00c0d01d459a4100703120b002d4110134001207000d80110a14800300a0500000b43c0543c0100e0014802c03030b00014001000c00f0908090318984000340c1207a51400704195585142c9a5008125002d401c5c2c85490001891041d203004103207140003641e081c9403003002c250900c4811030b00102c00610a854046a40e884000d0301da0640b903042c10300c00c40b21503180c20103900e4500c2921140f41d000000042950b84c0c00d5141c0c02070350003a00b0100c1142d407035840f44001c160b16401242e90032014400c0602c08941c0000003c40a00001d030040e150210070074200307403202d0710900d48000308100580c1c000c640404c1698000d104903e00c03400c59155640c203000c03d5030300160700d46100d407102606020000c808248280c0c8146003194500b248006001b00078a42443d9440d2914103103425100840d103072074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 402441879 1250 402440629 402440639
    0xa0e030f030a020a110f0d1106160f050c0102030a020d0c09060206130812070c0b011e030303050403030b030105150f01030207080d150909050307060e190b0c250309 72
    0x1500e204210008009007195100c03000d0000940207564848100020380c070640c90111802e01000d1816560000502441d0b0200e413405480c0010030291040d46600107020454a4009400500c80e03031400e43c231702480055a039600c1255103008243d40440c01e03520000600a2000d59980144000c2c141000284008208600c1c199036002c4140b05610250300a0b8000444444807404407642280c0318045450400034140841e000c2c03c0300450b18040810101d150841c18851490503084c0103081c1480481150000222075075080a01844000d00303042d02c6001082c10180280c111006545d0003400802141c5005504843e00d1441c20406d40d00030b03051566221901d5100e8001c84000541068080d0318003481c05000000501103806203098120070060049001d446a003d070180460041d4000c6885d003c0c28100602290300303c2c1e0524070075520020b020f504c208940142500b42d84d0700005178a141da950800084042d100d4078171000d4002a2098030b0780c0c2c0c0d030a00c00041d002500d0007641c6da440050380324 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 402443129 1250 402441879 402441883
    0xb01060f1715120a080c03070b0c0403080a030b1c030206190b060412020103020f0703030e0c060306010c0b09010e07091506051e07021302040e2509030f0c050a030b0a0e 74
    0x9403084520b65046010301c2c1542d0400b0180f158600701600308485004116803108450340d04041140452074200044083c144030f42a0407003900400c00401c428640740c65595107110f14402c00d00840145130f214070416030582d884c4480d40c1c0c595086600c10403d5000b892400a48508007102c2d100e0040760f440c03120144591052083c5101c4200142c0094a82418050728102040b0b1503403049040540800560100501c1c02c00903000c070702e10a1702c0100340880950401c500300020741c1a9940101d00910410882d6030b0b000c441e101815800451303034056030b29100703180c502400003203050841c507200301c0c040020301000c564012811071685000e43d29100ba141c5404a03681d128546081e15032415601d1003411243c0058002c2450074030062000141604082d80041aa04191b00c0610760100c0c1604105a414504080e881203010030140c5002503c9203c0380500402c010f400090511610b00700e403181001182030030343e805850014620314441d40d0301d01c1c01e500040c400300c802c146d5842c01e01803076030818400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 402444379 1250 402443129 402443131
    0x515031b0a03050d0207170c01050a030e010f1a010e10050901050310090f0207020405360a08130302032404030e0607020406170111120105010e0d0b01060f17 69
    0x4000d800d50150803a240841410080c148581c4034107004070000000300c003000181030255058000d00501c1e45044102c0c000071090441c0149240c0080c60b003031401d81c0c0d20004851400059003400107c807000126264010030326400c070172101c0d51510320100d01e8403003001965550054260780e50a52840440d0500039654248010840800e40611590700300d503000c3d0000e07591054850036001e85255445c50140c082d6200d108000e402140e0008420003541490700541d0390007028100600d07411035080b0707408a01c1080b02030710310015420000605032904c00a015180209801203000c0c3d8542c4006410715200700a01c1c80128800c0c4500c0c0d44288080001078070800148203206180650350b91a51030603202e0000b00c941c0c240d4480710800c898401a5034074440c40b809411803103d1490303211b950010040c01c4030700e04c3c21141c4204005004001c1841004040503055813030070310f807002d40c4502c0000800d94407036041d08010b095218483c00800d0159011311002c1c010b00c043d94542583c181083c0b080401c1d864 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 402445629 1250 402444379 402444421
    0x40e0102091e01050705010603111005090a06030c020a02090f0f3301090305102403020307051201060b0301171203150907020c0d0b01051504050a030303090602040e0a090605 76
    0x32511a403412449402c49165149030701c10705040d49070a5455640501b15051030708103c0d10707551254003600703650500e109203054000d2241482032038259450001801c1107114411603081507120750b00c2001c0c0620a00641c01d40c0c2d90b025180708014104000d03c0e40310040111003140e019410840018081c0c0c0c06032a0f04921001088489200700ca1442d6001d942c454030207187d03505001c1d07400300000c00500300b004804030036090140009046a101444510002c250000502010211400500150750301040c084200c480489011224910015500d8050822079008402300d48010000103100f00e032601881c0780000e5102c0650344940c0100c1481d50041c0410303108545194000042034841e420801d1055801c48224011034078003654100000e4070b805103514040b2080072106004006a042c122550b900244070080d1b650309150418020036207540840c44080c040503203407490f030000d200865040780c0c0500110614032400740352151a400c0917142c5160100c03569454040090034141100014440e00c0c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 402446879 1250 402445629 402445639
    0x31a010303091208040e010b09010806090910050411061b0c010504030c0e090a060f0b180402150a0504050432010f061d06070501150b0f27030a060b040e010209 70
    0x40e08044043c1c2c850240441d0880300c2c05001c00002c5404951004182d0081c02d00c040c0c80d80d51440d0b040e0004119200151056000303518640030b00c000118041413010001090000000380c0303556034103100342c441210b500800e40151000540643ca0141c1c20030590413042c9032070031518403004030300045078184200c1c4006450101c8140c070030300c540d210b002001e5130015104c004440100002d034075480200c440521068084a6482511061504040c1c82036511403103075810900e00740c1f505401044e0204540032004182c0000012003441d160b0083c41503130040c00c00504104403440f44c46d1642e0b40600c503420301c040c0c2d60501c81ca600440c0745e049960bd1034181c5076207003081c000392882c1400c25101c1100c0780100e908910424243c41c0780316210300c0082c01500d8012000414505024084802e01e00708640007a0f0004d0410007070307401100318031400c07200c2c84035085003808603c40c00c0914000000040186147c3d240c09405046805c0c800c841c3c00425441c801120100a400c0d0b084643c3c500300d1082002c030075000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 402448129 1250 402446879 402446897
    0xc09010f140a050703030f2c01021908130804030b040b0f040507090f0b0409230a0804120212100f1d1b150703020a061a011e02100c030204031a010303 66
    0x1503100d10050100203200341004251112000c04017025110003001810f0308c455207040d502251841114403000c8260707084003c40c50403070320383c4e040d001e914004104c850a0143d00000b04200c84a110a40c640300b5400c072418940300d0340c403460500c10440007650152109007081022410740824a086103000715031000051500b40c0c905007281003d082401440001c2c1f0359200c3e441000c0d07440b580a42c00301d0300d01c5104001400c90546980c4481c130110082c0c2c502d066070010048500040011040300d094406100048d0800307900e61000070f030244840c142000780c600644c48440c0b40c1d0181504403540500300b070781c030a006010241c85400d500c000d4101c0c0e6207071a80d002621400360340b00500d4003000c165070094003460a18004000b0100141d00c0328074110010f80c000107182d014498644184042c103038400c0c0e9101110900c1c080002c0c200c100451030384140c684011060016540200300150421142500901442902c010060000c5d00306c1e1000b1b070341940c0300000102000c41c080c84424103980e819181e1000c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 402449379 1250 402448129 402448147
    0xb0325020c1003061a0c0601060c0b0415020412110a0537051207060f140702010318060513110a0e01060c0303200a110a020310090c0e0c09010f14 64
    0x8040d12129081407684d11000460203403400300d0b02646a0a240e200199602105000107150050581c007a42c00c01042c1003e11300080d00400b05590455082180003017215041c1140700000d02c15070f805552810740b260703164410800070030801072410324100da100c425140d4031010310030b845ca03036603c0c40b4282e82c41c0030784030075209995210b007094080b070094032002da803035107070004a0b81100000881210a80c8024006c009403a802103003110244c000d868160442c0122000d01101d500901100174140f544a2034440740f004002e00310220425080582801641060741030340010140c00ca01c240c1b810b6040c0c04101046042042001040755040302d80f4000c9a031901e2030072a090310f8114801c90405403280d810602560307049811504804101080030356031440742c0d80150203000c5000e4440e0040d0003904820016940120b880490028250b6022640c2001450f0028403d000f03078000240c04064082840780d84c481010240820081c01c3c2c0381d00e182c0c1c00040e1429a80b28202d1030380324808410400c500b1762 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 402450629 1250 402449379 402449389
    0x3231812190903051e07080a030906030c02390301050402062b0f0605040609090308060609040f05180c030f06070c0c08010f0b0301060b0703090306050c070b010b0325020c 75
    0x10040d0703031614022010603102e9542a003003015000d50840e44450320200f500241005100c120024180c030b00c010509101566009441c10381a0700c100818141d9404d11608405c0c002d021400c0d514041c080b04400c00a2110300759030285844000d40e402d82200e03a00e1681131070030305104140c011030b0020220707401d1a0f8402c1e0841d28550b841c8944144c21781d040003503009496218041c0d948048824134010900c0380c1031809010844401e0b0b4800c40c0d41c1c50600781c10902007034000c8101a005403058030420303615881c0c4000700300500080c01c0d019403c2450841001821001c02001003245e50742002901c03580035010080503614030348054528060341113280401e15003402582c007100c4803881804021960fa0b91480d03001e007115003c49904404680b81e04d015000c602e0f080c4078800c040c1016180240c14140c503600c00503c410380718040108801e585030085415258010140d0300c2d120f82c403818001080da104c0105190907002600e511180c52602031046100c590010221215640780381d0050140c0c00b02c1e0400c00c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 402451879 1250 402450629 402450667
    0xd2c0a0c03020d1e0b010510051c0b010302090307090e060601140a05160b0403080907050306070f05070c030606032319080a030608011112010b03090601060f03231812 73
    0x59004805180b00d400c240321514404034813a00800c1c00d54111740c5000b080c401c2040e804c800e2001001801c01c6415011a4150007020404003c440006940030407200160f0080c800c00510a6140c4a2101c0000e60890317180c00840b4400d8140c0117640450b01c0720030064400e808802c0764141c800c3c45c14801402441d2080b405031109a000421030b01ca0032140d510340d1080004151380540c00075003a03c2c100541c1920030040d20b80101429401441240b92a000040005a00c083c080040180c0040c01000b401480248031000e5604072604201050352441c0000d2054a02140402d4000305888007036090080400c55000c41d020703070001030060804650341c41c0d0040c4c0c40900007905166440d2000b0910f41401d218180c0d4150041074090b607a41003140c0600002841644440074003601042000200100825014119980f60400360307000c43c4c00200c00d50152200f40300200302d201030184c0d907100030b4040107443c80c02408480c140840440070061010784903540560065100d8000b0017403066503010f5103240c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 402453129 1250 402451879 402451883
    0x9200a0e0d0804031a0106020d0c021c0c0801021801020f070f030b070c12031d0105160804030207080f0703140105041109060402070b010e040309080d21020d2c0a0c03020d 75
    0x41e14060322a035030902280f17003030802c141d01c4002c080300600c0b2541e010410700d5405640c3c3c6c10422509000c990029003024106021190520250140301040181c08010312014100d61002076450303100017404624100c1030303407005600522a04808c0304010101081980554801404080d0102c0c21900c462481e0400602030404100c010100d207400b04d0b030310180a0000103525540814400104040c05612031200800750f95640d14150600c00602110080706d802400203003010341c010b59440c141070303003031480580c4060081c1c003800d9012002c1400c08108601606e105902da6451554200c1241342261400c40b8003c107a034481c2d0112000c103180104440e54442002440980b410780c0d16901d4001c05e00080c1e100800058040c0140820585c1009204015201c2000281120078540b40010300220b140808010f403c14060032011300001d59404464011b040c80f1000d10503184075008540100c0700c1240306a13100002c40561440b00c0e4170204100290310307086001c0c001d00300c0c02c1d9003c000b0011480842 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 402454379 1250 402453129 402453143
    0x50102030a18030804300c0203070f05130506150a08040302160e0a0e0c0a0909020405180d0503060d06050702030d0c0908030a11160b03040c0f061409030109050709200a0e0d 76
    0x15200f848688511b010440300c0e1640d07121086407069106042c50a500e80d000081508250328007030009403190100c1240c12840c1d64400b04076510b488010070801c0041850850200400040710150700d904002e42d81c3c0110b120b03500715600e051600700c03a1440c55003d405411840844c0402140240c2d009800c2240c0c0946120700b40d0310b5400d101d10000700e0f00b6030385030700c088005030b00c0d1038040b0b0540c84c003841001d901c0504000540510000400c1c034035110726a00401a040c0480440450780d00d8032241440201c0582c001c03c00c00c424105214041d59a40040100c2101e05082c2402c80c01020b11888208044888440040d400d241d140c030010389043d000740303400030010302c03a04c018503802c8940c0e003440d1402081004070580e50382c2040e08202c014000985c110440c2403810010400c8800d6010726698aa038000020b132648580d030081c0042c1c09130500040143c0303644100040464805c6c41c0d41d0121030500900e019a244144480b01c4110b070501a20003118007041c900f058595440c10041d2002c52214880c2c11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 402455629 1250 402454379 402454433
    0x62a030304020d0321020c0f010506041a0d140d110c1e060c030d02030a0204060215010506030c0306180403080603150906040201230f040609050303090f060a0516050102030a18030804 80
    0x840491f0000c00c1c0c2c20341a64030040b000c0c0c910310020710070160002c0041e41e0510604e40c03004058080190921345850144854007800001c1c015020440030b203040898003a2080030b4030010f4000c01e10102c3e88070070001e5000d0020400e62515001280702d548038213848503222003c940400300300b8260018040030301c05000400c440941e4044070b2009502c80e401081c80140c44900713019000740f0b0043c240d1440401025010b005124664600e8281e96020001106099070380e0703510070110b0b09001103491303030407240003582c804d000070550000c803a14415402501100c44102c034090341c0e0078440364181d480803440d40101c03000c40c026520a181d4540200b207801c0c1054403020715040501125801070b4041c0511040200d018060301c0da01240020003400c08900442c01c2c05040d0000890584003113801130f01c0351000080b9405c4490081060392400c0141540045101c58181841800b03540110707400070190b842c0080c5071030501001da100c20740c4250160384540803a030343c640c0d034180d54401c12262031180c084441 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 402456879 1250 402455629 402455687
    0xe0103290612030c0601091a1002031801031404051e010b0f060c010e0a080304030f030e060a1a0402041404060e01060f05030702070b0403140d050a021b040902062a030304020d03 78
    0x3024000d15100c00002008041d01858a00f06110b842450340f0030a10509c0da18525a4004140c0d0032805228081074a041a80001070b401003a91008550703810703511800308820310402043d681d00035208072428000c80c00382128600c0c01c032840d0803015544220028400304450401c040a0043d80981000004280d80034401c0b40303241840c1900105c0d1590400802c010401d50300200a410410b030394101801007601d44a901741d124030000b44030418481c0c2d10800c645d03c4019200c800800113601400455030342c0c0c1c0780c100010489000d130b90460300403410b05100090b4032641c100303414102c64040c1d40d103514094507001c040b291540701414050441c4100035021402c0d45494000b84015840344074880014820100018100b074407408641c0c0a000d020300400306e00507000b04120350340700f0100102522a01803540060020880d021010b50010ba011179070b03081c00e0440074130308002c2c402441003100301504c5608203503070b81e0b10048400a4100c0c40503149100081e0003400004503007000e11003402d4216140c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 402458129 1250 402456879 402456883
    0x13060e18010e01080c09061005070501150f03050705100e1306051e0405091b010c0c0e01080a03020f030a050904111e0307090602031623070e0103290612030c 69
    0x7a04980e16802c814001000300940c05c0107200d0300d220054503002c1041c80c1000004441c1e42c1c0f102944414800009059410400207522246454080f000d446200795107541901d03090303480c107001c00c45682c42807150114043c0342149020b000c1d0b60040d61a0341c4440101ca0074032400250207040500544c1c0c03141c001103465514602c591650014102521071a14a114104400c2c1c503070180183e88550001c0005803c00302d0028070b100390502003800c00c1c1c5555225841d014070b42400551010780922000400400c00b802d020980b49a024025801c66910342c440500c8079859102c2e100246000c507004108021542c100b41e00003942100403402c504d4182407058000607840d0402002514002100008004a10ba08440903101801c5148011800c103048550110181c0c050003401800121402800b141100748880015154920360307002d41e0301c125940c0342c2ca9a151402800112500003401403200c0d0010f01c45200141c2107052150303007a21903100d680034030540003440c83c403100250208200e00241c02000f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 402459379 1250 402458129 402458131
    0x1b03060405060705160c180b0f01080a0b01090e010f080d020601060c03031a0613030501060909080f130f0b040602281502040b0c07080f031201031407050d031701050613060e18 77
    0x70001905a00d5186100d81c10441e664058550b102703104042c25100a0790740206899484051030000150074248480140d64001081e4442c0070b00406080010446e1300f9150030b008100c5003080101c5420011000f426a02c0b02c1c002d010700b00024040c0c40c00003000c24820f8020711490124104441011110780012418542c4180c0c40004e803e26131510801c2000400d200b500000c00d04000304100e0b01c60b040e91509007520903000c56680c0e02c500403500040c40c043c03030500d1000900110004030b04065071010030802c2d036041031040c0310250080c90407048009a641c1c200c9080585034401000074030069a031054560b002440c846400d0660a000c007095101e40080101112007800000340421807910020528000f50b901d01010170707800c02d20105241808214180b81541e42c0110641c503013402800c81c04d464003016a0107140d00c254415080400d054101144039801c0c0321910310914160788074003d0114912400c40e04110f4502c41c00001c01a051050741c807201c0f402c80c0280300b8400345069105500001310 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 402460629 1250 402459379 402459389
    0x308060103090c0e190506010e1e0a0e090606010c0213020c010f1a090a1802060d09060212040204053d050a0605090a170309100c12021b03060405060705160c 69
    0x314001401702e00d2040c0c20044101c01e00e030103030034042498200002001d5500911405001c0c60041203240340072245051911107044000d00500115645c440c0441408502650740240c240920000304280e94440d100c0058241e030040e144200038225020110025440300c10081c609542c0c41c80604001000781c01000351640780c81c0f001d074624412103001c01082c520050148403840c1e00d000c00c0c0d040c4043e2040d0106c0002a0110303901c40d104e2503c941c070600500121100248418070000e80005101041c000442c0524003d0324104032651716005081d45024444c160180f030491400817080d544400c1c002c1e089618440800355440d42c03580e950124400500c0354005d07402180c004a0781c400d240c00c20647d48002042402d0007100f181d01403031403090702c0b132041244040c000c912488084100744c0c06010501c80155001c0700840140c511408029250b0f0490300a03074150b205203007044d0f192441c000880a000c0e03500140a0401912072100c1034440d40d00c510718403804d6210000c046000300d402c4016010040c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 402461879 1250 402460629 402460649
    0x30d0603150c0c11030f15270703030513090212040b072303150612070206060a0303050919031410060b27010c020909060105031603050309040f020d0c0903110301060608040308060103090c 82
    0x81005540c1e10f0003080340001c01441c1d00040e9514044032230300003c003401202c0d010305000c0e5803100c064150000300d11380740d000380c07010b140001004e00000c1d148203107040c400c7d030060304003900da600c0d01c41e0101c410054412200c5d94034200d80305101000f000413401140c20080c0b04c4901d00c1001c0d07041000c40c3c0584c20003142145d103030350707203108002c045501801400e500c854100c8040c20480d0a60394058064061018464020740a10b40118504a82401c0307000103183c00c94a030f810361aa1545046a0342e001e1240c0c003040c80350074103c000405444e40f03415598041441101c84811800c81910542050000c141060401080000602c0540c80d0b0044144c06540b551002d000d9960401051502d405c01107120030601034003815003000428404010740e19620811540400c2c85040c0b07101080281c0a50003001c4e0183d49803031000ca054035000501076007100d01c94400211400301100805080b5500e41c420940030500c201d002800281c4140e18a030707070104d014100000c072064039464a41c40034400d900211040303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 402463129 1250 402461879 402461881
    0x30c0203010609050c0d0f0b131a0109050a05060708070b18010e06060109140409080d02120a0e15091606030614040c0219030e03030d0603150c0c11030f15 68
    0x941400e004201c09814445000d02c864106918426000c0c420032020400ca00c0c0d0b10000b140264801d50081c0c0b414500051402001e680e42c401c030a0010100807145203000c00c03403078604400c5035000d00b10110445100400c07400f03581d490541072013000d078807035002100c010608008120008101462003800350140c5c1100b04040d0905000260031a540340506000980c442030800400c0c0e82c0c03060141e000c1c3d0b0f5504d05050300351036100e4045006403402c000000d2118801140c0c6440e07030030040e8080c0c054034403c412100754689400c00d0360411940120000140317500a00e40481c3c0e2219180f508a03040400c880c21100b810072403048600003041640c00003000a91581070421000c10707505215094584219420800f920310746e42c019654661030421f0700000000d141052081c5801004101d01d424005001d07a50740f038510600a1005001d1800b0407105002c2004041c0040c0d40c00d80b0407040c10001030307255400c0255950f01c41d2031541c0c0d84220242e500d880340305e504a110704000d0000c03106d400180d0b10320307000d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 402464379 1250 402463129 402463133
    0x1305010305070f0311060a20010203070f0c020f010807090f080105060f1c030e03070e0a020c06010602030408120d0f090b240a0b07030c080f030106030c0e0622080a030c 74
    0x1050b0b07141c1d00080108405000c20704c0401c20000c51801c24041c100c58440c3c2d10906040b040c3e0b940f914540c0e1302d17056040403081d1001814410f40085d0312942c510740d10140751654000c000c2d070f01c0752488040a5006030703039000711040550240301072540010f00c07070500c0c0c4802655555007903a651072640003401140d4581d0706005450511400c13626815400b1660552050b620a04484071141c009a01804010100b25440907a45040c000000502002d00d0750200915044034202d029600428001507940304550000031034078804010340c0e050381c44403806010f6600c0e40c1400d511a035000b2540d03a0601c50399510b00300310201074900c20245410302c54000303510540790506103020b1464140307160002c801d00c2c007900e5008540c0d54001902c03d130399064070718540303804080c00c0c1200c521801d0704c0000c1c01240c0000e0f060030300d4020f580c041c0d4103c94003a601807020800e481011900c02d0605492550860424003e00300d090b030706250320807101a1410400203890703558078189032030003001400a41c08180e6040c00c03041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 402465629 1250 402464379 402464383
    0x20d08011208070b180307060225020604061107051210150f0905040807060e0708070b040e0a020306040b0618270117030702100503070f080903030a090f021305010305 73
    0xc0102880e040da2503a440341a00c40c11054810f000c1e0060058040030001540f1101103141d0900740300d003030002c49448202919092000354001c0d038401c41c0e60128442d4070346000740c00c800558103840e4003400141c117003031500d40d080e46d4518144200807214018000041180d4640560104040810200500412030360390351201c211a1503ea01e5141c281690000b40f00d4131070810660f03000c130342d03401e000021b01d41d480c1e0401e40942e0180440c01003100b820003008108484000680710160b8003600b060f0f601c46a900c00c0c0080c0c0d40e10a0b8441c0c80303944a00703000065600c0cdd0031a8042d681c803107401f500120b0f80e44600300002c2d00550050255507141813000d00307c0c4041e070602e01c848201c4100e4090074a86404507051402070b07401c005105103242c002c0b9002e01c0498140d403c1c02510815540a0720b0b410f401842d4030340141c059041181c4000010300e403540c0c05d02e066440b40c50705c10f02484000001d9403031500d50008030030203040e203231400792421036414100d4001a2502c648a5a1040c000b5000081550440c50118 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 402466879 1250 402465629 402465631
    0xb130f0c140904030e15160b090d02010203060108040605150a032a0f051c0501020a050d0b0402030618270705010e0604080309041a121b040c050708030a140106020d08 73
    0xc1c0030b42c0d520403c120010b5003101c400842c0100840741c141c10145a200e11b0030b20751003103003401903800c48040512000c00055090003806048020280c0c3c141c03d2489100301d0803408100d40203800500841c0200b004a15103a000c1da421407554400043e00f40e4034440403805074200d03a4011510b10050010010708104040811118034010780050752800e4070301140520107425030300a10b0710512044070580035901d20801a6004070b03078000300941d01d0b090015800b138410740004101c3c11856080c0311a100d002d02d054401ca030301c0707988010030100584402010741d0001c1c900c010803450304411702022511490801d95407803040084008020517500341031500050010320701030f29041c0210414481803024003000310a07916440c1d0f0540f00054401e40294400111f080507410700758101e642c0c03400304641c584000c0340044503160064992aa10390050051008844001d00070000055051044400003110310000f035400441d40e24000c2440044104401c8020b502a0321000140e1300035000c501d41c1c150031000e4070f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 402468129 1250 402466879 402466919
    0x150c11010e090414010204050d03020303150409122102390318030717061e010501120506030a05010e03031806070c030e0d0512090a0b040b070b130f0c 66
    0xc42403540c1c15001041c91104081c20061050003284c814205209095065900801c0014842180004a03050180d1030303501c161a01c200c2160551125561800e0038040c428010354040034440d0280003280c0102d4001d00000342e0051001c5040e00000e101e243c940c0040d040c40903002268507112036034018042c880d00006002002001207521103403480c450044103a54012501d0700c0c6172070740441d02d800003038203001803504109004400c2d00450118a50002202c910881e0b407405240d0070010101d90394040f41a09220701c0340010112242003d005003e508210f0708400064102c1d800c0d05002e640345800e40380d024a10b05496440801003101401840e0219040d0051940c003602c8503080c0b0b528000d003912185c002c05030503c04d041d41d0b1142c2545407070880c0c12910740c000703042c0c0300001c00b10386801c0c0c00d6a00008441e40b01d2442c80e6008203407948640d04a030300310396500340341070711703140c015602d804100c1002080484a1083d11a501d004118050700710a41e05103c0c40c1480e90b118207011000f00014000104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 402469379 1250 402468129 402468137
    0x102071409010e0c040e010e0a0e011407050a121107050d03050103120804150507030e0d020744150108010902090f1f0f0305070503061e0c04150c1101 66
    0x105280e81c40e8030912605464161001500c565540c0d0001000e9104d10b5100c2c41c481c003500e41c000a4a200c6441302103024181031101402000500440b040c2a2484032204404402c001c402140c100ca0103000203180c041858140074aa2039814280b007130441d480340c41071000441d4005204000c01005120580c0d203071400381401c014650454440d002e140d00240040d506000c1040c000c1020b000840c4031007860032011440c06e11081c50101002400b1303100101c10901c0718811039402c0c001c01400807603044255100c043c0c07031071001600103510601e840c0c100c450000540a80d520f5030a80502d204882001ca40441320003000c00304886446100d031124164002201a40f4005851005a980f00c401a8100305c52000200054803290000d508a2241c1580c40071f4851401200081407443e20351080101ca000e035058801c40d540d140c0c281611410102d8840f100c0c07402c992088203010030540c890079000240040813908084e00c4070010240c0421009100c408603080c003604004000c00e044070381203903001c20701e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 402470629 1250 402469379 402469409
    0x411010c0b04060c030b040c180b0408120d020f031e010e09100c02070816050a0b03070c120e0406060c060615020a1104090f0c08070608040206070206030402180a0b010207 75
    0x1204481c8440c0900010141a01c0c0c4440c1d03407025109402c1001d0080c07005208210100034414003600e900d610410403094010a0b240000e99075107007100340c90031556183c015240140c0203c810300c546a00a004c0d032001d20f503003403028003c015041400385116505c1d0900800001c0c680600e000c0c50400d051388807d54080500003003105045020a00c00c014000c00d40e004551714207094000d03400d14405d0303000101903125620100740414814a4107504580050390301080c15901d80054403950f10080303814102041c1486c0c0103500241c1f01100b02100320240703280c0346006903002c0c4009004c2d02c0440e070003800002c100308140b90a0050341e11841c0024942142c40c0e01800c40c0c10500651521071805005d0300701e010340c601088107501c0f1a013091807007580c05075600c03140b180685400c030500e03100c90140c0300031072080c1d40303001c80d4050192207446e0140303800603e01030800005508028003544010401c0340c2081803000302c58007010607404054090100b1500c003083c0700d035101c0002840c100441d444031328208030040e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 402471879 1250 402470629 402470633
    0x5090d0510110d3213350a0906050d090804091b0e01140d02041214060108280812040602180a0e041407031b05010318020a0b090123030411010c 63
    0x2141044c80000c0252560120b03035800f8034048181056070400351148080410303100d221040c441c1d02c01804984084030341005d0b20710190600c2070b80140c02e00100824a512400d000e424000c2c806171200c01c2412202082210303003680c440189030415400316000c1602d80c140280e1000544840c0389401d000b901e8108420108400000d04001d4048590740c070101c800078a002140003e901110f025000b40c1d4500016202e00d0726240740140c035501d0350201d41d40595400443d4142012a0410780462800e88002402c0401c42c500f414200d444d000c101e40c20031003000074141c041d12402c0030a205a000d80130058403100e5940c04041c501890021540c0b03d0903030600e0034000001c001d50340c590030540003c03e855051030081486032400b030360f80d040034212442c440c0d46c81803564021140700c2c003900c6080e6010312508c6d00d60010b0041c0401184402544512504002d2000701a800003414603210140f401c00f01c2500341c80b840c00c030b008129801070a9480400801c00041c080c3c640d2928030304120a1a00309190140b0f5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 402473129 1250 402471879 402471941
    0x2010c092c060a032a0803040b070615051c03030f0e1f020c06040615140d030c060b0a0306050a0c02062701200a020f0d05090d0510110d 60
    0x780c0100341e0010300400030854a031108a008809950b1142d81e442e50340840500c82e5480741c5020340c5203c40001010b0020600b4a408403e480c221285961098281220383d6940405413030078900006030915003020014140c1d071654032402e240c8280c030082003401e11309410020107482589000d1104182032495904008100103400200c2d43c038558900d00072031600d0325021002e4454010070080c036200340024803060040552101000703c1c1306419040304582d0350713042400c10007450101c1c2644110001c01002c0401c4c0686181c510141c07082c040002e0780145403002803000031030354000307881c0a0740d110102300c11154188103000d02007840703000500e100e2521050241a013021103000e01c811030726400760030b01d2490094020454a00207180d20754509247d01c507541080b6003210011000511440404010b0454041103900302c5580781d54800d85070080120500c021b51a90b52000c603900c1c41060842742011100f032090501800d20000401d60711105803d00d9415a01c403030780760640b1314108683e070048482d0702d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 402474379 1250 402473129 402473189
    0x7080a02060a0e0c1c0c170d0804020a14130507030213090902031e0111030c07050c040b01080619030204020f0406080708070807110a060e0706021002090f0108180d02010c09 76
    0x400c4494581e514905c0007501c1050f0a007510041c1401105c02002c560001804640f980550300c600480d0b10541e0f000f9000c844022090b10080d40041180c0c40c14420000700749065044114080e000104c0f01c103045d007800c0101c0b44100c810320b0000b503011894400c4100c0c2c01e100d07000242413a05090121200d00e1700080d458048e040000c1c048224214881400d00390700b03402c41d50140b03110122194881c41c103440c8040d200c0d44941421540790140c064030019074903182c841e0002092040e5190800b5545100900424000324083c0344028005484000016034490005140c4d0441e95551191600d181131400b81c1384082c0640704906000a00e4108100c0a03880210700707500c404a4603215003025418110035051803c400f5010302010308041d0344640b14040020380e0000c0720485e60031501002d02c080c0c4d0000880c0140c0075965070025405070181c0d00c6600c40e11040ea041240400744090840103408000d2400940c01030b40400750f5124054605540d4104910348000c09a13880c1824030240705081690038151 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 402475629 1250 402474379 402474403
    0x31506030105100e0d0c03030e120f1239010507020303091902041d0601080d0f020a0b07031e0603030807141b07080307030206060901140105180409020607080a02060a0e 74
    0x10640c0c0f91100360383da0f4618603174a0140c02c04181c5c80c001e0303207d06000f01b4070b02e58001c0d03140c06014103188002d5995400126102d401018202810506100c1011141036500c81c406020301c2a01c0b40b011101c42105529140380c00740b45042803140002c00c036503011400c2d01d1000f1b00c660259001407041100101703003c5001003901c0d0040308500354a030014400100104120b0a11807500702d260181d5030040607000030030302d050b244100c003281c001d407410031011035400100700c06910041c0c0111400070006050700049070b4001400c0d040c0440d03510310390002c2c4039102d1701859a948650f03880342010800c1c140c10003001d680200403860607642910f8811221116482550880104030031511500c0406003130a004000c0506443d4058968800060800954440d41a180c25205045c1c4000000b65030101800b092005c44068540c9811700181c0e15482c032520400f07440c00303500251110300110050707a07040010f11300244641d41007900c1d40686030009207016001085020316074501200746141c3d640000344841800303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 402476879 1250 402475629 402475637
    0x90c03022208070e0408190c060b09010b0a0c110405100303030b0a0506040b07051c020c01091403120a11010612060b090103021c03030b04050112350f090901080303150603010510 78
    0x5205c5260040c034074401e0301d02040900154a00000c010b0394452540020a4001d000c28030584000c502080130018003072085500c01c0c0420049216568000d41c540400b082c000e00006090101c00804507003910300c101c0340d0403102a4040c20620415400d80304440350b030305040d41d0904103181000040340f068031690044280003103000c280304081080c100700c583d078848415030b100c409100c005040656510850180640828102c080100d0840c7c2418003069280c100103004002c0c0f08507055402805a008040741d030100045000621030b9000c0c24000e00009180c0014441402141070501070112101301c64114460742d03001d001000540d0303420800c40000d4403120b80c280c804804c140340c190300503c9860704441c1c0180c100400010124200311f8885400e0f80184101c2e2121041e0040280c0d00202070744200001e142c120b640c00072141d5010b00030b009000d401e614028601f411030800100c1d210826440000780303910000030802100d80281e61400041e2068903114159410714001420007140c40804500700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 402478129 1250 402476879 402476881
    0x5030f0103030e0d0c030b0108100e0606101106071d040506010e0609040b09010314070b0c15040f2420030a0c03060f091a0901051f0207090c03022208070e 68
    0xd1351503002c01401c1d96400403107080215902d00d04504003000034031516070940921810b40e16013280da0300800e40d100440708007504113503a500007040442200700b090078040180c891114007a03001c08124240c06480e0340c0d214145461017403100540c07503c014007402401075003407406016407660400b0198a40701d0f800c80d01d81d9110b903030540120740140750030210258818100000003060000e0300403100c601c0001082510400d54032403101070b5140c842c2400d1040e640d4416413000000003021082c1c00c0d0010b205209400204610380c8441811070400d50000445515850300c0c0550fa08091040403c0c1d20840501180072000304602e0000a0100a00324180d503a190751a000c00240b29a001e4030103403000c0b405500c0c01d50b446800302d2000780500942c81e114140340071320040031443e11491050480c5d20061540d030601559441880040d40810044d0055200e40c900100c2c000005000b0f05528800301c0d540140c403820032041e030402043d10008822461080d6400c184801500415074000f584e03642d00760741e101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 402479379 1250 402478129 402478157
    0x100e01170610060804020d03031b031d0d0507120c0609050c0a050a0b0f09240307030c0c02090106030b150a110c12030f0a11070b1803010c02100c02010e15010f0605030f010303 77
    0x503104401c0042ca41c0e82800140c080c029405901c0550b540b0704440060003500d403346603ea036101101b030280c0700401e01c180303c03100019101003004101c10300b2078035088174903ca15503101d10940705842c0040300c054010303d0710310340171b42810303403520006000c2103035001c2c802072900640070182e101e080d887c468603801c0011404c00c00d0703ea031401c0294800012030008200041c0c0e18090595800940360710000a0030210080200c3d4480d03480c00c03603003980013404950719900c0d08805030f008062541c40036400c200b20b84030740258450b04902500d14040c8a8031004286040725401c0303800c02d5420300e04644079000505829040b070704008282ca41c400001c01c900c541d1404001c809440304000912500840e10442c50082030b581c0340480a00003e1610902c280d0111060204060980e0f0398400c2110043e03010400d8403078941d01035000f0241c0c0c60344a00002400c2c40e0414601400d12001d9094803464580b280010030264510200d5000103060328544141142040c8800c5445500c040c0300207010054542c1d52004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 402480629 1250 402479379 402479381
    0x30e0f0d0201020307090f060207060f02152404090503030103320d11010b03060a11040e100503061303020d0f03020d1503120315030209100e01170610060804020d0303 73
    0x550502040100d4203104256503000b4042d40c01100c1003400141d010348006030704441e0103c81403d452198010300b20541c02d00302c0480300c04ac00c03801d09004622903410f42540c186000102140210002c0d642038404420220b00035203c0b0a140300301d58041e41c6003084c03c00200f0350110942e0306483d031040c000035201300f01070b603010410040e407204007c8200c0d204044c10180d450001c0d080d82401c410f034540e00090510440118200c0b4081c000f002c2e015007240e00001d200040541c4612903228482400b50b0400c0d8448403041e80540c1d040742c0c0420942c4c0103840034801840c04114003540088002c8111502e54a0f5a070002d441d00c00380d145c0e8030140031516a155056038080d0301940c4101009403c00c02041e034941c1461292401240300594118041c8800100741301e201e805240700350041d01d514050958035503801e01c5414034005019407101c100007032021a400c4411800c160007800d1a130000f86203448415071890800c4009080c01514000d912001c016594002c400c259106030125028104c00c6542d0a09034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 402481879 1250 402480629 402480643
    0xb04030f020123070605181b131104090f0203061c060f090b070f032304020a09090b150609100503040f060507110f010b150d02070209010f05090f070807030e 69
    0x2c4229401e0311014450b07512100c0980030b81d174080c100512a40d2648020301d41c14001d03100c0f8542d15038022620402111445042c10b0310b070307840050b0081000515101c0356404507015108114250b0030300181c100078840c950701500c0c80e0900701100440c038508014001805078892000c1c00d046010404c1c20320303024080c441d4001c0104101c3d4010074007242460b03203000c1c00c440320304441900c0802d4003a80060700d02c500c00d21500e0403451248c0d4140c2c2c02e800140e01c100d1a80d800083c4120380c4200a0000440d4440050103040c0c3c10602c41c0e540b40100c1d052200590300359185d200001801001c080c0090a01035a44032100c4444040d5401c0c07060307072070f1140e050001c1080c01c80800500350f030b800e2400b400074041d44200d907500c8007d0300000756441c04028000007400c0c1c134290280198401c0c900c9001724503607442c0d40028000106c4100f801840d0100c00c4d40840c0700d4181c00d0b031000407411416070080025080a90380d4079440741c85d40c4608207072450725a00142c408a006082a02015518943e05181c85410804c0c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 402483129 1250 402481879 402481907
    0x6060b0414101e0c0f080a050c0714060301090b06130f18021e0310030c090b040b01081b030a110f071e080706051009090609110a0b04030f0201 63
    0x550355501c800c040a00320250040807030045100201d0440b03458410541c51144031245601c040740c0b860386035400c40e2440e564002c03d86010320000d903ca80059a0074004042c030440700d40354161580c40e03c00c9520305101c020340c84a0b00108140c40e40103a155944011681560a1868001020b0203c04040380e0300303000c0d0503002590282040d1020031550b13400100003049610101c111b00140030942440004c2e401800b4038019801400c890034a0b407004008061507004040341704404c1980e51b40d8a50050007031140d4010301b42c8664400f1824664206801546810b41003800d100d209401c1c2081c1660f880081c2071010002d2201c0400481e030610a50f403c0320f41044482084240c8902680c0c00b0707010194010407003101c6c0e4046140082614002e0306030326411594104e54002d007040c81d15110a8040e0000422000c01c07510a80c00104901c04540710740035800303010300ca0001e80034166250592164040d008000d124a544540411035134503010120ac084d02d80c00004103805140791710050b03844801d03c1d410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 402484379 1250 402483129 402483149
    0x3091505010f06051e0f0702100305040b0f01080d14040519091401030b040b0702010b1c0209010905010b04090b04022517070308070305100f060c060e030901090608040606 75
    0x24051442210340c11941c141d4240c44129091150f40c0c2900707440500c2001e9100c00750110018400040300c0c203890140101c10320454441d4a0252940d00048070305880701d4040300800c3d40c4006000600600e0041c83d0303840214000c9080203541400a040d0752080c2c0e4030062410007101e008210020f9200b00191401464050602007400c1d06102c09000704c0f400078021900031a10b0104910110701048410f0b5048a411500b0344855450301e03190701806c0c800061504040d90349030340c210107050721014250305c41c82c2d5800060044920251042000e07004060740124510f0341040018065500035004480489045001c009012800360011a02a018003c8181135200d0304206d000c040108094140103150300c40c2c0a009500325005210b080d25020344034001d030002d080340700040da006010b9404150030410f034100c040c18981c0d0703036141d034030703521a0f240c005000086042240c00c080254074014510154241c2e80075500381015080001c005000c140300301010031071700d00c0c00314090005d0391b440480a4444004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 402485629 1250 402484379 402484403
    0x50105090106170a120507080702130204051c031b03021024090501030c03021c020a0305010b100201060e0f1b030705070c06030b0f04050919050604110105070b0708070309 75
    0x34424000d0100d482080c0c0c20079100010020309101c0441d2040d2000d91008004060612460303003111150420181100d070104101b0040000d0f90318099500000c2c050854050f03600e90a1a041c0070b140300c0b5150070828580711110701e0200094100c1501c12400c1680b402003500701e000790400700d1500392040000c080c03052414000400f401c0201e4131045121551100485c1b40c140d1b904943c80c2100d02c24440903001c0842032909000510304100f80581c4800303100c024641a03025600007610803c580c0d40101c620f60364521702c0d98024240449440203040c001c2c00204900303880d00e400301143c2074008086001c4911620001400100c5170200c13907500080c000c0e50140c0707031b150409020340150b000f14800d03109440d042500113020b512034094000f01100c05040d900490800e102400041c180217844000b0074080c0501050800e2500d03160500f1190087d0b0080190341002c4c104149091045924513040003000c00020021650b0340c201c0c171b50404c2c5149011035807503035582d0f011801803070b0340e44008282c401c41039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 402486879 1250 402485629 402485641
    0x30111030a06031a010f060e0604090e0c040518060a27080a1d0f0d02040b10050904050901050123010c0b010608070810050f04020c03120c030406050a020f12070c050105 74
    0x3502c0754003540c0c40386030075100c2464180042ca02202c401d2156612a8024610034072250b4843d00400039081e1000d00014100740c0c403241c000d0203580b00102c108000b940f04500070200c07442c0c240134440d048081c407082d1500c03600440066a48502c002048060019150360070300142c8800d0489404444443c1560324003c0e4015240100c1c003540280510300010700340101445425080146d5200782c003d004110075041042c8409000c00c640381240107a9019540310358034407494540c9079040e1400000e0f030f692565038407004c50400045540240c8071425680c50f00005000701c440e55050089500010340e03a21001c8080740c0012103541e0740340c110042c00d0191020001906035001803c00d0701800007500c1c0c08106650301e0707203600000c030704c0f500c0b0702540721880c482d44c0d14107420300d0345c01886403072140410f9a1504a041e064180302031020380d2584002c1c003001013040244951031003140c0d0441a0940c082d850044075001c4040306028000480f000c003203d00740403c131828001e5440c40034142e440030013800750f0315100d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 402488129 1250 402486879 402486881
    0x1b0e10031a1f020f071d100e010b04061206082505060f0d050a11041a0f031501230708030903090d0303020a0e031603110307180506040f150302040b030111030a 70
    0xb82d02260090f2085420080382c0600200300d2105490185041c08003000f55000c10580e0414040d0003801c0c90ba0903000045210340d4428500380c040e14003440803507916840d00400403e11164a0035000c1c00d076160a07001d00c88c84c1300100322035541031910748078204a0102100500001e402540c040c0794001000610380e40d40e01c0d00b01c405001d210401e54001c229a81c2c40c600c03403c0c252401100c07160440f00c0100800c0c4804c071040b82c10005a4168104414101031443c183c0d12210340c4207403101e10b00130740c07000440f103240d6900c403094070071403801820b28030f006080840c1c10200501403d02c1c01000c424020000610300c100400a46030031440c010228040340300c6609019000390301103201e00001543d036504220b41c9080000c0d10440800d08070150006071403a546900500511101e40c16502d4012040000750f4155012510030505422903030010b080e0414404210862710100c122807942c9007448504110141000c900c40308482d01034401060044a100019004014040c01612a10000b105104440440d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 402489379 1250 402488129 402488179
    0x1e0203060a0b0d050a1805070b0307020a0605040819020d05090d0807020301090c051302120a0213030c080d0216050f09041b09051501020610030618080406031b0e10031a 74
    0x34145d0400201c0800b80100c1c260300000e6402030529413011100300604140c0800542e030040745032068406800c9650b80ea58150342e01540c00342c0b4000030100e80202c1e924004200114804440d000502141c105004040c21500808103200e226900e114100000c0c0f0502c6000c40f643e05500030000c0249400610f0400c4000c0380a019080c0240102c0001c043d2030a800c0c42164461240d9102140580e03030b40c460020003940c02440079181081c1d00240010008450b070406030083e14142000e02224880f8070002480e140c2003100c48210b41c005c40500300320070b8444e9806a05041c1d010303910400140d65030309150101800b0602a140c030700000c19000180002141c0c4983d00580b5825901040b07190702e1801281e03114802d445500f407440ba20f581c100001007041c0d2140813180500300f41c1024211b0300f91510120343e045035220401194483d80801040401d403030355140ca03081c1600300898200038610101c0c66828181d1440ca05143d6030300b1030356641550345171001007048402451145400100131000b1030b5840 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 402490629 1250 402489379 402489391
    0x1081911042601020f120a09170309012702063105030111041a03040311030d0b1206250e0a06020f120316080402060c0d0206191e0203060a0b0d05 64
    0x10b10107240c0d4502c000c060003101c02100440c61403034106000d42e412000340307100181100011726510852800000c6210034a00610f00d884280c481d100c0c5003280f15142521601500201c07200c40c1d42222041451054810128441d01912415200c401c0d81d800c00312011140c0c0742c003e201d2410440540710340103c6050b04030545d00d06030000d006005031403104504034011030098498001070b1900d001759070704030040603540c020301034545000310402103003071a820340d4480001075080340d4807207040d1801030500d5042e1b100000c0408004001c00c0c0740c508190402140b9040000401080c010707060010311384121a04074000100402c1d8100b050f642d140069500d445044107864240140d0290801003a0841c003901c0c40388000250114000d240480110f80200c00200120382c4203800380812411940700704921908059560014002c070b040000c01c03406000e0740c00c40a980d2050400008282d80300e424181c44012003002040075840344c40340c070002501100c0c15004800c1719000401c548030340a01d650811400b4603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 402491879 1250 402490629 402490679
    0x7020d23030f030c1c020715060b030403020c0909010e1603030311030c040302010f03060b0c070e06100903110d0b0f10062a0606080a050a02100305060108191104 71
    0x1914a501da000d44079001010100c14000100408090002000da94842d5a40400340180c031010080498200302e41c19286001044070800f079444803445000090020013a005040d031409960096071800b410718281e00840110000c191000002d40107520815048000d44884207461082c044100705144001d800090610b2401400c10003590222070144c0490b020b2685400d007180c0040d101180140118000c240e0368080000d030909000000d004c90324148000b8041d0b0914000d80000a000b02400103803007400482105072500d03403c4a445000c4a41c404101c1c08041c58001c0001c05d401e280ca08042d01d4082c2c41030411441e103002c4441e4511817021040a42c01c55520307020b0845a05440c60b031141d80c01c92905112101c0c1d00d1041140b9100c01d803003560f001c40c4080e145c02110f41407210001c2c01301c0d8160302c40031292003146840b85181000540e035243c200090301c3c02c100004e01040c00508040c08605426400f4409108150845800f550741503130003c0c0c5c0c0f503540e100c1c000030b40030781e0b0a6510008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 402493129 1250 402491879 402491933
    0x8031e210604150e0f04050c090408070209010b040f030b22030519080c03150409080a030b0405010b1216021911090702070321021c0e010932010507020d 67
    0x40c40b064900540d000652180079170b42d00c0304c40305200c40c41c0160050303c10388140132140e41c07541d0721107a04c580715170300c6241c80702c0e159404c03403040c00001c60040e0801d106295042c4401e0290360320303040050084a0f00880d000b407094a0b44107127005181106113100245201a4a108080c19044001880016840c0d150450140c0d50840101c40b005025a0221000c0303608101280308040e50200124910000410001f40c20340d20744d42e6210140d1107640e0400102c3c9e00c1c0c4d07070803084030f00d460f100300e40c010030b6000d500c20328015103038034019009540100b6004454030340101d00c4000a200300303d8042030f1514011000c80da00c9590a0030301c4861100300c020b910520b56240081c3c1d0081c400719840c0300312580710301c03d400d028101c0807c0350a0120b2120040c07085101d010b60000669010191120b1000c809442c2c2c40c00c01c20031200010407503049604100502120907c0c05031403490803104405200310b07001c42190040b401407004032143d104450019620104001e1f1110621003550380140c80c0e1030710350041d141e075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 402494379 1250 402493129 402493151
    0x3050c0f0d02100515030d0f030b06070c030f15090b060901120c03060b0102161403070b120a0203071704060b1e0f12010e151f08031e210604 62
    0x24492a00c030401c001038001d540440e60290030b50f00a1074110759110030301061401c4903004a890800d4806000c4005045051000b0720140c0500c10480c4a03241541e1642c507190098554038122090381c4001495005480c02c2c4400380441d100744004402c0c110b001c10f00043c0c0d824280b200348003c060b40c01910070307a41c1c14000503160740c9054080802690056404031403a00d561a51001446800041415030060105000c4422003640c0010301419060202d0142904503101307240c03400784a07402110400604025400d4804503204c00a50700c40300c04940542d50f07944a1b8800c0b5202441900503e24155444090004015540e044003103110b00075561008000d2450703158407880c40ca14504250040c6102c00c0040306801c0102c6142c43c3c0720030140001c540f401d040c90107c0d10300f0014044600c0d040070094140585540001c030207100380c0340150045510a4140300340070744c40744500300c0518508007503c0908240d041d519401ea40c405000040842c0d002800904050b84808088031054412440c108240c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 402495629 1250 402494379 402494383
    0x20102090a050f1e060405120a11060a140c03070c0b03151c03050717121006020d0504052e0201060906090501030803041e0b0705070b07030b03060613020d02040303050c0f 75
    0x241c3d4000601400c900d684840303107104040b00e1350385440c0d0094000c0202091540b0780d99000c8035200c0e8460000c19001d1203a09103010380c40715008580d4841c41080050741c8070168050301410b8034850f0b00c803c050b0b640916203500ac0c07941c807900710002d080141e0503d00240030300580024602c82c4490031000000f21340c0d00002c028a01806165245c2e150120040c03800c00f00b4454405401550f10440103014002049030003000da50f040b012260394811442400c00a00309030000c520700040515000610030380c13595040c054000c2c0a28002c042c080c2e20f100844040e0039111010303000104410100032841104082130080c042c02c1240558011036091100025490255125150403640c2040f41281076031265170f9808045e03c020510944420503440f00070000c20081003000e030107810591940c5942c0c1481c5c0c600040c8480009214400341440c1070142101c546002c42d565911070411202c0c0505d0703800e941c1644009004800b040c900e00d501c041000b00030036400000a0840e0312203503088544042d9076041d119 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 402496879 1250 402495629 402495649
    0x3010e100812250c080d050a09050d0221011a06070203060103060213150203070b180a030503090a140604110904030c0f020f04020703030c0906020712020d0606050d03020102090a05 79
    0x6295800070071008079a001460280502e030f10a0100072200942c043c0d83c0051401265105032804016101c04102e10401004846050070580c18101d0405003035100c06040460b8074410f01e400307581c030b081c1003030115034a1070f206c1705a00c2c12840e1465030050fa00d0080500800415580041402150281503002d1510a05482e4007071780c02001020568259540e03403010f5000040d030400c01440301c240102d00481814210034000740254000d544480350740c104140c0c0260080c04001004444d1050340c2e84010f00402c0705191550103043c40d0b50713030751540e085141c5821041140604010318002c004180705402151907401039000e680d030741001c07540300e80811074480b200b0b980003800304d1180c0c801000040c004e034078401b071143e000801c1404000d0040d0040342c00e9a200d03020840003e80d9548a800070306811405e001c014107a5440200742c0d19040c41040711401000794070103440356600060107420450540c02c24809014003614000283c4664030300a0f006c0d401840300580710340440d10f4049074038103015200d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 402498129 1250 402496879 402496889
    0x50f0a08060a0e0f0a0807061508370311060c030f07030b0d02060d0915020c0c010c02030106050301090b04050d0f08010501030209043c050c0a052d03010e10 69
    0x1e0700307654450071080300c02040c0b009180d000500510440070401075003032144040240c000d0718074a175103422a142c69003c41e244130440f079a0380980c10030203205034040008d1b8101c4c03041041ca98499060b01190444118004221001c145081517511000406030300c00c00642c1114100c1c421180c1c41d4403201d1600704907010031240e10691000d281d001031451031180c1c00008202c000034280b80900c0c000c607008103103d80c0c840c080c1c070624240c49800000401c000d000d10040e258501c3d80c0110308040c001ca608a0712191312a005030f04002a610601056503003c9d407000004040c020000c1080d008540707801c181a10048800790396500803030b940c1885450081d40e1441e0480213a81e10f250082e0f00301801075000b50010003400742c0140d0341302d40c000c0e400328850329a1903999103460b007450b4034100d440030026040c46240b151102280e0404083c40840c40442c2e003a551100190309120b40c507642030240d100c222080071164407100e401032849025800741c01d0701c010342c1640c0c0244040701d40b40e947c0e5216005110058411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 402499379 1250 402498129 402498133
    0x9140901020f07021c0203010c03020a020c0a060e0f0111030403051f0c02060c1b0607020c1e060a05090607080403150c0305040c051003022802061e040b0402010c06050f01050f0a08 79
    0x900d50040c42d0451405002c4084410508908105c98010038216581c0120840110b503002640941c5603404109400140e281154040c1c4042d090090090001100d1403625005482009010604c7d071b004a143c440032082803030807642c440381d480c14403503500d481d0000b292100500303180d941c940d003207001c0c025003003100a40d4000344220b465140c1e0070045a4051200148201080e0140f402400d200348180340c01602c681d0b00030444a51007a00b0800441b0006c014112514000c0c448010103031520416107042c0c2c001030524546480c0100041001840b418600a141000003c0e000c0200200024250100400c142d400c20544c0c0200c40c044d0202e410584002d030003415000402c024900d086010100c1c2c6000a02d00036090001003090207400f900e20b01c401c01481041c401c03500003408d5040280d90b0703200c0c01c00c40b00100060419120008070f0900640003a1080c0c08842c0014290f9004112408202c0da00c41d6040005280888c1130b503401110a00580748100c0c145c000c0b00c00c45242c5100614151000382c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 402500629 1250 402499379 402499387
    0x6080c03010b2a0f0601060f0906080a050c040302090903120604020c10052d010302031006050d1e120309050c03010e031206040905070602030c0d03110a1209020a09140901020f 77
    0x1844100d04040c10880004110750040b203c0c40061003031503441101c0700000c0c2065410000041c000021400225081001c0d8000c1000702c0740d84800c6440c0c100c90701240010345d5840310035400400340700c2c0303800194100d40c4110511080b018000020005814070804541c1c645e01d456003004240d04c03804112400561140b190f010361407045510494214010380da941c403c070044042c40b5038030024004090b8095500310f500400c19401d042c0704440060340641010004542028005802c40c0c1c4242c0003d440c02c90070311403102070940700351002c5d44065044231060290419400005014245d02003044480740110106c3c4680d41c10f05004079a140c40d564009182407514070b8103851240c0070300a03c03d991141d100e240e503c002c95000e00114010b80102e40c003440d501c01289914a01c0d2120180d007000805103095814580024002c00b5102c400780780d441c02d04220410441e01c203000d411100741c06036008400503000503103803540760b100048030000320303032016455900c1c20a19401c0340608014503c007000104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 402501879 1250 402500629 402500647
    0xc050309031218040c0507110a0e0c070308060d050d0c0303021c0e1507021b0307030227090a0206040620100c03110906071106040801090318080307030c080c01020f1306080c03010b 79
    0x9008523071340e41000e070540700d0242e90741d0350100d40243c040e2250240c0080019641041c150700404070741c3e00400a403031a206d47c030714507034032507540707102000e41d080400185203100000c042c400c0d0120784c2009d4440400030002c40d00d080301307080240303041c0b50420098404c09201c4400f0360b14001c601380c4a80c3c100c0e000380004036030103506035200e001aa501c2c1a03050040d0394020005030b490801c000f210070341440074103c107000584007001491030090503164182d8016803450380141d55540c216015a11140340050001354895519101c040742e404500c409030180741001e0140103a16801469488820f9030305010024035511800864400c0050207034006404001200202c1c008082c0f408600001070700142c0341a0750b03a2000390840702e0400084000900310500c94414a2803d44104040c1245070007443c030303003241558050103114900200400c2c040c00400c1040c0380d40d00a42c151464142540700080d03646204d0891204060220300603903002c20b81800203e440c4410500070340341a65901454180341101d0383e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 402503129 1250 402501879 402501893
    0x3c100c0504090905010b12120a18051810060504060801030f030c0f030908010c09050f120c10021606030905121e0d0507030b01020316030c050309031218040c0507 71
    0x160028810100030008011410b0301c201c0c20200d001c0c100000d4109503101c1002004140795200300340703540c41036080c00c0c910110341c000c41c0c2d0326041c1c0d8213161a640c0c14500d1104025001a13020944c00200400c0032003c04d840010b1503442a8405004541d4598881500b640c15002c1c6002d0000091030060061000030340405200101501908100402c15090703500c0c0580e410046030100c0000f414003504204090090088070444100340c1003244600b428080401d01c070f21500390350644160f06004c048072a820382441201604100502074500044840364065078881d07061002c8071803502403480004110f4882c2c03044260986d4400050b0200846061404059402c125809078503440c1d103075508843d1604180040c9541880c566020031146030051003d0211524890994190f410404c4241403055110400190450380360800340b42c034541508101d4554002c010380242c0520035005501080040080138000c0d141c10704a20074158910041800266401c94100b0790200d00c040c0071a20010f40030f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 402504379 1250 402503129 402503141
    0x3210b15030106201203010b1804060e0402060d060b0c03070b0112080307050c1009030c02010e0108071b06020d1503050610050303042d1518120f020d053c10 69
    0x4c80e00494400c40e00e143c039030800551080c5d00a00d401c1e10001002e082006000d021103040da0012241040070a2404a0030360700c1000050000b40309200015044485071510b82c4100e01600d02c03050725540b5501e0b80e065150303482c0d03c0701105071050b42e80d0b0b8000207114545441d251104561006100782992108441501d25070051305258100e0301900c0302034000100580314a09290b4008e9442d440c640c031550001400d0618200021410016240704000f100383e0040da08840403c410307140c0d45190180d030304002000303003c0c0380000c3c3c00c1c80e8100549488000b54079000705003568090000d440003500c07440014504043c4501c2200c0e019001800200816000b020100842003041c041d010289800300c140440800c1e04c94000130803010b0036030340031004980d000311010000300486aa0320a000e0070001031800c00351060500824410941c40043e0854884c581c1e003096a56003c0304440355021007640b407207012900e00085120409541540c6008000c41c01c48480703180c4000000307840d02303581101c00310001d044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 402505629 1250 402504379 402504437
    0xa2f04031b030b070503181914010204050303131403150f130b040510050a0c050d0b0a0f0f03030e0108070e040b0319060605100c0203030a0c03210b15030106 69
    0x101030071000000c5001040c031680b02d02c4441c0d403035555038680403691701c0d0f000038011a0300035070b0740c00700b807071032030300d80501d041020040d50086074044e001c0b1084041c1c280640f15941282d03825000100740d00805c0340b0010001d00542d143d045108000d8521140ac0c0b564450b000d41498a003000b1100100c1d160280c0102281d400403d820814042c21090b0b403a00c0543d580280c03000c0b240c0343d000740d803244025880e5100e2550040d59900d000c0c0141613031044010040d029094a0270000c1c1d03510609003900c1e40d5030359000d40040084141900300e4660350310501d03200c84400d1000b81c02140c41c1c6074004c2080d601c03a00310648501003584600e01c003044c40380148401004119102c9416101c1c1d0240038a40c464946c49280030a44a503401049080c1048144181c1001000e403031024480e8283c4990010307907010003940c02c0d50f41b0b5031072b00040111150404440c041ca28240600e040c4caa40500707010502c055811640c41c400e01500d880340b8030b11544800300f500340b00920410b80007a482e1101c09902c05a80c00103040201 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 402506879 1250 402505629 402505673
    0x30417010615050705101802060d0204090903260f0c03040212011d1209031c0504120803040201020d08010308190507061802120109110d1a0a2f0403 65
    0x2a11200340340302c03403400b000d44500861008507420f81002000c0140020070504442c2c1403080e0342ca02d0030592600c0b8505040203109800201d5940d0703002e00c05505031002860904414130018216040290485507102030400c004070040c0d01400543c1c1c5122902c82c0034106a5204007569134941512011507003000d081280d00c4210000c160707a048409000d020032882c000c9100d0f82c400190100e5062500c00d07520020581907034248640b02d01503502041ca41c82e0000800f40b200514100d045040350304d40304da82c1021655100d8240d404060000e0030018611540c800c1e0200c3c0e20703800200c8020f40c2d00c44d03401d2000034210f280c01c1250034608030501048404455150171f0140c01d11895030384000c00d48010076900c1094610401d01c030350640c5410000b540101031454002c00100c0c101da201c10444070700c809646130080d0340156007141080486419441440d0051042c0b00c200c0c01c10b40c881c440940700c1c0c4c243c01c0d080c600e000498031458074209509500391125044d051450b00e45560748035512184035143c244040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 402508129 1250 402506879 402506891
    0xb0f060f0103020a030f1a0a050108010e0403260403030c080c070c03080a0309080f070b010e0405100c051908060111010c0503040b0604060302091618030210120e03180a0608070203041701 82
    0x140c114010b188290807d021020b0300c224110060245206650380a40d04010b46d44004010980c50009450b030890b402d890500e6400c2580142034005403011640950394a02c100e04002c14164564880402e100040d950b40304036480d22070000949005100740500810484401000084d20101c0207003001c0b400d50601040e17441301e1703440380344090308400b1250210500004940c0100000ba210f103901400301d40844051600b0140c94150703032844580004034ac82d0b0f54804815140342d00071301c1035801a440c0c0045103042c481241c07030024110801559403e010420b01064004503841c18082c20790b02d405650b031601c0c1035589039142c95498842c041d105940040e0389032408405a124080d0f1742d880b501040d4466907002042c40b000900c2c009054290b00e440816118041c40180d4a200300b2a880801170321b4142809400c1615103001401640031f0301c0444c0c440001c50007414800340e9481c0000b01c004a031005070240e038031041584d001204580f440d0068200308000c0c00b24210345400b920314004884000114 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 402509379 1250 402508129 402508151
    0x1031d01020d060306110f04090207020f090702030a0207050603062b0602070b0f061507030309050f0102030109060302011103030127020f0d050105042415020124030b0f060f0103020a03 81
    0x226440004902c07009921104184103000d040d00800000381c16144101c0d152512040b24039283d405203000e0b510745a500002c003d0213642e18030b003410340d10310b4004004400c54104441d02a40ea9480f040d0800301601604200083d18035001080d648140009403507980c80e034440e00305100c0d41c2850b114610350040b040d000c0d00404500d00c0c2c4060b1800760f200d80e0701000d450070302038007a6030201001020903200e10100c003103400104a10f00c0540e1201ea0b4035060200e030800d41840c0807400d02d14081880742e465803001c030001419041c242c10140449000381c031000d94009203550b4003510391009021305c4001d004545900800d01e5555828a21190500c100050038200c80540d03040141d440f0552141150b40c6400040c46185041c0c481c10804010101d808403207036617018624440c1c507100d4424122441501601c0b55043d034000e401104c81c1c000e5085880110462912100d400600d00e0301090302d007801440f000684855004c000f103030241000030250002c2c9400c5400440296000030803480c201070b00c4141002d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 402510629 1250 402509379 402509381
    0xf0103020d23072c09131b15050c0d0c020112020a050a0807030e0a0b060a05041d0c060406020a0206280207030302190201080a1a030d02031210050f01031d01 69
    0x1d031140c50a0b11031524180103000600510b4040e00e0030380403550358800f98502d01c020380c007103911801e41079500e140250380d640001d180180d890000a010030b08000d03003884580fa50082c0c200700380c0700c1c1920341c400c0c41141540d040f58240a03100e5403e13207030303400180381100c00380c0118201c40c0181e10500d41908010700c0351140b10260f0b040940b40720042000480c2c45540c130382d0000c44182d4041180d25080290040c0044a0b503907545c00c47c9001f510350000b180c08503045071100700905002d4039010784240504c201c0004540c40c1043c0e8018002d43d0b0340582d40307504250f46080011202103509540c01045040d80540030032125500c45601000b6680d51040b08510a40d02501d074100500c116801811440346107003406803c200c0110690454158031003000700c0181e0b00981c140303801030201390780081c030501c000d2909104420395990b281d5051059040c0340468a030700000804075601c1ca40f120900b5a19200003940740b40350035000b1554412091180700c100e40d4466804841e41c4101040c5d0000c5240d40760400ca8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 402511879 1250 402510629 402510671
    0x315020307030b010f0f0f02010b1207030b0c1c110d0c0201051f0b0f03090c03030f18061c020334180b031801110d0b030c0d020f0103020d 61
    0x4044260040200700d4142d82501c24618162020308050001d030300740303400091140c0b0544400d0024401040203040020b8803d500c840d44400b0080c000c98031440d600903845580e40803503c4212046022400011042c00080064034919860680c030101c1c280c0074490f4000203480c01103458803100c00248801c4e2551200b0b80030307407841590306030000642410200450000e0045112040c00b604090840c100079410080e0202c40301c3c2d9110a41c3c80d500d175218211500c0c2407104c0600640c5d498032000c2140d2085500302002840085c0154465242c481a02000d00c11540600100011070f41712001044003820540d400556000c0c0c0c1841c0450030302030415010104000001c20100f00e0703046004441003525420040c99039035003c2d4805220480d0340740102c904010700c8000c154102c0c070b401d2041030030f25100c0c007500032011100d941e0404680b100130011100340140070701c02155119125890007000603003801458241da40b82c02500c00148401010b005402a502154556180b19270705c0c6600c0b2001c940e114815 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 402513129 1250 402511879 402511913
    0x309040516020d0c081b0a080301032d050703031b0203010c2303010e220501020a0203090a12050d2006150f01110303071d1e1c0b0606070c03 62
    0x12840d042680c441c000c1c580b03082032101c00c09200030140c845012401a1054406100700d1a94040a216950048904096480750300a004c4d540200c0044100030324040c60900b41e44c4200c05800340d0000f10309194030100c4403800c0280050700110300c14030120b4490041c0c81c01508682e081081c140b65254007107400c42e89072001e140009620308820341c42182c9510000130101043d11540b42c115414043c0125100801901002420045907228441c01c03003416040c458103a08074000319100d08444401a40720b0384030307080b064800c0481070b40c041150b00190040b402c000f60400300038500394500c00402d88040251403000302d003190203450400f070030400403c8003620401d0302005110410204005000c034801443c020301d41880b15081241c0b030201000803e070b039484072103440e01c4046450100d102d1604079842c19000c80c0c100c0100100b850001d454420040269003080d41d80359008010742c0313001040429100c0300100500a01d402068092800e040903200b60341c0298031130140b040e6250394010030282c101c451 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 402514379 1250 402513129 402513151
    0xb030a09121106010506120c0a1b0309080c0405010b0a18081009060b0603040302030a0507060b1002031c18030e0f0a06180812030408160503130f050f0f09040503090405 74
    0x10340b1544601806128010b0005a500508013209040c00c0b549204c0000c00d0380002c0400030a803125503507c03903802040c910030a143c01c0048402a420000c1c0059960700034004070f4410951481d0039401d01c0e02c1264101d40c1c0c0c14001c40d09152218070121200000e030700242a140445d00804904410180b01c8160f20803120030340000ea100e031500e8240c0070f031080c50010a101e00703000d104020100360048200c3d603040789a89001981e17038155113081c000410720680041c1c1c0010b001c0080f01007807a0000002e0540a4070041c00c550300c40f84d1102100182c0d0040c01c0d003c003040d0f150840c14030010340583d9000783c0406004028180702203590020844009041e481140080d100006000115200800e40800380641c81d000d003140303a01d41c003c0713030100d40b0000d817000308200800118000403802c0e8400b4620055440000c5d07903903415040e0080c04940110f0b02450002d052820800280c602d001442c0721680f50300604450315810748407080000c150341c001e00c00d40302c60100308180b040030340d80c1e0f10a103031140011440c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 402515629 1250 402514379 402514397
    0x90106050901080309061e130906030203010e2a0406080d09031403160807050a050f0102030a060801052214011503060501050d0b0c0306030a14030c06070c0b010b030a0912 75
    0x10802080c2041e800f60040e83c2040006003520f07143c1c0343c201d5411038843c246007050700d44072600c01d50b094890005403103c1603102180106580c031007904200c0481c1d000310002c2c0072101031b04403c00c0c1ca40c06480b42c807080b0a40c450034404210038600c403403200620b400400000301203954845460414007901c03032000005941c06402d004203c14401016800b00c0c8400045040c110419001c2d5041100003101403c0040041080e10410030200302807903030346920009940184540d00035003030107504142c501200315802d00038003180c41101442500d02c83c08181640e441030803680c884075101100f500d003083e598040300c011502e100c0c5009000d0441c401410711008200c0314070f107003050012110306802151281c0c40300114180414801d00351140c10456181c18a0760340d0326500002451320340004401130548646030f11a0840b00c2011007d00102000401036544e241d888035408c907119040400d00a0008900d03400600561b600103000c0c5500510303041001406a850752a00e80302449410b400000040344c3c60 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 402516879 1250 402515629 402515639
    0x40f0b0310061d040b0105010302130902070c1422180203121306050901120c02030c0709060306050108010207080d050702070506030c0c010c0306262b0f0516031b050303090106 77
    0x3e0407900030801c41d403189012a04041d82c07070003000501032045c2410143c0100d1010020701c0006482001008000d00031075485000c2d1600010724855032040040810f5203000009150030700d0031104101c4c3c01c0c25040768aa265440b61018000d00c1400c0e0344840e4511034a95100040e01c00300b100308074104000e404a07860340b101c000400000201c1d50803050400509004000721030f40c1107843c022403001e640030301003903642200300101c0ca140148100c0760940d208a803800100b40045603c09800d490140380d0901c0260303203a21802e401e034400d5580c01448110704000f01081d0001a910141c3c00c03d4540c41510b400e190b4950020b0010340090341c03c00000703000064900034950091207868455046420b05210507450700c49101f4020b000ca02141e43c002003500381202650f0f205200204c040016607412508030f079801c03010150100c20303c3c00e110010070303540003000c0c4032240248181d48040f012003d0411941d0b11664084904500000200070342c2c24032000024001070061018620481100c000041d01610300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 402517985 1106 402516879 402516899
    0xb090d0c060309030e18041b0b0304030305091507020d0309081608071505010f1a1e03060a0605120c1303050f0a060b1806040f0b031006 60
    0x69500070440e95010351010003542d0082c0e48060940e0342c0181400140d070301114030006982245000900000c2c241602040c3d05004010101d904580e20340c0d000c0d06a4000b620f0071004a40c480040203100c48081002c43d4a090143e5030150850503c500e019441341d8540450004040e204c00585060040d58021268841d1a4a42184010350a42880f44450b000280d0440d00405a285031108a01c0345005150580e620348a901e120315152200c4800f02d400030103000b41c10000c0c10b00c90f2040c5c841c1c2041d00b05030380d6414510503ea8a03e80304040240d40d4a1039002001401410320001f010184031a060170781c000c406a041c140c0d40c400381640c1c09141078440d0301c014911301c07841140382e044000c085250000184a0241400011030007001c02c006524083c140000364055200020030500c1c040d000a10b50b2610424005101501040468205505c00342c48511301526801c0c2008401d0403 = true := by decide +kernel

theorem cover : BRFrame.Cov 402338129 402517985 := by
  have h0 := BRFrame.cov_init 402338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 402338129 ≤ n) (h2 : n < 402517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
