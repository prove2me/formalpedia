-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4540
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:56:47.854918+00:00
-- url     : https://prove2.me/submissions/d33480b8-0c2f-482c-983b-cbdb5b6856a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 816366906 ≤ n < 816546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 816368156 1250 816366906 816366953
    0x306010f0215041208070918090201030b130902090a091e03020c0d06060f06030515010302030606040b131d251701030501060e0c0712030504030516030e09180703 71
    0x941d20314001c0b0402e01124200c60900f420506901815800400310b03801440c00e040c00390066042c2301205c9a003020b10500d4203280745d81d410745441568800c0c0c000110200c00a05640c0040b04220025000f4021400d0140d00600700301d808500512594421b07625059040301c070b2204000c11000d56404003043c5403206600314824401400c5040e90b032034150070041849450006006441c0c84000e14007602c440d400750062600e00410040401407440b4001d04618007480e0040c2ea075581c100c00107800740515007200b00646004140b41500c6560200d9900941d4110b0742112001c0030580308010219800b1900e081c50000f99445000c51600c407261084002841d07828485049004080040c0703025009900c26111603450720010003080e0511142e5a4104403c410075910f03107140750300d5610020410706000020180d40e0703c00101498440c02c02c2e10480341c0c1c900b001c0c0e00a620581002070190720000609842010000c010800b402064099032211552290140c2031080c6591030f05510010707003640001c05e070071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 816369406 1250 816368156 816368173
    0x1140c0a200607020d0306090606050708131a0c010b0d021c060209030d05070606080a02010c1101050405121f0213090b130608070819030e0415051302120f010b0306010f02 75
    0x260140040b502c500b2440d4020500c01094910003802c0c5c17144c0390302c0406050718048040c0030030b5a04c80b08440c040d541050701e13181e8440d41c01c150b11825000c50f501c02e149145042440502c0228410000c2805040200007031081c203a41100700102c50241040c002d52207a45016046d0000c10061609211140503600c018200592100820f043c42c3c0701e0038100740059000500035003004194030840000d0710303204000380b010741c1c400d41c0082c004040d80800502501404150410300307078894030480340070300b0000e0a0112210b414040c00c1d0340e522a80c040004500c503040b030158540c000c692090b1401e4007041c0c6950f180c44d92a1102e002e00900082c500301c0d80204110040c902d5003541030040d20000c201650007490300600c0d01804070304000c81d825040100d48080300f10348020940c401410010a00d04480001e004841c0c8401011071846a6000e50341110107600317650945656507001d004504000302e07107040b4a54800441c002014002d00511102520900101d445544104001c169200890046503403c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 816370656 1250 816369406 816369467
    0x806011110020d0f1d190507050a121104091104110706090b0105091501080412021e0d090f08070e190609200901140c070e0a060801140c0a 61
    0x9070300c010a01101e10751104c1100c0402400f40c0302d500f08481901d8240115010501d00d01901c925000d100001009200c0862106024042c85858000d010043c540da40701c0b40d48001e2281e01d0f4a20240903501040a01081c01090410340105030342e071907002000c5658911800108401044009a4103c2e030010620510000920520801201a01681210030951714180400c0001e410003002c00040c200c0500700000c00383d8000900c0c5405c540c0c0125070055005845404a1030075201d0300050012030460002c0140088000c03030345c2124040b441c3d489411054450340f542803410380e94800c0700e181c0d40c40048104081ca10255170b40d40c000c00804400c030080c441207261703402a18100e81162200c0780c0d5455500350308041481e9020340400c003445a444c2400d0080001810000881100c20001c40e0001003120001100744a008081c186165180803c2d0610409210061000b80921580c40d86402c00f01040000003110961040040c110950b00e1320109820031117a030751030000c520074188903101c901400c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 816371906 1250 816370656 816370661
    0xc081e061905090a0f05100b18010e0301020a030c1d09150d02030d1e030b1c15020d0b120304080d0c17070506060f120a02010c050a02091003061a010806011110 70
    0x1144da46201141d602c034244c8081003203900c00703480d006034550303c2603040020351441026130307880848070025071a2440c1d2400040e510b4403004800168954800a1190101501a8000c200708002d983c1c03182c1010404100343c103c856840174880b0703400086a400101d0031040001200036039080508129400c11007030340402d181c546031003454000700700210039400600001c00c60007a005951440c0c140460360789540801c08085021040c58850000c81c00c0c90014080710644428440d14400f0302103545115150341040241003426000d03109491001c80d80c3c03941d5000000741c6040e04e0328040a4182400400415140303021402400c642c1e00b40700c503074401106111600640300c114081c0b4003503c040d18141d000c01c0840540d206a10f0302c03501d82c0b459001481d8900041030a1341c650b0a0800300784071007150403d0344c60148d8103d0000d51040c0540100410174a4a81850f421240f05e0501401a052100b040c110b10001c5540303240c1c00125220700107a00e541c401c0071154501980c80c1d0030f4541800701980000d0a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 816373156 1250 816371906 816371911
    0xc020906041b0816090312050313020901120209010510270503010204060e040f1b0309110307060207080f0f1b0402070510061a070804050d0c08060a0c081e06190509 72
    0x31848007010000850040080c5010031601845d09540160550f1340d002a0040c0e0341e4400c030200100440094a41480064000c2c1b00c1900203100e5a101d42c0d4906041c0c04c00c560288040b07006020301c0e00002010f080090000c0d06034002600ca02090300f0807035041d044080f40f006480300188031101c0001400f61820b20041024012035601d21040d12410070600c41500c0480c4d400c0c034032040c60701e01c810602e43c142c074140e0b0514150b14900443c03451018101940100d4500c003800c0c2c0d06005100b00010910380005604040380c5108040d100708000e030044180e15610745a80b104055001003c9c40a81c5a8480d000b115000c40020401030514130f4507207800d45041240903441c40c40b15034644c414030407142c41107130b0300500100c10345d074035881c0c4407240d0795074000c40c0035500c5120700a100d00c0708040100020320388180050030b2044100c030080c1c40e01d9890035024180008000000c1034045000c034a194030181c03050790051441d6048030882c1e484940074064418070005074440700402c0084003251030354078101c01d00d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 816374406 1250 816373156 816373211
    0xf01150c060c2303040c0e07030605060c0f0d08090c04090f050a03020d08061203040e2212090b090105090f120a05030c100e0d0c1704030807060c0504060c02090604 72
    0x42c207040c06400e46400d03000c0c14610f025480c0d54184100400105002540d1003512046041807406407501e0300160045d03c0c19800580e449130000c11000c504410004031600d80f81e001d081118941c42806505030742e245820b41c3e8103d03e0341c015201d03880884c1010f810103400c4600c10703942240302c0702541c1c60f11804c01c00ca244044005030440303c110404907070300004c4942c00200c1210041e40030121480110356901c030303034800c1981070f000d000c000030550030000d211100a0200a00329044900082c94112080322849589074046016100c001c02d5641c41d62003a9032000806031502c07440d150128003000000200c00344015440703481035106007142c010130300482c04028800c400441d160907002c5529400c0282030080d4010700351030001c40c2d50b20048000707400c0394a00c58074200040003454130b0504002e0000c0c0a600c03041440c0d00000c0020411030520000c055590060908100c40c1c0303403001080300c81d44102d02c01c4000250b01d10342e0102c05440e100101030b8010400030300002e00c4c2901c005145084181641341d05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 816375656 1250 816374406 816374417
    0x121a0a09020c1c0207031b12051608010b060304031b0503040909140f060f0403020304031a18060411040e010618090b010608070210051e010f05030c0105030f01150c060c 74
    0x320400001080701800c03240540d030460389034010342c0fa0025a00c0e08144006081d640303101813001407000200c4a0715000d8214040500c03c0c0c24020b061080c0c1d2505100070108103052040c0340042c1030041881768421700c102c010030041c0b868a81e82c8044445080380a540680380e07000304141000901c040000780000c2001080c042001413007424000500042521340d4071307017500301c210000020040451200c2d840589131003201c190f600d450400b00d1a600a5420040000d803280240343c4440c0c00c8042210700c03694248070b210042c010f12400258880c142079400034482c40e03200c035203060f991510b82c119a40902e0340d0380000800aa50352948600d40380c904c4d40c4203548a44d034044403001c1c0150524464003400190605c8a0507040000000390394000c5240c1014001c1c0d6100003155140c0f20380450300000650b80c0c564040036507150b0f5141c445140345131003035078840d102c2d80b85001d4855000c3c0c0150703031103402e022500d106268a4822a980242990400007003088440140b240000788148200a03102c1e000d40d176213 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 816376906 1250 816375656 816375667
    0x7020f0a0c150c0c03080a0512071709210904151202011b0c030602090105071a0a0617061603061a040906060908030d0b0307050a24050703121a0a0902 66
    0x285400c119150040b0304210356010034402058410542c14204c0340d1101480742c0c5e40c02005e104450300c0c0151032a010521340d0800900000355403100c070400500440701600010303516801e643c15650040c8014803039041c2d850750240b8040e0040c3c031014100d83e100142010466100c1d00d50000144c14894001c6090100700e050f01e1015540e100590b0080740182c24015848111142c030358410358000c3c1d10004210030340001d40040c080e40724806403048294440c0c1c4540252580001d40310b8410310031038000366458076008000803000e0000000d0721503000c0d080060000b5031100182c01400018500c0031710141034854000098016010240c0588403604094030398465080c00300500540d0b485512100c100f00203146e05000441e00802101e4484800440c001480e1a810000c24205051a84600c0d8000304801c00040da0321103040d101c00e5480c03100041e078004010020130070307201030007100000340c0010300118070360801e04440d84c0030011000341d4009480410030100001105440715070400d030101c5401140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 816378156 1250 816376906 816376919
    0x30a0b071808100b0105070c030605130606061d091b070c0305070f081212010e1512010209012a14010609060f03030e0103090b06100c06020c010b12160b0307020f0a0c 73
    0x221902c04400f446c0262900d8100d44400500306032501000d09055543c101142075400320321107149034103a004405112042c0d48000180c4224035069005c41640040554a032007481c00c0c4046c1361140d1070741070240c25808040f0b0101c0c4c8880d00324440840d0040700c82003010002c240300300420402401070481440102c0d0610700301a09001d05007070b074210810810301410544518041d1400d054405981034032143d0340d20b004d82050115068064950440e42000c0d1900e4402d030190002e00c1c03a40070a80321481d100030740d034030707c020001c040404c6141814031100c8010000b500400c889070a0040c3c0e200045100d507282d940100440b40c16034400300702070b10144410001c140e0488c0011084150909040142c0412078840702860310000f801301d445401c0360078402001900410807058400d4210b201151680b0710005814001c0841421062141d181b0556007c96a540060400351000d0452512035187e86441428419070f08042d00d98429801040c4028910709020000311800074000c0c3c002c81400c82c600750 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 816379406 1250 816378156 816378161
    0x40b07142b05160f1701060c0203031323060f160302150907030605071b03030e012409050f0106050d050402220c030605060a0915020109080706060503011a030a0b07180810 75
    0x20900c061020a10610083d170042c00034550444606003170220f5201e4941c80000e09501c07a040b448004044900f001058040507c2a50300c7e00002e080940411508284200185406180c8111482c0d00013002021034862801a01000c124401c1c01100c000c104102842070070484100c030f9401055000c6401001405204d000c0c06030026041d052015588a1100b119600302c0c02004003e001c1c10b481b13140c041204142540f003c2104441c070300d0301c1464180f00b410010380c5034860381318555000d030034031f800704201c80e29500c800c40c12103955032105440e142410f65003001900d8001d100342d90016804030400c018910035094042c103020401400541052000350290072118a1f4000c5801035409214000c4159000b508003c20f5604110880ba00c0c0c21030140d04030301510349081c0003806c41c43c011039100100403191300984c0036070348114000e04c9805215201c0b002100102550f00e0350540c002500b0300085100c000e03a560300000340c1d02e401e402410703a01110324100495a4403400465000c2d62a01c00d40e10200c0c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 816380656 1250 816379406 816379427
    0x306020f21090c040c1b052e0f0507050403150b0a090b0109060e01050f0304050c030102070f030909140a0c03060503060c07031e0f0f09030c0e040b07142b0516 70
    0x100c070704002d111512000101051070400103805540d05060612007800300230046040400403248031078086420648000b0700420109006003a103604090302e01d100c258490040c6480f0f09440c0d41c0e03050401d81b941d19003010f441c4020070320219007581e50341164501d48650600b8405001c00e00c03408511800340d0f42c001052400307190300a07070801000241c101c06c1c50ba40a0b00300c0c3c1c003802e5910100d680b03940b12814520f040800c00c0303000303c0d0300d03610014080c41007000c2d07103068240c424005d480741810340f070740c5a00410030b4801503040c1030f00c1c03401c0030000076190101507480005090744502d00010000c1e2588003080c58650242d4403851005030100c6c070a003c060303014650312070224042e841581d041c03035110300240604810520210501501c110007010040c400c949890041d5082040d01c4122540d45449095541042d20161000b40b404d03000031368228019904001182040960240740c046910710850b44030101440091b8003030254012581810800e00a40c4d0160311180d00121203210300c041c02034042c0104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 816381906 1250 816380656 816380659
    0x30106230a06120c02010b030f1c0906080105010309050f060c03061306030218061c030c0b0f2e050414061002150703110702061b0c01180306020f21090c 67
    0xc0e45028400c0b154054501c801200070f03036202080c2c6041c1c4120030390140c40d40d290720315054400d0052036242007500140841a13008054850302d1260303101c0703104840e003c80b9401444042558480108180d503c240d01c2005540d0151090328807426101c081d01d400c000d000d891046040c0c40120034806503281c00d0316a00f98807552210304204030751545c1d01085401b0f503040401216100e00a0010b0f0890310b803100300700c1900074211004000740110385800f816010360680191210300406000408c0c1003e401807043c01083e01c1e41c465013208044ca20202c01202210102041c00f01d1840f2001540e0344440c0600048040c1c4240003006500c0d0400c00d20140020191aa0046502207203290501646041d401500024a46400b080c2c40007100c0c1807100d28412048025007000c40014880c400030301c0354a0310b0b240403800e0390a80b0441d551242c0119000c4030035501e450461038801c0004c01c00034955032b00401c40504c1401600382801000103040c146040b5900c00c0341d0280d4030000c108410302100388070041d8004070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 816383156 1250 816381906 816381919
    0x105070c0e250c021207120609060e060f040614220819020307050d0201110315040207080d02030f07081006111204060908070b03251404060f11150708040602070203010623 75
    0x82c0590200382151003180c003070710723240d5950f401d503003408400c5d0404070303035500c00c04201c0e4000d00384420740c2c0310b54074030481d003d4a5482c0f5000032071042e90300181c4158040c00082500d00e1316581e0700c0c0814072000d60001011103403000d0800802c1d50030710621280e01c0f14000d09070091500e03185542441420a0800382840c0116490500e100744205030080541c0e42180391204603a00c0a440000407074001d204002002d002e041011030582c202c507909400031442141e544c40100c0341c070380342c422301035540c003405403111401407401440a0140a104000c00321358004400111801d03c651041c500c50035a011360000000074030ba0000500118508011300d400900c0c90f0303104640b6520b4042400030a10714840510034a03546080c0f1505691442340a01c2006e801c254181c4a640c2c542d1000094191540b626140020030624820142180d9000c144241061503d08a600b01130f542e9510480b2282e40091040700c3c5036500703004803030158400b48120b8001d004407072404041e0401010359003940c08021024144070b070784c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 816384406 1250 816383156 816383159
    0x4051005041a061e04030c0f03140a05030f0a090b030405210a021c120f1b020c091f0806040305091e01210209040e010c0e0105070c0e250c021207 64
    0x103c480040b0b41c00702c0d01001451000310120030541c4043c3c49035910241c00c2188100c0003081c40d0800160f89021284913030f42c00380d007250048407069200c07101c80f075019100342c009000080001103010000c2a42003031901e000401c403a1685140c0c0c2c020f4000755000d6501780c0c030140200c1ca00080c5e05488980c0b0b10440980035050840c0350000946e141d2a000c41004c2d200384003100c8924044c01030044d081c1c4150071340f0050250300341000400004250000c0010100600c80c401d8500c6240041107000b4200b8002d40a2809540d44858440c01d145224048030341c0e40c1004800000d08410510031140914804d070b03103940d541d41900042004078012560360704619507800582035803d0ba027007070302403403200041801d00740164070008448009019403c11941c000e0700308041d0f41c0e8926810351207900c4941d09519a641d2401c2c20318011201405860001801405802c1041c0a4007501c801e42c42e0b48080d40304c81141000a01c0c3d07900c3d0b004c800c0d6522050006c942d0316003440d0b04516200080035041c48070f545c002c20005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 816385656 1250 816384406 816384409
    0xb06040b041202042f07060b1f030b0d020a090c11030705030903061e0f071b05160f1206050c09040911090108031e18041404140c06030a0e0c04051005041a 68
    0x2080511741c4005e0140c00081c2610412000760032403d514040200700302e07003480c0403540c0a03054013494103801000a10b4070801a031680b0b00200c5c40301a05802815026140341010f00701001041007072210020701c41512034108a00c0c0c41000148102c40c401c0c4051500d1740074420900d40303400c1000d050080c08400d007035005441c090700396040a81c40300b01c4484607805900c82d02000d0360f8111036190242501c1116403140014402c001a03010346050b0107035107030009195120380d071040d803141038000c9211000900c845140802c0035900200c1c0c000580c4d08c0b0061500d0081d00000301211200750040b103000350000602c0c480c501c1e044004e6030050242034003440c80c04148000f01a0b1401101070240201c04001c29031000c2030904110480c000c00001e0b0003080120404520030311012000c40301242c0c09a801c91090425910100302030f100c802000d410315086032100c00702d041c080c283e5101040c08520a076100c4038845c7e9514010316029101c00c030aa038070040c0c2081d050009030f03071001e0b011080151010704008100e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 816386906 1250 816385656 816385721
    0x8070507270504110d030c0b0106110c090c09090901062111040905071502030c030a08011a0406170606070f031e03021303030e1302030108030414180a0b06040b04120204 74
    0x136480c01c807161000e05003a0710b015204138107580406401c0310260800881d00940024403c0a40031340d142c201e03541c5245a1080280c40081100e11858010b01400b200c0f130305052010141c2c0c1c1190034000040b0307c9603155588401c010017016007698465103801039038014000084400108940140d030300384418841600c85580e10782d014441d40414001200d003c0f0300351482031055400100412054170340d6600e01400007002c941d404e004000b442540c80d2079840919694208031000c80744c041c6c80d41040d50020707201c5e03100d542c8401003040e90010420024003002402d5400d80c01b076418403d45504400c003000d480a0803400042c00d0011080c144100f013460424550080c0b4030080b00d41c9458141c500081d4140030809046a0321300341d4040c10b00100010070021004405082034511f01482001414a0b8408000c0c1741400c4030b2410340c44c01440c1000c5010300d9035641245840d104041c04517840c140d074400c45445a68045d6004040190712800040c0c00c524007402480700101c00d4011104010040d406079901 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 816388156 1250 816386906 816386933
    0x50a030c02150f0903040e090a11030703120509130e060f070c080702040b030c0d0605011a0a05030601110c1509040510033903050c0103060b0f1608070507270504 71
    0x21000e511070004d081d42104004642c00b802c0c603d14184024140b01d60070741c0d6079110200f012218039401003018092420001002c00c101c9802500308044208080020303940e503445500c806030031125170324250203000c106025614003021004020300c101e250403513803103400003800351a417801c011030741000300049039900e81540c21054040300c001071580a0503000a1810b40704c40c031025000801040341c0c0d0300b40220365204034125045250368060154422002c0301c4a03206400c50480894410300c00704110754407441e0900d00d14623207a4200e442040d0724800003160100d484410504100c40040d2805140c102400f406400580c100c0c4a8203000c2d043d81d86851103400048a2800034850010f801364400d9500c4402c2030f00401d0b000d0141d4151510390405986030f0040650083c046818120000303400c442c00ba044034018007000d42e0050505c0b015107040001d0070162202505c001d036040c0001c1011403011700c01e00c0f000300034444042e41c2d111492041c0c4032606812503407d1400350318001c208004240c26444900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 816389406 1250 816388156 816388171
    0x103020328021317060106031401030f0c0305100c09120c060c060b150705010b1801171c0507031b0c1215110309102a050c010c050a030c0215 62
    0x810750342a034180400280140f0304120f091466952000aa130403103414110410f40020381510801c0e80c03142d030190192040c0c10101c0a50110710f000402c0440d540d2381440001c9803260605803415035032602d9417890030950b035498942040d900c0d90044000313074000b0200001000f01d185403001f5980705841e40d141710f48640c8180c900b0301014019103030030400c3c1988000c00a40c0000c2112111900ca041c2e00709494100000881c0c00b517103044000d40051800009000c160000c6980203081c980c00c2501001307914030484104030703e13031080c00e00c1c20800c441e2541e041c02c841d9900703031b440c1c2e40c41d09214240240341036259800c10700c1d804110200341002c20b4050f15020b0569a0707070300d800c03030940d152890031611300507031513152800d41468148800c502c41c10031002107005107005402c4440b008441d07840c07541140c1c602d0300c00001c20f841244605e0002070104c03602c4078803018641000c42c107005441d6146401e4801035074041c1d001940009682c00d6007a00b6100701010f803c10784c4001c0425543d101940b2918482c046d1684 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 816390656 1250 816389406 816389461
    0x3020607080f160f03030b011e050c0114040b0615040b0f1c092f01050d0f02040522050f150409080d0f050103060b060f0315030c280501030203 63
    0x404031414542d00700d031444018610490003030340190401800d01d00501d0011000a0b00b03014101c0700315807058019000c941c110841c03149005200680c1a20180e20454640c05255201d04980301030101c01e0028038070650080c0111145468500c2c200b10b40d400405001d085022001d00080c0804620f05e000e440c807541c4d500002c203a46d14112070324011750108891991b40020704102d00c0d041001360100100380714940660f141c0600300c01502c00c00c0d0340c03010b01c1290300f4009903083c009912503441c0b58000542e0000c0c610070045c9000d13250004a4802c410001e8003e201d495902d850303003203001d0123116091380151601c01991a41c1000c6d00242204052a1101c0c4d200c2c603110300c0594144540441240d613411211041045402d01c10804080a802c0901c02980c803030307181c000072900e5420f040085810410449501c1c03071070f6541d408504010564030444c0e403070b050310409120070000d0310b03020348540108861707070b03010007000e40c0001c0c3e4290305c081346800007410140103006206082c1c070400041038102d03a608400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 816391906 1250 816390656 816390667
    0x10050d05070207050406140102060a060501121a0402030106022104030f23031306090f060206040b0a0f060605090f0f010206070507140304060908100204030c0509040f170a02160302060708 82
    0x80380f8101d0690049a0f0003841d014000038030b01d2406030442981c501c20b8003075a0040d55030001071001c07207116202d000e0104030007002c4c4114018440e484242190b00c0c80031069081c00d02e0801140032604240c0100015030b22400c0722180000d034802a049101112007031141c80c090965a41c201640001c07070000b051188602c01141c1c100c0781294154041745c90300390440b516035480e220a015003000c035220f414085509014081450b1040200d0740080e40c5003030300188003c2e105d95070f031141c01c0b44c40141f410321000c1d5905099601c1004c01c0c0103001c000e20032a03030b4984c0c030754041e2010402541e01c01010944188900c404000c0240d07000710f0000d40c4070825081641d111a076608000d4031820940d500b042190000180205640350403013005025281c4140c106c5c0e044c00303182c00021040f849180805400d02c0c99501c001c001d50f1524500e000e1b8480d100d44c03890228641c4603601c28059a01c16041d40240c481c2c045104100607504200100080d5201c1c10079802113840c54002c50058860440060800e82d0002407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 816393156 1250 816391906 816391921
    0x20307120503040302060a02031b013e210f01050906040504030206040602090102160e1f060c121202071a07051c0903030b0a0906030312020415031e0216020f10050d05 73
    0x40e20400e01404c2042d410090240b0251400bc089c03045e1885407501c07103204049502d0103043d0504030703a08075330342100d0504030705081c07514032680200039030b01650403040144180b100b43d800300003409520402c17000c9011307504190410200c0d501c001e1040d4050b6142404100c08240e0004000d900290015001a0350701031800040741060404000d10404442043d0001507c24021100b02d104802d0b07034500b0400c2e050038082502030382c1028442d0701300090403074a903003010415171961000601075508040d10b003201290030040a9812100d025550703200e14002305000c0c00820341420368824054a440303440c10041440000c0e98500700b25640714081d0b0785a82c04010540603034084501c000300140b2140106550b003403808050320b03850108030700248000100c542840d40500980301511260b6a428056a171008021402040e640d801c10742ca400c02a20541990346982c8020000036509071060040c0c080b82e40180104103070154140c0c0c0c0116410094440c100760300c01c1c20384024808444001c0780c19101d460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 816394406 1250 816393156 816393163
    0x13050604112704151409060604081b0109090c020607020c0919020c190516060206010b0a12142d0c030c0d0b10080106030510060f0e0a1e03020307120503040302060a02 73
    0x185104c0d0005480100072400320070603140d8000c10901219044820340d28803042c0302c0076010354800c0911940c8407190807102225000080d08003c03506240054005035590700110030b40703541000080c00743e003000781441603265061003510310b08102651503803441e0500e14407880191318907801d0780d10380644c04510517009080c1840744d4028050403000e0401c6208040c10940c3c2c40d19200381500c0c4030014031703110000e4264000714440e4102c4403c82c51140c104143d0070700a549095964080c0d45c0c0d142d5865000d640c4a5400c440304600440c50359200d40450440039a102d030705084048804410041200c041060909110040b280d0010b1a04842c0e626212030b010b030301d0090802c5040044e4450020521151011b40c00b25010381214001d071b0301404607031910114080c2002c4c144c080c01e40000e66212401c01d0060103501c0a544d0440301824155080c0d582d022038980c03c40d81243c0d11000c1d5541000d0030019850100000001727825070003c5018401001c0d135581e652449a80f000a02885012840c10711542c000e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 816395656 1250 816394406 816394421
    0x3150b0607050d03050f01080f033009100c030204050607020121020a08060f041a060c0f1c0906140703032313050d1103120405030913050604112704 65
    0x10b0b00b1511000e1440c103000d0068072044a4211003d500ca400008119400007000f06c12000380c100030f140340c0310300c0036000c0040c1c06207502c0e0300443e001c080c600028401c0d01c00700b030507201c0d6000c40c2c0504000a800701d4440c0a0707845901012003010700500c0140f000d6030711101120085542400d0041e41c1e600f80342c901c0301800d844042c100c140284045124452180c220410718072a000c00c40d060f000d588250340400c42107801084803010925090000c400b44c6003003100c01041c01d4940740b000c480803c00c0030548589030058440900020361007014a801125800240d808080c0060b400e000c2c2a0a22852890790315003e0114060b0815031078100300c3e1040910848903032249407002110085500d404403100138142805d40f81182c2c18030607407400c21030710703482600c0180b103010101d0080c501c0c100b000880b4846001001c1d000b501d243c0020444d018442d41c1f80014404c502030542404a590300d4003c040004456007a002c40d4520a02002840b8100300700b0080301c030820000d40d003200e5010f40c0e2a0041401048130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 816396906 1250 816395656 816395663
    0x406030512040513090503031b09120c09060342091f1503061509020a08010303080c0403030f080a0608010f0b0f0d11010c0303021c0b0f03010603150b0607 68
    0x751100000100018030080040d00d50a440851112600400f1202150307000c01d40501250003e001040300105101c0080d4185104040c5403810441c100001940c02c400200380201c040d40404040c6000382001454258450f504130050308119000d21008003419454405012034400e90280c045030210172451480504120a03401d1080d03031230001c180642e03402c074203080b003840000040d9040035042d085004400301800540010180380d0b01e586d4412001e04441011003103024544040491001d1036032015180a02582c1d032013501c19491410701824003200071b450801032190421080c80400d070490784420b06220070b0301e0001601e54030005160020b0000b038005803150b50800808a0001d00f1640040800c0e640032140440002400c108102d17100d0b43c0d18600030513404102c28040000d601425003040e082d40a410b0151500c0c42000c01860f045481d036035a00310844d5100c1d128038586c1084021211615425002005040c0c113548941181040440c601ca00e40e0351520700303042c401d071a201d0603074060551 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 816398156 1250 816396906 816396913
    0xb0c070509100801050429060f0d290f01080604082712011b08010510030507230307090902090d1407080a050c1c0c090c050705241003031d04060305 65
    0x3018500b0486011417180341d41050358405025902c5034040300407403401a03500070a040820752700001400a0010008801c2c1c030f1000010395510030180c1d01e4100c0b00303000240d18040ca103840c988161141c2e007113081a0081d03500c03544003104000000300000704642c8040e030851100d0301c101c80400c2c1c0c24182821807200c41d0350000550030f80702072210f1054101c0703003108004044d44915984942c4040390482d100f441101c4e4000d9001c019051680d00a40c0050b070003158529040c0401290303142d450340e100c009440070305003520000041101584d40310746524013402c0543c0c0203503d01030300e2400081080421802c040c0c600483d002c5a6616244104501e02c000c1029000b0344000e13000c1030400729254032040d40070300e0103051707880640085090b11071251100d09500c0707981000700301d0400c48e0600040c01540500f40074800308000c12404508104104014940708140c01c5142d0302d182040c8840a010140020342c44405680080c000260400815004442e1007801000859484400507002d48810b0303002520900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 816399406 1250 816398156 816398161
    0xf050705060a1e0f0c0801090b0a05042a09050a0b070b06090c16050a12080c0a030e01090204020d1e06050d0602030a02070b070c0302150106050307120b0a1404060b0c07050910080105 80
    0x13995000202100702a80328070107030740c0c0e07200100340540c1d210700f441c0d03603104100074014403152606a003c4450f9615403122507800c284d2001200010340c840c1e0401c0e0020486036441085540b418481b800b020301070348a01d0380e04000c11136544203080079000e4030552103207214000050b5400050360513550300024500c01c3e01e20703610700307420156140e45541d201910b811150300c0071105250f0150000c1c82c01041c1b8050014508040b10004030004c0c460386102d40e140395240c401407405a40c4500141410040009000803000740c0303d07041c40041c407142e00b03619101d5428100100450b40d141803501142c6034000b140541e6a40d9582c83c640e001788200b040040142e4404814040703080d074007060380351425129408507030300c0d404501a91030400030240700d201c0c0024401c0000401d09441203a100403122014031020aa42100d100000c800089642203441807015a6110785528503042c01007100070300c08207110720b16154102004c42d89680c218000c0c240a10140f02c0441c1c0d800101290040003004810020011030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 816400656 1250 816399406 816399431
    0x21207030c140d02120114031e010e0a0b09011a06040b070201090e1302181332010b030705010e0f0603072604020907030c1d0a0801051005010f050705060a1e 69
    0x3d403c091417003c503402111002082400d10980b01c00c00d81d0034000c0091001c40450007104030381c02102e600740030352952220340003035442d00300300290f0b6800e501c2072401017064034190b070080c0c1c01c658200107208103806500d03101515545500080342c0541d440f070300e00c040c3c0e81c40311400141e03800e09079036010341c06502a0404002101e8100a400c0309220310881c0e140d011440c40d011108042c200c03d494000c10030452280b04000522120003140c180f10003c03803d104008403100807541c01c002040c0005513165101d01e04404540340a04c05000900310900700612199069400700340c403096030700c00260280700b00001240409004500c6444000848007030311034043c0e202c40c101900850b0665040780114803407404202c1c164060b00407610002c145541d12501c08445ca8500b01e10800310491030380d00700542400c0421407600138000d2034070801040f2083c0580c640b5000005110f802ca48600c1c00401005014810000e00b020130070941102c0086800b084c4541d180c40032017601000f2054050503140340004c0304002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 816401906 1250 816400656 816400661
    0xa0509060f0c16061b03090803120901060602072d03120203090a0504020f2a07060c170c061303030204090e0c0112180f0510050c030118021207030c140d 67
    0x1103020100549150f9100881c0c024000c941034000c110101e003041c0014107000640c4d400720203000707000b850b014041c69079034240d01c0d007103038001c014000442e40910200f1034940700901400e4010f040d10300c01800507910b04800901c501c4074487c250b09604410011081c049010800014043c41d00500c0c40c040b00000c140000c1c3d902d9002800c200e002d802d0704100014107142c58825143d0400b44212002d107405030035690380700d090140300007507100c0440c136003051380e050031040020201800843d00c1e00e200c0d41c203240c10440c8080001a5060704091000c220b0015592004140c0c01d40154410017030540110b09494250701900803a00000e030994038028420103542400901c640b1488400c3c1c83da5055001801d6030700302550302d0b0110503400b40c248030004000041d01c0c811070510150061041e00d8002d0300d100740240030b651042d1420060b0000c040014480c9a40c07200d11003240e020000c00c01c41c500210a20b52100c0b40c20700a042e402896074400d800c60300c00c0c0c007400000d4086a0f50750f003c95039450800280000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 816403156 1250 816401906 816401917
    0x516030c020f1c060b0102070303090e0714030109060f0806061813051204140109080606062b060303020d180b030a1b031d070308040b0912100b1c02090703020a0509060f 74
    0x70f1130f0703061608195080d40003059a03002d880c1c06580701d079660360406110b0103540c600601110100010611005100511940030b540649141c001c08614903103018001107078241d85800010300c0703800040501240c2ea41c1c4000b01426455845280301c8980c1d501c0000300c2e081031140c4e10284c00e60160718882e8000c8031042d0010400e8820307251041c4410030350750340116240c48950042241d180c0c030280102d059842c088000e855040e074000d120903129910a0034400f140b42c441890794814075103a40c0d05208242e01442046a02c000a00d4401c2d000412100c55441c010202e100700240c0400010203d90710100750b030040004000c00401d54180da01520300000c0007451280c1d03610543d0381c643c0b4081d5801020100e1001b0480c0d0b04003212038103050804c8003448039680540d400551200410403120200c1209000600c80c4250780440040c0110400b818450040d0042d4500b154240b80c01d1180c1c1c0050303880500840d080015880c0060f1903103c90b00003070700c0038813614628940c48100885d40e8a80d60716090700a10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 816404406 1250 816403156 816403163
    0x70b120a060b2b0209040f0c02060f0408090103050a020f070b0906090318060c07080f0a020a0f050105030a0507030b0a0f0f0801050f040609050c0d08070c060516030c020f1c 76
    0x880140e4400000d402c034000d10b018850403100907540c03030514015034111050310f100b010800520708004d001c000b50032241107030010b10441e0b86400010301910b4061101c0342e0712241c1e2410402d403510342652000402d1050890b45c40c181a07035900481d03c0b0500b0b581c161555048075031003483d9192032604100e40b001100f02c4100c440d5118400001c0c110304004000c0d030b0f010354000301c03134200700c00080340800c059600071301e111000510660800003030a42d0100441260300c24480e0207400d10134002c0c018489000ea06420031020012200c2d420012641c0c400100d07075000c40f803840001400d072920007045015015203803145500c01d201300b9000c40d2641c00403603c0c3c000c441e00c00c221010207960361003100d401e0700d1085a81415540c1c2da10002004a06a500005043c82c0f092043c0d030030501d5900000f40340c58030101421794065601250b210f00700880d40048002400150a01600780120420f000e25401154540101041303140c030700c001d00b1511902c8001c0004d00f00100701c152180c0714130303080381110f035504401078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 816405656 1250 816404406 816404411
    0x50f04140d0504051e040903180b0f0304061509020c1f09020d02060c101103060f0108060f061b03040b03041208060a0b03370b041a040e070b120a 64
    0x98103030040008007041036004580382e0909051400341006002c425203400554081d1035998078528503034580c842c588105110784c0740c581c0c98010396429480400015045121001010041484c042130702c001603da11035072040340071500300121010740c45403598643c03040403580d002040b034035040f91000c55001e4510502641c00928a8104807045040e181c41000180d00802085030000c058100540101092032081089423030b0076281000d000300311391091083c801e010401005004180c40d082c2ca41400c48039003464039a071982800f00008032500c10059072144540c42c0002d401150050f211091607050141c00203881e03c5586da03101d00207585e40115011110366801c1d02d13008524600170106980030320805000700e15042d0800d00b08642e258070141022110500244401d40603002c42c00b4610b05494441d02c486028490181c296810743d9042d6000c0d0f445103007440708107014148000c1d070909114008941c04240c00e045150b007942407641d6600b056030300510008400f803164440d922024010f041c600c504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 816406906 1250 816405656 816405683
    0x190b0108010c080114010c0318121101020609060c160611040509010506130312110d09181109041a0d0c0e0f04020f04050603010605060a0804060e032a030706050f04 72
    0x843e50700509014540901100c2800c00006500c20422414554842d05103008141c07400841107245030816440044510030000441e03080103003c0000c3e0700c4a0350203000402c00707070a001c141e1a848007801090580c0c410004180c521220410460781d081003600f2030020824580030328181440341d402401382e58013441d0203000018041c200713002140e84184d003d04100680c50b00f155106c0e160485a04205010480c04031032407004c01406000e1111882e0b400e03200d41407000d01d0b00024544001c00e255041500600e00910a06071403c5102247c9c00d45100304c030002030854042d094050302c1100040c0c1c0f1508241d0900602042091044441c0152a52107c0500303069480007018840c1c204100c50003504800e484d07014a0290915030419900040c0003400460307079649a178003040840e0800388064000030401e00c24042030240b1840f6240c1c180d0325005c0550324010303544e07940900340c0884940340459103144c04506140c5503400d20a54100c558085028800e07414100400c60310892b00340c405030b4071491840030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 816408156 1250 816406906 816406931
    0x2f0a03210c0203060c03040c03080d09060b03010c0e0105160b01060c05160f1e030b090a0212070308030403050315060706020901020c0a050109140f09250f020a1202190b010801 77
    0x6503459060b500900a00d041e03078500222240340d8101820465086002c0d11001c00000c1d501400380910050b010400216001542016000d0740d180e04600c40c00b1307034075048684210700d0340101060b030b03040d0003070810317079a5000e40d54240e910b21140c016000d041045214000b148596004140ca03c000b0300031006c469280c03015060500341040e4a00c24000d0f0b202094808010685908000c442c402c85c0c02500c3e020040d43c2e1b61100c4107140000c03141101c4d00e0704024020310071858500e1482606c200c00500402e802401d613940c0c848540300150002c0c013484004000a0030300300300e221107040110342c041c22080c0c17502254034002e00a9085032a00300e001d400b840181c0045030401d440c4003411690160741e003400103403030505201c404054a095440d04500401c0d228452601c030903000174000c000c51034031107242c0946508084e502c002c1540135402000321700328402c1c00d481da002825614650300200c203518110744500c026450310150400e1075101213110680c030814054050460b904032480c8000a0242c0c0755a2103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 816409406 1250 816408156 816408167
    0x1006020d1701060e0d060504030504050a0e101e03170913020307020615010e04020715110c0307081639120f0201030204050d0602070201020c0d2f0a0321 67
    0x81c003801001c000400145110f0819221003d43c042d11160410090344c80b810140c500484040e0046200082c00300458281510386100a26613007004207000c1c200f280c40121192658170410f82004800c03c0d0030240c8206c001c52140007950301a0003240000700a100780b20441d0040c0011038455601105401181d001138000c0301e2058000d80e010b0300d07a03076a6014107204002942d1030310798104040c0d500300d2003603900c032440104400342c062440800a42401c048402c103403409100034041c03280f018804101c2d007120010544010750b522040454903190545012229410b14200240c004400d020071607048a51a841c1c210510380d01c1740c035084008060f0038910300c180f0210f100341034a01441c101c41c400460701c4400003200c100c0c1705240c05880c10fa0350b8000540c480d050f2000070394a840d03001540c03004541c0c04010003184070b4000d841d204c15407031a80d119501540140c4c9403440c0441ca440000c10604103004120204403107004041452207920307820500325001e415140714002c0300508d0214140240200e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 816410656 1250 816409406 816409427
    0x609010b040e1c02070902040e0901060803070c0e0417040311031c0c0303050a020f190809010b130207021f02030a0206010803070f080a0c050a06050601031d280b1006020d 75
    0x80203080c4201d0f28503d0507440101e01010404600810342c0200e0341940c1400200300400c40183c190210741400d60815003110030740d60040e00290f20030000100020702d085010800ca4a08007103400b4a0f40c0e4600701042e00340c2d0101140b4105000004d0b022003040b011802800c08050298100d80441d4500d02e031041c5030319410140034004c10b0b00c05502070002446904100c0e84031030203102c058100140d00010b0300d1140c01c81c503100031000900c1740c004421a50701c02c101e158445400300090210614201c041243c031000000a0b0001c00d0f0005801d10542d101c454072a511240e07004c106007084070002e08000e449030040e00c070074401801410b00015407071900009035041d40d034102560b2021088107986104d040d81c0b0080300801489075464402c4007098042c000c0100f0103020700c1001c00c21b0b240c041c00040032984410100381407064030104500704c001d00001e4240040a1080c032800020b50300c0c640720300d801a6042c00050907950420108078031044441c0d00b00088420903021150142419103007580d2401c5903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 816411906 1250 816410656 816410681
    0x804090f06061215080d0f080c0405010e0f060c070905011401110606010509030f0d0c3f0201090813050103050105060f16032d022e020a11030a020609010b04 69
    0x10094444000d118542c80210380300a0442146200395403103041c41e0030045000304503408a58070445c4521f99135040200140d1080910b58014946424000003a124441e61010580140b10b4440304a07010380b070300411940070503034000898a0541da600d59100c0900170034026101000a1080440c10359401440b400844440700809801c076980d5040044500fa00415600c42e0b0500c03688285804034102070001410b10303186036560100884803400c104d05804941c0c26011214030255010790782814048000e080c00ca901c0c0c100302001d0642c0e0080407400341c0b44101001c0e094080001c0c10881c0c803109040340104075482a20248010b070b0b40c03001040f10701e01460310201079185080003040801142d40b04054207061090500e04115440c5040304c2041d0034040018a20b00c42d40100c0d082c1990340c0401c05410b0b905c00c029502c15102810220320020030326107a49043c402600801c28503500c40c010000944c038071410301e04498440c00d200390000e68608050b40c0707480030341d4a44072009800303080038041c60510004c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 816413156 1250 816411906 816411917
    0x150305070b0f04050d0515100302031c050c010c030e0f2b050f180301050f1311031e031903050c0f03040f050106120b0a06030c0e1509040804090f0606 66
    0x9000c546103507540c42600100700c0071104100c0411544d07690b10610300d07207034011070080c44407544111105940c01d1028020480440b0301035002c00050b900041e00c00d00f12800b03800317001607404030b52905554600070580540903a5080c02c500b524031a50503800b0740e8103040c401e8100c0c0e10b88042050400d0725401503181000b2174a52003910115404000058000d98903030341d140140c034044040d0f41016140c0c00c015030061481409500f200d5041c5400d020741038115402c101d1140403400c1031910941c8003010350754010103807074501c65003200b1940c0501c419200b1007d0106c6001d0410304400c407080e2290300200142c050020103218401d41c0c00d02c640b185510420010b00e11504c0e00301221104038194000800498030314003140680700000e6401e00881c401050410142054401d00c2d20b424005030380c0041080c020146031800030000300e44440000c900b2140f06c54045661511041447c010500c1d0744402141c0104c540c1080c0010081c00c0d800608c04c4505408040003461b11004420054812520500d8000782 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 816414406 1250 816413156 816413159
    0x20a1a010e1b09030a140607020607050a0e0a0b03070807140313060f0b04060f0f0602240910020316030e0c101b0609060501051f0206010b2a0a0615030507 68
    0x100d0308810701c480b0000a2441400d0800c104006072418014034003c80380d9841444008001714010048a50401500e0000e0300b214070b80703030a00a02a010341034010040084540144e901525003030050005801c0404034076070340c0e10303025101500503c003d41d01103000130261480d80c0188481ca00990340550040c0c065900f00c202580c656802402c41100000303c20f540c0c41901c0b80c400e6a5a21070f01c0010500701c07a10740344c00c61500d444110300e030b651940030005540010740720b00e405500c2c20a10000c0181c0040301555a42c407104056440c1c2041c600d11812076030710000501641e811841080c1c11002d00c50355040c44401c841100c0c2e1034640c50108112508203500030a0000d8150080d044d60520789180394a006841c030362611058191100410107403240e66503000180b001d03050046040100c0c2c200486104100852040020f6895605107d02d217043c580c00303c0c101c1455100c94108060301c2d00e8000001d8141c1c2030700f221003a02c503140303210101c8004d80b038404d40b0a60740800080c0d84080700e4220010709001d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 816415656 1250 816414406 816414421
    0xf1701090c1704061a03030901171308030717010f24020322030204060e0c0717070206030a0e06070315120c0801150303031a0d020402090f10020a1a010e 67
    0x41190000580070b01102101e002414800800035074855401107a000c1014010b04000e00441c43e056500c0c1d5009400070401e400d0182d03045004000501003410481046507075120034222a01c203041e800600c6918000305005440c1d6110190f480c941113200d01d8903001c4d0341e85072541d41401710b00b48100d2001180200e94200c1d8030b200e4500c03500300c03d401401900d151014146000020800c0c8050301e8a00c0e04080f4814130035070400c0d10940c009840800950300d854100b1240e080ca4602413042e0041c0f0a00b0b0f90902c00d800c1c25941d509561080340c0c0a4021501c0b410140ca01c04c001e44a03c102c07000003803141b040000c1000d03210f07025640303024041c07104880c04682000701d00c42c100b800c450f50589040122050010303c0880034424068802d01141c0c81c5041103040d40b0300181522100504015001a200c40514140e034603068841d14007030b0304442c0165281440008038003029145019140c0c000880c4c40c48070001500410304d480d48034070460205109030141113440c44805001e000c1c2c40c615180718000101e12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 816416906 1250 816415656 816415661
    0x9060518070305130b010f140409171e0d0209030c0409020a050f12030403060507091a0a050d14010801021c061a0a09091104090c0c12081f150f170109 66
    0x25a60303503544c1800a00ca40b070b0072070f280c003080c0d00490400504a404111010039401e050600c43c80c2160140151260364488080441050041c549841000078031118130209114410483c2c07004001001d4941c40203040960082d0082c4076564024010f0700e6410302185814802c040d01c0590003407104404605103824801000004107800345c10002d2140c0041d00b014003000900011031064801181d40d2620f81d600034241c1040e50300a0050a00c4000c40d04207100b6000d041e035000c2d001c7c40c1b80c01610b42010080000140c08102d10030b8202e900c1c18400481d00c1032040d00104080d07440c000781160350a500d00c0c0e410084a6851203115036000112841714814111f520040c41002100c0c87c20856298441b84c000b801c5030b9951030059462940001c01b000344400768000d0a180980300d04059002491545902446404642c51344040010010024624032800c40154041d1483d490200e649a40c440c000154034070fa000c4000400309109040701c6030700c1c80c030500c81e2214020400c0ca0082e40f030791808440001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 816418156 1250 816416906 816416911
    0x1e01090b1302090409151a0603070f030b0f0607031e0507020a090e01020f1603090e220201020708010e06060a0e0907060c051c0206071404260102090402040f09060518070305 76
    0x703004c2d40b213815800206403404034404c0c40c600080c5000413011942c1d010004020240d4021070700a0005004005205400c002a01c3e0440e561381070228100080000040c0750703105000000798020400f083c0e040c10b040d0306c05075030301d40c03500303d454041c10600690034160346c0c5000340d080c02540481090001d2007641c180f07070419564041020009030400125117001011030f0841d0001221032442210f5800906a014135550010100b071320840324a07040504107403c15000c580084141e450742008a0307003c69108000220040450800801024920710005a22603106555091140181b004040790002000c2901401015608000c0140c10714045050760000591501a07410b40154240301003440e01003d04004182c5c0f45034003800843c680700708080c0150a11140e103112160b8103210600000200206440d0b2441c0208010681c400b200210701c4d02901c22140201d40050000c1400140447d1950032901614000801404102e858005001d00000b0750100401c81d440804045000340c2d0203079010a4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 816419406 1250 816418156 816418159
    0x70f02060325030b0f01120f1b140a080402210d09090e03132105030f0a02010c08040506362d06070c150e0607032405091e1e01090b130209 61
    0x10f2500400d2040344101d42c240c0440102c802c03840034034108020307404001e0ac0ba040c00c007222103604050390703404003c00d44100144024005d02e1007201035070200c205405015460084003013207030f001003401040205007601d1407041e0718400742009601d514105000c001e03a24070045591314401d0305841e0407181c0b0028180041d5242d0741c1817111001c40d010a20500080885440240c60300c1c1d500d00e003400d402402c40710070324000c40800c040355041c03100040c00400c80346d40000d5601c40b20384d040c032500700f0300c8900000c10b01c0c01d94030170500500c1c01022000c0042171443c90089a0300428030208070180810a2503d80b000d5010019000a00080d1100e400b48003003041c0e0314003498007010745003100c100010440c1d06009a00440c0c0d40028104800c1a5060280c00340803001c401c00224030301d1415a19201c000e03441e0082134819024000014020144501c0c00501071103a800910700303a04189007002203290011441060a68ad6035002113000d041600541387c000c0320107459400c0c94040342013040c00035005200300c117 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 816420656 1250 816419406 816419411
    0x130305090105070606080309091e01060f0e04060e090c03030705070509041a130c09060303020705132405010836031903050a0501050d0b0c070f02060325030b0f0112 72
    0x41c0c00329440780305d900c0251940100450741c8028480400c644000020700c480340148070160480c00100544000c94110307a643d0400d0030b500300900b0b80c142d074440c8000c04030075005071810380c001602c0c40038540c0f03103405003911405803041d0700d4014051580b00c1c401c5400c05480c50b840a1010041424040c903410341c403600580082010b600000c4000404c4041612017540500006c8442410b1002c0f240d15840100100c1000300140c03491030781c020b91200d4441c407560740728228198038400703490501d4001c0b400c1c0b0b903a08603a0140000d5021800101440309004031400221008001031442810034a114469044841100c1c0c030180c0440402c1010041101e080c03b440c00148480b02503a4601c0342c44039420196910089044d180c4440c40b903080b81d005a01140c4100281e98581010510240c502c681255420b40c040b07903524881d08080468104901009401c4800042000780c48090041d102480c54421003d022001c001214200c0c1601c140003501136010703032051251300140d0b0013145000031410844101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 816421906 1250 816420656 816420667
    0x1e0e0916062a050d030e071a030a090606151103041211010c1202010902030c100503041b0803040e0601030b0f060417100c0203040f0f0e0c030702030702090a020c070e130305090105 79
    0x190386440b840c00078110b5240d0302030503003849142e03014068030200d01880402005070518100001d4031041010300f003815540d40000200e400c443c11500103a9146070040c4040c401030307640c1c0b0303011038100c0c4d103403001036000401c0204543e02c0c00e00c001c02280c04403154107911040d0f400f0b0380e0321860030304040d200005042c0300500c080d0100051035581413140000c40d540000a0541c02c41c014103080c202d4070704103e4850241e603681ca503492900441900c0c1c210341c001c1035071600c450040040b440c00c5c1c3c90344e420940280c8400318000456103030b0040d40600c01c001c01c0c0e80620440100700203001d81e000f0711030409584400c051006014500b0b55481d500300051040c3d08a442060600c40030701c040b9403041d00c1180068000140522035600110419001030402c1989134031418a00003484000da0b60140100f401d035603001001c110024400c200360385483d500101700b61044e00f005032503980254042c00c401045400360842c00985034541c521120b00c180400c0030300021000c403170399007242c440e0701c100c0806060107414840d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 816423156 1250 816421906 816421967
    0x60406030e0102070c030b19060e0705130e090a0c14030c0f042405211c05040918052a06090a0806010e040b1003030c11010201061e0e091606 62
    0x401400a5024019800e8a130a00054100300707260281286242c0c00c0c102881086840ea55200d100d40c0300c6828078cc25031304c0e400300c02d0051803c668613901000c100c40801040c0141000c0c0840c0c201c4c0a41c0c4507003118180c0999600c40c2a5401c2039003001607a0680000115401600704529503003100072000f480001c801c540324501982140c5000b0f980654055111800c1c0314501301240c1c00c4418469000c0d1310381004180806942d507a081c02c84012120340f5200c0c8042807200d0241054402500400c50f0900c860f44900c2c620710704020314450155014414803e5942c034056401d101121840910900840900f003041d0a0007160b510076600780707030028200c800028170f80a00b0700000b8081d01950b1140c682604280c1811079091001401019001c040b44400b040045d41080901e40116409005081c0b00c0a036080181d0042c00d807680440c04c0c500644d9000c103a1800301802001c1a100c41d48401c0312140c450700c201c1603403051400014480c082c03c00400b444020b0145070740080050710340a107034528181d07551 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 816424406 1250 816423156 816423173
    0x5282a03060641090d03050c1005040c1422050a06060801080a020609030c09012607260106090617011b080414070b0a050301061106070909020c01090501060305030910030902060406030e010207 84
    0x81003030340041c00108604920781c0c41030150b007032700300d880340030520503411f03c0d4940a82e10b25251088a07040705d41d0010030200c90310348540041030b1300b0707500d040501451003144565010f410100c80d0401040d1806001291040c001c03840f40e810303150301d5001064080c440782d00f44a03169101a0040d645803083d80c0700080d142c0e88a410407806800d0051100141500349400702d445600040c40d00c00098210b16010f00400e51044049942101c0e0203507020340036030007070040c3c46c014410b5400c10302007103040800101d098004c000c40c100f2020510002042440f1200d0f4a04003d01840c48110002903581c0c6e02003004511860380f540342d01107041059500943d5602c44000d0070380d01440721307440860000300041241d65049060003c941c0340d508090310b035614018500a00300026401490b041c0c0e030303010660422111007540f14601c485d40c407000801081e5142d041c440d0f80d07078100c9400f4030301c2000300d000b8400301d0354131074012010010b9000e8555420f007420040300350003804d445d00c1c0c0760030950340c00d1000c02c2c00b060004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 816425656 1250 816424406 816424429
    0x30f110c190e1003031119030e040b0d030203030907090b0f04021c1a040c030b13180c030c08010507050a0e0409030309210305282a0306064109 63
    0x50fa01005151441c503018000341d80c442d4500c50990050701a1256296244034076074841c651520b4015210010700002070010a000c03c0d0064024480c581c0c10001c040d0004019800380070354000319034440c0c0c5d4954150040ea994a014513401891142c074035413407820070b50050100d40720329a003004030080e480d0a1000441c1c07030900d80c049641c007000504c0700d682d082510590b4089503103489d042c401c00e5140404142c00d12002c180c05a180d44d562a0f991114072800400104010b0b40102148400c6699040c401249103141c02896030a52801000c504081e0040301220700a02e03c40d211078001d98081401c010080c0242a02034090680b0340c41c0300000504164004100601e901c880d46c10b403601281d10080803554001d05501e180c60180100c1480c208500316401c0c0d007201c0180b13020616070500200908201200c0300c0444929441c80111400d1941640265098030000c2c0d946c20109036a1402c40d01500e000c5071a003100c00c20f845012945660b01402e076001c4000d009891141c545051003000c40d043c4682d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 816426906 1250 816425656 816425671
    0x2112070801050a0e0103050a0b04022214152805040203090d0201050601090b1204060e010c200307030906030f2a020c060301081c0e0a0f03030f110c190e 67
    0x1006009603c0d00c0700703607500600382d01c50508000758110742c4d486a90340a169009051902d1207400602150b0791203c0c9441c000c1d0f0780f504081124030340700304c0711005001c42c1d2100b0021070007031400185104001404000c0103000080084403030201d52450741e21501c5000c129528000a1074074045950380315400194014041c034002003401e4621050002c1c2101ea01074a00350400120440402a01c1700c148141c2e04103a80b11550303090940c489240520060a0003a410300840d400c104203460600d4000300040403104640c10300440f80d42d0503800c1c5035124404c504000b004100d2400040c015684250b021407000514502d0001d0710010310401d00550015a408490160045039140e92259605100c80501c2440c10b0321102e0031541002130a546500071b000131031507040c1031800e1056400384500314080f900300010f40b00c049855243c129a40310005580800e0340406c0b45155070b402046d22a0340d4945289085101804103103183c8400c006031048280741101403150360000208800b0146e130b0842d8000c0c000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 816428156 1250 816426906 816426917
    0x70608041b06050d0e070e0c09010c020301061403100606050d020901022b020705010c080904051e2401020d020a060509031218060106050c0a1203180303140a090203211207 75
    0xd860fa80030007900c0c2051786910340b0350080b0b4010000804480011074220a40300051522901c0b10340c0100d80290030070b07170003a52540c02d050f40090540410b4040058071750302941940c41c10085a6144c8040d42c400340b068100052003007200c820342070140e5010700001c1905105407040103c1c0c1e20f06040c1c004407407018030146003040b80300c480f0600c0d40402007940240020f080207003508400303441e1003101e4000c08030a2401a07868a0001d80c40140101e60904465210915032445091603400c00341c05842c0d044034182000700d0035004076400d41c00040d1440203401c00c2c0d40240036035031265541d4006420060601c84840c0303c140208540e40761030070103c80c03286c401ca011100b40d941000e05001d191020690248090007000c1024a0200f000850076010785908501c00c8040e1a0401408400400300b0540880350110f00b00045070825905030880180c02c0910081c00071603448110210084510350440250706074800311b91107000c6122072601c075140610880101d804d14481640704420b02804440c00c600041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 816429406 1250 816428156 816428167
    0x108060c1b1506041a061903020c060907150c11041a040c0809010b061204060e070510051305060c03040e090a020904141203070503193b0102030405070608041b0605 72
    0x4051180441d41600500070b00085e04444000c9800b500c9aa45038845240b81c44140c403281034007a07011035480302c41e21022501c80b86483d080d2161244214003e03007598000c864050414144111a007070b262640255019503001800c00412004040d8400520301c0400c2c1604160b0030b50f904c1d0702c40d0301000043e0f5203c40c08286440c405160855121040d502c2c4288400d00038114000d51102200f54032a40c0a0300c0050061407644038070b840e0801c250712495024060b03001031540c7c075901801030000a16042c1c0315101c2c01e40c031242005040d0040408a00c0d0344d500030300040100a04000719550000100d409403502801e03990041000481c0458058032141001d9140c90210401003103c01211101c0c49149410340c200004018024840030340300c44c04400b0076161070407101801e50300508a6241044400910180b5080c40e400805425000c251007004114074089200106008407442180d2040241c626681444401d460030f0354040c006580e01d03800300c42c0b074201c1d5040302841d94001c1c01507915529290b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 816430656 1250 816429406 816429409
    0x50d090b0d0e12550c0209100e0a060305030f070609171207020604080403020f120d11011508060a1808030108030403140c1f020a1e0204060e0108060c1b1506 69
    0xa60032007800e98496401c0a07081c400b41920040150b184c40c013401e107416030a00b07194089420b0341c0c0c0d0301d8001e58030183e5031040c40306502d0050ba4010072035642d403000e400507581d500c07513140840e0458400a45560070802c121301500319440002c11105210f214005217201031f54172401e1040030010013071008107c1c0050f0120184568400da240e22140b24401450540f0b0315550b210b140e4052803000a016030035819030040a955050450160705000000300c8254080301c000c02003d525060b11b6103140795180000301d440b100c05502c0d10f0420386a1940040c801b40e180c103198240200410b10300e600d41106404030f201c0008201c0c100540c0244040c80003180c490f422b504007509d45016940084400382c0c040b07500310820307132556074440f43c000c610b03040401041f0200c581d0680c100404000018106c3c046000304520011303c80d6000d190b21802070794100a03068035848001e9406900f8081c40c07200380e00103000500100c104500600d60015a0301004c912901500c030325600d0820a001200e50310401107013005410f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 816431906 1250 816430656 816430717
    0x30606030501150b0906030a06080f100507020c0a0b030604180b060f0409022d030a0302070f08121204051006030303050a150f030213090c080703050d090b0d0e12 71
    0x503140c100d4036501c2e07441c03422a144c901803051200e0302d8014240031000079504059648480e0040440d40d081e02c2e4491001003c10342c03180301c0c003195000100e180001003680644001540311f014000540804034450404080d91210b400080416030312980300c0e8503200940342a02601e00b08076206100c542200d08080003002300c0440200ca10b00d018514103880540942d88442c00d0300c0400d003660f200490205001140c0c1b400b8220040d03011034240c4120032100c420150f00003140b44c125002d0b072044100080d161041140c4540700514161111501484a8160107052805040e080f500c14002ca810085024807100181c840e99401030700880d071b4448c100310108106004840c0c00b183c0024010821038203064040b071b8420600c1c00042e00403082c113400f0b284400195030010720640d400038214a1116035034001960f60310b070075010858941c00b41d90001000103000790115001d03544041074050a1006290a4500619002080880a00c04c04a201c0700c04004240105030400c1d030860118003600010182014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 816433156 1250 816431906 816431921
    0x608010801110712022b110a050d20011b08090d0206070e060733021615020d0f020915030c0d02091912031d0f06030a15030606030501 59
    0x803a4144030300b26030504098811100b007560b00440d035008051000794201d2070a0f1114075184841e048000d250346030a5840e0750f101c003d013050795a4030207407001d0228160352240c2c1001d03001801e560142907650000c5004882c1802e001c8514004000c818a030a4081e60950f042e81e1120700518416402000240354091240340e4440c082500800c524642048029a82c2034010701481c101b24407003d07160071039039a50007181c3d40703690400660f441d2051780c0081c40c09010840300070a8803451011207141c104401c0d034020b8650582c80d01d489042403060644902d1b00841c00300d020b9000590703081019440a0a083c403d5061b0600078020050702c44d0344503403c0c004080c41d5401044250001407040110001e40c0808403134540b1140325015844643c81400f088030b011f00c2030130f401c0d4030211811000c240345407010401000c081c041d54a02c101e10018250010f1a518130a044e6900a0317540c07000070145080002c0250303044507400b00001004903c41c43d06481008040e04101d0710281c44003010000d0050034001c0c2c94 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 816434406 1250 816433156 816433169
    0x3040c1a13030311030f04030b100e0c12130f050c03120f0d09050f0a0b0f100e28090b0612070602071e0302060a08092a120111040807060801 62
    0x14a42070307045455200d0010544401010800e08801480103190300f0700035036030760704942c60319103844a44900c5d0403520050101d174010030802d030000c000200400d801103100c0c06143c050010340c0c58000031100d441c0e00303c1c40040c01c2400c4a039082d503140c03002038450082c0c00550f5014002400200000e0300425003000e203010304c1c43c604494140b00300341c1001103101c100d501e40011281e0006842d44a4039003581403450340d04100100b4005c50410704280800904824440c21030115100482e59139022000c00822580c0200c2c2d0480520388005030b44020381648002d1240000c0c0080205401c9450181c4e0544011b21700480d10202d142043c00801e0038100801c80d080b15040d40988419400d064009550310700c503100d03096078000d40200c0d4510301c0f541c0300c495802854002d041590b032215450000f8100b07080903202c1d904903210701e0401420007040101c8030381c7c04e80c00c07a0f15106090700310a0704114035074031038071103c0c03c180d540d07281c2107905520000010b100404e07400b00039000c0e5504d4001d000c1d00d205016030049 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 816435656 1250 816434406 816434459
    0xb1f0207090b130506120102121515180f030105010f031403030136060f03030e0f011b05030f04060305040203070f0f1518080c0f180c03040203030f03040c 68
    0x2d403243c0e540c07030b00280860b0000c080c002110740e10000000d0049024a45020541d4800100d40c00c5040d040101548110000521820a0115a03042c0207420001007210100030405000d1480440c0035410780c0c0003807004c01070100440c2500d010010b421a0400e07030101d45a1482200e0400030041c0328034a40b00c0c2e140c5004050343c20740d0300d0406402445c240113104030b040c0755020403440310101040510b40c01120360058040090a46030b60071303030b440100c040c001a80858071b0b807502d03907680d49005600f01444010694441841d102c402d410420116004d52003107942c2e02050140c6c03c04071102801410060100fa03070042610301b8a40141030070016950070000c54042400424041c0c01e0300e44024504480851061004c0c40e850540201e80103420543c1c2816150001e282c00a410400003031454091329084a40d5072152101c0c0d4104540303500d003d400c000c00002002c0001c0c61003449100a5644a400641520f103001d80b121504e1a603680111f42c211100c4604590921109041c58481002d240814151 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 816436906 1250 816435656 816435671
    0xe010905030c0904170703080402150309100c020708061905010e040b0403122403060e010b0a090b040608030d14011202031515060c1f0b06041403010b1f020709 70
    0x129403907650b00c00c5554010f80d0000042420000302c901d103140e1008800741d016403511000c2c034000348403100a0704e00380e20819010b003c0610300a51402264082c40340d600007800d4401820f1050741c0600f008629210950144200018500707405018a074421540290384e0100c25690600300c0c001c460042c0c01c1081c0400d0b1020801000030078501d41c003500b264041c10a00c44005045608001402061880c80064614030003014203c40740aa034038401c0e00d1207550b0520440503042d0b01c036400c803203070483c04035403082000030304201020155002840c640009070002c6111074480c802e00b861544001400002e00c0e540320081c104900041d000b2901520600740a80d4075200550000380e0340e5191108414144006080810050300d81c015440b0003071072010340301c0c80c0c440850054a80e11001c020015456103541c43e81b201195800a100e480c505110090125060a042441c0307076034402c0720000071540642d07890ba40441c840e03aa06410b01e0400c2c50008246400280c10400203061017081da01a400c01800d2205 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 816438156 1250 816436906 816436909
    0xd020307030f1b02061215030f1f0905150711070f1701150b18040b011e030e1e010c080f13032312010e01030804090f0f1406010e010905 60
    0x2500301c034000a01d450030003183c0b0400003007090381e180407000750b0152001500b8030060103402d070220303c0761769a40d04042c0e05018220525441d01036003007036003005070808503001000138000c0301c400011044508001413081080daa842c0d142050036001802d2481c10101003148407640002484414450240a041803c1c500703c2040d03114a15802a489503807004030880403003070007d40c000c44240c8200da44810445540d1290170300d096005a1100c076020b0901200d03808582064002d20380c200b00180c2d07401d100ba01120904290700c41c0c0e040340d02e404068403807a240c0760010081100901005d5080104420f01c00c0380341d0182d0845000446076800d0145c038100b08005090920060381d80100d03001009040a1850300c1e084404200700164416550050051103c412101c0c1d4040e01c1c044940500302c244590f250400c16000304002d02c40203160280c100300134840540300383c000c1d000c41d1154000114400761601d1481d81a5807400b14000c803103052210400446691020000380c1820b0b080c01c0010b505d81c00c000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 816439406 1250 816438156 816438167
    0x40203092d03030c0d0b0d06060504140c0304030c14011a0405160915050c03030a200412060903030e101a0409031b0206090d14010c050f120702031b01050105030d02030703 75
    0x700804c02c41c242c045540310700888960400070b0100c2c001409800703854018a0907600400302c8d8000c1a0103a8500400c020100c0f14076411746006100d0580d10f141166907075a0f04450420940c10100c3d071074030046c0d1400440e00c03003d000e0544084000b00c01c892001998005210403504010b1001507818411036a90900c1ca0b0020000000e4805e03202e000381d00841722460075201e5203d0204000418440042083b000410701e40c40072070710781000d5100b07041909919035040c126003c0c50142404220848980800244040c1c0c41308002c030744203040226104985645c818100160341c0d6a9640d026144d4a0000d03c92465051400400c0c80490b0100402022900c00030202d03000890165050203040b0700d0300701075503155419130700c2201000300000600011483c0481c103504949a0700d025560804000e04003060041c002e4a9480c07500006c444d0a140c410a41074003803040250100b401d50200b000741e00c1e041c103116031a0100344d804450020640c0d501d0102414a40b0b02640c404204540051002100007070340724 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 816440656 1250 816439406 816439411
    0xd080705151e040c080312091c020d050705070b04060804020102010e010e12030408130312080901050403050706090f0215040f050307050303040e250c0b1015120b040203092d0303 78
    0x1a80b4409140c2e03540c1c034181c407004445800012151201051492014040306000c81c8a500b80310103681c001120003e000903d10042e105000140c0c01003400e04460a03c00c0029203940350148040742c841d155260450303c4d095000e030b00000300044040c0c08000a558090160140c0d10b52070740c3c02003211000705c95400c1d417a40843d101c0d0212011000011605204290003541c90a0b6220740314105226034914005c1c242c48008500400410380d00800200c0c452010301c521b500c216003645849280c0b0290307a480000505c00a0b108444490501c00a80c01589410300c2d103044955004601c1c0d60340b94204820008040c00c6507111a2003503005620034000d58034048140c0d421103000740090802030301c5402280510403603000144100468401d0f949061652040c0d10b20503c0d8091a0300d042c85031192160440e400020340504003044030000380b60722a0a11524488000c01841c060002d48000b00340e000401766442074030b21000c1075005940c2001c08040c4d800d032011034030301c07a4424810320000d000d40ba43e8903070100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 816441906 1250 816440656 816440701
    0x50601120309051903031e080403050c011b080a1109062505030c0105040b0a0c090302010f020102040f1404112104030c0f0b190204031109060a050d08070515 69
    0x1100041080500510880b0b0243c10020040e901000c1010000354900025200940000c1d4580c21051417450000c3c0e0028454a030075034410002c0e50f1540c8054640d9444105100004d41da2030f847d00307800614010b4508038080d000d81d180721250404070009400d0301c41010700303e5452202000340c2c5020b50340701021190f4260a040b502401ca00c003651030110040c082c000c025044d800b0000d00d50901a030198032051003640308080d410341036241c980d0281c0888181054040104040300740520256010f1700903100c6800151001520b45a00d403802d5440c0f903400c43d40255a203024140b080c184920305409203018100030760900c5030619480901c40300d130803195840300b03c0c2082c00f0400032034181449100c00503030440d001420716444414614007140001c901321041c3c005a02c004031514130340d07405c0303008640440340c06c82d1000e201000c451040050400c4040d201d01d90010745148002000d40f91410145001d5015a1032541c0f140d440c1e0400c1805c10080043c0c03c1701e10f004c401c080000c81d2011035005c0a10f5040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 816443156 1250 816441906 816441929
    0x20d02040915020940020903030c010603060e01200705010605100806030705010207050112020f1303050604030f2c15031003020f0405040c05100504050634050601 71
    0x50020500a01d26900094012a69010484202c0000b90000d02080d84107644040400d210810b00a00c25031516515259030110043e035141120190080c031140380044140062609103240c0000c0e255030b000c02e402940e565107449040080c049280725070130340c0c21003a41c000d0100809200c6c0b085070b03140c101e0290500c1e4203008140501880307402d600400150201030101d01151564180280c0800380807584207220380f10303105020400e035101103030010440b50181c64881511079841d022001940143d0030040d04100144100b082440d07680090340b004500440142105050a0600405400c4400c443c1003e00c20601180c00c85800c0b5150005a0781021304020749102c5220000144e071030341c4040c003034805245e01000340000c44000d0309aa10490313208640d803081c01301103d82480705480d030485018081d119045030801c07071400d102070104100e000c1403602e1450300b511100003d11903081244103d024074155070014440d03524000705402d0440c0f07400559140c40002d59940e41d85c1e0907050088000642 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 816444406 1250 816443156 816443179
    0x2c0102090d14010e010203150f032107030c0b0406060303020d0201020918091009050d20060a050711010603050c010909090f020f01090302090109200712081003081912060b0702 77
    0x20340c00c4d072200304215502d800030747d660309040c0d80700d102804541450b9842114240c246a0040c034001690382d00450302000000315000040b000c03020690480f0500ba400d100180804400060f00d81017150312680c030422001940c0c84c2103080003450500940300d846c0c00d6a10400007241940c2c0c5050f8002c0c28003085000050031641c07148102403c0c4004c1c00d0740c003402c881c280700e01b0104004c008600c04483c1e0318227030758507144480003c220703040c03014a41c0e08401e510381110303021078407000054010540c88541410110344002003102c1c19401c41d0315039072042d40c05422402c8035005560b40a11000c0c01016954814000840380740c540700c0540d034451000034030030420749120711850f034040c0e08404001c540083c02100b0310769448003640007400180951820105880d500b20100d00c0d4640d05884080780c018280c500501c2072401d0a031000c5c0ca0141040d14100c01d44540000080c07100c400915801100286a4000c10040d00014280100c2e040240816904003901030103001c04000035101803c0c3c0468071480c110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 816445656 1250 816444406 816444443
    0x8010909081b10110a09030803042f1f02150916030c0e0a0e030301030803061f0f090e0106020d080a020409061d0105190e192c0102090d 60
    0x3449214440c00312000c810452a094000c00700d19200c100c0203d010030f1001618608400d822881022412400b08501e41e40c24004540040c0145238014071402012800301e8001c00c64075030000e05056050200c0d100b60b014a407a90a0118080d031f1219142001d01040c88503100700a900c0740803170001c5c0ea1899140f0800104002c1080000070341c8031261111b12136000340c8070b04140d00c0c81680c0d4002e010040120001051052510703100e40742e0201303102c4024506503401c41da11103910f61f101520f02c5510880ea0522440f00c4459a001000082c41e08c3e03c1e102d0703041e17912010180c204030305940501c00b611015001003100359000700b0f00c03009404181c60005000e1340c0e50200306000380100d401c290201c0d0300c0d1850106030709500070b840500001e0810400d18240c1e9031401000440e00340c1d03000d0301c20500200c410400017107004610f803e4114404000350110700090001041c00c07607459152070702030b0070500400e00c132201400801504e65180028002d5107007110040c0403c10560141a004080603400c0b005d50404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 816446906 1250 816445656 816445673
    0x10e180a140102070302120f090111010207080409020408010f0c1b23010e280b15040f0f0b0301060f03230114010914060102070501050d0b030a0b040507050901030308010909 76
    0x4035503004a01d421000c030840c12480c001c1d00301032011401351240d0440c079001d4002c06020f4885a071500c460043c41c4c00e60303a400444201410170f20b81d0340d80307640900c07440c1c0014461001600140190400c0141c0303840c0340c010030609452045a68080c181d18101c4003440c107581c00540701503503452141a802c1041520300d05120601c0140420000400c0d2000224000740d206400103901d61003650200c94034040800d0038070941c0c8024483c60032180c81c5104140c00014401041c9650140814030389003026440080410141d600c55541101220350741c0003403501d103e440344120050080168001c201e4941030110104e000e180b14080900b5854001352840c025650089800c101d000f8000000d0111880020104519035000c1c002c2400150402004901d4052120043c61044005034018102c09150400640716079000441c00c00c01e10303481f444030b5049628100981c080b40d03032142848240e41c0c41d06040c81030600380b25800c0b01c0d101d02a68401080420760003d80340e0305480340f4000001d01808107141c803803103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 816448156 1250 816446906 816446923
    0xf06091e09031306020d0801060e0d061803180302090a0209040905191a190e030c2e051b091801080c12060c0a1412010e040c050603010e18 61
    0xe011820400c0d907080200140006070300310340700c00c911103454101c00d90b25075000c03030301c2000001c444d0070042007401d03c50710402148007030282c00c409040e602a11b8600c150b510380d85105a82e01c51a031818000c01d9413000c0c1c0400f0917940c1959581000c0d00b154005509003402601c09000160007182c40561641e499222940e810390020071240e03041008005140050843c442c00e540c6945040b100c50039032100700113001c2c4501c040000d5520309039140d451800040115400d003069900c018403805000740750400c1901211b405a24404000d40300750440c054500a1480030803141c181048140008103d0b810681e42c411168a201d05454a5884e00807649450b01d0300c0701c5601c0704c00480d0002a00c00c0010400c0400e4030410360348018a64003441d265580c3d011300b9203005c500c0d580d0800060301e0030362240003c040d2454500a845107840d5815140141e03d20080e003000d50882102c1c6c06000801c00c180100000034203050b500d2074119031400c44650319000d4000c1006820000060001c2c0039280180007094 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 816449406 1250 816448156 816448201
    0x30815030318091504090b0109050115050d151a2206020a1e170a020606040c0207050d0204020409020a0801061d060a1116060315090e03030c13080105071e080f0609 72
    0x502041d84c20000684070080c8100540a42b81100100e82c40341000c4082c0c14548080e110f140c1b4044046100c3c000a01016020b0042c0c0054004041045040e4030b00b0348115221180d21240c8909016095240c110044004402d403210245400c104070340d004500c141c41503802c540c00380c106011f07080c054050200e80e454004c0150000a850181005a03e409402d50200507801c5400941d120010700084498a0a0a001581c0002030401c4103140c0b2038050128584050405070a003580e4240030000c1c1e8105031400c9021440340401800403640c4440c50760550b1111140c072151412104c00401c0c42480380040c418104207a8200c007140c0d0000401107084822044500c0702040b0b03a4450b030060007007400c0001204060f8003402c001580041600401d4441c51000001d1451a203400c1a6404a5032091400d40218603600c500080c8502c0203100700d034400c00d019113031070810804540120080c0744000142d201800540d2042c0a508513030405203a90100341030780c42c00c007a912049079041103441d1040122 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 816450656 1250 816449406 816449411
    0xc0e030303160509220c0306090513060c12020304050105010806070c2001031409100e01020f12070e100e10110c040b010302091309050c10020a12090b07030815030318091504 76
    0x132517080086500c00a903450f4641da0401006403500c038079505440303003603c2c071400c0881d014450001060b410b81c4422418541401c000902c03108941c00711081e60030882e01943c40341d55074001000940d00074002c01b83e02107600d20344483c03003540c0c0340e03503480d00707070b1003440824210501450350a102030340681e000e01085105a07118a22500d85a02e04507641d098000324801d003035040031400807100105000f90b41202100451040c03c05e61006032035840710400034080c0341004450a01d140f01c646a05c0c0300110500266590520442c4225092044601d2003d074424200708408440036225500807c3ca000d00ca4011200403c6480d035050048001c0c1c01100310090380035030340107140c5030340c1d4580c1e90000c1d0301c2c80e02ca981602d598116a01c1003102c008a0010010056001303010b0010006920b405001c0800ca44c9041c1404019160f00109105402c404012004141c81c1c030103000c4044076000d1043c4002000324001c601d44400182602c609000c01e0030000e02800c40d540110308580401c0c0d0f01142d2954024208 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 816451906 1250 816450656 816450709
    0x10050603010e09010605190e0402040b0a300309060804020315070c051c0203091c050601031410090c050d150905070e1506071e150c0e030303160509 65
    0x4405002c0000d50b5601c225600c0c008000546080c96564441640d00e440903800d42546044120f840311a4000c10032684142c1e00c09800580d6601c95690001070106030461803005003402c510101003041089501c5c034900d141c09056030000e40d100c031880f030a541d0701e403509442544071840800e10700030004c002031010484e21020000595440f48041d00070b14040c20449101e02c41d000360421046880d44101d0340160010040000746081416050240c44600350007002d81d007a01d911901c0c2070420a810441e0460107800007295941c00402c0b01c1a0900c0704e0810400413944140d071400d03281c40d01441414001d0400c03ea0b4041400104080b21081c02540b03c0c007403094450034980f441d1111918020380d0411880007006c5529401221740b00d2000c0e07100a0721961a101c0952590410001ca03441181420711042003c1000504454851038540720441d40214203034100c181c001d4987c0318900350180c008d900c280f00300300d899040341510305070705070803800e11310f50358000607000c60860801c040d03610590500ca1840c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 816453156 1250 816451906 816451919
    0x20c0106171e070905220b0114060a0903122d0206010f1505070809030a0303200906071103012a03060b1809061311070c0e060901030b1005060301 64
    0xd2000784814a409803500c04048070aa0442c60500c0031030a601944041014000030b00940c2c03202e41c000c0d000c003121b80d803060a4011030040c075210180301250140040d0340108051950034855030303500f1404030340c03103410081c503480c1c001d0595034144005030059010002920300c00e40150510780c203d000518544285020f04014444201c2000003401c0061103507400002c4c0e0b2800c0000c00000341e50100c0d4100709190002d070000c490035080700a0a07604a8410040b00403950780c20003416130120700c0380d10701280300000c09207002d041c0108914584000c0390100400d410565038001190100399000151031000068500441d0041140c503200c0f0b200c000c0001110001100c0001e50480c034002d040da030a100300d030303100c50003000316008551810800c1c80d46840b0141891400b0001164400406840241c4c20404016614113840103200b40750740e1b0f0540020303c02c007440381c5031031410301800ba4007080242508116001c00e5154905110240c40300c22044081500c1c4400880f4240003040d00800389516542c503003e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 816454406 1250 816453156 816453179
    0xb010c02220f02070209060105030108190611270303090112181e06050a14070c0516120303140c03010e0702150403120b09250318140709021903020a03020c0106 70
    0x40c401e0348261b144200081c81d9601c1102100e05907014080a05a4100c80705011040a4255981210344d152585034541e07642010501510240d0300512030501d00108150743c1c2c100015210119074029001003110031801d03600f00c1c08281102d4201d200000b189212045801009401e40d807009090410108070306d13003924040b00d5800c1e0402e001d0b0304104030030b8840c070079148101d40c810070425008400540c00111464060343c0349002c05401a0103540d0b0405411150b085810a41e801c0364810402d0600200e040c5235241c0f15046491601175580d038224103100c10008100d000500c200e4024401e410000f07a0000c0c8203024520300402d6045c00507074181043d18018140200010369040100e251101c04d01452408040702409040d8489080030000200c3c8000848010b43c90383c2079060580f070f82900c0c042c010000780f40c0c000d02401056042c3e61109410080f40c1480510b6008980450041c020808180280c0d10524020016414010303600d120f0003030250f0190003a42095440755113007003030014895500a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 816455656 1250 816454406 816454417
    0x50f031309090b041106130b03011806050306010b0c160b09150a17060d050304080109030e01020a0507230613031103120909090319210b010c02220f02 66
    0x300e030540016403169a0801202e12810340079118004020104000c201215210095004041c052070324205141d10341482c6110380b50311100504c0310000c0100450000c144890059004070300003841040e02d0710b00020f81d507000600035040c00807000164013280000400c0704401c200d04204904040a503200f010010a4100100d5a03009080f106c1140ca00441810112611031003d0346030018a14034032500e010b0440001081d02e03800c6207201c220540481c000f00042c1008091003400846d80c9501d40c03a0040114030490011419940901280c2e000a100030516505841d03441042401000140d201a40082d04000c2103075004074002628051403050203141d4015240600e071b0aa0091803450300389552008030b5850900002c0d010321510940c0e20b0300c10380e030540203041c0a00b03d909050b507020414103640d102032110804608041d0b114135104c0072100c1c0410f03400c8060310301001080002c100182000c940203800901c15820700540920403100c6a040036004008142c00700020540202e8460095110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 816456906 1250 816455656 816455677
    0x16060e0102070e06031506310e070312050a120f0b01030509160308090402091906030c140a0305071206080706030f05090a021507021e010e180106140403050f03 70
    0x948001251403151201d600c0d0013410041c0007403e510780344c141d589400f054080c00f0360354460b080c945566121003a0300d0180f44a24010101c4002c101e000e005150201c1d0307907600d4164059041030344100702081d8116030b01150400340f81000c560301c8141c50b00c110b60100300d0006e0b0f0300c0094605580010007480702e901285200c2020303201080245c482ca007010380c0e1007081c0c04180c03020b000d000c2d00c00d00000703140ca405020a460082c001608002480700011181c040d012030100403800b070944c04000b00c69141c0502c940c1c5111900f0505040144905a104c0c0c1e48140301408080c10f80307400118140306e111b04072480c885202d40388204065a101ea88440e20342ca924031407840064188900d00d10b082403203125072405810f26000408881100350300303002c10309000c1040035101c03000901461000da1a090f14000d021800c0d80403628003140464000f52041c42c1108000b4020040c102001c080e940d8051a1170741580d03018200036115034541c48031002c85105603040100640280c600258100310b0000181400d1040c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 816458156 1250 816456906 816456913
    0x91008160305060708060f01110a08032d010e060d03210f110c030405010c2d02042a030e0a0f0501060806010611030a051e0307080609090109051b010216060e0102 71
    0x54904045030141d0781561b00b0340e0321031a01e5410b05001c0d0700689485122140220540e2442c1e031f444c1d16416030507001121407415915040002100070805200945515000e04280241c15410b00400d044042001021180118100300b02c010030b0601410405585d1680e114107400c80303404200145010301310132011001c42904246000c2e00d92803909066604110001c3c006600381840c0100442e0b0000714600d068880d0b42040340d400758019a0003c0902950009040b42c60001c41c2503c14003080f640c0030124030565180c04040369648030000950a805d415042c640030a22501c0c2030709090801e01d64900003481e0311000d1102504001c41074100350104c13840d02e0103590690380d8482040c6d03500341031450450071940041200042040c040c1e80601311103600381d00c0c52810741c0d03000401808503910030ba40345008100b00c00304014051078060302c1103a01004200c000e002c005003a50307940c1d55032507442c6001c0030f00603031012000f8000d9100b0072003000c504200c1420001205d6072400060035000154030300030b00500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 816459406 1250 816458156 816458161
    0x415030e060702010e03092106161707081512030a080402090601080106050d05090c0d1110031109090612060f070f0801061b15060f050a150e09100816030506 69
    0x60040c81750702d0f00d008400c409185008030180801140088102c2c540d0300407a15424111040102000030510518104170540100d42a101000d090707a4403580d01c500465511104200300c00d80c2c4041d05542001004c07525405010b01d010005468002504c020a41c0e403001098041d9425849000d243c0a54000d0304e002d1340c2601d07032800445020b03100f40035080c0402c0c03017001000300d042039650010794041e0041d01610140320003000043c01c1203041031402d80b039400712048200e20500e081401c261031005141007c105048210251015500031420210312030400d040004081d86c84050b111850018440b0a0303c2c00ca00d421076240c4003066040d80d0320700003d0360b040703004811107025862084c1a0ba0403901c41054100307024000c02d5040150003000c4400034207a01002405080034003885024111080710b022881c1d00f03000c02e2044900c00c5a000742d92002150400032010794005012150781001926400155038505004445c2d0400c29071003205a17120f0861203959102c10030080d103041c1c900ca10195030458 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 816460656 1250 816459406 816459421
    0x1210051005070f05032d09060304030809150106050408060a0504030909020a02031201030b0708070c0507050d080706050c0a1d0f0f0111031611040e1203060109030510050405160609060e060415030e06 87
    0x3401f484401640001d010800306010900514441380e101c80c600040b40c1030903240c0c0c0c103c45c1c4070030420b9001c20003180f40410103001c108000e00200d5030002403801c00300000d142588006001d00d1151142d83d16050b800103c030071a807882802140c03007621034030141384510f5a407403600d800044002c4651400081425010032a003a10849029810540000003040c09908000070003100b500c100c0400c603190202040f0001c000340309406154403854006001035101c2181d0070026081104011814080601c00d40d8901130590710f0280404400c3d2090300c0c0d0499000c040401681c1018020030100404d20020a035803e401110300c15a280107803046080350701d071003c503009102c03d80c0c0710340d0310700600c0d80c000381c3d4104088036191b00510ba01007014501a054143c1d40d0b252241010300e50446280380700c2e154020002807040400c122820000c5840c000f0700e032245042c6004056180303134021101040030361b000940031940e4560036500902800d0561030445420014003600401920340340d5a0b01317014500006605 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 816461906 1250 816460656 816460747
    0x30106240513090c11010e0a030207060e0112110f12010f0f050d06200a08040b070f120504020a090e03180906181312051210051005070f0503 62
    0x10034000440c15241c0c241446440c4004c1c10404c282c0da82000b01d900105211038000340180e20100c00d4031401b8140302c031a41d05000703041100e19080b500c1409007294656003280d031700c0380d2520010311480d80001843c0e41c113031240076100c0c400d22511000c4070002251440c40f80213604006412100003a141030300c2c0664606200301440d035a07102e03440d409003203c0090741c04515550044010803081c2c080b880c195100a801c4854641c0011810340006948030701001304202d000c2c00d903d40c2040301400c011950110b0702d88003c0c141a0400741441d8481d8444001c641107458a41c07000c00035041d113410600410340e49140190f0741ba0441c0b0920705400960811a5009080008440e40030340405005c034011000003150480e04900060405004901d00400c80c40200d9080400403004c4545d41d41c1e517079511603030010782c2241d50002810030007030035420040800c403950325a0f04c075002e04074440c10540d40701c0c0094105080310983c0c0308000f030024080011519090301100410500c40e1031000c42d65080c460f4642e40c110344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 816463156 1250 816461906 816461917
    0x4090b0a051305040f0b0109200c030406140403170309160315110403080d2a2016090b010908011107080304050f0f0303160809070e07030b0301062405 66
    0x821a802d420948040c007070725046554000e02031401c03580729540c10342da0414100ca0076400840c40315513a040c50448024002014844140340b48002c41c140001c15140300c3e140d12591045030240091000481c01d488083c400fa100219041014080401c05448081c035403580200d0f130301e140d140201e80801017088280c0031070805498002e407a6400b91002d40c0c5464004000d9207074540710f2007005100000000d00b00c9030003000284110f440105050101114905080709484403034245544442c42c514091640000e00c0240502d030446d1110390710420b110064109a80034144060000704c0c4032001c210142140c02840309101c003a41c5900c620740d96940748a00300c3d2105c05c0c80e07886461007006290042055840610342060180c4103641000070400032140c034020425004031055000802041014050451441c140340c4481c10080e61528003d2942c87c0c4034003940c02202803005030704020412840c401c0e0300413045000003030b00030810283c450102e0b245110054504248551400c0da40c4980b20f48550309480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 816464406 1250 816463156 816463159
    0x903080609190e0f071d0609130f14190209070201060b0405091e1501080c0a12050405011814010e0c0603011505211009060812090d12020304090b0a05 66
    0x440d00c00c000030081c03001e03083c0b1294294842c403034a81c0141562000b801030728001c00c0b4000140b13442e600007032a074010001c0c00401d0144034503114802c0001449400216034400307940204500840300b5540381000e070284603195041078900c600050703011408101040302c5c00507070084030301400070340d2614000c03400c0c0c6965004010382d5200c2800200010705202098940080320200c1589825a040302d043c440c0c0142100e440c80c0c89440303807110b10020f58100107401c0d0450200c2101c140780c40d02c0e858010b840c0703180d04160529550fa0791070010301849000e602080c85150304d81040749201c1d23514240303c2020880c000d80c822055281010340300c2d44600014280601c014003822079070940c0c0c41d0126030301d13552400050a0007404000c1203d43d500ea9148060010858400d10084000f0b0411601e403581910040d08002540703403401c001840407010001d408802061900066640e801d080300200d4400ca400c0c2c180240300a00305d11000b81d2003500800600190345540c601002507600d500200004030700341d8840c0701d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 816465656 1250 816464406 816464431
    0x903080603030906091c0204020307090f05150a05130803160b0f01080d0804050106080111041805070801120203010603051221040c030303270804050a05040915020a0c150903080609 79
    0x178a00d03400d000e00180588503000040350058041600810144c0c0e01c1207486400040d03251205011005c3c800803c9400b50100751403514248402c45103148070340c8501d41010f0240072010858004460002000d10064008001074039100c0c100300054074803180c0352890445145680200040040c2d03040041d0038100c942c0f000c01051030010006050728007940141040d2101c3d521000d0104002c1005d029021a804075003030b01c15a51307850f110811403130307400303662403500322505000902010341d600c0498507064a07601d059028a42c8400c5c80003070b00501d80c0c0d03030000b000d82c0240141e450388202c0b075602a14801500c2d948070131b58040e400703c0c61204c0980448004100030000201403002c24401e41c400359400c4040005502005000d81020210880c20b0400301d5020800140610131410160200d00007440166420300c1180c0d42951084c064030918001d8115059003c2200d080c0d5500c61140300d0750b401c0d04091411107403410304002c1c1001c0c00302c420040d00401d490001150950429200300d6128007c400100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 816466906 1250 816465656 816465667
    0xc08010f1e0515070b04051b09040c090506032103010303110a151509090b040210140405060703020703080d15050621150604080f1606020a1101020a080403060903080603030906 77
    0x8003e503942840c604868900700c10f0110b2000281c2e14900e50b400340340210001d00c8030300b90b4000d050244580288000e8051746055060100040e07845c1c1d1444240c1d007510303802083c551703281e20209103450240200c080d8000c04095240f64041d02c21001541600d0007507407103018090101a106030f84141042005111404008010107a007540d40d10aa40032608900e0b00728500e036940e0521400e444d400c00301529030341016401e001c110b2a1901c41c0001c90300c030604004541c20311006800707995020301c1c4541400760000146003020903109015290155610a0720340b525494009521401007180707105e0b000441d000d21a000c030341c502d806c106450424003060700308045840a608404a00c0e04d0183c280c07c001030355044d443c5140d542e018060405411034070002c00301440d500c00f1242c83c1450010b55099018031444040c0001035011514203405500120303a40025403200004074038001c403807540503103501c00c0800d0100800110350024100079000c5e541e00190b5849010815840344202e480ea1503014104019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 816468156 1250 816466906 816466909
    0x7050c06010b0306041814012f0f2a46050105070e030105060405060f09180604060e0606010207061b140607020304030201080c0a09090f020c010c08010f1e05 69
    0x4680c84100604041446c1d040388021107000e03003481400725000f054060705402c1050f4240325203c540410f07071510840e0100034510784211610300c20341c80f8024a000041c00c0c441b020012044400d008120410b030307480d800c000c5049920000c1c2e2050040300501a030100314070fa90280605011029103403040410b21151550003503050b5030b0300e6107551140c88180b10001404500b0a106442c811600c0351902c0500888036000c240c210b9500600d1180306615200c1401200e4070f074403802c4225200c090300c5607480e50b20303601d01002c200150b04030844d115224a4081000f086030343d810240700c55450808641151301c0d004010390301c0b03c01038086e0346e002641d405a10300030340510300d005030b03002409001c6100c10b08a003a94014104a4120388840140e40002410003c42d680040903960040c007280c521401c111250b0802481e143d060b201d031084040e240c6e18020310a00c200d03412100c2200c5103800801a102d00c4e4100a04550750910a0368040c01101800040f8452100464480c80c02030000c0740881a040c0030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 816469406 1250 816468156 816468179
    0x201060e070c030e030f010c0e04020403050703110619051905030f160c0533011203030504110306130b0901020a270b0c03040e01050d02030d031d011104050907050c0601 74
    0x81e400d82c10400300d6003150801e80c03001d01400b52946e81c50300001c151140340301f00c050100c0160b4036945001d03910400c02000401c4002c00c00e4410780c0e5121101d180f0b60310171302d000680365015040c0078104115030003031030040c80c035048001040c080c480301000700b0703a07406400e20513602c07804116080e9108490038000036020400840d040a1500c01600f003944881d0000d4642c10702d0031034000b07814106506400351259000c140c03a448500d4a5500c84071303210f1191304200e604010313112040d20003818984c07140d01240804c840c5100d18205214060b013211901e00d07081e00031402e07a6011020030340d089031a80c404941903640c10b0003150803e8041d600c0e41c0c042d044140001101c0690362000c500250407805d80041440040e0000074410844414015a181c90403c1902d0f00046810fa21851041704224920070050300d0200380f4204445650800080120b200429403c18003550360125000354640a10042601c020358090401d480082d5254022075803030041c281ea40e842801604111544000300404c100034658 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 816470656 1250 816469406 816469427
    0xc03061509100c03050417060405190f1103100c08060108060a06141809010f0f082a0d051606110703170a050d06030305041e050907031109030706020d09060201060e07 73
    0x3171034058074090395002450540c001b0b9842c6011184c20400500c41032060800261007480b074110500b00281829590358501d0580102e0000d207860120103890030255424406800041d81814083c4411620354400900900040b503034107010644070804107240d8204207841405903100d07611840ca881c0706020901042c0c0d04490b0f180d00c2c06545a140390301050305d90300c401500910344030700c7c80b075051030800d101d4840c902003981110403141e00c200c1041c107408110640c040400403e449120784000c60000c0469290703006800040c0c8288180010300442c042541c0d0b9640407107400daa20350641010418103581c0310400d42c4009001d901c000080b280c50365030542d000300b9032803074542002e03803a00d42e050780c00405071000d80e401580407900100341084282c4150b040d0070100d00c21a16082030482c1400002001c0314400342052041550b41c81e001234946000c80100d4103142c100408580b0055520710000356500c8134159410006024041c0018800f8014090b4034107039180a101c8038007590340d19034112050200f1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 816471906 1250 816470656 816470663
    0x304060c02040e01090533240915190e041209030c08070f050409051b0301062112050313060b0616050601060f09180917030c03061509100c 61
    0x700c6a0b12890207409202c0c1701135131481000034141c03080c101c20321050000c0d01524051450041220014038500350005102e0b88041c131041c18440c0744c45550007507100c0b59201a549500251500d09010107080036100020701584104c4607507041045642d20b04e0304100c40e0b44941ca5000502401040000b44c0000c000410743c080c900e0700403612543c0b41c40c0d5140446c1c19a1012100e03411100041c03044119841004e0013800040d1001c0c8a4080c8070303074070700d030b40d41e80c9182e0480317061813129101b030303249175429000030001b0010841e5165614200c41d03003050820455110486030420484000c1d040c10b400340c000d980c8542c400c00820041c54400c0d444d040040d01c0032607601030384140100140820008e8040c0d8102040b406080140004d606006010b02003940c424280824003d0030364041101200000102040403086080070aa01c00389290281c40209108030000c9090000300c00c00c82c409101c94007451281c00304488070001c5c00301d0341c5294141840380c0c11101e5000004d02500503c214020303e103001d03500d4031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 816473156 1250 816471906 816471911
    0xa0f030825080a022a0d050c060703021c0215040609060f0c05031008070b0f0f16031706040902130c120f09030e04020310060c26030403120b01020304060c0204 70
    0xc103811000c0c007100d18141c049030040300216240301055810045c40d0740c03454010b0f0150000c8502843d8055000d00300c010f510344144211061142008014030594a8060010b4030030741d2100d10030718000e07449010301c044240384000ea400c2c000341030b03610000b42c1c00f041d08080c00b0352640f20386480d220301000d40201c01c4151341040d1191030840001c8854440c1d00d01011080c1e484a407a400e005421406c01d070919402681c1591007003905101a0041c14121003045041c850a144e40d0801c82402191038020305201c11343d6454400161014550004403040440529411442e03140c1c0e1450100805c841c000d40b07010b504800203040c00081941a40d0002c00caa122905250040d00c0141540d00152280340c01c0c540002c5e5125640716041542025200c1c1d070441c012a819403d610f0480301c40d0380340d500140b05a80070000d8040c1144184084000ca02a80f16215200000d2005584030f91030960341c02694100c0005905080c03449810082c1c0c401d80710b41c08070503405545032901d0941c0c122401e0380d9202c026684540d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 816474406 1250 816473156 816473197
    0x1c032606010f03180305040e060a0b090d0203010b0310050414030a020c010807051218010b060c192402031b0705060c090a18090515100509040309270b0a0f0308 70
    0x300b41d0444d0f6400d50301c260303070781d55076541042c000721100c6e800988aa8001c5041c1d50b0b0601c4101e41c00401d40345240015119854240c81500000c0e002d00341c186002905409898600c6283d8400d60304034a1065000c0c5084540d00f100710008250b40b803103401001300c0160040d44c0c00b11420341c424024107820242a2801c1070402c2d404420381b60349890107580c071542d0400b20003d081c19240003030255451142c001c031210740c20855010440f5031216a0959a02428030703e02500b00c04200d96580c1103481c1702d03150b20302c0b420440e01542030308000754030a4560001070032503c000499002444021988610b901101409941d141d00e081070402d0f400540046074400b80415000c196500b11100980407880400004540c140950030158184a50303043d0b0800b40614000800507004001a842d2040795070580784106596a64101110f450382a41c101c3c402881d100780c0c0b024104000310307580302c2d12042c01440c1004103e6501041002501181c0f2a04174820131071001000810100409400c081e05c152210580c243c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 816475656 1250 816474406 816474431
    0x608060d0c05100f0207051c0b0c16120e0d02062703120d060501080f010311030c0907020c0a06030c020d0302031b030f0a06050a050a14040b1c032606010f03 69
    0x1605503008003c009180b180300c194001c0d034104084001841c007914000203c4051440c18a5aa000c80001404400010300410850b03280c0d641140c00c120340300b00c110009080c007458911108400b41107407400003070150250001307514240b0180350049500034140b500e050018890008440c0c20100c0230401c001e00303280e4516450b1014440081c00b158280d1000341c6e540d01a142c940c089075660703080035041041d41e0041102038480c0d000f4460542c0d4124800b0031a2891000c0001c0c90074410b191040e40069808081c480c280c3d03000111034508071005c481c000c4a41d43c82e150110b0454412500e03500050b4040810b14820300c0c001c0d070040d50405105d40300612440000074680101d07a01c1910003c4551518000300030181c14144641c07009000119107c2008a1501000609018040c0038110a10084104040711561560701402d1440c41c060f08201400b401d04100c850040d0722040d0039400324501119000340d14101e0740c9107200e140070507195162552542801102c2d0410f00c400000281542c03910001d031003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 816476906 1250 816475656 816475669
    0x3060405040204111308070902031e1306060306050a0e060705031f030f0803220503040302060a031404051b01390605010806061005070b1504090204020c0d180608060d0c05 75
    0xe1805d0541e60710b0b078030300d4000c20503d000c1240d840b0403e85172042c014000ca507240210400e583d200c0b5500344400603212040c18452004440e04001e00c40c3d49080400420400c89810091080e040351904100200c0301410950b2107803001c4030401c0020300300300001401d0070b00ca60180c00144000080c10300c4a203490303684072802c520b002c0700c09440c1c84501000b005a100300c500c1da4002400c034681091012280c0a41d00d10380d407400b407400024030580002c1420812039101c1c0d400110545e05107617801d0400d05080c01c0003900c41503a4800c0701c940e1b0761031000f15084c950051b0b8070103035040500c110b4924111080d81004e80c2050f030500e00080102c40c0b481901011540c240182130180c15520050621410480d081060103052414040d043c00400d0140d080450359100c0c1300d9901c94080006601401c00741c2001400404004c1c0d0020351240c400700f80d110514100244440c002d01640e1a00e04051720029040c0180d09028410100016103107000a0124240301c0c0540c0d00061090000d08540e584810010b080d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 816478156 1250 816476906 816476917
    0x270c04050607050a020f010c120813060207150f1103060907110d17181e0705040c0207090b0a05030304060c1e0302060603060c0f0702040b0d080f0c0616050306040504020411 76
    0x1200c1e0b0159070444c007540741a04c004090000e09003061075202006070b840c043c405000400c2d107000c0c06058000961890741400000c040b15601c42c7e0300310f503603031900e2900046001c4c1c06400c20741254903056012508610314031030041d081c10740414090031039650400700409100d00410714000c000103006a0305110504002141150a15440390b4031701803544e1900340207068006012681400104051460000c0007080b10160740d425205800640078030342c2012071502d141c45d80401d402c036207032500c51900541e000c01c014081da540c0e0241070010702c0000c4100300000515005550703040e0401c00040003840c0c0075581d080903591007547c94640c0300e4498110700c091480521002c0d4091b0b0094010005280b50500c075040d071150552001030300380010340613040e05074043c0c403c00030302035a80e441c4591143d59812403a600200e030701c090b00c165038294041010f042500301c60b0b4031450521030100032a5000c14900d540c1320042c1c40340ea881d40e0a5654140070800504000ba1040e44c00c107985e02e2001c50401c440354000d12 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 816479406 1250 816478156 816478163
    0x7080903070e0103050d0f08060a060c11130e06090708060f07170a02031e011a0c010e030a09051306052409030d0f02210306060a020312010f05010e270c04050607 71
    0x9041c2d021406c02520b2108070641c503404202403001000107039584c00c07038410103840c802c1c40d102c0c00740c03101d0b880d09061466030103444503448050059071800c07d100c582c01041c0c2e008005001e0320b130b4907100c0009441d074500e200c0c010748555410507000030320b04210900320950701900780e02e4480c18182c0c0e420050000c4103010b84580c00710030b40020800545c1c420300c00d15440354240000f40c180310346d8981031030a104e101903070843c4941a50002420300c243c02c025080000d1802c81c403020f43e6a9400c40c200c01900010b0a482105d00030b15580003407500d03105180c4a54000c40fa0050224034200640f0100c809002030810415031900d0001d000a20f6076440400585284500c1d98580c2009501808000707071038000050014040d00c1111580001c0b04200c28003900d81102c03065500e03a07220002090140e0440c0070781c418045192a004000084144150f00c0726030460384203807262081c410210f400d0144130f4480c118159020b504400180750f05410922010794040d80c2220542d080c2903d950004402c1d900c100010b9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 816480656 1250 816479406 816479413
    0x601330903030801050f031023010e06180708070e040f050a051015090b16240c03020301061d1909020310050d0b0c0c0a0b0f041103011107080903070e010305 69
    0x1c0c4109a0401c00b0749014040c211080624600c01500280d0756650008080800755280c0c65514488103207c0071843e030441426541010075070710795020300c0940320100c94041c4140080d041c107000d041c081840043c041d01c41592410b19a5a03403100a555a40074100181d400c2aa1810884c810280074403505000d244408070118060601803001d210091243d00168a00200400400b101c01d0f0002411000c4440141d540307922220724000303a69402c01c554201821816003100c0c1000704094a04030110802100c45e800c004451504030110300b00c5c08240101408594a65542d544a031450301c0550102000104103424100000c40840c02440195000c07100150300801400700459a9188410107000180d403001c0115009848402c08460301800385c1803ca500001c884406000500100440603000301c107200b018200f94402601080c012a800d4400781c60a4070b1015040c601030040d840d42000d02103c16041401c0c5454090440e88065040e6070300d48070f00200010100d050803141c500850146015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 816481906 1250 816480656 816480659
    0x110339150d480f050d0f0b090103050304080f0303070e280f03030e041b0804060905122505060105150c0d0504030510020301030b01090e190b06031204050306013309 72
    0x24070340a003400b94001c00900462940320310010b548141651200100820086030042d468412540103203072000d01d654104000d03d00110501400100810448207203604449500d122140d4042d10380c0030949000b00016002d912070b112528041d20790301080d2146580304504291030021200d03000895238010424156003600c01c1080c140c10110444c0503071010796050002000c4140725520740004c64000034240000d001c0407a0a021450703200914496100040b2803652014600c81d032082c1e04040780a0b0b0f01801c025941405210000031440d11300c5602400400143c0d08120401422290580c105201e03044144400c0c040040300704403504005655448040d42c4074154206a400c0c00900d196600c58a801000100000342040840364111080c0d03480004100100191090502e400c403d0482d141c0b0518941c20014041c1482445000b1071080701155848001d0b000591a54060340c458198150009401003084151901171a000c120b08400302031008500308a41c90300803814020f410001038101e850 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 816483156 1250 816481906 816482021
    0x30909011511010603050d111207050312181f02070218010906060207080303150109081f0b0307030803130302010605152212110339150d 60
    0x40c0c440c5440007500083c04072a05548860342d40d01280841c001c1009003032945c11030303025400e0006138400d18000660554640c040e040c426033340c1c1c11542c9460320b0111060003040035121079900c6002c083e0f00410280c03070744001070a0300710b803110700091000c0303151902000146c00503992909a0216143c101103000e5603541001000d10031983d55402100955104410030300c984240001a0399002c444103101050300900100100c401722115030260603644141c44030f18121054800111880318511071041110100340380070550b80303e41c00d03c0060a2100104080b80650344d072540258020b501900000c1503103543c034030100f401a2401c0f049140110404104502c0c5802403814070704954034aa001402c2682c1042060002841388071002001c1e403454840c009000d850a100010f142c2c143c0e11180240c040c0d9880792000454001108000d1581901c4004c0b81180f0b01544d4000ca2441180c008900307002c0712030301c40c4000340603445010000b1843d0b070007007480f003039a08035200c2a0b9480028030141020881e80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 816484406 1250 816483156 816483167
    0xd020a0c14160b0f0d051302030c093112120f15091d01061818030813031b0809040506151909050d061b08040c0501030203090309090115 60
    0x10351140c5180c000c00b03100c034240d50000382020151040d0b0070619680e00101825002039200b120101310b4118207080c2041030090203552002c0d034860003a029200c55002503401c12048282c11a40c030b01c51181c9514140030041841c0d03200c20540190094285003402850700d42c0c40c01800c500100c4000a0004020a030309040705028259081d0100c0c0c4040c0300306c4015803003000f1809041d000342403802c0c3d03489900c000c0e840d0303100b444458a40b000000801c4925180d0625901c030046410000601504007003400400c02d2050b22800722130303601903880a985032640d41000c601102030030400c1c0d0170031160308540c0031442c095a503201d10b214800c21a407581d03540e00b0014003050b10b400411080c0715216040c2c000c00441240300c12198510048103540c1c2c80915070306020340d030303151540d009260000503541e5502e04200e1180d2191007000d04000030b0786500307520003d048868203011140204100c01a01040091354040d4001d0b5400c10380074000d490402c61000003150010000364040401c4006241c8201803c54101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 816485656 1250 816484406 816484433
    0x80c0106031703070e010c05030712050316020613062003070309060b0d170a110f0304030b0907060e040510090e010605090603030a0806090c070b010609050108071e0c02060d020a0c 79
    0x79a42d50305500e802d15025000c05010940c290610240a010108112080c001c46c1c501347e60200480848032011100100603410403030340d8409069050b1420308070a800040e042d4410b00404080820194450b0b560300e000d00791401c1840c6510000004005650019101551042d050b503500007500480c6401c000c02070710401c42803503005000420300c5a002c10b042e04445202651851305196807202200c00c1114190002d042c20400307030098030000c585092021004100300c80c0918600c180d5a159040301e6500c88015100d2000494460b4004100318202034100ca944140c08020341d50f440e0f9035501200081e988032070810f04d401e0b5540d1500380f1103032601000c142c0d0820002c2d0019400c0c07120716440548200ca000d400607100e0040b42c40003e4405141e00c080700c0219620a02c10215540e58120103490107256001d11400300d02403000140d22a84240005080c605034003629020010f00341ca02952804909041070360448800c00484542480c24001054517548680d1400703235104182c02c00141e1408027 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 816486906 1250 816485656 816485693
    0xc0d0309020112020a050915090604060c12081905070201060b160c060807050d1503060c020f0f2407111608011a1f02030c01090c030201020c09270703080c010603 71
    0x41c41703a0b40c201603000d0181c072a241c400f9150303d013440701c0c00003042c009400780842182d4011000074001c42c805038030000302c040d03162088902000080d03400070195011681166a804030f41140740b641983d400c03542d00107039049521070000041c2c59440e03d913600460b0303001c52104caa501013101410000c00c10038202e603c0043c1024a01501c0ca0b007032040d801050352160800d0300f11000e4a131940c0c0700c10080785088000003180c1c03020080000030100440603450307440c0e0790440e040307902912085c0c1d041c010012642a000d90003042c039001000d41181c280042c690130181400381040079424030701700c513190104601c0c00180c0030030480380d11080c500700c15035003036903a2001c07600c100036103105085103d516281204031011a0b03100d1510201c000c0c0030b00407031450081412400315903082403085020310801107140c80039a4001e81c01e82d0f8002e210002070088110003034903440102d16600c1480312514104001004840554109951380241c3d03d80382e90225400058560391165500c5104004000404640d9580041c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 816488156 1250 816486906 816486911
    0x13501080d021b1e041d0715020c090a15090e0d02010e070e060643021305060310050a02130f08030a050d0902130b03010e0c091306020c0d0309020112 66
    0x10303004021a05149505241c6000d42418082c1190040591100403142c2d1030282c400c0090141c02c1481100748070b81b180354444980500e074404901c1003015105070010b00d4694005010000c01541444203211009100050303a5035544210601e8482c80404080100f503180c00104035291060780072420810314000c1e00c015a0316000100d41c1a61002c2040301c11211070740c2d480105540c80201041142c030584440040e4040040c481c01ca031160381c00700c15450f92070103c5000000c0c0d4005610006030404480e0044d520501071800844068000d4200990202d0003806881c2070203882070b440c0e0151031342030b03500307151031034000c40c80034030741284c0c03466920003032000d2012801c10b240340c9244142c0741d20420600bc0d00700a00040c1a5072591301c25000031003580c1c0d0282901c0181201342442c10010300056003090f110b5401c01ca9910082e4400195224901d0030081c924426a180c420358044101008582100c0080c2c007400b00c902541400e0080840112803070710042076400c054800140f4210403a0b280e041d1041c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 816489406 1250 816488156 816488173
    0x106081b0315010f030b0117281b0e09041103070b070c0312050a0c0803060301180503030703051014041e051f0b04060504150903060609090c080714013501080d02 71
    0x1c1c0d000160240003452080c031031920345c070b41c49c0c2030b86020950500910001c1078110b4040c3c42d9482c00c0da0000c245d26099014204202909140803100c04800400c00d5502002c098041400b2039404014041001001002c4804945d80e5610851075a0400b100503030710555449020820301900c0c04280c611901c962809524200509002904132070384000054282e48000c0009031154400350701006c0f02035a07000c003072840b86940d460226030b80c0d4001c41320180088d040c0400704501310b8036035900c04290307500c3c03000080d2080740d00d8017400014603e00342c0320301501e00952a101d100d40d516200740b50081040503450f034002410840c0907030b906082e5900c00c0300d01c070404200c1088076944c000159000c1d640e4841000000403c009030880d00f6a030aa0000f418113443d2020000c1c002e20140d015640480c4070307111000c000d41c0c0c1c80c465240c46128034820360480c600030f6681c0c1086584071303440e0394404000d03010301e9081c600d801141400140c10166000c124403800e09005000c50b2404002c10300b4048603501c010000403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 816490656 1250 816489406 816489409
    0x613050f0f0303160c0c090e010b01030b150a03060e1008150c031506070501050903041a0c0a021c0803070306030b1302030a021201140a05011e0308030106081b0315010f030b 76
    0x1e10000301904c603c0b1409420300c4840511a291101d00c06400070f4036030710341e00d0703c59404800400d442141c0c2c00c0ca5600c2c1c6410341025502038001d8550702c9400030702c2c200802460502c13490455006c00384240405640e40c601080801c082c0382c440d801508201a03604565082011040c035180b04c6180707400186c0c03079040070408804140e400316940000c0001c80c5c484401102d0001c9070490082c0320005216500f08810040400d80c000050b108a03100800010101c15080c021007085108000f01003145400409046e005418103e1000e10000c144482000130f04d02c9030b48804400350003e403503290020b03880d41000c1042c85010354103660850709035202c00e0b445900320750000f030740d422141c0343c0240600c1484164640000b400c2d40035a1100c05003400c1e660705031800c1600d19005080c24011201440c01c41d00d410380b50120b40916000580303500c20781507881d5908220303095a1141000300b501d03550b0301000801c8444040e900b405540a11060349c00a0b910403011070000d8540002c842c2c01500301407902c140040203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 816491906 1250 816490656 816490663
    0x215030f041e060e0105060306100602060c0f0912030705010c140901080a0f02040306060f290903010216031706060309070302090a0e0706021c051305120f0613050f0f 73
    0x3041d8000420381c03400701082d40c00440034464450140000f85007640385050014190480c600c5000110152501961412080342028030940940c07001603219500281d6452040d00c002c01c2001000f1082074149607a07000014420359041e003581200e034002040d2101005424000e050204600e4144000d0080e0001042803450080040241c10810008041080b89007141e00c0345001c44040141503503070701c0e120b0401c203010340480d00c03415406070f851400014100c01c4861688a6507038110000018003c0d00352000300705900404480740e4595400c000c1310324680f2920406450041c40382d121582070380e540f80800c0700840340003800140039100030001c200f540e20021500e041520390444000f000398441d119000e0040c65410f945401900c078400010400b80c2d000620451480481e10016155889402c400c5600d402800d9503a40903150120f020700051070405603001c401c803000c00854034141240c0c801c0e245802c500b0355084034100c0c5d052039100d061010520411524049010040422814a89007140d6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 816493156 1250 816491906 816491911
    0x3020d06050415020301080a021212070f08041806080d020c031908040308040605190203191103120106081b271201050405010f0b040b13240308070215030f 68
    0xc21a0755500160410a80c510502c00d0a00503c408640725a111049903903220385403103060b4400c6005a030154000d0000003800380c16003698820072418a4450b6850041d004907100c0119485d80f0180030211b0590564501082d2910107481c0201d5070780d16041010307007448030000e0b002c0c00b107400c6481414159100020b9510901031103805402c151086401c26035150301590300010a01c2000182c0000c4243d440700c00350018600e100c3d01c580c101d01c02403100341e90b203208182078104e01000e1714004030b004602a00c4103180403041442035030715003003a00c2000980711400340c2021001c00c4070321040c0240f00c6800e900107022271245c420703007915261402080b103e000303c903d0034a0038032074481218201580c98500c010400002e00400901c101d0910345041e60207440074840500700d503840c103102c1d400e20b850b250140a9110b03d01514000329161444840c0c8090318a000038044a024a201e405ca2030032083c40600340194001c2503042d8642a0502c104103800c00300701c240542e01002441400f400312010545240c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 816494406 1250 816493156 816493163
    0x2090907020d140309120d020d240b090103020706020a03270c0e09010b10120b1e190f0308040e09070506160302150109020309010606091d060d0206030c0712050403020d 74
    0xb5202e0380c03100c2180f8135000c2000c500450100300447c1014aa0f102034000d01011134000c1400d00606045003401910320b40b862044480c2c08459800c20415902820020222080180f402600d407141c0c41d1035040a0b030f07000c0c0480b0000669200c90342c2c007207a03080f42034440810218400e54841c541c00340d2035584a4480500072000f9070340c42c00022071030b180d03001d500c190b103c032001801c050420880100090050700c103510480912505007610360665242c040000e1071040c121303030399041c0500301d11000d00000100440840c0e1a1008618000c40c62490f900c2c0c0880007980f043c0010b6503900d04015070800044401b0b8486071455204050911080e91001c3c00e940520501c80300e1000c1860007400c089241020100560181222400c000320310f0301c019400462083c030210009020850b9160740c119000034081c0b240510750f109501c004244a010101800c0c0c0082000380452241142d90700050310b6070b0b1007a01c2c454400b6070002914802c00144030200440740260381007036820289550080380c0350115144004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 816495656 1250 816494406 816494447
    0xf080a2c04110d0c0f0806040c0504140a05040608010207150507020c150d050117010b010c0302030a1202131509150c03050c0f0609010e1b18070203040e0a02090907020d 74
    0x2040700c0007a8050700c0c805500d00e50180f11040b6080340160a05d0b8074420b20030000391090000598501f4603000310744003401d29a4038540350514100c03100066504d90920581d2004100000094551355801001c0161403100c00060b683c00451800105050f000130720201418140800c200c407032600803a03504400c07001543d90940100d25007140020b540b01d00d501040b0903034580300010601007566504039218003500d50080181c002e107500103655284044400a0042e401003000765036180c8100e005041091403040c0150600c1092144120b50103415040103c00040c8642a410702650113040000140181c04903051a035400c258018407200310090041e040c85000290761840401c10441d14074610021425a2454180340c0031140c0039040d01e00040046124003000210304441c83d04003c140810020072481100040240e0507a07800002400201940000d0000081d003103150300d009449000c126500581e260380d403804000c294600900384908540c4a9004d010b0f04507004a4560004040c4800e034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 816496906 1250 816495656 816495671
    0xf0603010509091228030e060106050901050d320106021b0604030b1602120a052a060109020316030902061c06080a032006040f0f0206070f080a2c04 65
    0x40c03a240007134440402d529040002480200000100c0300083c00d000041e42d40c0c2120715500100300c054818412441c103180d0400401009003d0041004007810036040c180303281040320400c605011590300403100010040b0b02103c0c0a4007602640101d8801d4003000e009020030b50600e20020360b2030046501c10145460900400b405a603109000d540085900c02c41c22403440c9004d03400a100703055039900d402c026100e140000840000107406803808a91165641410303c01d4040101c1605124540501a449084132200401a4041c411540a41810764000d03a40e81810201102c0031500c41050b81e0416150101d090016070ba40c3d4101e58a41e20001c1102143c80700a46800700205101d41c0403600e548a004250010140c102104803003074040e9858402850b4200d0081c0e07500c47c84222001070042b10307043d101c20009400c1d0308030b01f54403d0020344564140070302c03680d504005100b1502d045d61815008190041b00d0703a402a01c1d800c03040c502003c403d02404c1401050200e24400c03020251240d80c56050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 816498156 1250 816496906 816496921
    0x1b09150b090607080a0e03100501080c06030a1401150212041406180604092403020a0b072f0415061e0e09040804050108150108010911131e050f0603010509 68
    0xd0f40c0c07180b80c01c07500c40b80e03070703a5030700c10020f01003081c0b28004600074003800c00307181c0042d019403103014102c0d11810060240360040000304070103075200078005446190b4464403240c0603e03400c521703103002e010012030250035800e907010060300d42140005100c10306a002c2100780a054400300c01044502c8042e500c43e03840d8008900074940d4000c0c2241e000da0000008640000c03500000c0c1c100a815120905618200e0781d0606c510140200300d03804007070f4004510200401c0003521410050001e9030059034000c05c9045030700010864802c03481003440d4060340b440724a010500d0144200c054030440901c00314041c0e8034000b0701400303800905001c42203010210b111207941901400e0085100d140013042c2c3c5499184c107150142081c2c100703001d0107000401c0070300024202500d000340100b0228058481000030b81c0707000d0500780a0509014154075140e41030110404402c8a5000b02d00a0100006078001154540c072100850f075031940d00c003900c07480c15607103600c0d241d48510341103a042d034500340c0d1070301d0301995500b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 816499406 1250 816498156 816498169
    0x31104020307110d051804090206040302010c1b030302070617091e0307020d0f1103030c062409130303050a090c0314120409021305040e0c090402011b1b09150b09 71
    0x20b42c9040c0744d000710002154101e5200c0020241c1d00d00c0484030200b401006800c0c0422580c0601c802900102d08000600256000300d070781c00b6403284545541c65040c0740f059481b88242e6102d0740100c000d41d001c1e00d01840802e0b0000580781140159542041052030501d00b525a500b0f101514943c003080421b2680250040c180115522650044c00015952940c2e1030b04071682d4804000695120044c240c03110700714a404400c480020305000c00400c029101d828590140440b07111600142808203544c2082c1e540b140402507100d510181c440300740b036030f020341005815034400601c01120745182c502c00380b000030003040c80102580e4000b03128130b044440d003424242c580002c0d40180c14944002060010f401c3c8503603001800716007244e0003411500c40e0b6417400c0c401030f2806042c17945041d03080811055910f00300a4151030340329005140c03030341c0146900e54051544590000040c6c07116418000e80c40c1d9100d0303200354034000804000301e00300400d6980d40d0203180d50000c07a0085c446060b4000400280595620 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 816500656 1250 816499406 816499427
    0x5010f0507030f121b050711010504080601031103100513060b1c0822180c080c030a091a090114151f050904140a150b1c0f0903030b01090e01031104020307 68
    0x31701804111003c0c0700005017854001c04011180410350302d02928255106106443c110b482002c001c1ca034030307401e40d500c0c81070400c524003900b5018850700345a42c0e0021882e0040b0707405003a004113041400e101c0e5050050540745405d40701d500031030000d40d01040303010302c03030b11101266a001510300342c40754520806400b0034260305030f8110290520410209031100141205503920504000811207408040c1c025103d0301002c640b1694080c50910004407104030320f4005807071040c4103241090840410700301c8031141c0310b0700ba02c504c41d0702c0e99500c208110800242d0340d029000310241080f12844d0f4540d00010350013030342c42d00100c0c0d08001c83d40e1007d0702c554000d50540340320a000401c00d010009c2c0c22800c0c2e0b4485041103504180301818030046100c41f07018205c2c03040650341c0300c0d40c52510f8070b42c16128200521070451520301c030883d9680d16280c6414240c1c450b280501d4420b95020504100c81000104500160f800c038903280802d003401040000d03000c1c0e02d82d1040d510143c50250b01c0340c2e1001d000b554600c0c0740 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 816501906 1250 816500656 816500681
    0x4020f040b0f0f21070503100501050105030604090f020a0303110d09050907180f180c030b0a090203062101020d060b03150d08070f1a010b040506070f06150803030105010f0507030f12 80
    0x4100e04501c81e0f00c40441c00c0011b0320001c0e41220700202d5a050381c0e405840742031041d6404200c4c02c101181c6282441d8001001ca14040e6000d502c20207801c2c0d0104248601c564406d5000410100501852002c01d100c280940003c502c0d0440006003024006500c01c0c5d000740c200820300429198a018031a04a0344038070041807100d290510039641d444104420600031182c04801e40e10b0300d07800e903420314000c0c0300703402031030001604c0008003600788040c4000a52024190720360200c0105141c0075110070854002c1d004200b00d200241c1c44150b0203078074100b80c0d0402e0b0051103510b0014810000402c5441c4035549030080116000c02c521043c1d8240a042445548005001041920007071020701096550810b082e144814098003d0381e658052650346006500a555000d0003c00a90380881c030f00c81e142410341c50294000042000003544468007c6202e9880b44a90b03804c007100400040d85c110010300a000001d0410030b00c1c0140c0c0b030760006c01080205600d030007804044140120003024036444582444070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 816503156 1250 816501906 816501949
    0xb0403030203090405011508160216030c09110306060d09060219020a120504080a03051810020601030303140c0909090c0a091e0c0f122304020f040b0f0f 67
    0x2100c0c24000d480798070201c0c489005074201340001035100e600102c40c00310400306948403001522407000c00341001d04200f0302d9404510854a080501c1454600c030003000b50700c0341040003e0385103002013000650354004810824000103004002807038903120202c820052a890001030101003d1901000034000e050f41c0b01a645184070262010300e400003450845e0b1401102c106401040d00c92003195076115030b00607142070360001d03004440001e014502038851000034122082e104003443c008541d03142d000000413001a07000c540104140340c0c040c81500c0700384148508000f00d40c940348403021454841d451500e40a50224000100d405100340316604c0f820400405242003140c1c0c88180c00058050504202683e090402c0b950b4500754440c41034110f0501941c07242d8200e810f0341c01307081e0b4850104080894026840c0d40d1004d400912445820682849484180d00c1c603041c68010b0100d102c44144ac040c0c00341c0d02e403e03040e0209960340380c0000c2580d0b00403111103200200c01404101c8150081420110401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 816504406 1250 816503156 816503159
    0x4b0c010f050121031215081212070309020105040317070f05031b0c0d0201030c020a0f080a0807050a0207140111071409060306101a040e1302120708030f0d060b04 71
    0x1045400450480d0184100c00b4407001c10f400c040541d1a410000060109904400c41d12403000150003908050446408484900350781e4040319050061040384240d010100043e201000d08511024640050b03440c901001030205a50010b4814800c1c1d0101400c80350880d11801401010701084650541d0300c44a082d541c51803d03e0856500d41003041001050150561031407a4103800150169880400070095610100c0380c3c1c006500824840a02108600034038001c0030116002e4203042d20b21034811642e42d90b94010340341d0000c007810005822181042003c2000092050b4009074000548031103c02c2207000c802c5050043e602da40c4075654001c02c034011480001044810540b010041c180b05841841d0140d40e5082010340702c0c4001c440800b00031103403039414000c01840750302e030680003800a011145001c0d250409001c00702c90441f5140806881558010110304104203e0103006030504c0041149905000215460340900e060f10280d14001040580c501540f940002004000046807a41c1da207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 816505656 1250 816504406 816504431
    0x9060e15040b36071a0304020904020105070f0b040c0501050408100e010f0c0201061802030c0403030834090807080c091b0406080106170412030f0e124b0c01 69
    0x554030341c64583c203006000700041e800e050b001c01c41201d80411310381c851441e600c40d800c1048001c0042d0043c5d040180c14040000001c012443c820340d524080c4c2c0d01000d81d890315182a440204603500294100f20302270004014007140002c0c00d0468010080002c0f0780e05100d5440b460060411042c1d070142d480c20a4900f503102c035010b50210040d202d0001c91050b4003450024a4070691000341c0d0b0707800e10044100810004244104000303900140301c0044c540607080c40c181884100e00d50001c030390891405603008c40014a401041100081001c0300207040b0891400300a107403640002e060807402055500001740c0c540104680380400c00a00c880455203c0e82c41d5003005044003000d002d44008207031400403604000b05886100d9202c0ca92000040150407680001200980f403510705806046071121f0624400000520124007603d99900c2601d89403010201d0202d10a08001c5000d4042259201c075503204614a20b00f036807280452001c412260500b5048188080c800d924109200e5440c011144845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 816506906 1250 816505656 816505741
    0xc0506130303050105030604020d03050d140c12090f0607030c020c060c01272001030209130f0b0105160b13120201091205030610031a04050a09060e15040b 68
    0xc8a02aa0741003003d40c2c2c840080c07541d90102650042e43c00307030902d4151800a4070a0004100c0c0c0d0604c040d003c2405405107122000014080e0381e28134074110301240030300c52004010700181e0f1080c0344500810800c081c001c41303ea00c032a800b400a00402d5120f90100c14107600030000d00c04035141c05804a95601c2205100600a03c0c90701c13142c800494a11041c0740304440d110301c2c0301e010181c1090210801c07511500c7c451221002424026060540a1042020941d16900c07031200703d045144d004903000f00a20844412a003c00c952503040c0070043c0302030107400101d980210700081d808500082141c0b1080040c0c09a003c0f28200101284130811401c40d0555040d0480b000a41c403c40d8410070640b0250400c0e07800340021510700d0b4000b0aa240f500715410b01c01c0e041100746041c0c000706000094000d01c0840c040e1201207d000042c1604c5640d6a802c2281c0e510401c40d60340c25400c058000f00d8110481d0b130b8020703c0c2c003403c054540d00501020a2004129019100441e400304d00f02e0300100d5800200c240d038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 816508156 1250 816506906 816506941
    0x7062405100e0618090601050705030d0216021806010f0306350303160807050403110d06060815220206070807080d1802010906030615120603052d031602010f0c0506 72
    0x26044c0d03000806c00c0c0354000d8042c3c4c5c1c440d0758044080c40c14066041c1c4030000035048040f07030744002540341c0c88440160715020f81d030307005005010a44c01e03010314203540090030540b86103000200301450a44c0c00c10484000c140c025440c0740144003060492668052050341554842c071000085003c000207101e801141905c808950070010f480e85055961080403d98160055110160140011040d08117440c0350602032043d00c180300310760026600d03803901c0c032191400912807003681d00d070202241800a0a8690180c0291840c08940d6821422682e40d010407282c1c060940f004041d100b0210f084d10801c00f50300d0540d1001c954140c000c0040c8a060000103d40700d44601c41a4003150f1004408a41c40e0b20a01944060350418071066000489945046410f4003a56648448181e49c480700840090010311414080c200c1e122205d8031070b03200d4807850303102403400034140d44025441000760301080c541c035110071412980c0900b401e01c00c00c0c0d0048015590220440301c01000c501460003004003c4020020210 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 816509406 1250 816508156 816508159
    0xe033412030e0f0130050a0c02060a09050706050f1603090e0a05240105070602040b0417010204120f0f05062d101203050409020d0207062405100e0618 66
    0x20740d02c003400c1041c0089084514007660004000d80d40950021200002c40c5400541c03041c00e4601031100802144201c0f18140d0b90001007070f890360414448254100b000c80d400c60310305030080040c540640e68180e07507004548625000e1000c0861501c00740621030b0280c550084507281240003410305407500030880c05150049400c050802004150746162a12966100d9a040d45840c43c0f070300707036600c0801c2c1611401d9061904110041018500192580c00600000d29002d100d040c1c440c2c1c2480040015042c000c00010350070380c4144401c0002c000e030340d440d2620701034200131045100340d12420007452602240300f0260040c4102001d000405280503c90390840c0e144c0c248001c40030600c07103616410588261228900c503480300000f40b04620200c0004150300344241031540c6400d81d00c1c51050160307003000c2d010000d110340c08200d00301448250b024225941d506141d0101e00d44801e60b4403a440481030f0f0040034018100400100503160180111254645c0000c00d80350b01c56140c45400300e10114298030f420b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 816510656 1250 816509406 816509417
    0x70b040603090b0a02070c030b0925080606030f0c0114091f03110a14030c070f030c021509060715020c030d2408030d09110a081005070e03341203 64
    0x130341d006072140300744c81c18a548050320010181c5035881d80b004501020303145c240180504582804800b0007a050417014030028090202050b00c0c0100c803600b04400100a24000d4008510707041d01c0b80c201007680f10807601e00b424202c86804101c0a0f00384180a83c40e03a283e04803481c956042c15150000c144809012100e540a01c4240d0131002414107500800c2404004600801c0c0090110380600c0007850703011100410703590400889072118a50502a108203801044e50007070b900003581000c4a1103500d0b5420f22804501d00010755001c144207210310000508044040a0401d644000b01d4040b13070481d4141d0400c80c1e444a00c940d22000c01000240001c040001000f00c80d100324680c40350151040351060f802070360800c88030b01c600700c002d040328810444680c000103420650350340d1202090780181000c50010560808c803100e4003022030703201a14050a10001d58a05030403940d00043d2103101c2261080f50103e07075a0321480c418000c044c00038541c14004112400400d9440341035600110b0903010303a440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 816511906 1250 816510656 816510661
    0x10306022814030a140103080a0210020909060f010c210e09010501050a0c140d1d0406080d11010f0e010b0315060603010306051510270e010611070b040603090b 70
    0x161010707580303940c844003082410400300d09102890002d140d00140c030300c001041d188a0601c2000d8501c000340c1040711183e50105e48503408030340c10410b040c41050500740031441c255079240011090107009150910600d0b1501c0c0c10101644a29244d404540e8418a21083c41440c10700c95062281100ca070003000514000d801c00031440c042039460704031503040c1c40e110700d080034498044801d0f48842205490701402d0304141c1a00b0310b010441d099207019143c0d03034459180e0303c00c0b085c0d0b0391004031401c002e07100b182080c509100c0c110010402c036142c840a070400010b921454040c0b02d000d45810440602e42030315060800c0341c0300c401034000c520440822420ba401c44442d41050030b520034420303130704141c01400a00040c40050b02e140c0c0081c4e00040b541d075504c02c4c50103401c00083d08d2403000841d04030008003030001c4100d408801d00881030762042c90601d0ba004450404243d0001e0080512035201040a802c0003100810800c1c4683c4005e0818406180c0d03030303103444d000c02501501c0a20011501c003400c9000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 816513156 1250 816511906 816511957
    0x30c01030603080901030504020a0f030305090a15083912091c050a09051c121713030e03030712090e011212021e0f0c1008041205040b0301030602 64
    0x6401c00340c07a44003219a00b00034400004400420005204982040c0d003154041481c05158004100441c8241d03185a035600328041840701d81041640300402d030100071550184c4142e000f200c61a0b00c14007646161002c403480c03841d116909904031014449050b11400c19942ca0080c3c0381c014552a21400d85001481e155440c9082e42e80106000f5641c0c0e5420070401501001d104034000c1c00c100c015450325200702900d40300080c0500f41600341c1e2500092980b401082045003280914140d8506800d00c000c01c07404428807641942c03001080803400311030f03102040c402c03d03000310310f12008440b010b41126252a002c1c41c1249901c0e00a000c2c0c440031802c0c07480001103010b070001c0b0160590740106071448070101c0503035a5101c0c03021210008000d41c0100d0708008004010a0690701d0140d0980c00282030b00703000855038034104004110094000c102000e1880d00103504000c42e5034107c1e03400126180084641e1800704c529004540100d551040000300000a20503d60007522440000c42d03110445880c5154 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 816514406 1250 816513156 816513161
    0x150a26060f0412020115081f05090c0909031204150b030a0f1407050301051006140703170c0c010f0204091401051f12021b0d051e090f0d0c05030c0103 66
    0x110700105054801002400150b44039803884515076075400081000e469041c01c3c11003240341e60b00b0a0780140c0c007080340740c04001c00d000384804502c85200410009420030100c2e40d83c8800050080d2030260b265400810f0841c4010022121140007000003c03c860820b40f500a00c1801c2c88205240741c5810140c5a00c1d01d4034006c2482c00c5219804074504650020319030b0382540d26603584404210f40d00604000090380e480a0241d0740c481d0000d4010301211034100a0041c00c290118500640c01090034041440001d1700300b2541422648514802c414580da00b807014401c0b48585103030754042d5403c01c010361090342566000340050721411070041c8480070060100c100140001d10680e907000300301500352684241c8000ca0402641d011786050010f414650001c0820f0342e004500000b21920a219108016442806208402c24203072509d1031400c0c1d40500d9100058465540c480100000080c07881081d5171100c000480d420800b5041240400b401d04010700000310900c186801380c004c080744001c0c0340d8800c2c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 816515656 1250 816514406 816514411
    0xc01120606020c10031808030a0c0203120117030c0a0c0311010c03080a0e01090503040f0f0b0a121a120105190905150403090308070c060f0504030b060405150a2606 72
    0xa0b402480704002c00e80c2003220800300c0300e031203905244d540c124400b0400c0800c5a03001440f03004034803040d9a41404501842202c0d5010314000440d0000d1014000c9410003850ba281101c03420b4290440366421207004606503c11f26600c8130040c828000035000308000c100000040b280984480c03030038000d840700113458030001000c0007400500c0807070004410b00041c1c0c0c881e0749610300ca500000b854000e640c0e243c5141d40d10513080050900d90201c420094201030703446000242001f10501414042540c03000f0b030a050010b06510000c90f01e03400703c4014110b90f0503141c081200010b00030281101e01c140c141d4000d013001e550a002588002003041d00c0e4000c64024402650303445001410050705606101020900144c000c8003000041c2174000040780d809d801a14a03a03000350b1030110003620f4400c0241100f0401e64006c818882c052000300040f0f184c41081ca079000e0f0b0280e4001c26141c0d40c00f48156001180c0d25000d43c1d010b50710395030108400a640c0c020342807000801d850402e2610f00a00800d0743e51104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 816516906 1250 816515656 816515669
    0xe0405121c110405040e0114130b0103030804110418020a15090314120a09170706141e040611010b0f030706120e01051e07030603030519140c0c011206 66
    0x285420703007940242a400341c03040714030450107030742401e803030780300003000d030303a075004415644c4e039102c0500c40d84e082c40c20000c2c2900300201e0b0b440e030003011180390388400301003105200142c1400360220004050020105900e0002c13100108204249802d5204070420404409800e0b8002d4500d01800308100c4400800c00e1803031121520340c2d1544514541d500b0003107600d8203140c1700c1d550082091010194016001034003214809458500716a420442090036041000300008020350046004002854021012030003444901640c45c0da034003001078442201c0c00c04010700381814040050001500c942c820b41c0200b5240e11000244800301c064420800d5a492405203150300d6000590100b00c0240a4101050f02e04400d000100c0c042080c80d001d54215101190040c210075042118541c1c6c59105c1c3c141950701004c507040800076a415134130001e0860146088007041c2002da842c01314620b038026481b44041a11703c48110741c1e0343ca801c0000726204d1100d00c48080c0455501b0002c83ea4141c02c2c0e000d0a015180d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 816518156 1250 816516906 816516937
    0x40b0a0f0e1b0f09010f05032b030e0114091b0301020702030d0c170f0d141005190503030304050f0708030c19150207030206010513150b0c0708070e040512 68
    0x540014150056414a0b40c00395080703036528144e4480c80000c03402051468480325400789440700740f508041891640289081032659170540c034501021445102e840e103803400107081100000403a0040c0f0702c4000d24181001d00c0c80400c101030710005404604014005c81c2c610980300c60805043c245d0040c044d0081d8075410000b0181021842440080741c504c1c068000208444032000304450740c0c0c0d00100c1840542d81000480100720320060160841401000d55042c800e46810607454848900900505101e84580300300c0040d21030264007014082c1200030180e030303580d040a00d0038a03a10060424100040e000d01c00c00018030280110a0755108507240d4054800d80014803000d40564030381040031650703505910307111747d4060820710191110b1031082d0000c1007154184800c00881d40006064508814207041000381c900307510b240c5200458503840801a01ea500203625541441220b810110262040b04400941108203201c41400b90780950700751040010350701f00d142190310845000083c0240f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 816519406 1250 816518156 816518173
    0x612020d0210021c0302090f0d02090a09062007050c06041d0c0f0c0c0906091302040f0b060c0d1404030b06100e04020c0102130e011d040c030b040b0a0f0e 68
    0x1d02c10154064100c5a1044c1d84284024030a071095040d4040ca8120001e0340c007165285650a0003c610346c001030702161812410000b03980051130346d203130040500072810745440d40142002060b4202040146124098107010504040c83c030403950070428013900c45104a140c0840181803280444080d03c00c2800c28006d07040c4101101060b4000c00b6000d0b202c0c00ca000c0205840d1000c00070047d10314404020040e05000309030300c0411180441c06000360348206913003400d0101807080e041030010020380c1034401103000041c40c440300c0001e00c031902d11144c00203c0094020750881d8017007a440c154150302c0d25503d41114076903145103114081e07400018240b0310001f000c2034040c03406040c3c001c2d8108161070030b104144100c0e80820103130307080406500200e030340104480307545070751158110002d000200b140740919071500000c448640f014405048011200c400410280003c01400350059508510400d0441c00c0c18a408141904100c4074800e00b01e20308044905078020714000c0d402c288454038000c00084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 816520656 1250 816519406 816519409
    0xc1513092304050c03120d0c020f07060e1315030b181e0c0a0602030c0705041e0c050403290906071d030307060510151e080c04051807030612020d02 65
    0x207031030150003501c9510400b0488801070340e040144d900d0510142c2c024944420801344607206448010000701f0954105280c841e406100000f00142114030b68580728521a101e54003140e0448040141c0f524241d050200c5030420f00105a9000101c3e48600c016242958031b1010351340c4195462000b100060300300741c15031000c1c0544581c48035601d071101c8040d50071400c400750001e8001c181641c408000b507000031580d000c0f9140c09014040040070255000e102004000030360081e000303030480c02c200700583d0785c0d503070948000c0c8140207a5019590003601c00c0305078400e94050110300d030032000246c010001c0342000100044404141a07001d520319481c0c030305890080b151000031462456607642d40512091054201150090007042d0040400024010221342011920180000192081e6051040304500743c1d07448200109500c1a000032860080aa0b03120160025154403c1d81d0140390300540c000d40140e0b00140400342d4178015402034a017002025640ca040c1101c400801d41d01a5021714034080e810b015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 816521906 1250 816520656 816520721
    0x6010803190c0f060b01050d0507020a03110f070e070e1201061a0f120408160c1503200c010f050a0b0f090c0706020c070f0807080610180e0c151309 65
    0x1198414100503003041400001c140489d001181d05900680c415400340c8141608200007035400c2101d1005040c0205141c1501a80c48029200f03070a5810400c0c0c0c00101e0f240c1c89100303540c000340d00c000d0844083c80280c41d0018081d010600841e00070902c1c0c4420511a2060981196207d01c8164a82810300940da004c42c4283e6100900a42d00c1c004100035040451606a0072076041500c40e00040d180c150600d4515840e0a19540c440e01c01e1500d0b014824407190840c00845010030906482e4039590180d95040d24050b0921441c03c00d1141e0904041c03080d04131f21600080d8440348261440310078440703400100900601c0640e4a1420100100300020110f14039070001e007d000c41000c02c960206559407102001401c0603445142546c001400a03c60751a0900c4543c0e000381c440d9001c1071041b424003064865429070f490709016030a0303840b0000c1414030400e0061480d0010000d140c210517840310b6403128a0b40d80024440d21a203180400046a03841c0e041c420200b5403450b0300f036800008011903114150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 816523156 1250 816521906 816521921
    0x2606060603060a17070306050108070806011202061b1903080a1b080a15030b070206180601050a0509190c09060306050108090a020607080f040b130602010e0a080a090806010803190c0f06 81
    0x1000d0081034001b2000c00c03030502810b402050450000c002d000d00d890505802c2c44010f0300080d20802d4541c0a1070096680c01c4207503200e808042c5100c0c0d00c135410702c04210b45000300804130403007000e08011200060607000305405206a03030550003401b110841d08501090b848030240e00c1004620b1110108010240e95401007072402c100b00c0840701e10713503102e031510383c05903508603041001a4022410401c01c1d0000310321000030005454002d000c154104000a400e41c1560b00a407405a02a500050080307038032801035a08032004108104006e2440c1007006003100701600407100403a040007000100340d481445024400c04020000d411124026070810403150b11160040d42c08020502207100034a9007980240000c104852030141e441c02d0340400004041615400a815a490310350035034024140421901c3e0029880851290780c0c1c1e0700400c040d10044025000030619100d074900200d540f100c0000101002c2030303442c09210450200e06011034004607540001004458055601030004d040c0f90010303032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 816524406 1250 816523156 816523199
    0xc121803030516061503171c020a05160b1812030c220602011410030b070804020301231b0c03251e0213051308132606060603060a 57
    0x2144450340c1c0341d050648500342171380c5100035980311080003048940b810f00700229200c544207500b800802d40c1c06000c1c0d505442d801c0e804141d000145003038220b1065049910300b800e09076114042050505214016040803600121442450140304048070000a4402000c03000422801e00d9130703440864030700042d0007504500d40b000065855108080b0040100900030b0708050380001074100546580501d03100340a0208071040c1e040000c240040703490143c01e070381c1c442520700348107205840340c1c0301007801481202c0c181d80c1c0d045238000340502410010b484240c02801646505030f41110b05030f1003140903100c1c3e601d254156500801c1284407607007201c88041380c01e1051581c1000d4460207610b6400c2d01d03c15420081c4454401141710004516001c0f407000d0303c0c1e2025100400041c03401070401c043d00301c40007401501d4260040b400aa5440002c40998050505882880c05030702000000400e501d000080c010207500a0900082071400c0035019244906001019505414078144260500114200d44013 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 816525656 1250 816524406 816524437
    0x109140c031e0f01020c0607140405010e01032d0f14010e0105090405011b0e01031a2107171507021204030803370b0f0a03060225030c1218030305 64
    0x1807403a03d080c4003900200821901801c035038585060700034861207070b810000c060f805060000f8002c99911050002d1506c9080c2800240c4504c1c50b00421160844680c8003001d50249018002c00e07d034240e0401581c044c1540d80074089210001d0001d10440c1b8240580c00d4610711540c010402c514140705d4450b00980580000180440c040307031105040031b100e42c010400b017030f802080088556850b00ca000640c0080d54901c0074195680c43c0080c44e884043c0c43c0c0141c12090b070009450f046202400b5030b1000f415000c0e0f44256004904072015100c03071090090a00c00c810381c40015114600202d400044802010005031409040d6034038580c040c0c00140c010031918681c2c104130013900c41a82d01d20114062a4040d0542d1941140f080c0410b03601c0c440841e5009da008a819134140c0c1d10b84c80e15035015240d1203072015032030740b42168a68098101d801918203038450548021802d141d0072200e0084018001c941442100d820307100140c4240d5030025000f101e1044d900405c0000c05c1c0710b40060b068410504600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 816526906 1250 816525656 816525673
    0xb0306060d1b03050604110402070c05060f0f04090606080f01240306030204180b090d02060604020d1e02070501180506131407030b15030c06070809010905120109140c031e 75
    0x44010b44000c540084403994445400d100c14400052412501064101c3d0190b140c03558076a01e03203075800668815907010780c1005c685d100142200c4404e80d020003502107800c648030790351a4a928007a1800c1d10501d00400c040c1008251408000030096040e110710300526108408441c404100b245181003040003003555034100800107075a1801200e90f0303402083c0c41034440000c103041113009010054400d0f0003690000025120064001c80c8055001001700d070700585409407a15640302600076021003504c844e401602c066060400756004e880e605004030001c01811605240705035060203900c90142095005038002540c084084107100343c00c074441d00e065901174612441040c40c16400360012106290140c0c2000000682c035154007030740c0c0701d00310010b00080c40b844000c030b0018400c83da0b0240100c0d000107403581b0142d014030344960003040081d00040d00c400d80070003080c2c02040940000c68080510001002840000043c0301003800001401340800040c202584044808c040034207140c0b90103130110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 816528156 1250 816526906 816526943
    0x2070b0706060e0a090303050903030603070b0d0e0708030c0f0a0b040b0406061703120a0903050a0c140709020913050c030c0c07031a09070b0c0714030a050d020309130b0306060d 78
    0x1441400382d21031184c0451461510711340902580c50040c0b00080690045c400c1014503035001480904032401c0390390700ca03500c0e0406041040507100c0000401c50364440d9040009490400000070412141c180058031200075031240c12a4035103100c0000075000d500e50802240104202c00e10080c2c00c50f01c119400229190743d584601c505a00c0c000d01d0f05901d4101241d210000260360042c04e0340000d0100c402c00900d80d1656001d403450081c5500c160800aa4092070030030000080c100750181080e41d01220403180e42e642c641406540145e801c14020f1301034002200d210b03610b13401f0b07150241444140d21800d43d41e61075041101600484150212803048d518004003003248080341548100d10454148034514000310001e24040c8142d01c41840c402003000090740c0700c80d000c9103034015221051141c800070a10341d000245003104080c1e0186c03460090b8a400082c00d034000005102c1c581341034465016105136042e00208403900758280d290142c00c10344c0012003030314142201c100b00341d106800c80c0a40c3e01c1d400c007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 816529406 1250 816528156 816528179
    0x3110105091305040b1906080613141f060603020307020619061d040506132d05160e013206040b13050301050a02030c1812030f030609060f0102070b070606 68
    0x2134090344c4c2e50039500d06010300d10040807054113415903240d1080c00103902c0e08081c250307503520050100400e138644c000d1120400100e00c910701c1e80c0710f01d200b00716011030001c000403000d0748081548c581e245601e03005000690a0181c02500d01c0381c0c000340c01400203595210342440440481821000b00d0a84e694400308d0301c0f1031151042200d980302003c000440303103401c0c0f074900d1410344081d00000500c01030a04010002d01100545641d6607081040c1c0e031300862541e240e601014180c000001d0040c05003000d05c80b0184030500d01c40b4100c807015554440581d82e80d0040d020401401140072105414103145c503004160413511035038107418082c0229180076176810500b030007900400f15000c4503041c00300782088075103003d00070705401c400600c03021480c0d81040f070416642c9118241448416602c48000d030603140d55510b024290210b0b0210542c2c0c0c0c3c0d82d1540c40030f020b09602c100c640c01d108400b140003085540c01c0c01c1402900505040c1c0041050030308104c80800e568002d00070469401c0d4841c280881c0b40c07000038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 816530656 1250 816529406 816529411
    0x2010e0d0203090f040e030f0705030d05070503060a150516080405060406090e2d1527010e07051e07120306030203010c0806090703020d0207020d0c0608070903110105091305 76
    0x59010b075456145100070000074000c2194180d2085040c1480400b1081c4048211a49100390189403565040240b81003410750180780b44d00081f4a250804000780c48da00a0011445298100c40c224880d0b91102206801d5209251400300050750030302040c10800344000000c2800741c000d03415a0f0825694030001441603001d508408000340841c5000c0062090b203110745078104141d45c109401009100c04d00d00d0000c92542d1300c04040c0254800482c0048110102202000602400001c02074210641c4540d820780c409008600006140c400082c0034902c00d28401c1c054109540e5503850f00c6450a601410303000f428050280d100010000c2e013000556000301c0301954403240d10003240b40c91031401090f0071100042c080d441800042d20400001d0358640d000c440d4449528207005807240003c502440087c011054000e4129054900640074851811442006c84040e680c40d00c1c09650b501070101c03107070300c07061000500030f10b0300421004540d80980302810a8120203030cc0f4009646440900a05070b540a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 816531906 1250 816530656 816530683
    0xb0103080901020714010507151401090b0f01020c0f040903021e060a0f0c0e1c020607050601031403070c1202221a10020307061a1801090522030f02010e 67
    0x59000d920b503018032000008001a03141c4102404018001a0036171080790002002110001550803101c44603074412013000d18503409410352581c54140c4a070052030b800044520903900141c01203c2580b0001c2c9007541c19030040e160381850b0011000380000b401480408030b0035070180000c100e1746030600c2c0956660241000001304128100300c0440801c942c0304003100045c880c01d2991603140d1a0300800c20360003110f4207903140e4006001c00c125100b64002c1d41d52000790312904c002007000c2403003400105241a00c0c050303206602102c1070000c100d0b40c4d9108401c13000300310411403281017000b00c0d0802108484680081c102c0d0394107075020040c21501505d4403504203101640c0c1c00c1c8402180700e000040360100b190039140700c0845000640069528000c10300c0080060b500c5925101c150440342018042d81031003c0c2c1120240b204c41c41800c40c41240900450350310a03e40400100e26000c40c00114900d00b01004043c00c00c0401920202d448001c0703032500e0b506664880017582c00380780081280b445108030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 816533156 1250 816531906 816531923
    0x7060e030304120f0305060319081e12070509010903061104030221070609080703150b031504050d080f0a0b150d09050606032b02150103030305011d0c040603020708070b0103 76
    0x80041c0184c58079200ca0010420149040100303c4030751800602d034135010204082449181c112441c0c100d103281700da88180030854900c0f60003110103101250151140c2480001040d0040e5128001111503000381c86000740044d140c207c042000c41e06035031046849203800c00c1800d1509071a500030a081c00d85001d031081c400340c0402285210250148070203405000c00e881e154188d14581003d042d40c4021900015202826000c00f40036861400d80c010584214080c1c20342d0744845503040034040c0340c4011101629180209503070f010300390744541d020b50320030204064203035070320b489c2d01d0107002c010440a50038030b40100d0030800d2805036401307181c080c100601d500343c0c010480034224a4500d0a2020141c1814000c0d030210503030f422140d5030108116082d101c100389a11040000e041c080f450511030000300c001074016071001109259140e04040c3c16220000c425045042440410106184044a840100581c207010910400e4404e8000b05010f40c01442510f00717198040d1500421210280d01c1102c070400f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 816534406 1250 816533156 816533183
    0x6071b0608060906030f120d48090e040503070b010b0310052d150d0b0405090c01020703030806190b19020a201f02070501030605101407060e030304 65
    0x3400e11007484d884003082c3c0c0504011403400d407a4075540d00840c1c0c0c4c80304c4140e40c042000230b2448070b90f50200c0c00280000d0928011482c0c01c1030030b0f1220506c192400044c2900001c219401c0d49520080c20350040650350f66a00d40700d00e062803120341d184000c0d10499190100300b182c24003150401c00713200e0180c40c207240420342c1c9041001541040942d9580301a01940403c00a000b054004541020304041d00c0c03600703080c5800380140050040380e140700c40890f141a0218114043c1d03901644802c0003100e0a076010013a41c0c4440c0c14031541c40d101850400d0059101d8a02400001c2c440c01c7c2840e04044c02800045c161101003d2101d90350303c281d0846140312602180a601c3c00c0e00249185e200321469001414884c1c03c0342e1141000301000c0c1500e102e0403070030451011040d403101004503900c0c0404c000303005503034104128025100c000c1446418002814410042014075090f40d07008904000750316001d03600d14200b03480c0c00031340d080124155046580c4000c440311020040c001184121701c00c0e040c500401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 816535656 1250 816534406 816534409
    0x40c08010b01030b06030114061e071a06060720030106140a0e040c0306021c06080f060109061d040f02030f0303010f0e0103030c03111c0f020f0c06040506071b060806 73
    0x58034041c0a25040600701140070140741c855008580c1076031a006500c021007112400494054403d0745100002003034219210501c851035203000d412464822501c003290b03901500e0400d12441016210545d01c0102004240300080c9906408603441d00c9082105a502c2c40c8100040c3c2142c20551010302040c0240e00d4100b40352401c00400c101500c0307103490380000c60804d41c403881c400340c10303c1c080105400d50004d40301c1410480030350440c1070a29a0030b030905c00c0d242c030b480700e0b2a00c51242200c8440148113010020805035400d00599040c0e4210b030305240e0704c4104150000e4100d02d4098802c0d503030062040302c00000760720b003070121a0700c00d08224000d540e2549080d01000300c542c05c0da4424602038a5620040c40041d0b44030a41c603502e41e8161a14445a8948010080c2070503030001c1201e0001000400b00891141c100000040c800b14036001c0e611001038172289603480b4510343c901030340c4c000c5041100b0b001920b0000c01801603140103950140e005485900c812109144540103800840ca1701030410049 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 816536906 1250 816535656 816535661
    0xf110a1805030303091f02130b0903010f05060f010e010908060c0301060f020a030909020702060d0608100f020721021c03060504110c0a06050a0f09080c010606090608010b130e040c0801 81
    0xa0000b0b078020b41c61482d002410715101d040c000c1600382030b4a2510b250281c0406141c055880342005000c48241d040c0e03541e405400160311518240d8044d5003461005440003c1034030a01d4070403040903001c001d2140c042c500440341d0202e002d81d29410f00811030350200341824101302061140c80014912a900c0d410f245001d803031180d00e03000d440110341c0b2001c0c8950000e58050301490468000c00d80140e00c031307407170380c4005102d600610401016940c9081c07400580c1c3e40c00041d020041002c0c2c80010800542a01c0c1510103074828a04050701441c60740301507201116400c446048203146d5031055900c200000c86a048600322142d50f9000040d884003401c1c4100d00e440e205460101c505500203d141013120091b080d181d0004002c041e100583e650000b4139200800e4101c0d00000076403000400c520b94103454030301055081b403030581d54a9807034400c0100b2050b0040002c9000e8610036140c06d0410782c6003d002071082d0b44060700b140d101c101007000010b4051900b490980c0901d10804044400754105850b40b400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 816538156 1250 816536906 816536909
    0x10b01020c0306041a0c0f1815040803040b03060301110409091e0b0a0c09050a080102131205030d020d140106020f0f0606010f050d2d050a1e0f110a18 66
    0xb1a0b00f003501440f000881117810761030940404e15100c2032075a00c3d8807541503140a001080c59100400040e00b40c8015041d10b12080190070440b0f03400740603161105280d4890055024a1006910400003440b0078641c0300065031317000c8401800816044c05944c0a009150000e07408040301c1a107450090b030400010407103002c00141707811451060340e80203807075100e41105c0c054001c0c1ca061342d44071013080e50244100542400381001030000e00c1e80c45e903140103c50003588103510b0f6030056504a400400e083d07610b5542042c04982003001541440d240b2a0031500a5021304049800c2c1a074501100d0102a00c2100da6070081c102d0f500540100c400c058940d03800c010802002c4911504a10100f001d60f13a0000071080500905142c003585031101e11054200410b4407140d0480107404042e80d03006d02c1c008612150382c0d00c0340014014405504c1d00c065120694803a404d020101620b0340c3c2c03020380c501101d5888104174490381c21011482820052081040381c0c440701c0801c00040c40181f000349100a101c20400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 816539406 1250 816538156 816538159
    0x4050c1f020c060f0301060c050a0203060718090b150d0906060b07020103050609041e0201030e07090504030f0c0f080c0a0c26070b07031107170706080f0f0a0506061b010b01020c 78
    0x61903d1800c4c1d40a96103031205002c0c4005114212840c60b0a0000401500c403903564003a007100d0301410403403005040c00300384410101008580003170200e62010b04d0300454a250101900d0700039042d07160555944035030410000d1a1045588180300c02c080b136858080c1030014000d515810b695003019000041c1039440003400d59020781c84200500c00050f00e150a842c001c24541480d810012110f480101c007d07082c2c0520011b0948104600482c00003a190b12950055100c2c1e19901e80500c8414010380e445400400082c0114504001e0f280104008200601c2c1e895080820f83c0e10012044d55000410109504034898100641c2c02c03586465043c07085d40e840d69000309006001062401035080964411305078000c0070049062080c2c82c00b0b6004008000180c4a0100640301c045840556903554000d2071041e00c00040a2201241501440c01d040c6801a48498030382c802d10782e11400988040c0901400707142e000f401c00c002c106058a02440311a00000342c410011580503240800245401442503032107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 816540656 1250 816539406 816539419
    0xa15050610051c050718030c08071505030c0a050f030708010e0903040302030a02040b0102071d06100f05070f0201050903032101060e0303120405010b09091609150b0304050c1f020c 79
    0x300c40d1590000a076804000d1200030128459807a040102c403904012813201c51b1005e09203c1c080200811014260141d4042030221280300f5907900300030050010004400300031850803c0460b08200940c001407000f0390250030000d2900004001c82111507000b00c42c51800190420010b010403e14203458a40151001d0001e508040c103607000241c4407212000700034071a43e6101c0c0e4410069000f03000e00001800303140e10111403030607400495440014125501445201c201010810b141c2c06070800c55010a000e50341e0f00d041600c580c0e10803145600100050341071240a02044140355420002024107074030040c001015002410412103100006070800341c181303d15980004102e8030008243c030481c0d50032500c0052a9222400e0590040404100341900728034414100003d030200002c02c0f115001581000b0100e00d0b91b80c10160301281d2203100c0328131505e09000d0b070400140c1d030320401558103d400755059801c102002c10006200e0b0580c11000c25071a1001000c0c052850b40500c03400b02c0d540070980d0030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 816541906 1250 816540656 816540667
    0x210203090a080d0509040b0d060c120c020a0f11040f15080f30130b07230c0607060b060c010b1504050607080f070615151418030a1505061005 62
    0x1501c10b008542115008a07611000180c10795244030148c88015080b203001c00c002101010014004020780c03409900c5c940c2061031000c1107510002c3c0c0b2140868110a241e043d4424503540e02c484062031204499200b0340300c0c08100c83e2100c2510070300203515a00a42c1c96004c070b1400c011107090140725840c22001c0d0700000d41080134852280c038689544504259034400f840321030904d405542c0650b00015085c082d070b03d50041003812841000f0030500380240d04000e88540c0c0d6403210300c100c0301000401181d5802055a1003800c0c10080f01030480c161143d0b901151102c0b010021403400e410040383c0c0300c0c440e91aa83c84480d0b07410b0403194003070fa5003610b04080c1d02e01400d01011424500c17072081c0003440e52400160000c0040d00750429621580ea20450520400a070b00761070b40240030050050421100310350400c1c1030b031140100c2c2449a00300d000224a0300307007444110490501c880c91a0341a805010388181c3c0000250783d40c2021a0501d0b2107000002e05040100500c055900e44403d2041405004c020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 816543156 1250 816541906 816541933
    0x21605040e0613051501090b0a0b0a1e0219050d030c0215010303050a2105060a05010504080a06020d060e130506010f1809060b0d0503030109050c0a050a0804210203090a08 75
    0x14a150700807088514583c204803107281440c0382000c1c1550510f540d0411100100b4500384503003010420401c1243d02010650b200c3c03014255a1065200c40c1010456500c0d0f110a190244d0207540d031118a41d006a50b04d180c0852034a2804034107400045078540c01c4034003840002505441904000c0d01244028003002d140c202c1c0000b8800810300024080c4070001c103200c0d400600c00d210406600801412200800042c5106000a0101915124414039110700041855441346e000e035001c031a81000200343c3c0304407907190400250301a2403114138082c0c55020210b4506968407019008211842e06180c0d00c0f0460b0802c91709024040e0810182c01e02c8800e0200a4081c03900c660b0001075014640000d245415481c100e402080c0003501a5080040c00e0141030a225000c4081c604031403030900e081c40346942e06034050100f131142c2c1c1040e1000c01c400740480e18102d807280c20714079800b070f01c500c003411001c030080d10140c00b000501d240d00c040140c0c000a000c103000c2c1001d00b55a0001e0441c1001001141030418 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 816544406 1250 816543156 816543163
    0x306050423220b1b0406020c0307140d082505061909030806100e09090c0306010b040608180c030a08091c031d0a1d040309440d021605040e 61
    0x89010b4030155985001c00d94118201d048001e4007254085481c0c2d1759035480c01c01039206c000700314086100e400b40c060b0009824000d241006041c0e080188a0340107902582d444600d13580000880552400480014080b211031281856403c540a10014840b80c94007011524849030051402c84055041016800010b5001052135401030421202d41c140740804041c1161040702c044201640070305120240800a540882c640041c090141c05075070103681c070b640340c2d00a94840c070b20560000403200c10025000c42d890740201a408440d900c01d46c4d0140d5800c0d0b00007450402500d034142d540650004a2501a2a10503010100071021344100c415100080d14042c0c65445810a210100900c1e410541d250350b0311000888094800b0315406481c00e00451840103890400300da01700c01080903510040340c20480031510910b04640d290603869840b80400b24040440c60f030420712495420380301d05050940505201192140d845c9078002c024009110070781c4191000f0b150302c020300036840c2980c411401403012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 816545656 1250 816544406 816544471
    0x1a0f1003030503070c02030a020301060605030a0e12030103020d050a0546030e0d0803090a05010501060903080405041e181e320d0203090a090614010f0306050423 71
    0x1400e280400e00e17403d0002c20f05040410500030b6140d4a4600040340e4590004065070040c3c0482c04208940c070900701d40309541d260141c0903010078a00038801000185000100316181c10f20410540311b4030200c2d5a641442d20701c2003901020320000205521001210011941c0549841125222444005040315105106403440e000d01008080403c440040d101c58a100280f6a44003403515920319001011a4441441440440395035003800300004419110703000800039640c01c683c00b1031826260100b0080144147d0052000110f10f4100740c09403881148140d4091040b0a030071403c01d807076685818908514111018110040ca440f5640041031000340e4204081c050480e0a001c401c0000000c080380300300f041110b00340c03442800c2641640c80e0303011028003680c04003a1540f00c1401c2d2034201d0101501c2890054600800d09038540005541c0b00740f1708060194400e003000641291a04d01050944189416604038040504500c030f010040303414200da03000c00104a25241484083d043d91081c0c0c004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 816546762 1106 816545656 816545671
    0x80414060105031c090e010312032d09020d05191208041205030a060f090614040e070611011e14071805010311071a0f1003030503 57
    0x11954142c40004028100d00807480e50040400741c0e9840d903941c100902030000040d122143c2d2446030180d80110f11202c42e400c02000081c4c10780b2412001641d01c51120b4005041030081e9400600c2c41100d1342d540418043d499000088104020500240c01401510410a000c09a8110b1403108500c504c1c4113010105401c041030340c400c80308840c09030241c0c0b02840c85090852040b0b000350340c022405140010b0141c4c5615080108201c1c2d83c011109080d5140810302001501d2200141004001c40b030034005220300c0d40110f40c841c440f900c60340d0140b213007010642060050a4221031041e0700c1d0380c200c80f6548074664160101801b51344099811000c561000b05580c1c80c428082001451503c2c049003e01918000c0110001c0072165000c800144092015000080e41d42c410313045480c00e010102141343c10131500c1c0103e4540094000844130759200e81c1040002d8000040e654042203 = true := by decide +kernel

theorem cover : BRFrame.Cov 816366906 816546762 := by
  have h0 := BRFrame.cov_init 816366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 816366906 ≤ n) (h2 : n < 816546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
