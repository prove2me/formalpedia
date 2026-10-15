-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4410
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:31:45.686594+00:00
-- url     : https://prove2.me/submissions/82943ff8-1593-4b29-8346-d8ae36f3695c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 792985611 ≤ n < 793165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 792986861 1250 792985611 792985649
    0xb1f0507150b0d0f06021317010501060309020f06030601122903060103080712050c0d050702090f040b01210b090705270708060d0f06021c02040b03011505130807 71
    0x2080742d5002009a811045049454011910f20b6404020304c0c0c1c4551005803405104d0700c0f80030b01060380c541c03000d0300d40c489403c0c6120000b40c00303004040c00b420240c0340c01c008484d51900003483c44004030f11041d000f402c0c000302091590f40300c1d04910b48844004002031001d03c80350a84a0840f00510006501c1d0307001d004800c1300c06150125980b4101d03a040307580241071801c030b902d4505008880302232110600c281008442e04184052110000001603920b6507a04d48010380103101c042030000306120f203000d071050304000c000ba01590a007030554000c86140c6807070402c201a00c00c00042841c02c0600503e01c2c0310100110103a00046000a40d0b0050721a00c0c15110348100304642011070400030328204840500203101d4500c90401164420002005600c1d90b80080d25000001841060140c0d1880d0b00091405080c10306203004010110000404624062030700c207444bc8140818001c405c048002948450f501700c0c495030507160300c10041c0c2d40e000300303065956003007681c0c40c1c1c01446144807404115400f20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 792988111 1250 792986861 792986903
    0x201020c03010c05130b1e22240e031f020f040e09010b030d021005190f1d07030b040f1a0a0f0b09040f0f08040b0a051b031306030b1f0507 61
    0x549000390310791f61814001d01c4120003456940043c84a02042e00d40201e20401c0f9414241c2c4800090900d0401240e11604040030a0b000080c1101404144000c00c090082c041d100014841d00c800028499454a076000b400d51001034400c81c00307031115441010a02003104121921424007170f6400038000c100c4400c864043c50b48604242468a0250300140d0440040e2103070368202b01d130701450080e840c94142a480004100b19121072001e020116610044c141c600c0b51442c00200c0342e00c4010004154440c42c60342c6048544900900c014610034260940804002d0940e0908924150b91840b440003441d01d111004014003492101800c11420040410024145001e0150099421078440c4a0b1b0700a10b480da609045c82c81042204c0004007000000341240c5008058803d101d5144c0d5240d980b06140b03140b45018511071400f50980d83c004200e41c02000c280406000d0495495060104034044c0190020b142013a9002c080e45103009190200e031645948200100021441101c00b40b90200c407040c898 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 792989361 1250 792988111 792988117
    0x4050403051801120507030b0a05241b030a0c0516140f190f03030e0a060504180b030601060801031406010501020c120715020a0201390201020c03010c05130b 69
    0x16020920410080004034540a0001441c24041c140810703418100e0b240e920443d6001c1b07a90000181e641e9000d401c0919080b00034400810041310309655107641c440240009003641d10000070b40d004005681002e8004034011a15407c041e8001c2c0c0e5203d0724191300c00b034032002910000301c600f8000c0c404030008a81e0602501c006481400b0203006110311080184050f0041c0040c01c0c03644103501e09844003d03401300c3c001d1400074189080303100703480514501c0c01418a54000c0b41051050210790800c1c41110303441010b80e400c079204850032002010120f00840b000b441e96280c81905030141a001081d92504008400d0480c2e1040340d050719044002048607807529028028980160400840344c13000d40f41000400303c14508460942c0c0501da582c5090503c0545441c40c503601682000c40440709541c0c10200c912120301154940b0002020411b40c8031480d1036840f601450903400d600c10b1070055900c00c004110400902030000c10028400707840242c042d805c841203a04104c524030502040100e561019 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 792990611 1250 792989361 792989363
    0x2031f0608070801110d020f0d1a040c05030c0d05100906060201020a120903020c0f15070f020f09010311090a140702010609060603020a090b0706090f1415090d08090c0a17010605040504 81
    0x40030708201105101c040070b94001a0006400602800008000050351080ad10107180020000100c8041901031105480c0180458005d101e018801c20914621100407655502c035400e01c0081c0075038981400815480c80740c3c200082e143d00d80840030800070b0301503000709800c203159103c44103000300c440c46c884140c900b04440140140c000760481e001d9810704034002c14200700b0040013114030450480882426404c00d4030700352403003800c03e203543c0250b081040080c44840c5094500400030742c1103841d05500c040c40611002c2c041d020160004400400903445001088070315900404242002c5e00001e01030700c0c450107284401c2d4507020b0f000483d2402407003213a21001d003544449104620703004034554180c0003100e0681d40c0b0358a0b24100b4000034285109014680c5c45180e010079141c405801301e86c5407405c0f024002c0320190500301440440c00001030003084002442c90311000541d501803690b800c00035100000c6070002d02141e400b080340c20b0142c1101c10792000c51802084007a5688040000b5070300140c034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 792991861 1250 792990611 792990641
    0x408180609130506012c0406140307060e01020a0f0308040201090501111002030c0d111c02091507050f070b0909090c010e060d02070803070806030609060106140702031f0608070801 79
    0x2030300710b540c440356003060b5401003050508a00d440d511000c03c0200803500f0403a80030700c3d031101484540d1481c1500c42c8001810107005224000c062050110380c1c0c88903103010b40001d00c02d103084041c20a138402c110464000343e1100c100401d5982e14540030b002c020b401d035003c03408904541c0c80466194825031500350024a440c00500d000704010701560025400540b03e811000c40411581e0024400c6008540c0d031082c1070099580e440c03110f1960180d02d014550155180d10b80100f00d6000146c0d44c860718240c00a04481c80255280554035127286460f000c4861001280560100040c600a821000d842121425904440d40359100302010751a4428403507020f0100b00c00c95030051007401c108000c0c00309035140302c00061070003620382c6803090f16401c1199010300007004002003102500342844202d800c46100b0000701015414010082c1221164100710071081c040400c2d90030956130204030300300c8240e107442c160301c5119140e0010040134240d6402585224826607100088100c0144244c00d111a8186 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 792993111 1250 792991861 792991879
    0x409060e1602071e030605011e060905030a06020a03020903010f0b030c030a0b070c0804031e060c021906020f04030204020304150b030d020316140f16060e0904060c0c05060408180609 80
    0x1d44603e240c040d404142400811444c5404000030b103d03032103428003a110390740354407081c503500242c8000c800e001c0741c000701c08104680c0420032541d01c001600c0d6414591050000d80c840c510140c1c114000d0085200321581582082c41c0070080d003580340c3c00141200e00036025070717070701840380000c1c199605141c1300c005200003400c00025010501c40d41c0d0b04003070140719200f158034042c5d90785c80344410b020040641400e0f0102c5c0b243c005080141a1042d00030403c502e001416001c420042c00c41a26200600c014048d140c0000e41c074100b0210f001c04072009150f0041c41151030b03040c2810049001030440d000a100366103001090441b515000034040d46000b880ea0013145000110203207070503030882c40e480803a1070703140eaa0005428500240500481e110181d8018807501c11711628030441c84402c5d074490b105000704190741420300c0d143d4410859000780c0008010036042e070114411140e4507980280544036008100500041001d40e00c020318641812905050701e25800b00c04214840c8100501d00d64840d03e02c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 792994361 1250 792993111 792993119
    0x306090204030b13021f03060e1605030a050411030f010209040f0902030d0c29060a06090503030702011b120504030507052b03030b030d030207051b0d1502040b0409060e160207 77
    0x414040000c248042c1c059042c6041c4006162006c0d03c3c0e8001c0f14010940b1043d044c04080b44100c6860381c4000d0000031a45184188100038199200c0602426801d41e1540300280501040f0300854040e05000390490b02011002100d00b03000b0f42118005a20490a10b066040b058010b40503140f0b0164000b40604041d4100344001c2d104580c9070907046880303d422540684030000c0b181020410001515001209458614100115001e04c1d81200301071103141c4106100c02d88001094914056080c01c1060314004003d0070844100003914000b000010000601002c40f603009020303100701ea20500440344516201c90030441c0121980800003414544258090701c4141032082c4e066039a80207007000100c246400300401c0c10b101d031fa0b010400100b60000380c00410800308001c5d06000c034040c2c00400020089042c0000da014200d6078001e0100d044105190700b09000301d504075001030480b800829901c0d5581e48456028141a21a0111b50b45086000038003210038203c061011107003d0f409050750a0078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 792995611 1250 792994361 792994381
    0xc08010e1008120909130b1303050408030d1d010216150216120f1704230607121a0d142104030606060c052116120306090204030b 57
    0xa100c004054420000002e084800b48540d4142c3d01e000c986580c1d680a158051202e41003024003051440c11070316443c1c8000c0344940c0c106a8110347c2c4030804c054884160304007118940140d42168040d03000002c0c1d1740406120340e03441400a00c10f80c40c0b01e20240210029031608034011032040400c00b0704003a0441c00061840b00868440240d403030300050910803c0c40312594400c002c40350864200d00109140c540d40d5410000c038008890103403030000c481d0650300403042c00c00000035000406078540c08503000b01d48808081d02c003042020b03410407100a86003588004211201405901240340e2900728801d0741e4190a5040c54031030203014180200d11010b5a5034504900070424007000203020b0a07040e9410410701c0488406600c42d04108030392581c0c21801c100080351000c6c0c2c0400144240c490298000490102d641c07107110340040c41460514001412400b82d910078103429103164605000c41d407042000d1000200101c0005540030045a5255040e104c00c034403450102515400054001400e0080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 792996861 1250 792995611 792995639
    0x209090601051008100e190218040f181104060806040305030403080c0f1608040b0a0c061406100f0c0803090f010605040c0c0b041a0f070e03060402060306041518020c0c03010c0801 79
    0x758000e4a40340c5410400e00002320782110b04140d003a443e60340400303840c518141c000c040070105500030400c43c5070401c1094440c82d580203040101030007106402d21003250340d194440307001030100e4002d40f422450986001030407a44221030450109004401043e1622016400e503184a102040c000780381158560403040700000841049841c05c07000c010114044c21200c01410b01020540c58260018106280140c2070310701c1e04805104d881c180324100316159484901503040c005440c202544408120b040484454400401c0900410800400d00c5152100019074a42d06003666000b00700b40c584400030442540c80e24404200014901c061640109212040f4643c11500c2140c004502156407411003002240843c2c41010204854041218054110010a4020004070050009480c0690004500703020141425006039647c20089010b044141c60040c040c0801d00c626141601c90f1040c074a01035440a000700e15a402014002d11075400c050254410340350151b1247c03c1c10360300700728074220b84817 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 792998111 1250 792996861 792996871
    0x80f070801120212010c05040504060806040222090804060c11032b090f0303020106180209210a1b080c2d030a060f0515121209030a0209090601051008100e 68
    0x203440d5280c614003941309114902c5000019128503890b01c1c13a000c1000308481e42c0f5445280b4603045081000016542c013004007240c44400d5413400840c00d603501030760005084000c0001e091100000b0085030b040e4000c605411203074860700c60018540521000d054880c11b1084034030f182800403054040d904d6811060242d0032144a00d042001d49582c0e4030181a082a80d91041e4050b0755a0f01090100d84013061048209aa1051055150041220220346440381039404400008505516100c2c000c1052200405854100a0402d0b0348514800c80704c905504030b1041c7c03080742c0304200942c50305040889408142d04846041d01a91004400300c091701000c00418096041c00303810390f8003002561038490f030f104024816070000ba0528109074051a0340b6400f0002c0341c42008800326540050100090403812720300b08464450b102c08840021070b14001c031040c0001d41c0407510800300406d403500020f92904840b021110901c1c40c6107200000d556403030b41545d510f0baa0900c404414040c3d1070380510303019003003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 792999361 1250 792998111 792998119
    0x4260a03051b0115030506090706020304140f102f03030f0a1509020705011409030a0f0201021c1b030b06030f070c02040c11060a0c0c030e06090a06050307080f0708011202 75
    0x2e1001020f00b1520b51300c0ca10010410120024030900ca01081296440003e210041ca800b82c18194041d64034042d604c0b030980d801300e1203800e10b4041d40b21003800c00c8c00c0e10b401410751085280c5009014046403000720501e806200841413411070341c1d0b607445a03070200c900c820014501d141c6070f02e001e1845000e13004154010f03040d1600c1c2400802c8940300711001c020b208841005880c0c1c0ca65241072800d56107001e01540c46031203e02e0034881d48400c0403027202c01341d50060418031980032041300264064094071380d02c04180c5005d05540b984141c40c80e0000d4815031650f041d180070381040e0070300c16812120b002e070312503070401020300000324002440700489401c00300d90706100100034408d500042c20313111018240320000b1010000d09202c6281044801c4c1c0010300e40030284480403100303000804241400d1006400c01180005402150312401d0031520080005000f1100594641e503015180f944146c41000c002802100011840320840e1000390080503035640f02d40961346000071103202e01c1e04c403c00c1680d02c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 793000611 1250 792999361 792999397
    0x612200406080a050f153c01110105010b03011517130201170f1b040f17070f030206030a0c020c032d0106080c061e0f04260a0305 57
    0x2124114602a00051039142d4039626203241c560034050588801400c00d03848070340f202043c0310801d0545400c0c1011544240c070640850740d1148205120500b09442100c03141034030348280354000c1010150010b590000381ca90214841ca03210b0510300b2168248504458103c003800180440b1107001c50076660701d02c00d40b800303650201c070790301380ac00250409956102451b0f481e03c100c142156000030307049020b11030402200d0b20518198100100c1598001d00d010250100c4898030044949040b00b524050402296208029510b0709540e100c0f40031203202d250154410072400140080d508941360042e658050100c034159254849200050100d00720800c095001d81011103860b61400c00c060613100c1200218000300002d92415007101c102c0754000901c5c0c0b641001c00500c52180000781ea41c040d0701080d5071003070351082400ca6042c0c0b80398806c990710091083c00103050400541080c080c00981d8000e030903014046040705000b20940c42d510010f0301650300031030a400003003800740d8044e02d04880040a0505 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 793001861 1250 793000611 793000661
    0x30312010e0604060503030a121805120408010e0604120509040f0e150a09030206060d031814040506011e0804210206010905060301060f1e03140a02030c0a0612 70
    0x204045098020210a01c6410100038407490a8002c1d0402040c2c20780c0a90b25001c0200c400420149819500c5044145c0711217440c200141d003034440c0740085800c502501c0c0b2036040030059612541c410b01c1922015801c10058560114000c22054020740c0d1000001c250140210000d0300d07940c2084050341e038010740d030300701901d140035150044044008441025005001e405508100461006004001524505180d42000980000d5281d421880480d54051110440d282c1216104a400c848040c00e00c0b110400241014510b4840900040c0c200c5040c0481da9505004469200074140e000c410310f0204e60800d0349443c0614010b941060184404102e20807050701015a002c005400000060f80034200400001a2910030307d6003003c070031002400030300e2070001680c1903a0a1401482d03400080e14a581e1184903459590784029540b240308001c4805000701a9034894251f04403d0b402030040c00b00c8100d580c0342650b62501030710640e07220412990410708810004001c4141344520407031802410b11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 793003111 1250 793001861 793001887
    0xc0c090905010c08010e0c07020f060903011112070215040b09010905190606051905122a010f0305160e03010204030f0f02180c0d090218100906060203040b04050d020303 74
    0x3400365014500104030b4080d41c0200400c4541c1c168080c82408036460140103008015030201d0715084e804a0b440100341c40c14800041c824800c03140180d61541c80c0005503040c03040403901810825401081c2e100c540d64a8210a907204d0340803001209841c0d00d80400200090a25408241c20070345c4000001401b25503990744620f0201e0b0010407522040c0119425020410607006084c094503054a20000440e841004480c1c60300081c025180f04840700c141c080300100c2d08200c0011843c4450201000040d041c0c501010462071690300c0da4002400300290380101c50017405800c0c01124020780f01541c0000301d24080b1400303280188007980c0355400b0000000442c81d020000051075004003000d40030240d0500c101704800012202c0317034039100d00382070402240c00c0d92041902c4116080c5400850394260500c0044c01055103a600290512141d80034000e40407001c203c038600340e034501c6504022494440d042a0794070302980c0310707040d42c4890812007400141040c1d10b0301100310748094100c80c181400c203030140e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 793004361 1250 793003111 793003121
    0xa0c0c06020717190b0910020d0203041707050a11060f04081c0207062a081206010806190302060a05040b0f070309090e1504050705030318040b04060b07030c0c09 71
    0xd800691007903400303124200d0200e08a206088100300109621400d207442c1d201928290711001d04600d24403c00a0f032802003e0007680c00c080c2c00b62130115981c1401c910004000d4005540c00e403a24102e400b81c02c1080e007607641c2118a0b064000000b0642c402c0140e50b04103500600c0c0308000d82103032042c06505c60310403800c0d0180015280c54009880003003620003401c0300800c10703482510304562250500b0004d10b5001404442804554220800c05851000c1c0d04208000d11150003003e41d8800544030500d0b600c0341204034082c440c2643c4900141e1208000c00000f106030031040428514181010401850200002c14580300310303013881ca04250352100d41494641045010001e01e8078000b42280030160f20a180310050405030008114802a040c6420340d951101500c03141e141e80c514000c01c06000041107082e00506005003140c1d503508a602c0c401c0b4190404410b01030190741014002440c62600340584c8080d10341e5101c80e58104209600c0441c0e81895044007600c2e07103800310a02041d65540d40c018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 793005611 1250 793004361 793004369
    0x50711090a2405030f120403060b0102120a1806080114010302030a0f02031305060f040b0f0601020a05030f0d0605091b1606150602060a0b0a0b180604060c05190201140a0c0c 76
    0x90b00e0385141c500000d042c01d0400514460000e500248200c0300030586072410b0b40c0c2aa80c002c48002102c0400b100142d103040d0f000c82174248944808903500c541310380e10403241c0c0d1920500350078651006d9990207003921000c00a000f07988582e103848072105d0055100364080c41d80031029420202e0041c40d00c00c2c1d54401c03a40b00303a842011040310802a8028481c3c20402260401d003402011a81450039480f80c1c141401c000d0a0003811105000c08680e160384200410041160040280ca540740402e03c420b03074640d4003024006c41054281100040d0301d02d4001c40c0184904403018603600320a980c0400d81c0d80c07592104038402c1700e0b601442c2c850404281c0324031030000d000c0c00c862458410a82840c9010b85001402400c03040a1814802111081d0b1240031405080b5104061100d44407584206205400c80318101416040100440d001507943da1110403110020f01900c01e44207031035504500d03607400c01000c2c04080d012540c4e44d410640d07005219001086291079a140ca9011030032580d0343c844412680f940 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 793006861 1250 793005611 793005671
    0x3030601080c031302090402060c070b1b07150f0903050d0305070e041a0907210b01091a0307120f020c0f01050702162303070f0e0106050711090a 64
    0x4118603560899125504448610203841c01c3d071070050074038490143c400c040280649440d40208085403a110259280100f0b0101941c041d65114881c1c1e00007034100c0f4001d240e500100c1d005d02c4a0382c0da0702262180503240300201c40f00390001035070303810742d014039018080c5002c01070444e00c0000850014024010103c4055402040c2414010f1004212281b100c080900c110720344290ba2103005101d07690240d4541c2d0079900c0c40440c0d035400c0c50a8440750718040c0d89103a0001d254042712001801e543c8400300502c02620341d981c0c405e403201405821000e08840016031007608102041103580168091205095001d1001c14402c444080e0501640c21a8862240d242d110f00840183c4800078042c03c0c0d401002d51000b44104500709889010040f03251282940f841030031041030380409a0740c3ca1078140c803e0060102d61045540e010945076682c1e00d8451641c0500c0c2c110000700703a0500c0f5000f1100c0080e006607602243d40303580b20030081d2010002d8040c03a040c603a0351200c1d96888420702072101401c00484 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 793008111 1250 793006861 793006867
    0x70c050901140303070b0901020d02070c2c0a0216020411031014030c060d02090901030308090d03062d05030706050c12030402010206042a0e070e09040809150409050903 74
    0x8248031503100181c00c00d2042d0420469003500907100001910045504045115442c5d11004201d034020320401c1c051030341440c000980d00d01845035442010085440055116040116803040c2d102c104d2440c13007a201020848a02180c624015500580503c2c0368118180d10240e0f026030010b030448402d100d030819040004004c208800080034100c1000380054841419403940c02d400190319600003055aa104440c00b0031000c0114849a040d252440030103003001c1030070350712410050314800c03040342e500c40320340300380c004000b0914464046d42c0d086403100e40010318003015402d4100001d003401e50000d101c6201030300d0005145d0707408110701c900410064803032a075940800f00107507040200c40a403c800c5150f08000f8040140d034001030040e070043d002420751040a4028800081c4c0c3c10201201888070580300c5400328111b1108000030340114483c0e2500a915585d09007404007046045501a20544052003091035034100b03450308840c51170081804600d49a2142c4a01b01122410b0740c00706455030002c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 793009361 1250 793008111 793008119
    0x50903100506040b0f0f100e0a030c0513090302070627060908010c020f1203130f0302101b080402040c050f04120302011425050d0f0b0f0a080703081e070c 68
    0xa105900302e401c13003034540042c0722100c1d40215440100801201d40217801c7e003102c0c3c229030b40c450003c903210490020924070b149a503c0c1002d00c041c001c2401260310a0940241c07481c401880d91140b001c201d503040c5c000c0e1400e50702e0040103540c0030b50a890440314440c0180300d83c0e0a104130300714501010b424952100e6656030701340000d003403c450344941504207551000c481c883c1c1000c2c002640c200c41c0e00440f1642950303a03642d09495400141034410080450a580215a04254000c01c00b5081264a0752041000d208040c4c0881441c401c030302e200324045160f440104016040c2034010701d01c6001c136410310500d413801500000000341c4c800c1d0b02c00141c00750031400b40300c10507034280520004400134861404c0036090404118450752a060070031035180301083c2107480c400303005105449015240c48410000300240901e40009050000482d03482a10102448844c0346420f10408064030206c200800c1c1c89420342c0d0714014564402c4401280c0140c095102000100500c0000c11003140315284014829240c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 793010611 1250 793009361 793009369
    0x2040e060f250504120305190509090f04020117181912111902030c0603070c050c0102030c0312270304030606060203160f2315060405061807050903100506 68
    0x10203801e580001102d03804203400b01c0c1d00c4070642d010789041d1501040325040d60301d0107a6440c821180f081c0c00b41044401001c4410784c218001e405200001c0e42c00c512207036204201000c0d084400c540003808505805049101c01c07403c14100c640c400c4006240c188580c290301c1c0501c0c9020300c0401e1031100c10504100c54410442c0032030704542c00302c1c003c0c2041360198110910310b03511807000002d401d007030720440651241555130400810b1510580580003d6603030800b0500181220508201540c01d88200c000d5401c01c0c2d440001102c55460400c030141d400c001790301a59149404010b071851080c4c22002c811401003001c00030714440818440801540e940c0c0c03851515030292020759010205541050200c030000401050307011108940c000c240c500c02820321302d480031124040300b10014a540b50310400c800c9400000440110301d03003006214610342c0d55140c04100070b44030203e542d203821401001710b05043c03a95400703040750800352a0408a0a0440303e0010034541080d1030b8003c10000c1d1a142440100c0c20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 793011861 1250 793010611 793010641
    0x40803100f181a0a0e0a110f09030d020c0310021e030705090907020712030302071a180c041104031113050a0b0a0611121309140618010f050d02040e060f 67
    0x103e102c2107107071001400540010907500c200810480140c0c005001c079111684044403010b10401210340f9070700710024456140c0c21110009010707129101008250500008405c141d402e4014000d1008400c0d00350003c0103500304040300581204048145d41c1682210b0015501c5822142d90f86901c40300510304021410f00d0152408065403c00c2005000d41c448c40c0034141d8987e41c0609000d17035207545a180c2180c9030f640b03240c20054113061503801c0c8022107070301c81540303a005900d070b4086400f8401070070108011140156000e6010500411040000807096081c40c00c0c02c150040100c0d2450b1200e0606070165a41102c000c604255103a003205d150740f82c1500d003180541000c0c0b42c20000420351000d501c1d510804404294903150020030456140c000e800500703006003038030100611441c0d02c12840c0803d0740109031100ba11450703c8029042d520750101121034100ca015012071100e107480c2c007092207510300035404240d800589506404117a654100301d514010b11010540411624001c400851204 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 793013111 1250 793011861 793011881
    0x1b1d043c050a0308100f060e06071b170c0105071101110304060806030d090b0a30090506070507020a0603090303090605130203010e030f09040b1c03080a060b070803040803100f18 78
    0xa403040c1081c1b02d081000c111450070b03110f071030074004201a29880003c9003800f410100504a40d1450f00d44055040078600e16000c841c04640051202d0040c2070a00d51500d9042c41c00f240028014000c040c00700c1c401c92807241c030519040c1441072141910103481c5056620680000b40440c20b003c0900200342000c0100a41c0201e43d0325004122a0814110040601c030303030202c4004200b541001130084002c00b411451701d60403549091000b0b007030300d901c0c50b602400a11605403841d00498000030303041400307401190780300e1303900404c0c50b10081d040c150240d00806069800740d0400d980c1d8107690001171802d20846000383d49003145903201003074510405082d100701a02c1f64105400c2404207a1a00090105540700100d04036070210b00c00c1e01a1011444600c802030b450455180746174101014541c00404150103042045014400030f6140c8206180c1c0703104006008024900030030005002c01d103064003440c0c000308100703045901d080e40c0b080103041c880342175049135661000c420300d500d080404074420807103a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 793014361 1250 793013111 793013131
    0xa0c0e010f0302061b0706022401140607050304150c0b06010f120e0a050a061b050c0703140c130c0e010305090a0b07020a1b1d043c050a0308 62
    0x40d81040c1c0c070a61035041034030000340034a0340850741c00e801840200703002d014629007804540042c0e5031810000c2d83c1d01d44141c145502c00268060a250040b4078000190680d40c1c500b2400040300099024441294030044007078030280424003000c03071b950240030300781d194000c0c4030703542c040b20003045c0d09003950180c0340134220b10306102011380c803400712540011007501c41400711300b0001448100d80c4c1c01c3ca401c3c20203501005045001e80040001000031079804546030510412a24030702c0c40c0d00c1c0100751114030458582c085c181c1d00c01a4100000b0342880a014001c41c42002074070540140762006c0340141010148001d1000e44410302031a110343d00030103c00220001340383c140071301c3c20644035164980c0c080c4000502402902000681d0b968001c02c202680503900240e00000c0345034182e440300010703507180144109030f402a4400302c01043d80d4502c15001d5504500d01c20642c1066428800d0f0915000e6005460390040c1d200b18500884106429001c89000e20040c00314124039280080c84984010306103222 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 793015611 1250 793014361 793014389
    0xf0807051e0c0405091b060a110a080705190506040602070c03120305040501110f040306020a090b030c0c060115080a0c1809021c020a020d05030601230d050a020408151f080a0c 77
    0x2201d1030141b000a202c481602c40d1507881290f00b00480d9006484a0034004034858021104100503a000c0240140b90049007601c10900400124010050548001500b070703512010102e00402e94a0340200003061180d0f420125041c0d4039a102050001962810000304c0d130b0b0744013000180b000a001c3c0084050161180d21f107000000002d5450a002e240805000c4903070108000c0b2103540030b0a080c03000703007085441c130917102c1c03401447d004c10aa10203408607900d401403400001d02440303001c9519401d51141d03250030101d5a510004900203000e044120020001c14440081d114003452038110302501d81041d0142c0e40b07040c0c002e400e480950821540f500401d104210b05144142c4c04181d12400c500a454000d660744c0724400120703455120074044070744001d240c09286075580484001040903c000d010f0034002ca40d104401d0100300c4c0524030071080c49400c1010350080405c118050b555000c1444130500840e00403440d22510103c00c0383c3c00283c0341c0d5006100030700c107210f02a100c4000500884481005d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 793016861 1250 793015611 793015633
    0x171f05091e03040303030f0b09090d0210060b07110f1908010b03160b0a0519050403061415010309021810081501080c011224050103180f0807051e0c040509 68
    0x242d00d1040d07103c007904159591003030640550305604600b2114000038001580e03800c0c105216034a4a81044901e4094402c01e28512032201d85400341c8004c49d408012a80e0610421f03441c0c41128081000d061684602c00003104080c543e2011883c111101c180d02110408070706001c0c40f982144c2000ba107c40c860b40c8020f51095280c48640100300c103030f038181040c640c3c03030b040c0d04c47c0269058018198403450300c2042c128100141e60307208018000312402090f003800450b84410394005034800a440803103030201c01d22104003c55000f0340113000e200c1d1018003620142c40c1469200c2c142da00b400c0d0350b50100e456a502d41003043c02403c01240c000b00c103a9500c4107103154980b905069070f1351104c0310042c0c10301c0150490301045a4503580560740004c01d01c0c9030040002402014004040903078011980480c1c904001405030745403520501c403000768400c101c0703031071f001481e2a0b00c145500b040408607214400e000b007256284100059424280c03000780014036881219170200800d60381c5c014940201a44861802c40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 793018111 1250 793016861 793016863
    0xd02060105090408070c0305030a1d0108040213230109151d012c040c1701060b070609020f03030c0604111e010c0318290f04171f05091e 60
    0x1038210342c1c407043d1150b85091a1410b241b60700107581c00584580000304200306215004491151020066503010f4084072201c40151101c1c60156030181d001045411036150780040c0d64000e2201070b03041c10100500c9940303c00d2250b00c0035403d0302305051058440c40c44001c1d858411060a004c1d184000d94219900d0003242020210f0205101d1002401c0312008507806c1c0d440c074000f00c605800311000310a409807800d410b2401c40da50643c421301100c0310010300c00140b0f1010610035030f0700390f905501c803071450710760b1a44840015015811050b41d101442038080d4019070703030400050400b002d100002e0220782c81c3c6070418200030606420440e000b81708039190300c0c03000c0c0485809035642c0a800d080a0a10494606045841c282c8100f004041e650091101040c1c120100403540041c80200c0031040d004503544800505038000ca602c69000040244020701102107102c000641250703ca8080300c08000c1c00300e0041100400c1c030034491602d1507070f55040c003148620520410743c1544240442c51100d002c0300300c0103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 793019361 1250 793018111 793018129
    0x2070314070804051503041119090209060c01060303020d02010b152b150e0117060f09010f0504060614040606080c070303020909090309190501090306020f0c07090203090d02060105 79
    0x40d00a090000707503510401c481c000035a0041d10024103852444c0c91007a00100160340180e409503080c04280c0c0103000b031841c10342c00e900031202d410030028411600d8072601038007a4019540c134990280041c400f00c05011800d10410f0b000710300a40c01018040441040a401c680011520320302031049a01c000d66200355020844185412180ca0003000d018907846490280c001d10810040300c2c0d0400038660565000080c01ba0b0584010080040707540e40c0e1000c0f01c00b404000c0c0f0740903200c59040440003400c00d507882040942e10414010005c01d10307050251180e01201d0b0100d45c100c030100e64a01041c4a0384c8114480512a6401a03c5c01c00485081c920060704140b001811290b5480d000038000341054401c0d0144d450040c4040d003050014104030300d01c80d8607a009029820f0040300d0b403544031240d0001000004e01142c40c107841f6080f5150840d01d41c234000e5485101072200314442003281c910030003010090840200f0401000580f2400d003003004c40e041c015058052021540700b038006100c0c1c2c0c0e4403201c2c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 793020611 1250 793019361 793019387
    0x206040c061110050a0510050306040c030b0402150406030c0f03020a080f1b1c180c06080403110334150902040605030d050c0c01091d0405121813020703 67
    0xc1002d0403034000e407120340340c86107581d10440346a052a00307101c030000f02030b0081d80c01240744901c46031480741c0700c0d0181641c42104460180c8041014481003011618040b0f540381c0050018141d031050350580c1041c0085075000342e0107640042e9170391860120071503101200b2403c10149185c158505030003500001c001240103480e000d28685000081480a4402c2c8440e040101c03211070003a03160b002d1620168546074040d40381900c42410b0407051803041b8240c15080800c56171005014103900d060050071034103075400500c00c50500c4042c003031701c8207030182c104041c10801c1c41504d5610030050071205110040c40211000c840d00482d10300769100040c40d4105040c002202c4800000750280c92030001802802e440d9200a030107000e446c141d05d51007540f01c40201800e42c1024100d94003503801100442d802c2c203452043c1da0342540a064056032a0031130b00704094105001d002100e2002d40070382c0d4504019402241c0b00958070b000380d8010421800c10051543c445580c1001c00c50074505180c401400c55038004ca1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 793021861 1250 793020611 793020617
    0x908221715090f011a0a0f080303010e1b071b09110d0906060902040b07060b0d03050d0e0a0209070c02010201060b041a0c01021608030105090f0705390601150206040c06 74
    0x5141c40b03400c01c01100c8425200d4002e001c0c5800080e044016610000880c9000d29800d0030040341c1900410452012203503860000c40c0740d60301e8288015111071019086004c1084010988180d03180c5146c003802c5158003c10000541301100d090174400104245e00001c83d903820041115800380e50441911aa50080140070403034096519050000b01055009410480c1c40801d0100e01e40d024a009401c1640c86948100000c42400c400c120b40c4c5044c7c02c000400056041249005050403600329151042811088480516450f4002080c4030303021241540000e601086c0300c0c040d503909004220090a00d21700700342c941030812001d62001c1c2001e034107100f060b002c00500420450303001d40c121800c01100d0040c07109106480e24000d0f032681e00c2841039620500c81d08010130700d602210b80100f40203031040c7d2201c034034102907105010000a0542d074001c0c11070340140422041c500140360310010111142d005404298180392000e8405034400004500311743c03140c0100030014040c0c10b448001e42d044c600f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 793023111 1250 793021861 793021903
    0x501030e030c0a08030f0109020f0702060d1b02100f141b040f150f0e01200312090a02040c020a03080f270c0108061813050109082217 59
    0x31003454610300c241a0340654a104a9049409014a0700041c50003928a0741040200b41d0740c0c0d441c074005900030318404c8040581d04011140041c603201c8010720f0b400c00303a1200401c802645001400240c0802e5240d2005a0030051b6140203803241c07481006540051007000700a0308a552049255031203008103004201c5901c0a0a034240034240010b1301d00504807007042c5e0340003d48450a85143c81e940784201c1011402c0d6a004080c480d00540c45014050010780d1445804040c07048400f9507240014486030b030780c1c081001003018843c2b502e200c00c0c0c8242d807003100a2158100c10b10510084810304150041150843c0c1241c0e00003a52040c3d80c5038205004480142850700d494030501200c583d411100c441d0001542100903201d031011521481e0403001f62500760b2a59610814014402c0e0380c401501070807030f20400090384010050b1134400c0510b01a03000065103c0b44c0350741d05031407a40103d0b02c10041028003480080e04440d00c2b91103d003d482d260380042207014224480139a181c500010107401c104076a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 793024361 1250 793023111 793023131
    0x102130312180306021b0303070207031a010b0d050703060816031e0506070309020a0905130506010b030712020c030403290901090f020607021807170112030f050a0e04060b0405180709050103 83
    0x24041a1b4981003089090f030341c0e03900b05a03002075a0b40c00c00d48401c8403001c90707006a88841c0c0310030450960407220100b4101f4540220548c00c0c40007004010a410103160781c0310404540b000040041040700c2d28101100340c0031030705500301301000f480348803140115444209803da0004101041e05500100c20342804101100a0310000f0b000070203642041d440c2529001c00c011198484010701810140141c05031000c590700c0d100050110b00c003c4902b48081205810b201460701621781c024035503818854180c03410300740c4075a203030203100d107800405684c2240d044501c0310400c0500c48125400c9043d40b80208449010307580e400600000031000a4031920000c201003095440700342c0d12040485100d95a11154035010303d01601f0f840c180c2442200c1c180d014400032800d615080201180140c0546807400a400b8503007086841e580400340442c200706000150034096100d6001c1c4c140903040e50101d16881d5400c100c24002c43d48040301406e82180c0e084010b0184a680266800007a00c3c000c0c41c0c081103030540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 793025611 1250 793024361 793024387
    0xf1211100c0803040818011706101101020d020406020d020706022e060e0703060501020703081603053a1a09090102071b05090705030c0d1805010213031218030602 71
    0x250700409040c080c0300000304410000300342d006002e404180001d041003428001c0c0111445405d0b180c0b09011880c03024042a03041c5043c07400c1401110941c942081800364507a00c00707099070015545141c8141d004601480320b2038042c8410003015805200400703e940c50680000e550707070020b100ca0710150711300e07c042080d00c02c4024030302100808080f40500150790b40340c00340ca80c00a411101140020b1910f540802c40d50b2002c00c084048a4106c01e0041c10088582d074400080300c8820030440604c00300300030500396070b11101c8071840c202040758042c00d14006d49180c160036103040e0610305425946040e200c21100c01201c10003010299058840d1600c80e40e40803c050f00904c501c82c0c0280c900b21520000ca0052144001040d061352030540b202021f0340c42e4442c094800d400145c500d0560030406001424840c00c060340300100e60320601c500703d11804202e0311002d01326803001b50007907000c0030704680900502400d42c03d540011030461410007105000803100e9a00780855000040526400145002c88400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 793026861 1250 793025611 793025627
    0x20102060705180f011e0804021e0d080a17040b061f0f2714040b09071b0f0b0a0203090615011d0a0306051003030201050c0a08010312021f060f121110 66
    0x50b034130003040c40c01c406c05902a103014400c0b103080f0b1280365006043c2141c9203c2c826140303140354015002028034a2540d807035428a03003004030b4420810090a401606500b0600e403001c0c029401b0382c407005081d0508100703211540e20404460115285040c103520343c215440440c03805400da140c0307449040854108242c4002800098801d01070441107030020401104c45000403030100c0d81100c0401010321024180400e01501f21140c401040419040b6100f107041c0d03c011540c0076115240075000070a4940d10103140000070f0710100c5440c3c1c1d0100c02c1048400d81080540d402c42c0c03010300012241500040000d2950450240000d49490714420b05c080c551520f4128070007450780480d0074496440d29080410622580c0d120640042d804c00000c69000c04034031040790b108200c0b983d6401c0040c0e0850b260409002e0000c0075440851160183c1814010b1400d5104003095030810340114003503191120101d0303281d42d035400000c1980c1007541403034005480c12000340c103140d00507207003401201c84d145401d0340d00c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 793028111 1250 793026861 793026887
    0x141c0308130b103311150c07030e0a0305031e0c1b090c161103210d060f0509180f150420090c0d0e19020102060705180f01 54
    0x900c1001d111980502503000000c0ea002d00718400c1c02e032400c90400d407440d00643c080c0352113042c40000441103054800c3c404417401c034451208842c0700c001c1d0300c50070201a0390308403507541002c4030109288080640c888100c8407041011140040541d040d900d0b141c1c6c4a1040b000480829000340945d01d05014800058613200005103040e035102d0b40d012182450880064a4182e20a46994002950002070356080e560306001802001051240c5036407884101001e099070a64540b240c0e59000300c065004d211020000c4c1d002e209026200c2c98900000c0058800c1900440780200911100f4040d030346941001075805080c034030222202d154101d10a0703003030034a5144080900d015680740001034512210f1901e010728814081c4a40c50306c0076a1140c404004038203102d5500c000c060012881ca1a400c501070226540c2d1b0110000f0b800e80c01001c40c40c035020240801da511502181400400d540e0180540e036404403403400c0039403410341604003d03010700d00c1404015200340103015504845901c1031519031544 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 793029361 1250 793028111 793028123
    0x100e040f0501081608060f0406020d06050405040606290909060109080f03220669080a050c0f0a020102030a0e0f03090622030c141c030813 61
    0x42d42c40340f81c4140c0381d0406911301c803c58400c5102c00520f40c000040c04038420301101d01d4214850b21a551140081d51044900d604444c0d00c1380d401150640e0765204460013540305560025690386018900c05400d030151040c03a039098041100c001d810244030f003c41321903030300403100080303241e83d008010f0381c148116410400712880754441c0d0401a0500000a001911780c130407061003250480e0320141544000307400350600190101552000c94810b01c484441030140c404000328050301841891107500d4158000118050940f007442d544603110500310134185962000000e122070018100a04900000b510143d8202e5440c0002880c022a402c240c9140c1045494142d50304c40c100100240030307400540d00d0080365403612812540c0c0c100300254003404025150b02950910030744000b04000d5400006140607001041a0111220201000868091403241114002181c00c09149841c0e680c100048030340070f50014040b080c0d00180102a9032505545454021020780c0d4103045009030b00d0a0071401025 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 793030611 1250 793029361 793029371
    0xc1506030b01330e061b061501090e070903020d080d180516030b070e0a0506040b070302120705060a0e0c0904290114010c051c170108010b100e040f 65
    0x1c3c840000102c41c0a01450349100d03145000c07122801000c43da920340d2039000309048100042075810043d002c1c00111264060054490b5000444a03003440c2c803c44403055040300d11a0385641030341c2c0009070348014010a090b10740d201d00d400303100502074801b903000180c0310342c0b01d1003040f004100d130741c00880d4180d10701c080f8188a8200140300c1d0401015081c0011166405003920089204c400c00e0228800c0b2a00440c103032803280c603202d40690700202c2d106003041d00030f0701d4200c0100da962aa040103000611090120701d079500000d080c024200402103100c00d0b482c807410005000407910000702207810122403c40054924036500501703152000c503c5000760003e464104100034070404000703001c41e0030000c0300080119140c0f2800550b1074802401170b40d00881c140320542d64154411065105450321410868103c02102c4615044a801c000b1075400003800e800c0728081496074210030340e401050444001e100c2d21010394001200c480c88412084200300c0e10407020500350f40d42d0780015140a06034101000b03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 793031861 1250 793030611 793030619
    0x180f060504090501060806032a03070b04090b01050301030f060c0e220c14031611030c03030901060b070803070f030b190e070512070c030c080301080f070602010c0c1506030b01 77
    0x20031908184980b1001510380000081c02d40d00408000f442103a000b0b016024041d071700c0c048210940c07003d91031a040020219000f640c252810882040a08408807180351038906d03150130706080e1085518214100141070004100084943c41d015580a52003800401c942640c00f03821903c2650641c051503006000d00c1ea00361003207461001d6406407a810107801d01140c2d015040070344054035600d26603110288100005005051041411080012640341003804007400041203465a0803040b44040d060f0000414840244424810f0000030000d03c4a11403c04d030040d12100c05d40d00000709980c0a001c8894000d14696100380d000c0f0100310340041500d45030b4905005006040a0607001b02000443c000d40414031441c01801600c164a0084001140710754a10030212242e03012020b040f42800280c0c00e519001464902c00b650180c550314000b002110800200c00746040c00c5030703101d4419640741801d41503009601800386088a0340105680111480c0000500e008001c103034030141040c000140081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 793033111 1250 793031861 793031867
    0x91a0a1407030e21040314070317030f060306070f03150b0a0e040f0e0606121c030c1b03090b0913020a0804020a090209010207090f140405030a0f031b180f06 69
    0x800f020b2a0404a0f80b6482c1030664059042c42c1d0f0516201102c1414031080001030005500300c02441c40f40815681099500e07039130840d110b00714083c0700001c02004000c020740075200940c0640d02060440041c4442c1c1099840541601d103031004c0c5804060b15612000d000d03058181000000b80003481a6658030785401a008141d854071106480c426030230200d0049071b40d01c40e40a0309032010300b0003010306155100c5608101001300b40c6420b030b0005002d002e1903071001c1030601482002c1540240c8000c6109000e03980e0041081d800c030825011002e401c0989240401c2c0e0103031040701555294070030240d447c40d0420010300401d103401c105608031400088c800740c410360b2107225540520f10a65019140c40d032541220001d034001c40c0002401680b050b481003003011000c1d08075211103100380d24001803c658102c0d030403411074402c032020390301944009051007005a002c4052443d2840518003084a00107050303e14550440e400110001c0106004001c600080c081072488000c0c9010340c071005c0301d1960380c0c0002d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 793034361 1250 793033111 793033121
    0x50a0f17090f0c040b1509010c0602030a02041401050c0a03030e0304050406171204030f0f0f08210c09010c0b1b1204021003110912030409181203091a0a140703 70
    0x10340c102d4010140500c0107804c142c020410b0341d02c0002e110010b01c1442150b45c00c0c46420010070f1504009003e40c400740440c9040c070003580510160b200140e503403402c040a8502d450519000c1c0390400030f0030000480c141e2400300c0c81004160741440c01084980b9005906441d500551f0042135010380360180014643d5044405041c2e410f00140070781c0c0c2407581d40b0100d54214000c0f88000340c041b040d18200b5000085410785401c1305188207100034400d0401d19214090b0540140c01c0e40150700207a03440341b0800724a19424140c1c400c0d916449280307001c41000000b0000800400d00910102510000ca07441c20b04032055110041c1068171040d40303641c5485040c0320102d80555051780a012007611082d21240310340586c02031140021006881c2c010424284004d54000290321801c900040c0408600c0d03510f140100580502d00c031a09070104991420224002c0040600400a0500e0b1040c2200080d003020f2408d011020316603100200b564498904e1409421070140c9000c0c103c81010411401d540c140e448 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 793035611 1250 793034361 793034383
    0x100305060307050a080d080a02270a050603010513020918041b0803030c1603120f0603030806040213030b0a200c0d0305060a1202060403020913050f010c050a0f1709 72
    0x8449180d07503203a040c085114028014602546c20901c5014100b5000b03140c1030350018030364500149004901c65030960341c1c0e820701f88141c2c0742861404040016213003c7e1801e00140c041115000c0c0746500d040001256044018000314110341c0110745c2d41c00710f0390366036039041c0300e240c12226200940c505443c145412500d000840141901e01c524081502440007043c0c0e885182441b031560b15100902c1c01041e04010311080484c100070b607401c0e4440d00780956006001c5564800392000c1540c50440c54081c0149000408483c001d92042c4001c0020b507860882c1b09c02101e17040b0309514210340f19004d40d880603150490600408103108400b2039022600c140080c842c0581070000e48020b44403618049081d40c0c001d0710307016400002d0310400e106142d446042c5128140c401850546001d59070f502242c00510308650103407201500307090312414007009000d0f40d140414444c0081044083e00200540103000c1e4100d80d10410241c00b040b042400c4c041c1811500f800ea00004942d02d924202032241c4da0340c140106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 793036861 1250 793035611 793035613
    0x3070b010f180b010c17090a141309050a02040b0a0905090d08090c091602011d01090627110a030203100f150b041518030305070203060708010308030f060f1003050603 73
    0x40c440010b1120710030350748642c005a440440c2d000c01ca4640942c495600b0f40e030241116410002d0781c03a5581c0d0340310403000a140c103c02491000f841e0340e0420100403149101124458104035495000400200e010203072181c0c119000207010038140085840511150056200d0b24a040e042c05640c9200255210010010f940d51511170341e04d5141540e103505030000074a4024002c0700c0850310448003014001340c811154800020b8820351003100803807034080140320000302d95442d640d0905000040c021500d041400b006440c26100002080c032928070b2024202500040410309000516515801e00c040110b8005045400521400f0450b9006001c7c4550741e4011a1501d02d01048452000903140111000c540c40d1034100b912b092602000303407140c1c0d801c000421101c0181c0c480145080150700010b103010740d0f251034841c0380503c1414a014005400c10080c000f019004100003001e1008aa9011110406805090700c4810201c2c6000c030501714610390101d100040c050965138564401031250320300710 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 793038111 1250 793036861 793036889
    0x5100f061d010e030a0f0203010b0604300b13080f0a08070305010504050603030412051606081602060112031110050a0902040524010c05120f180108151203070b010f 72
    0x98010741d207000d501e007441a003540004401802249005002e00d02c01b07800500003243c1210b10400007011540507030032004205464090051a41201700000001240101c0200843d078a054551101c0500014258540c0881500c140c0c0f003008580c03000c0e02c0310f1752030b4401c0080c0c9907060107001501c180001c40300c1000003803400303000081a240074000c80c8d00501c0040c02a510781800c055104555131240701e0241d496100b44008480d40184009544000344007070f66505100d810302c0c039179000010408040d1070003158041801444101c0a000f40141b04543c581040da080c0c24a500c0942c4c189921004e1051403a0700d840104480854107420009605108550030410307903580e032106401310303103078112219420358480703969991039405075011040d424090303000c882c034013101500315802d103a105104803903552401041d4004190410900c1a0000509080401903031800903004500210a40b009600c5003071501c5a8140c10401801140d0b2100d412039501407886d03850304480c68110125101c1c001c0074103618 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 793039361 1250 793038111 793038167
    0x120c0504051602160b0d0c05070b0a02040305121305060d20030114061903200c03120f09120d11030a2007080d0902120607030b0f030309090a05100f06 66
    0x10b03540031341503400380d000b050f0a150f61907013000c00400b2020008000d0000c00c100f19400315566804451041795a500056a520700314a06a410113004404030000a481440849844210700d00414155003081e02e2031074a900e0803569903400350103100c11140c81c3d88810944a40d41614400055058580000d1001e03451110307401888000c2c4120541d0011000304a50401d0f0100e12030b8014007010104054402c48440181c0b00d800100c1d4401400b0f0303040f81d0b1002030030300805044005480d6101480789459000da151941946880d0803410301600c03107910300082c040340703220100d900111600781c00d401081c2e22850308210980007001250340c0d80d00058a41c04c030034007080c0700210444000d035601032240d074284000e030140d000203440052070807a0301c4401206680314503c42000850b00c5588a0390340400c0b40245038050084564502100c9402500101701001c02a00e51116681c0c21400f07400000034543c2c1c528209440b50525904244110165003200092951f84419080c1c00e20034402c401064010320 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 793040611 1250 793039361 793039393
    0x32a0f020d080a0203090f07092003010605180619092607030816120c0b01090b030d2304030305071203020a12090606170f100203090601120c0504051602 67
    0x90030041d00010707035040005480c03094180c010b580c10208403001c0b1154009948000c1d070038100550030a240d032a941310f0380c0142c11003074502c0f29200b188c11014450301d154144000245103100f14612031020200d24035520146491b62402c0b201010100b5581307080e04200003500070940c2d442403080002d0555a0900c1c0350740900c10750344144103070f00e6950052101501d103550320354040c0c02c070492128604900c45101c001103202c0c984482d090302d4840d55070b90703541c100a00d00720007583d2041c0c01082c80700d89401c04502a980380001c2566040b050b03030900c1201d62a0030140800d0351440030320140e900c040082030010425410201800c0d03c944141c1104140c1807070b5903c110100c0c003481c2001c900055850080d4118080c15034803030814140a041c0208456071520240d50105005200400c4150712000d103c43e21078405100b4a03040d11890002545181040d402c6180e40d40c0042c040d5140403042d85e40498200601000d20344028800904103100501d89003048810327618466000601501454000c0303680580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 793041861 1250 793040611 793040623
    0x6140402031006120207061b03200301060516050703050c011b050c04020307030e010c090f060206190c052205090606030f010e18010906200f09010f032a0f02 69
    0x203404842c0078509151040440f140c1228005444010303500304100d00c0855018001d0540712060303402c0d0000c00290f0b80c440103084441595182e0142c401200c8a200e00128840c12241103a02618001c0d4440400800c050124045040010071511600400204015020801c02107190707013600c40b84415401c4a55811a000c1d0500d80141281c02c00d901c444c2007441d01e030f40075640011483c600000c0c1c00c0e03020300c26242125100300400000c120208001c00580300600200d5001d230066202034401e900303208009039468400c01e41602c030070548403404484920300c02d000ba50076580b003030f6003482c1140180100d0104400218000c040c044c1548900061603801d1000032640981c00640b034910a41c1c0c603080c03c40c0d0110f40c015003202d010441000411a1180c001d0042024044c000c00000a804049280d03692204502d10032100112906110310280714000c5000d44080183c00c0c2401080095070b03c000b100104000c0c00000280220b040c180207140550b03407000204080d584e103807074030f0151502e001660354103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 793043111 1250 793041861 793041871
    0x50108090304030b130c1d09100b06090f0f0315010f0b0301060e010c031b0b010f05031219050418140105030105220c0305060c030f0610050a0c0c0305010c02010614040203 75
    0xc2c130060102c0e003200103450301c8003040350181c5414112181c0707415500e028448903403009a4030072158000e00c002c08100f40310300600380d0714004c000c00800b100310011410900503403c20500c115118000100a0707100c40c1112400104c00030300ba1b1342040e02d200415409500300380a00d40d00e40c40d10340000310302d03140000d0450f4140c4015440e044042e190040044585e103482d40c2084041084041902d40a02d00c0c02c800344042e18400c204003035441d03041c0b462103a00004194040c6200f588690089000c101080048980c1c03075100c2d080414001e80c1002090f60188600d5010701610824915400d88958259000c804a030850750350306442070741e84204041c240e40301a12031006440303012250099000001140c12032140c13003545148a490b640351581410440c007119402103403a0000208444105416205c43e4004012075501100c06641c00001780f890040240000c1841914105042400307480b14400000b182d008000740203105000000902a10b120b01c039444419080505001442c60603009a074468 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 793044361 1250 793043111 793043123
    0x607030905040513201315260a0804210b0a0216060203070c051608060c03070c0c0f0630020306060d0501270e0d050c03090901090605010809030403 65
    0x6281070004000081c2406048004130401a041c9440040d690359150a0510012940c84c9814869003003404403a041c1c4c244540402443c1c065000300103022481c80ca030a81c0c07001c0f10340e140110b0030300a0010b1101000b40c0745001c2c501c1515081010408800d00500688007941804507811000031550401280521401842d40c004203000608045142d405040c202d4800e010700120702400d51030ba0b0f0100c2c1d0094481c02c000603074040c2e9110500c0010808041141e0103c0030fa6984c01c0e00d0254901e88408014100300c410040000204c0c002a114507103955465403c5080720707420b20341c0c50902d040e1f19403140c841e020215060502c420030195400800800c1d11449107400c1445000c00c108480c002c0d84000d0440d540030f9410301c0440080ca59610585000e0304ad1440c50035030740186006c054100010a407603045d21142025004189030a0200f010b16100d20141801512000d00b801014254000c04001542233483d05000180c0f0903002d4101000700c44007a00d60640382d803a40e040094407032007140009000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 793045611 1250 793044361 793044377
    0x1063606110610060f090308130503061008030f030a060b0d06140f060d150b03010806040303050609090a021210020a0302090907020c0d0318050915010e060901170402041d0d0e060703 80
    0x100c64041e6100c80f40b07005c074914140c0807054072540d58191607048400d548040c4c1c0d0080034280030303e00b0200005a048100d01c004220741c9450401e00e60340e81c1c420f03504a5642c1039404400303e0800205a000030b00508000020b01ea21070034032104050041603144580c1d2900d038602c01001e286406d00f00380c0003940001c060300352031404144a101c100a010960080398808800d28400200040d54030095406801a04040d00b07642c206030030002d0640f14060074181c803a500d03134014860415000500043e40d0741c1d050340c0f2035052000041d0f489041c6644141c10058650002516038038080d07042d402014411070031598404613442e111000c84c0d80300f00c0060069040003114164802180c000c448400b1018960700800b4076598603103002c60034918064500607a502d0750b86c80f0746641c41d80c02441d908003106c000d84241e41804180400284011a1511803904600880c0e01040941d03c441e00142d03402070026589050205903c260181c0e683c81c810700c03400000740601c401110b00d20b40442201e050581681d070f802c036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 793046861 1250 793045611 793045619
    0x32303040b030f09100b0a1a040b0a120606021b0d0f02061801020f030f040e1302040f02030402010215040c05130902060705072603090112090633080601063606110610 73
    0x1c038801d00303141c03400c0301c8c400c003400001000301c1403000514a20800d951540490350f41108240d0555101c1e8204005640001d24030804000c20200c84982040702100c40b4910b0364403600700122402d580340d002940000001404503c0440c40074400e0403509001c0c0d0840d000302d03651100d05920b84c00780200c040304240f0204020000c000e159020150040840381800c0c00762040303540081d0840e4080322140301e803c0e8002c0208015585c051240c0d0800710640300c110406490155240d04001561b40112807080749e03242c00000704558076602440c2642d42c05440a0782d161139505042d55120380b184070b2280341200e82c00c0500d6040031402c055090150310240103500300020440150782ca04203118500b1081d90350b400400011400314003829004400c11505003111801c880e0901504101c80030602c030300b03c040c0b40750030082140c000501a04640d020300d0200c0171054101c40300301941f8401c0d141d00980d11010540e0b80240070b003844070701c401c880c0c5d26158a01401940701d2115140c110445102e540b8415501c8104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 793048111 1250 793046861 793046879
    0x510050306090f06180702060f0a1b030510270506011803020d02120d0e0111010204120209062707120e0a12140a02070302030c0a032303040b030f09100b0a 68
    0xb13604000b00510103030507111405900d03220001c1c12903103040160721030310601400610b14820140c020302580000c0c1700302d003d45480c01d110005400c88000802d65070300006810340342c00d620800d02905108078036034406240801c03446109a20310003a154042d1502021600c40e40c01810080e02004130f104d4000c0b41c16183d5020458604000f40382070b030f00031b483c030440081841d409010301034400d81641c035181c4003004072a00051500030740c0c10320721401da80304101c1404900d50401301d00003410b604407040141c0c0d640d480046440707040081320254800c40104082082c00c401c2c004c03110710454240d51103030505c000803002c078815154510250090364001c001c03c407000c07a03140c6095170004ac15270f081950720780d0112801061f0a50250b4000340058000305001c0c000c6140502082c03550703034421950f555a150450301d546d806507030300c85032502815502030203402400c841401a00c00070503544040944928003a00c070711050460440343c1200074041d5440b05080c1c1c4030079208480c01c50b84042e00c415001401c000c111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 793049361 1250 793048111 793048141
    0x60304210309080c1614010210110d02070807050d031802090901110315090a2c0f10090308180c0d030201060504060303090f081f0b010e030106030606051005030609 72
    0x50360415845948541c0420ba03500000c20b20009000c00074045016040c1000c0750072000c9401015840d064040c512440d40e80c0013075031a03d0710b2200700b000181b80e010201010709a1284104441d07100d8000300c1e982d010b000300103015080d00c900a2064500a10010600702c0844181c40f8941c812901105d09000260030201a840ea00c01c04050001a810614029056854004550081040c0c4000d0a80b000d2410001110f07a00301032244001d1040d02002070b01c0c80340c1001e164440481140b8801c0c407030340e404a070803c103140006640d02e0640701c8800c40490f042001d0300182805401244185000c60134840340b241100c002260454003501d4031550110404c80c6d90708a03080194215901d45002142c41d503503078400d401c004c511076143c1c4811980750404184c0c8250711607102102a40060500c0c0d581240312a80e00c48050f076003900c0c001440181c01005031030500b01c0f90a01c503050b40c42c000c3e01100300015644004150b40003125015007600c403c060480385841b04480c01031700404080045035801c0d03101e02c18 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 793050611 1250 793049361 793049423
    0x608180a030c1104050f09010c0314010509060109030b04030512070e09070f09080f06040311030301060206060603040c15121d03090918030a021f060b03060108070509190311060304 79
    0x643c0890040040c005015a403040d18481c40a0800c03505210050409100b50009070526081c00d000031001c00f014081034240c14800c19014160032000180160f10a07465403000e160310046000e01400c1038200100303282c101c2403050904402813008500a00c2c010031025550000c001d0112f40701d684c0f9032404841c030013190b074580c0c4184940008089034011081c040441e4035040000201000d10b03207810300030403580750f0451070b0495070000c1005020b6164041985a031005090700c8041d40ca0715146082110340c0b885a02010b90f5403545e4104144c3d241d84140071188250410a0034001c810341c0303500b51f5420800c00c0f040c141a69108008403101402c010006030782c00a152209000079400030300c980c0342558000c01d4aa8010780214000341d82a048805c01400040c51002003004110f013040c4401d00c0b1480040c103e141070022910010702c14610440c115020740700050002024160000c94072840403030b90340000c83d45600d0001d5030003640c2c100308080d6445140c1020816003808441940c00b9940011044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 793051861 1250 793050611 793050623
    0xe030408070806090115081209060904060306051e2406071a011719060b0d05010c090602100507020d1103090603130b16080a0b011809060608180a030c 66
    0x50102030601035103006199a2018010b1444c02201d41e60844850440b102e889410b51b00d0180218400000d64501081d40c3c05403480d61503034802c00080369809200d0940e0303801410f118000c42081003580102d030080204081c589070000c2d425603044e0442400311048003941c070150345120314103456104c1001821501400041c600007181e102c0480900000e00e4841500d8211001040010b121003c0a401c1480c24000b03070009a8000c002c1148400104102501e841d460b026041c3e1903a95113100d54106035030000081001d10b80010024104100a128000143c0140f1100c024045407074083c0511508450b4058000e1042c0810140c03011411441d00c42d2140c80240701c00c40f200c1d04c1c0d0200031400781e0044000c44103020814541540b45050040c5860440d50351034603000d8405800100654114100c0040031407072000900040742c088454054400c19004844400240e40c003050f03200d00280c400ca55100e900a80c0c0d00406400e6605001400c0a899802000410042440380c0a803503144da00c202 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 793053111 1250 793051861 793051867
    0x40e0609030a0c11091f0902120105011223150f0d02091003060509011a041407121413060e07080604080a050405060a02010c0207080c010806040209031c03050403140702030a060e03 79
    0x90007040c417092080b1007000599548104101c44441c0303a16808009011310380703003540340c080d01201c614a0303c403042c0b11f024144248036044444d1000c0302d801016503144664410100c6440300390100f4402102a542448004940c0d518400c03d400c121403584001040a0110000305900e5800c0c8003840000030046d00c00b02c075143c1804000260302e401418043c10100001103000581464a0303d500d188007002d0700c0c8554506070002450000450366107074400c0003400e05401094003601c0203005003610500c02c0900c3caa9080070003030b201c440c0340310f43c10748103005141c10000c0c5915100c64607980c1c0420700616185070700c00000a000140c41c01300030805080305107030607030600f65140d0110380c5a800074005040540d46590003082c3c2507504100c0e01c2c000f071011100400c90540e2050001e400e40b5806410300740516000a400794440e1810402d1740301c0310075060780c800c2c413449014200900525044e42c00f107000426907542c0483c080c032001d060780d60b50b6400034050005c55000d41d81d03050041c400c1e800a446980028 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 793054361 1250 793053111 793053143
    0x612170a110a050109110a0321030b03250b0f0414030a0c062111041701090b0403200321100e010b0d1d120a0e0a14040e0609030a0c 58
    0xb40000d0401c140304400100d140324a503d0244044a035840740140103a0444e4000c00100e02d0010b080440da00f4010021801c3d003800e64002c9000e0603004801c142c0501c01d5114101400300c6003a0807680b2a8890200010910349842c0c406e085842660f041c040383d090203100070b200c050f01c5a000750228040060071603880c104250784810412423107030b002101041c0c9006180000d8442c80808208800032800300304104811854613640b0f6000714002d000704c4064020303001c1c1c4102e409500407681950482004240742ca02450b0080c100d14220012080100a0074640201d0000c00010b840c0c50448000b01e10b4407a050203c0f4070f10101100406a100705451503c0001d250207510240f80d0281c900c05146c1c90f0340790840c0d81c1180a0750380789056410003803001d4203400304d0a4030105018440074405914103030307619070440e401c440c6800e410321043d80c02035042c00001211000c503076900d14005001d850500003142d400c21455111101100c3d880003a40003081504003441c440c441c038042c0c0c1480b0340d4a40071a4031700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 793055611 1250 793054361 793054363
    0x6071805150f0d1b030f0f0605010f11010f06120203070803031003060902060d0c110c0a15050a110f0a0b0901090b010515041206020d20040b0906071e060612170a11 72
    0x380440150209945206e408075081050061080a091154040c48010314001c0000d002c000500310308001c0148100c607200150b0029000448201c901140600c0030b203031034003000340358107503d40340880c0301c0d1161410004070428084184d83c400c201141c0e019620f98031359254003000d8003554404a900c0442048501480d10351031049020301c9850b40d40f0f54801c401c0e0700201d189407846040700b09118000c151000c012002c440d03030002c9004c13550b0749050768854440b4141618814404142c03e9294015407800e203a0b00c09001684840e500c1c080c0c801070920b80c0703942607611300303c0d4200c02c40913080c1d0503130000600040c10301ca001c0c1540a005041090700c0c0a6807405010b0b140d030040041100c0854000071a040403020a000360ac001701034a4419401c3e00340308000d403045900c03581c1706d85c4c82c00c42404242c2402c5940c401041c0c510180c0c01841e014003805030016035030b001c00c0c0c25107000c8650310b2034a540411400101d048094006500c124030514102c50009100310312740010a00508000d5008107018a0b41701c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 793056861 1250 793055611 793055651
    0x10090e10030503030f0f06120325021e19050f010c020a0f1205010501080c1c0203150a05040309080303060310053606060f1e0a0806071805150f0d 64
    0x306040d1011785802e2452140748a01d42c0070f40542d104880303444000307510071b1000c0f040b912100701843d170008d1214210145075600302d00100c0081d500c05085609078200c4501d016100b0350500c002c80314400d0804a05540040c00c9200d4064690403964110041c0020350061120b19566800140f6880b100d9540d150f5048401196030445c0469644500d08641080024050719000d13088010150030b08803800000306428220200c9414100030b9103030355500c1075450030b200c40b082ca2002101c2039159460645000000b408060784c0440014071181c0e8001255040401580d02500008026111981040c02005c018100103040007030000410941102e01a054107911400d415035080020740c081300c0440f0590030650000d18250054181d111040c185554856404080d13503d1038071650740347c00c510000b05010803840d03004441e4500c9900d0900c10312030303040520420034242403248000a2038aa070241720440703040c2c0503080c41c2140188485e141c00c082003409420f40c0452103e00140390b8500c2c40310350b42c03802 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 793058111 1250 793056861 793056871
    0x1170a06020c0307150207050d20030f0703080f09031b10090309180b010503040b09012009360601021c050307080708090a0b0c0906030f1510090e1003050303 69
    0x90f100040c0b031310800210f945102500e144940b411410846661030f643d44a64107c1252000c10482c1c400a50741c01c64102d0200d50f122070302c40304032074541e8420490303809180d1054000350049a8070b0300004030a021441d5859204000880140d810245003403600003140000603054a218003400b6030323450748600b59129580100c3d000f41c0d20309443c145855100203080c0c809003e64000a03081600d00460782c0d0b0001c0c2180c2d080707544426849403541c0c0e0302400301d0061443c4040c0c010762000115205e00e03907505040190004440880e801c03540300c0038243d4103007085180c0880c000041040c5a0041041070683d0482d10307401070042c015101d2a100710001d9034842d4030000d5248010a0010082c0b040e81c642c015803c82d40300030b0713500700041d090801c404515540c552580005011b044d28400040c459402c1c40c054600c4010042c1c42640c0b40d09042101010340d900460307070703842c20000f90020044035217030a00012044081680310180410308000303070810f500c60020981c5081503400c45000001031800c000071171040e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 793059361 1250 793058111 793058113
    0x3070c02031c140a0c121e0806120a030c02040f0b0303130f06110a0f030e0d0c032a0312020316080910021b33180a0e01170a06020c 58
    0x140120200107081200d50a0b43e0018104081c41881c189542001d000c91034a5005a440303942c1100d400c50454008484000f00942100125440c4204503007140301c4a020f550129215a09003020b500f002d0b607218081840500080c803c191451301604141c1e010003052602840042950698070b00801e00d1684110b4000695440f400c1040004440c410441c3c00604610303c0e085d60700b000301b504402c3d600d107082c02c0c0152560200c8114070341014021402c0103441c02c0081e10101c1941018102074401d00910f10080e02d00400425100301401079220986907038282caa44001201415500c0702c0e1041e071904035000303056100410074901c0d02109118209209440b4502e00c5948100c00c5003408a044180d80b44182035502051401d8584001c1c045e0221900a003a03d00c1071840e811090441c400e01c04411460100405d0540505040f0901d0700041c40b030410614044d440301481c1c1414000100001d03c00c4281d502c214800501907629400c441000d03095140048442c4814980c031840122390001c066946a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 793060611 1250 793059361 793059403
    0x1c050a0912111c171807080a0611030103030c0807031103030a1a1503071110020d0213270c0c050d1e02010908030109020702010207120c0608010816030803070c0203 72
    0x45100304043d40e2000c4a00d001d40a0b00f02c035032040a020341e110783e50040e0124031501d002901103905030310424000d11024003200d40040c0c0d0b8079107080c1c54010b011010b443c10360820440500c61a00d250840b0304907681551102d0810040d5210aa4650402401202000b429145240d0b031980c8c1080614041d110070800090301b0083c0c4180e030b43c03011008061480c004c4048040c0c03000381d888000182c90b442300841c00d03d0401c81c40361072400b50a080007458901a05c910124003005c000308035901400b807408a504000c0341c0507448410704103805032650412468035000b40030001b01c0000e142c100014160980c04c11100b205c800f46d07241c0c0c0c10324000340310510005080d120698040075800b00c01d820600102e0008100100854544040340c2c4014010100504e8000880d0001c5910801c210001400703110845070051240d490b00646440403480790380c0008100030008220080c000ca4503c1b03000c08140f40705281d0724a980d60f01c01c501e4000400701c4090182000b040c0b00962414082c10088003130f01c004800c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 793061861 1250 793060611 793060637
    0x12090e2205070f230108070e09060f0a0815011205030702060d061805090d140403020d110909010b130b010c03080c0f07060f051003030f050c0111040b130b1c050a0912 73
    0x3d074985160850604106d004000e1090a540001c2041040c403002d8580c01d030580d42e1000845c9070070719400700054001a2104002030b40c508081418007500c1c1149940e54800e90361044000740c40441079101a0554000308110001482c0140081080c0c0100d503901092170750343d440c0005008240441c4200ca030540303070380400c654000d080c01804805149410482c2c0c200300d403207140c0b949500031400020700602002e40c498052100c048200c22803510300620045440c030b8440041c80c00717844200c1426024152044189040700417a0040581c1c00170180c2d541060f40f0302d1520100c031030400c043d1010080140c20030111011803606801000d0f0305026020100d6200c0740b2100660440f480104038050b1480c0724401800025413040394822100c00c00e181c0039071070f201032004050040154810440c40742d800001d00181a001a501410010f01d00b50b0b0510b00b041e40d0b41069880c4c900c1922004490302100c10180110700410707502c1035401250030100001d100846070348040d1030b0400c41c1000008140c4842c1c0c089 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 793063111 1250 793061861 793061909
    0x190c0b04140f0319140106080d020d1d0d03030f0f02040603150f080706050d0b0618210d0f200c0a08010605011b02010c060912090e2205070f 62
    0x400c002c801e500a2259114809103c0700620110320010800c20001000c1d24980f0b100350440300c007070101c4005039038003650350040281d59003000c042d8510100c2c7c1c28080c01c1c0ca1103030311900244c0040700040c00c00011003507140e40071401040041210070345141d4035034042581c10aa4400380014085a40340041c42c124580000440c1d450240e014800ea110480428070002070045440421a01d05041c550340f12106400280050f190314000c282d0001004a0000301c400010040c0c1c1c00884010341e40c42d1a451030784020f500011150315400c5095501034280c03800306d5886203003045041642e902d40b21001401c1100700450600860312000c0c07055004171440d051510340750030000e00910070300008201051400c00080c0058000791182d40c0c0605801902d2409c0d6402144501440d9a010408020010291424030311101c60205008009445850081907040014990034098082400090b0448416134400300070f6841490044039140a900000101007070746c00c030300c4000341803502181004c00049103008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 793064361 1250 793063111 793063129
    0x2090415090b191a0a0306023004150b03070e1518061009060807030b280e0c04080a110109170d020c010f0c03141c050603010c030e190c0b0414 63
    0x4138082001c64001801d050303403220901c0044940c80031001d031300c541d00e110743c6500c03035601031401143c0d03844142d950078984001010582d10035032041c0d8501c2e079460b012680e04012185100381c9150181e00081d800d21600c5409404654003443c0c210640696030014408540c907048582c0030300c0d00c4d0003d41424003140e03160280f444200140c951a100d0b14592400d10001c0042c0c01c060812000d040d42c440114040b510b450510a01034103490b200e0325400b404001320030040a20522802865440000218103070304c125204950489611000414203502c0743e03280c1c80b5015030320704800ca050001800300015071409112142c40c01450b80000303030030581c01d0600e0290a00c5925903c250402c000301100540c070541201142100d203405191810040d5500c0c00c1035111841344070b80014607070784100c506002281454100074842c2c0000c3e00244000851080c043c0e040da44881548030710303900101d604981c101c4c0e00400f03c240c22401048032001280e61503601c026035a105801981c018011400306480703500740f00c440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 793065611 1250 793064361 793064381
    0x11401060203030f0c0f04050a12170306210114160e0307061d03210a09051905090403020106031a0609070e1f09350a02090415090b19 59
    0x554518038042048404204c001081c01c207000c900422100c042c58111800d80d00a40b0028003454503131900d81502d8015424489011111420031442e100401851641922300462004e41000070b94410801818181c480c1203009407060366981d03c44800f140c07103000c0828021032a2050f0500d00c60360b0800300410100801984500981c4044010021140d01130100a40095085001c0c6020024a80040d08003a1103041d42611406440b0759045004000802064550a039488850103daa01c1c0103108102109561450b101d0070003020802641c03c0c0700c06000ea00510034400040c1880c1c0703030f55400720034941c40c1140300b604664940410000d400c00d1149075810414504010885403120400200c150500340514860050711104d015019402044100050a6035040541098410204a400e260300750307152140c0d11074807007044182550012501d480c101d44c01619144031566a0340303e40d0041035803013000489003039807038000901052481101d00d00a4a400c0c000510b140d051290030400c2d6001084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 793066861 1250 793065611 793065613
    0x601090911040903050d0c02030405011d03070920031501110a0512090102073c0308040909080405060309010c0f0f0804060509031b070303021006030b04020d0618050114010602 77
    0x3000d020603241503504080001c02c07100801d00c442145421200c0d80a800158100c05080c10031111240f07030040040c00541d0740a03078407100f512841c0c4c0a84c042a002068105800d03030404d003400d200039405a002882d4500c2606100d0042500f840d41001c281c1d481280c01c3e100360081d461803080e056903c1200e00c3c401106460007813103003a0254503090703101c96100000d158401e0002a55044d164000c2c407110f0014150003d6040d58000c1440500c22513a200b017000320034056000c0c8030a400c0f01d034090b65040c00e40b50020f0b4020304060600000b4401004040c5041d54240c03014040007400d03681c0e4000443c0b144490000110f04002c181d60702401003402e008060080c8802d50180001650f885801240d00540180010030780d0f407500c01c0040c3c154800c642c54118007030603212002d8091180024090100e070702c01e0342120f17a41d001d020900c0c0111805404001d2141d18010081000351401169900c40b40740188d4000030b449000c00c100c0301c68800c029034208c8199464040e48800c0c010745007001c1d4014542c0740 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 793068111 1250 793066861 793066871
    0x9050103060e06090708070e04020c160902040b120a02070c060507021201051b030a0b120d08090102280201060b030109140105030613121103040f0306050a060b0901030902151b060109 80
    0x3c0c0025a00a1000b4007440030410500002504103108102c020500b98010f042155a10042940c80707071200603044001c9801c0f8600500040d0701d031001d100329011640e42010b501d003004401094522401006402c10000c0d540a100c2c54010070702041d20b1030024010750700e07000c0da22040d0348103020021204880122850b49480e04000e012400300309403800c0c03420010001d43d565910462104010301d0321542880e007110b015280450380602c0014100c02400c46d58607000310340d80d506a0f40e54203138451108602c601403699801c2c05417051100700340c00c0280c070f003600021880395210070140d074690300240d00844c2c1440c2c035481741070a141c100355a528050708050b40500620700c1c2194440542c0d03403203980b000344104444007100d410300384200f2641035140d0b110015265220313525a0300c0f01c1205442d02081d00e10f00d103000e012554034400c034441d036012501070040d15070608800c0300054004040682060b6000115100c03c282142100340c001c000951940b0f00000381c0490700071004d0310300350058010b5070201d8644 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 793069361 1250 793068111 793068121
    0xf07060305010503010e07210219092301140d03021c08011401050412020d021c0303020322020f01050c0f03070f111e060703140a03061a042907020a0609050103060e 72
    0xb0010761060745628807a0b01e4903023001c91010030309141d2151092000c0341511a00424080c841c0c0d0814040301c003c2d820145001e0003100c180701140300b82803040c5c110080c11a140c00c0241d06204810100150007801540c114001044040d1715007070708038810700d001610500040c040e0705103030182e01008200a00c2c0440c1040d0410040240c91040480c1c0a4403e101c1000c400045540300300111000002c2010100d5816505140c01742c00fa42056581440d07000342c0d00811034514000d03801403a48503030014220f4510900302c200541d515444510140c80341c1c0161030440c6001d8008000500080e4070030b50904c2e26410050600710344030903888403003070322030034400c000010303104030380840c1500446040355002e6070b0300e100b03150a4482c1407000e90844512240460181e05050300750340007000325600c0c2002c01030343e450228440d025a00c614011a00d0b00c02100c5002220301001d40301000420b2005240d0f5480c01c1b601c6e40015100c1106a80414001260580c0502c000e50b8903005010040c01c4540c401c800c3d0b0300746 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 793070611 1250 793069361 793069379
    0x19030507020d0518120708100f0b04020f160503090a1d0705040e1609180b03070801020906071e0203070f0314060c12071808030d0e0c0108070807020f07060305010503010e07 76
    0x85441c90310b101d005401c0c81c0c0324600700d081c0641b01c0100042001c40da200c559000411002c0c003185403019900c589042442007e41c00d0074022038844900c88443c10749401510013009090030504201520148018450072000b5201d10105ca009814020249004200c0d1188480f04192004054504020090004000e4450b00541083e008090400004240d03201500c003110050b08aa1081c0030000301c3c41d42d01c00c2e5655282c0d0010355030780700030b405032081d40c2d032501465800c1c1d10a1032121a0400d600b0071000c804199422009001500303e501038500c1d401680d000a40f41580f03c0c1c104640d5820040d50410800449441140301d021100c0050121458a5182010f083c003c1030460070350b2503004000541322a01c540111031492420b03100d8100d0994075848072aa498009108542c0240e05d480780f542442000025200c0754080140c1d119041580c0d00c50b0101d8205002a02480c00d51042181c00c40103450284031840c0500340c103580015540d85004100350a4407803c0d00f144855410101d4180a1485 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 793071861 1250 793070611 793070647
    0x1306020f25050601170f15070f0905150d0f0212060a2903150a030606050f042714030316141207050903072c0c0c0703031419030507020d05 61
    0x110b000e1001442110011005c0e05010101c410584507005130307458000d25001030400580034070841c0e96043c1e03001c80145002d803505c0d00039000c0d0b1944100003c903038840800a4100415015840301c80c0032411200490602e000d90f041815100c109071100000c007c0a410f080090038003c2541c2c43e2018140ea0440e135200c22824018003100303201200c0000002c0c5203c0c4a83c0041240365000f138a860300c41d5940c2d0034a1002003607076016103480391003504000d056624083c05584c80f130480310244c186561650101061981004039800c444c41c0076209603150100740e050001c3c41c030801070420010700007120220010040c4001d5911201003c005100904c2c09048003144903a02229078244941d440440400081c1b804a05600900d0f040e08114108090241149112581c0b1400c030a1150415224003110402a000b404056140c55100c20300c208040f074810895850280015007416103060406100c81c400499241d4503800400d444405218400703034100018482107549141c10b03410041d428992490300e04c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 793073111 1250 793071861 793071869
    0x1a1504020306011b0507061e080c1810030506040c090303020d0f0e030a060e060f1902070c0308122e03020f030f03040f0807051906081306020f25050601 67
    0x5540480055116401510042041d540404004000403001c1c580240c6d1403a041c0541000a000b008500200844400101d0080e000e6615008030341c1c1d61701c00e0844002d800c2035024044c203000000d0f08607403d4a881c03004404420840e540450700d4940041400281c1700c081ca2140f0422551041c2000800d5003c03074005180c2000346480c0081000541d011121402e49a005607030601506420b1400c000041d8080c841003603c100a69400b0b94030004980403d410440304030916903103010141001081c56402000b25030f00c941200c000301c0c2d4580e00c070340381d040e044030032500089401e00302400451030f04082048216002d10f01e17031040314038204034802c000301458400240102000264000740f55420710000002520260072030340c82d6580c4000185800300343c3d03c40c080c00c41c022a200800c0500f450300030302050b4040c2200f0f00b8040c0c0c1c40c0c80c00c103c0780c1e428010300601c0704907002c10301880001c580c2d0008080b15020010000c0e1a102182039007184417801c0195800000c4000113990009140820701034119 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 793074361 1250 793073111 793073119
    0x1202130f15020d120b0310110a031a100807120903030905060a1109130603150213080c0102030307120b101d010e090a05070c0c0e04030e06030420030309030f03071a15 73
    0x301d219500464035001d40321f0380500f0200e00381944103d880007000d02815400035160707010301c64200290b19101090003040d43c3c440d006290313a280040098061404990422240e00d0108500045200924100c8400c1c1a0031030000b925031080c0c0003441410490a13402c0700c483c0b581040b10000c0b44105110340d1146410503402800041046092050154810801036403c9400865090780c8040d810300298040c01501c56800b6081001244000000510711280b0b00107800841c9192a20503081c1d80c1d1301c54560341c0b088801d0321541c049040c0c3d00c80da01701043c0c60b41d0b00d448000740c2200d0351901c902c0c0c298002100303034100180041038120b81ea6803000402d401400304a4009043d4031203100440f4032079800ca070041c02c9150502000540c8002e00f07428544294042e569410040e03285100f0041d462200baa409012860003410520480912244064012100030103d07803800d110382c4040b03800c1010500d149107036500007090f02420b101030040181c40b40011400034103900e103441609440a030300200c03031040c09 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 793075611 1250 793074361 793074371
    0x50c070309080607230d1a10110a020402090a05030d11010507030903050423120d0806100518060904091419050d0302130b07112d011202130f15020d12 66
    0x8079400201c100c0f0500c4406040c240202207144c500c00202c16807d0641a014200728444481081e2250741059803501c01000913125040c1a602003001941000041c194415100200007580c4c2c4d0b010010283d100840d9110f048150402003000350071500001e08150030b0504101a400010351300074100e40948041115940740552152480d4665100365000030b80c110b4400141c41511500014054110f51803d40c1c6140c55592184180400400c0080c0e002003c258248a0015440000b03541508800805044603041018680c0000c0540d203c4c240b05840c0d1680c01c05000c0c04450003403246090000e001c628109001440350740f241d0399824100042c00030198007140b40407682d01064140380c01011f40b2814140c441c0a00e0802403042c08240300c110b44030300801e103444000707070a60003a806008504100009142220400195000d1106003042c1d0150341e0b0030021013090b100d03c3c0b541c0d14090b0801c41040c4803500d09003003002c224000c40c1d01c0500c0c113550010742e048100030340c070002031503821843d07007000f241c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 793076861 1250 793075611 793075667
    0xd0c0f17010f030314091203071704030c0905132001030b0607022413090219091505090d0203010e1e030c0d03090f200f04140103020919050c070309080607 68
    0x4020300480f14a540c7c80441000d00d10000100040074289681c041c28070081c003000501e010013168401c40c400107054400c58902040704404540c00305034840c1c18081643c42d810a107654003005650b81c003501900c40c8220b036082034440c0d60306204d0f068a00105440c0d40c0c1c500300c00da40010341403079400040c91400140343d10040d40040c07000700544540d920780c40055040103890340c0c401c02c0a5048203195082c0c1240c010b640100440c8501ea02070211440c2c51130440307010401c07a908a881c0d5100d91000758100030210b0707042c00180c500344500c10340d003003030800540441c0c0300344841c0a840390b05031800102a54410300c0b469442d00400710700386120a03031604001818008078505080003003032000010780380c11407540d5910307000c26901d0203c0344501000c440c40d0440078034000400084801d074592515451a0305030041c0700600b854a038003500400810f0508400f0868400c0b004280d5404503212140e104c401705001c4201900111450081d000641c054001da180030070004100c283c10007880b420000503004041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 793078111 1250 793076861 793076897
    0x605070b13030c140318010203131a09090c0a091d01150c05030c0615030a0b0c030a0e0d030c02010b27180f06180d0507080705030d0c0f17010f0303 65
    0x843d10303071209800c01200d101d103281d540c80b0303000380e01c06a0042e220481120020f61010080750420710100c000c01c5900360802d0754044514070f150710ba43c000f0035010850b517000c507904c00c030216105145a42d00190740f034100d214002c0110610307900415007480c101403110005104400082e06642000e41e0740c460200c1400011215144000b40c040c0042c00001381010340d415010601502c282e0084540403511000c0320149656002450303400342814aa0b0b401003a041ca101c0001581c001a121001140301030f50302d902e8034145540ba01051001c259600c0b00e910907a902801400f440c000f046451008002020b9202c680040a015070003101d80c1c0c2d0314002582e0040c400c42102c508100500484000d2010002d805685d00800d80c0c400d864000c0b08486110103440c009100400f07903003295120703401c0103115a204105a0802c80d0100c4041c041804a411408403501c190040034440384c0d150300c0284400300c00908006848440744c110315800100500048504840315001c40c0c2d4075240504a00701940e20302 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 793079361 1250 793078111 793078127
    0x303140a02010f020f07140d0903111302040e09070f030c060c02130f2c0d05180303030a02030601030e0d02030405220504081e1e0a0201020c0717070605070b1303 71
    0x40451184045140e117108141440600310943c89010203541d541d00007010b41e5500c0030811981c2e800a50781040030301c0010003001400c5520b40000c1c08a0031815901031110050f600079400003640760610400b00b00080000f005442c00a00802204c1550207003982c03540403600495004840c11b0000314a02c40045449408205c1a26100708074100501d4407a901003e01038030302112103c144110351049000e140400d100141d0200c05554002c140490b00004150361542240c456204201c2e031108c441140c80d10140001c622802c041c0800503a0791038280005000c0364503490304d80e40b241d404120740b0100c0d260000111019140201c880d441c001100c81c0b09400100c22044d00400450b007440240710400800c000544030a100f807089100c000301c4418400aa14000c1e0040c4410001806801407900e100850042400020902c00545090b1140d030410340b6010f02d035806400201070481c00c510403c05d05100910250003a4034201d4508402da441d0207810341d0b4007070480b10341c46001d941d4200415000b0169 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 793080611 1250 793079361 793079381
    0x6050906072f031c032301061205071106010308090d020402071424070f0917071806030f020f060c06010303080f0a111e0405121c0203040303140a0201 66
    0x703408164014a20a402d0301c05030622842da241114402100325868045840c40058140401c0d0365403400c054002200540260314641d56102030b00d0f01c01000c5007480d05441400303003003682c50300100203498591410890f407004041e007040000e4030070002c5224201081941c1140e07000300c101600c8070ba107800010790001d1280c100a6016100041c05810841c5c1910811810700100040d00da0602c90a5010a6450807000035042c505035800c00040885020300d0581c5080e00d018500000520703164072640d6800c039003403021031006030b00481040240d0720a11000b81c844e440f0014091010900d1a55141e030525505c0000070303c61881e030b00300c03411282c60b440103540c00c01016001312141d55a6a040203018510141c4c0c0c8041c8001c0c9000001c0c0000c1658090401140940c15595241150313030741002150700404110400484010031000510755035008a1000c0c1c0d0101c440901804451038400701000c80768a902001507400c2404104086134001080349101e840302d180302030341e83c03107480784c200c0c010107003221 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 793081861 1250 793080611 793080623
    0x1b04080703050c06160f05030706022701140405041a101d180f0402210d1d030307030c0c05040f02071506080d05250516060e0105040605090607 63
    0x1400182014009a00021280a2030585004484040034801284144129018501d041c0e045200002e440d9500900c505030190f000c0d0703814511142c1d199800d0364090102600b1415514803600044a1658070402d03401800342403100060b841011070441500035403141600c907550b11107040e03440a505c52078011801c0c0b401040c4024400e510740001c1e08040c1502da0980e4400040c121031003142c1403100c0000006880344034061450341d100308007004100c0d0b000340205d8100310040340074080c40806145400300c00500340042c0000c45c20300c00c002003240081c41c3d892030031032241440b40b824a48020003220240b980624145001030540d06165500220301e50003590050f00d88052810384030a0755014280d15849114800e504c0c00d6000c0403002650b50743e000311601600104400b51680e40940c004040c071000c0f4414120100000a00700901580d02e00002e44560f0806d813090b84502a503006098007400440c10218003031210200000c115003da809104140701000071a080c003552240c0540c1d00b400da00903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 793083111 1250 793081861 793081867
    0x8120406060806160806060f120c03092401031b080303070c150506010806041d06010305031308070b09010c030e040c02010f1a1503040f12030506190308121b 69
    0xc58480014072007482a1962401100003103841580d9000c0c0841350542c2d41e5030b030400180c40d40740402c0000d5000900d402c40300e840401c1064912041416540d00c1200401c4610380c6070f01e0507403034050030500503980c62203010800c042c0810f40c51144050b00b606581d0400c1180c1940300104403200c0e0810a070703130044d40c007a2002001b00001b26600c18042c1e061140b180803142400c0940c460341c00d0649006994050100385650005202d50429901402188032a4240547c2e0940f8000c2044e0514100382c02c05c0e00c1907040050380b030b0121310003042810020690803004145040c900200c40520303014282e5014100807003949841d0070305202d83c50790400000000d0040100009100c0040d0080c060503011802c01c84c00e060b1072085161407030710a0b581d045406000c8001e40034030909219032951004104490407941c0d05643e0000c40e840300407041c2204010b03180001c01c1c3c10401c00304042001890030000c401030b0205410702c005101901680e003074096903c802c2010b0344407103001c02c0588050204540d040e400c04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 793084361 1250 793083111 793083113
    0x40b0405121215120c0111010f020f0720100e2e0807050901020d051b0a0b010e0a05010501050d0c0306270501081c082e05010e0f1c081204 61
    0x4042d003038000e80159121902e540384050a0101c078440c40c08019450360805484441554000c00141c24400004c000021300c42803c894008101c0c3c04c200740d200764000010504808100010f01d03015031010380c22120b001705100f26400282902140c2107000d04001c403000310311046031031300142c04440c003151b200c801c0e14150784c841c84082c2003000da0700b00c0030015092201103000203000f0012111034507010f9024000d04054003e05641e1540104504545591100080385807950309106405605114000e14849540341071640c0701c1051020745404442890704004000c3d6a8000c42240c902c41030345400402d034440010b50680003481c05034803c0050310000c071031080368162070110700b050003005400204800d980307481c40c06980300c0c42c0d10f1034200c40314581402801600c0c0201012940040c00348031300f81c0c05034103d41a190204522001c54500908841c409000a41e04050400c03584101a01e840140502c030000058060501c8814800a26401840c0c40d090280d944201c407100c50740c94a1042c058109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 793085611 1250 793084361 793084387
    0x60402130e33040308011a04170606010f0809030703121d1606090506030604090c1e0603060b1201051002211207080103050a0602030601030603021309060b06040b03040b040512 77
    0x2c191015080c1e04000002d107121140041d2a0901507034065440118980c00e05542c1c00048044072804040202c0074040000c42444420060148a9030200900b007213040c50b40024100034004a11070040c4445032041011415000040d0b4401580510f00b10790800c403440005002040e035a6034089001684004510360401c0000c1c460b25983c15580d050340d6510307600c09003101c0305004c41c0101030380180c080021903010301d419044014400e0044460383c3c641503030303425031062034918100c0d01b45880000745003c00c2030a4051050700014082c2940c003a01c0d142c14500503042408050281d42e00c5020300b005520700303203442084100e1508403005d50301d01005030501c41c03480894004083c4504009801d500045515202c1c05206d8100ca42c054000e221a40c610f80c0c5220180d040140010304065803900c002026945401001009044c01e000c0000d0f40821400d00009441c1c6244155025605c10841000080800800c490f4095004003144905486510700305080550490480030a1100441d1070b40071b42c45 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 793086861 1250 793085611 793085653
    0x12091305040b012306040330080103060606031b030e030d02070c05100c12050a021501060c0614070e12011103010f180c0503060d0507052d030f060402130e 68
    0x10f8810704c180c0d001040081c0c00401004c41e1045070004c4050100b00001803030f081d801240c2100307010b011600120845000b1007000c480e0703c0060300158000700100240402845900054152031500b80b0440c2c11148020b60000e481d901c0c0ca20030107a46000d042e005c541e050056940421108009549d0742800c1e090071a40310104e03008461180c0e07240701e00e4042e41402010202146680046c5090540340d0801e0107680c9034000c100240c0540c00340ca131200c1e40300c11210b000035028107016151101188141c0c2003c07400c5996000d000c0c1c0c1d005031075000303020781d5640041c0e4544404004890035003034141c2150046024140c4161040038a010100012800fa16851401010f07224a0094100040c14114801013a25114880407012450820120b0024280400280d142a000714101c0e041581d5131710100304032105806100c81000003010381d144403034903056044044a50114010061484018020b03a1030f041c0140c0300900c2601003040714455884280c2126230031403403a500341d030403d0305100011505c0c44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 793088111 1250 793086861 793086869
    0x2405220f060303110f06011217070b040506160806060d0f06060509030d0e0604050f01021c021605030a0b01090b120706030b042d050612010e0106140904030212091305040b01 76
    0xa80388080b010341c000f00050721102d1312248134000d006c1640f070000d51640c1c440c194001034840300310980200780f891034018010130700a44a00f82151540c80e06050180c1004d401901c402c41044a088032103210700d070f0001402c2d070007000c2203842c3c5681d000703626980c400600041140446c1c250500340001141c54100c00a4104c0120136000d95921400c201022240b4003c10f203d00e5501640900091085003032070151406003031018011284408035a0707031b21503c0024030091030001a4000340f4415802055014800300420007900241840001a6508441200c0502170b00c3e040d2503a50001c0b001030780c2c4800300c070302c231910468080d02c1c00c65440b000010080d100384411540106d05014071044400c80303c3c201005111224884502c80c03903c00701e0003d01508020b414a5407000ca40350720100d03004030a1203410443c103034010001510ba4600f00c407820b0941c13070341c1c250144204400030400000c0703500810000180d0380482c00e0207a0b40c201c4200000e01c001c00011026000d14a0402084104007400030748074169 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 793089361 1250 793088111 793088117
    0x6090f1003230d11070b090a090203130c080a08090d030311030408130501080c09010f0203040518010e090f0d0e03071d07020c0301020f041412061003062405220f060303 74
    0x100e0b81e01e44060b110303130248540101c980d038070000e070410445025001a1000500051101c2000b551b42d02c002c0d407d81c0c00694521948844001c2e03240d08212180303000b080200072500151161100c2a240e03010b450042c0703031140d802182003445600815119900c0040140c0300922002e480742001d0a0002c4584c1090460107099000808046400c3d1f00456500740b1070b00038080300c10b14004d0120f004440e0a084030100105603c4207210200303542c0c0d1001840c4082c031042050311000c540c903222080c200c1000240c050462a04a5070701c0742240c0901040256021400d8100b18100c04003a4000c24070700600340d0f0001b4240e9005442c0b10b9265200aa41580114902c0e422a8110001a0205400c13442481904034409408002c2049445586580d95205000090003216001c0219005501706041200c6002006841c41824000c001c65482810440060008800c1e040c00d0400310407007000d031a80c017403640b01d51102402c0e5185d44080d08252080a02c209a0620654801511410140c001400100d000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 793090611 1250 793089361 793089373
    0x9010501090603120f090812180a05090c210a0c0305100501050a031d0a030206070206010f1202060d021b010b130207050d0c14060106050d1406090f100323 68
    0x2001501c1d005207829030750080406052000e24076420b40c0c0409075483da05c41400501000044c07040014003000e00340f0508100385565545126181d038440d807414403c1c1b6442264281020b00413915601510ba40c00980b1035006656810203411001c03030680b02c0012441401d194104110013001c2e13603003242501c02c540ea141406552106000c080c10407075607006084c0001c03014010350503803034802d800050302003444140c8030600d0070440c0100b9052036140b950a80141c1e000c04184044982e04110450050448800c4070000b142041c82074800c0481000300644504804205000750313501c16811220030045c110000d0310b80c24800f011040c0a00003008a00b842400d000f05440d034004098000c590301142d001010706070b400001c0005403551104408251441b185101180309001410800140a80710940341e2079155050680600280d0b04040c50b02c0070f24922400034802c07140c46d03107600c05800401280000c101551381c216500001c0c00240d0010305403070b00500100e1004400402400f9140d07000c5415108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 793091861 1250 793090611 793090619
    0x181514060d050604120c0f291003080304112107080313170c031614060913110d021305040b0a05150a031d01050a14060a120f0501060e09010501 63
    0xa2240741541c0240c41034000600240000c2e00c80641d001c9510f4150500008100c00c07a21884141d107d4203e08603024103003540c54103400c24010500384410404000c00c2c8129103050010030707a450100b840004c0c13440e100071000c2410080500c03d0b820442402130045030b1a1000360522000032407142c1c50902c0517000d01b140100b02e804c800b1085401001d24a001c02091920b40b6003d02c2c0f88800010b0540d500340100401c3c2d840940e010701a400d0114808101012514201b034156001c08000d580340a1145030b04200c15045501e59107107000d441c2910b500c000804021102142e03040e4481d042d501c260241c40003d00e044107010f49580841071f24000d070f0b810440e08100d6428404c50741c030703680501a802303103114040da030104107814024800c110759441c003c54044e52400b00380141404c00040d04829944031003c0080c4400c4901c69509914440c0700307881271500344000426035842050044150140c01c1c1c010100510120140859042c1d5006000700103203943c401083d001d81d40140c8580c0d5065013810700005d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 793093111 1250 793091861 793091869
    0x20d0e0c090109052806050402030705030403020c030334050304080102040f050402400e06010831030201090b04060501031b05060901050a02011508071a040b07020418151406 76
    0x240b00d0075000a215120442c0210017039002e143c140c070310a01c0680c4455000c40c070750b00d40d40065806081561245070722410289006420a16580400ca019520901c4a6940420500c07000c59850218002e9030704100b0b08404090040c091000c4003070600c1c40001000201ca444c154000c00854543e020740d4101c0756122004c00099128010380070011010046002c14003c0126030140c0810320000400c9a4001d5031800c1031403280c860358403050318240e010301080860b58104200d00d600a075051200c02d89150000b0042180100302102000c081c00d03101510701c1014002d5001c03000558019101a1807440d003803400001400c001d0204458031701c00d003003107130590055850402040e02c0000701000c2c02d1400381c000448840e0406206201150340b641c24450103200302014480103809540050324005081c810303150501058082d2484031507000304010000c20440f14140c84404e9812100400d0301650900818071046142070098190f10311055001d1644806500000b584084d008e61505550f440500f00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 793094361 1250 793093111 793093121
    0x200a0908010911090c0715020a120203070818160e010611071404110d0c030b090606070201020c13140702010c0f03061503050c250c0e04170d020d0e0c090109 69
    0x2012481000b0080f4054a05081d000c1e5020340c10300381181c182021a03c0740403811006410b40201154000358411100360701084921620038005030a40c95420144001020114002d1032800008240241c00381c1c482c00501050b04200d005c4041e8a0a481e01c59440d445426420700c207d002242402d00034000c41040440c040d02145d00e102d050090f061803c0d002d1102505140d154042c1c00d4034100144a403401c1039100750503003155242d0300051040c10309000e00c44d003190040e00c0903205920503c04040140c0c0c0c006010304815a042d10340ca014907038000b000c0d002401c140c642240c02c070000002005621641584950740d4061995120f0340c00d900300070320940884080c1e00510054022070096001c06500030303085640c000c0b42d80a16103140207410650042030084000d0602040e002100c40c920500c20b00580f200c028107808000c4048500700384d91030584c24000074035070340913210001c5200d6a038043e180c3e040d13400c82170100300203001030f007600c91b200c9071201c080b003101a1041c102a000801c43c00c50a01c28 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 793095611 1250 793094361 793094363
    0xb13090b0f031b1c0809010e0f0310020d0e03030412080606031e07090f0906050a0b1306110708011407080a1109130e030a0309170c0606040e01200a09080109 69
    0x7406142180100100400f580c038015a0340100c407482c02d0f11080d028900d084114070b4016010b01e600c0b2035461000600d540b0722140c10038810805082000155540491004020446d1500060350b0b440c941030820040c0c410b112101c20140004410081802600e03c020031465419946442c0503a40300380c10896640030680310b0144201c01e8034544014504c01909064110f242410442407643c0d0b00d982481604140f50050001180ca400c001c01c040d042280107074024000b0b407462982003528010014642c513609124802c1045002101c8064402c414408500940030100081c4100041641c0c4140354810582e485800039120301c0005c0c410300414440d410000200550311803602203e001040240310b45103484402c1959200390a4151a004200403d1007402649003c10f0b11580ca08003444a08840060118048001c0111a20840012400e260f0000c0d08480002c2ca2011007803c413801404901400070ba08042d0440507000c0031a030801400b540d00c43c0b60384141c0020380f0340b86031a09890020360 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 793096861 1250 793095611 793095613
    0x30103050715171305010c180801110702190e01060206192a11031903060803030c0a030f0b090711070602070e040209070e0618011b24060b13090b0f03 66
    0x1000107096100341400700d412080c0c5008113201286a502c529007194a010061404640340004019010311a00d80ca0401042c2000c001c1007890500d03015071050f4420390000070301c581003c14051510b031541140c400c01030030102620f05c0d102d684511002c0e540b040240da580d4007141140c01c0101400b0114015064008841034041100114840181e000d04d41e1900f4940144030005480d07010b0000100060510001c50000d0380810408130380000c3d040700c0441c0c01415250300108204001110a035084030340c100b000d8a000a04110201141c4004101340d0180303680c00030300075080c46810b51f0b0005050076609060f00550780307459031701c01050b030703032000a4401d01010005440015000d40344c18090a17500c5502c1d410003542d0744250f8000210349a0002902216060f441040e401803075a2003010a81d66003654556044c0c0e41c01e260f1100c05038491aa001802280014000d01d42c00c031105801400083c00035043c0c1e5601d81060501042c4207013071900440700b50b51b29111080e0024900781c07001960b03c543c050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 793098111 1250 793096861 793096877
    0x71403010b0906130509030f0d091103030a0504140402192006010f05010c1e0503030117010b01050f130e070504031b0509070807020109080a110c09010b1c0609060b030103050715 78
    0x10204d4806404000c1510080b8002031150b000d41301c42d10001050740d2408501c4c001240e038030300c2ca01a084600000c2003e07019520a001c0710500c0381e008001c44060300c6110300382c00344000b4071900140c00b92240c50072005400645a01c0c4692141d049004000f03440d0300a030345840788402e1045101d540740c2e0240b2070102002424042001954003d1519050160040241d03910175801c501c1740380300382d56180000f2a4550710000c0100090440d03030780c140c4098a00d100082c8100f514400000707209002e0540315906664002032600003030000c100c4c4450003080141407085c842e03d80301e280134000341c015120030344041c0808800300c2424070740d2a850005a03100100f20000341c0d02c03408400c503944000203102c20199036803a10003c001c202e03504041c04242455668903c500d5080f481418200080a410a030155100340014005004007000343d0700316070841d00c040c42034110130b00e0350200a013500c0c0d88041621490305101086120050001714140c0f80208110740d0119030701d035401d01003d0006010200029000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 793099361 1250 793098111 793098139
    0x815011407060207020a0f0e070201090209010e0705190302030a0f02030420060c0a20100c0b150d1104050112110402070804090f05010905091f0b040608071403010b0906 74
    0x48030140c41680d0080b040103003442c05a40c042201c007080c0f0f410020808411141c10030240f4054015190b011419100a00c0034000a9005c10f60b6000180107464001c211080028002e0740300b201078a0314296001e8002005030010800074009501c00e982c060740302c6050800203100c0219074003c4900455204954180a21000e03411030404400da8080c140d002208000c03030762500d0000c1141d5806c0e1ba00920001c500d51318180b502440d44110000b03003e01449606104030313801608040300c80034081d0048460b001554078140c070001c00032800f4810540c008007407549441880902c03c5410b05001042c0c0c3c0801c03081c1d8075503056142803804404024520080303003440c04202d05041e0080d0070f03058032651045080c29100d1120600f40ca00c003584c160b0f076042d0b45000401c9141402e016154100055001418080c0c0040c1b030110455031840c00c124100549420080489488a6106600401d2840c050b206c106889031145c0070300a2444000b640b0030360806001c1a06890321f541c2d09801001c0040401c0c00c50f040c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 793100611 1250 793099361 793099397
    0x509060919060822030503070e0102030412140f031312020301090b0106050c0c060a1706120a050a050c09071b1505090a02030105010e06030a140f070312081501 70
    0x40a039460350810070070560042504294200701d005000c880e2142c02c0e10b40b81202e85001c4038a1405890340c81d80f80080c0c2c020000c41c2e0040102e0350400e1252420400400908006034070f584035a0f8050111402c02080913014860800c1c021050200c5184c00d5520700d0031003200b596a280100e480341c0900c04034080c0300b04582d502c04c412605400d840600081140c9013142c07150400d04800361b03c0040401d04c000f5241c00b201c4814800304100c280c1c11940c6a003017140301032000705400c148410718034201c446140480d50a80d5907012070058a88000100c411061192a0658941e407020104450038415070400d940c2e20f2508448091240707030380355503041c2c98080390f441041250300c500c0c10540341c0c03140740e591520086900c2d000d000d2040b0f41c203600500191030184185030071600140c0c001200302d94984148270099401261406401e90400320f048140c0a8248160303040c5421141016264882c54500004014416052001c0e0020355100d10810b41e40d880c1c0c0220000100240840c00500340a68041044003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 793101861 1250 793100611 793100617
    0x121006140c010e10021b060709060c0515130c080d08191e0c0207050915190e0906040209060f0d03031a060c0a0203061003080a080a021611100906050906 67
    0x10400030541c5004a40e0f010300388119240442c0030580c0018502c00c0a088070464520401952401010706103018200100005410302908042184103c1a24240001040203095082c20170201c1925400c1404200e03039040950724080700d0010f001c510003d010b20011030991180502a10340140e03603581d06465000c82213082441c03420282d60340008001986145c14030070302d4114140e00004002220f444040c0c61710180d44d0125128010b407504001555403150100d26083c03509803a20300042c11044044004030600340c2210301c0140005080012058000800c82c1c0928000e0312108115200c03841480b0b00d10b50f4860303070140c100a10703000e0300c00080d10a611100d92a441c03000003041c0c0300b85400000d00294005904508a40c1c0b0030003c02083d450b00740720158000820740b1008861034916610069240690500e40e428003010300d0014610f800e0640443d00c103940d0240d02401114030918245000c1409c5c0780f0407501607489807044040a40c040c42343c440a43e070080e12240d052286007030812640758 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 793103111 1250 793101861 793101877
    0x9020c25090e1c0807120513031e021906020f0d02071101050c03031501030b1002010219020105100308030402060d0e0a20031506030a05150a0e0c280305100212100614 73
    0x4986c0c0840c058086200d0301c5068040c00c006000a05840d0305418020a50601c800c0140c81d0b58591a1060391031580025240080700c080c003407000c1c00a02d10341807040080c01404512141c2d23040000300f1540c00e00c1103900400b0201c1c46044107a11280c060801140c9a00400002e504298810130200c0c0031150480d04c2507020305030524000c580d208070240455800003100f9000005030790041400c5514807000c8850014010f018402002a0328002c000d80c40c122203a0f110152100300004041425529007000b00c460000d0680700a20881072000d0381c041c0d0f40c0c034140c0350944000861040c004549a0003411a1160703400007002040541007824202c41c0f8484054038091b0301d8852429001d00040090000c03c490701e4001c200314495140120119090320480300c250252030304074507584011a034854281a51680b03002c1d81090310100c4882922001944640016100c0d10801c001100000f040c0c0e0018480300100e03c40c554103684500030041145c10700b5010718000700b814032041d07034440c01c03049020303007110 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 793104361 1250 793103111 793103117
    0x129070b06091003150e0601150e01120e0610140a0e0a1805010e03040806250f120e03030a0c0507050a0204020a1404030b011401020a03080109020c25090e1c0807 71
    0x382d6600d9452200c001c4403400310a20841e102c1c91b242004c03010501c141801088840983e800f884207206004156000174081c50b41442000e080b440c00c0c829165014010422458040b921075040980070f144000465104d81003030980c41740030718001410000070301c0b400c503100f1102c0541036449840c108009084c801c0c0082090b103908085d05030114500340500d000c60f1f203d44015583d01c40c1011411424844001c03c03010310880c041d592401d00d8104000c0c4298044681d180180301003c0c90041141c21414250200500e142400e4200700c4100d00400194054810100208205504120306032210b010302807000d4260f4022021710805810590010511b02005140000845680c0c281010168019801c2911001e00c5500140030781d400b095070b0781484034400d0004141c0c22460f69002002c0a405004038440c00380c012a0030141c20720200035040240e8005083e0ba64810030188003181e54600c2e40c4189041c00d401e003541c0e03c0c007803100031410041e03100c550580140002c01c4500203403960200a40901d0030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 793105611 1250 793104361 793104391
    0x140d060c11030f03061801030510021e0a090e280c140d06080106050d210e040f0e010b01030608070b071104051e06120a02130906050129070b0609 64
    0x3003030700c240003d060042010340303d10b44a0070044c0a010502514510f0715012142840050010400014402c00a0034020b1005aa0f0b41c04010b81c00001d440008800c82e0103080124a40160540252590040e2030404101c001d15961746d8503c64009a4071980c4031803801c20007003803108414019004000769400c241481010303070014204040c420b60068203001d044954130300d014001e0441c02c3c029240100400c0741d40031141082a103410038800c80c1201030601042007004424400c7d4010b00400658000081040020702466440310014040620102c4665480c02c040806158041e110b134100741d4850100502c110f9003810145a010341c048001520b060545101d0390ac074907035403401403e200d80ca09807038000c2c001c4195000c90100b5503011342464419180703c85600b404050010f00c2d2424142c0490340a8040500704640070300400303180314050141814000085940c404955620344600f450301e850244d01022500c0b948058000e0030f90040c070201014011403480c1c50025509504180a05c0900700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 793106861 1250 793105611 793105637
    0xc0f0d060605150d060815060405040c080313051503090717070f0902040e0a14160c060e0604020a091103010611010e01051017010e031e070b150a140d060c 68
    0x403036000040c840f50341000000d210407000459006410003042c445004008062036403d01c0180d4103001000301e4000c507030700c900141c140702a0300c4081d00203003071003030540b81c0d520001061452200c04078000c49020341003000701203003008411801c591241c9503090207406118100040100c1da0743e260040c40500b13204180c0c010469607003810003071004280540780103070307500c0c50104401b4060400a000466161600d03070621003104140014552222540803068400748080c0381c291f0b03406441d5040580490310b014008011060000f6400303003c0c80c003c5540d076551a0744d40603075006541c0444c10216001506000402c45180683e1000c1800d5a90500218030348950305503840c21200304a541d007201b402e41a9040010701e1040700256085240c2c80000c0c090b10158500e169920f10851241003a1740c801b10100b40b1860b20070806031541c0e075034805003a0b6000e0401c1c0003170307041541c140b9510a209034615400000c1d50700781c02c43d04800501d4080c2a1915039a02d5448040003401d135070012005002e03400050300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 793108111 1250 793106861 793106869
    0x6130b04080607200a060b0d0b040c0e0f04120e010507050f060a06090b010203030c07030504080a05010b100306030f0213150905090106060305060312030c04050409060506030c030c0f0d060605 84
    0xc4040d00d034074001802145800c81c002800b030701d8070808100850f1140c8007488551480031406401443d085900441c0c1c080803c4081401980c07070500c060049000101070004105104402400302c0b001514000c0c5952108022703c2c29412041d1402030011141e2010510b4083c0569420001c07240c05050490074011030762580c9051034441184d031aa079401000401c40360100511821001d00f1400804000c0c0501c014000b039541e12010302070183c503101c08590941010703c10001c4401410010050710301d00030b500d00e841406040c1e43d0300400e11071211460351148091081c42010226900a07011541a28054003070100000c810343c040424941c441904403a58045400d034035008000c556800180e070320741906000e0843da80c540110301014108000e00402e5540022040d04034402c000e501355032074440c071842d802d80744215801140c016051040840030f111141d0f001c54400c010907810b55500131100020552502260004941e010781c42111004070350410505031501603108440000300b075520b483c002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 793109361 1250 793108111 793108117
    0x80118021902300a030b0a0f06121a1e0f09130b010e070905060a21061d16030c050c012a050301140d0203150103141203130206130b 58
    0x3000240c2e001d1051142a40d12180c6410f010007441c1803510b0246810a0840b18144104084141003507181c0811220607030751558401c004011480404800a94509015043c461100b002c450020305c0c082d54004031003140b042e40d01d51034800a01c00781c1441c0c0401e182d0444c010460b0401c5410841c48803541103643c0b184d60f0348070300a02c580c0951100f840c038280303080100343c603058201945841c50712080c40046a0011095000e50701302312307096929456000000c4500d001803a40308240709110240e4940f80c0b0320241d02c5a015107103081d00300151f1030503822418440350303000d40d410183d10f115021b6884010388642e01800340d03204149819031601040100c4682518840c602c94221900c4011038200e80c2002c041c1f5840c0e080f99070b410701900310742c905104040c600b640c420362a0700400003559800f0456505004080c00c1054948092045507124180310304000419180c4e01040d204841d40b51004d1450201660720550300403d04207240501ea50a1041d980c01503404541420380e84140821f01044003009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 793110611 1250 793109361 793109407
    0x4090602040807090b090604180506100f0602013809091b0d0f030c060608010c08100518150d0506040501020901020709180b091f1b020303060108011802 67
    0x150300e860030b010b401e60901c41c081d03102c291824648840000e094a4040f0f5065000350121130000e0302801c201060000c2e8036451794010031500401d02000f007000003880f400000d5480364044e0a9050f82c0380d82c000e900300d0ba4007041d0100c04a42c00304070340088001881c102c00114290040106a40c068100401e510340b805483c0801d15400ca0140e142d241d00a44000c00507400003111400c045d0301c9a610b50012070100c0d9200581000f1801e1135174000d002240c3c100c18020001480200b099103a991001030035644140c0390400b03034610403480001c20740f4100034115800b481c00780b800b0b42c00e0303103c2407501c001101989840070b401c0807019400c038000c14410700103540b20318081d800260381c0d4a9020002070a002c2d00c4d81056a040d441c207151300800458842c004100c2c42e80c0410b00d01040d17121082d200b4034041e540d0f103540c0f11040c031400d43d80103902e030213411061441800007a402e01402c9241416030320307400212071060024000320300420180403140e07058195200050030052804240060300d00540e006040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 793111861 1250 793110611 793110623
    0xc140708010905060412080c0a0302070615120c08012003061302070309061b0308010b0306030703020a290a050a0f050909181506030607050d1517070918080d02090409 73
    0x100303c20302507400444072280380b0526201f210b80c60409840c00d600d0143c0c0041100301580407802104111392070380080145101003a1403400c071036850512610030300200c4021115400341000c0003801400c1405a043c44421120602108218140142e0300d1904001d00b169031100126909a15501552009100c058020f6a5416556080140c060240e80c28406600c50f00311228204030f010079400034003141074540200886640b5100d001c0080c0c5801c600382c01c003035408045a600000c41442d2000600f542100c0700440d01c0203a5000030403076145004690340ca0000c11010419280c14920030220142040800e0902c1c600b4000c0f04000324000003000c8034041c9041d01001c900c042041c03000c120300129141041d61130001440c0c07174400701c2e4541c08060808028400c002c00c201c13410010b00d801c0703205124204039440102503500e00d20409140e0352460303801c00c1802031000c0402c1c42d03462800385000500240410039007041480da16541c00358008101d07141c02c107600780b1407481d05a945c0d01a181003980200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 793113111 1250 793111861 793111873
    0x80c100b060919030602040f170c01020a0b04230c10020a0506012105070b04051810030b0907080a0b0703050709080730050d0e0a05010801150203090613080d0504060c140708010905 79
    0x5801800300341c1e04900c9c3c00b5035102c60250110f0340e0b0b00084559401c0c2d80041d1115103900c40b45090b00810110480c060350360383c6111840000b02030009038041021104940b4158944c0040d9010ba898140700c0e2006031080d088840144007070820002e400c200c40d0940c0c440300812811035100c850402060350403400d071b030880c0004c0401803486d02580d5240d000340c0d86498501ca608200040c03c010400d5480010b0201070460001020024144002001401140c0958000600340d18182803d40307011100340c004a413404001c5441e2600c504885001c2d01c01784001014140e0411141102c42101c00ca180c0b43c0c21010300e1500210600450382c0c8040c9a8400c00c0203040381c94002c2e802402c4600c40c1d104560151501440812032607a005140c507044540e4089034000d10102c40404034254480c3d0040d0b0f0390400d00c002a614241070511021404171060101a914000d0030503000b2200c0d07204034800d25002801e0140c1d0403000c41c01418118034581080021118620385daa21001c0c29078078110700c242c1b1203070402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 793114361 1250 793113111 793113119
    0x6220506010906050c0309040c11010c1206151403090102040f03080a120e100e07031e1208060f10210c120207030f081e04080c100b060919030602040f 66
    0x4150b01d08040d000c14149141805503c0e816182e49008404043e41300e1610380d604d2517000d0b030040044036490b00e15100240314280180c3c1000e000c030040180004a000c1c5081c1c000141d495850081910030411541c61035801c40558a0856494001801c1c0380102e55003084000f40e520b01e00b1528000861148070260b803a0303084000090001174222084845d12410308400744040200810000c0102c55107000c00120000103c040320b18001c02d503040185140001c1202c111a46a0b40d960080b40d03c1c070900900100769111b0704120740807881502c034681c2102e003045000c801480c0c51408442280154074110910014400e8280c40070b52a8a5142070215a501840445940c0c082d000d04805600b6420940c586800e66400414456511089a042000000201e01440114910f4291442d40180e40171100e003481c2c01e00301c1140c1e00c19001380042c0d201d80030f100d400000460048044844008110508001c0010706120403000010307003a91050742c0b83e22012000903800e1028201420030b44003411700903410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 793115611 1250 793114361 793114367
    0x1306110403030801060e010f1e09090e010203180a0507120609060903081024200703051b0907120b040b060c0705040506120d03021614010b0907090b030408030622050601 74
    0xb8008007d0404c10400c6c020449150041142c2d07807000c40000000191003060f81c0d003110704000a8102d903d64604151400b03181140540140d0700038613007554502c42e111071020059540d46105e540060142d085200100040e0726080c060a06150154002080c44081aa9920708442c0040800ca0214070440b003400352113030300c591088000e0840c0004030003654003c1c1c4d0922040409214543d401c00c0a807010881c000c003440e14042600049403011030324419289c3c54800e80710001d12a80368000c203010005100b041c40c1080c1214080e98a546822680511154440c0047c002904815070440c0c0c0302d0802c001d454803143c00420442c04408007414185080104004c01c0d03960103815648560101c505602100001103480b41ca90740300f0b800c0069695540c680e581d0360031409030401400d66207240714403540e0030303506401c0303041c45400440302041c55a885c0702c1c0540e0100c0c114090307541500b2080c000500091022002140c01c110b005010480e540d5070b038104051a50800000e84c0c0f140c82d200e8040c880c01d560 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 793116861 1250 793115611 793115627
    0x2090d030903030818031603051b030717090d060b010e0a030f05010506010c03080a27060509070602030c0706030b040617030c070e07300f020a02061e130611040303080106 75
    0x207800c820740030042180e801702c26903c3c02030031292078000c4034042c801c0003014060001c840c07541c1d02912070301c4406041c104800761a074000c49803e03070310b003075000c01d001c681500d50030308954003140024181e001e04030f616160f0302c0041445c3c007d51810310401154425890f40c41c4899907000310b10038150041010040c0c50003500f5150003a069605206917031480c100001d801640c03007a409004004c1c001044c8a0b413900521041100c1c80414002542401c490000d00c010754200c00d111f5820f02c8111200e072551480d08903130300d00c00d103c40b000280d0070000b414410107200ea00b1480e51000010030203e402500e6040f440c1081d082080a0b40c0b042d0310008801180c0003041c00013000418000710030500310710308484003038110080c003074134110210040034820101d801c0110416001c1190f040c0d040004c1607800c0c0700c0310700070b43c01500420058032039000020a028907400714200541d59528003403090361030b4060105445a0f4015040345c0c0c40d5103d4814200358a0301030007510085000380d8440c0c6243d4502840500144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 793118111 1250 793116861 793116871
    0x7030c090e160303090501120f06090506030c01090f0504090804170309100903080306040e010207050a0c06110f030d05072705011b0b01050f150d0501150906021b010302090d0309030308 81
    0x10341d1400b0800c003080c3c004408500f00e03035007800c1c2080004411000c1500a25000394050a024607004020908004d6030348807a05c2610107404640c1d04440640054904d09000d10943d03040c0e1004450910440c1070039005422201e202e8100039060a48600303000f0300e0404084100151035202240b10300c41e42ca80100700c00c42ca0105402e200780c0850440e100d29855200080ca81c60007291075406aa000d84000d50480e502d16411405865900140c0d20f41130ac2401e001e4412040001e50320708980d900041c3c049034414180030300301c00540c50a45e0503c4290040d040042190082c0558609090619045c02188070314042800f5021f8072054200f400141c840e0f600c0e800c000e03050b120074000c15400207070008407090540744226044c1e200607114200141c084503800140902004000c1098940c0c0d10035a08089e05030340c3c0004602c01c42b00682c1c1011030b0303034245c18465400164495504010010085000740ca0ba4920614015240c0585140810380005c0444030440005050301410024107a200c61059044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 793119361 1250 793118111 793118143
    0x2060c01150314250306021308030a170907061d0f1503070201050a0e03090f06090d050c0a080307080a03180b040803270304181508031c1b0e0307030c090e 68
    0x813440c0001c0545411940002440540d00280c00c5280700c806030000c00061420341c007182e55820011600401864038140c0103400d581c00c6402080b40031001041010a0b03170990b40d81d103031410740741d03d202003044414030020540105451400018544a0404064020701c42e2801c407592800d08800c02401c40d0b0f0000c106c0c4034500e00e00208440d03222000700807145441c04c2112040005001340340094201d128003400e25a002d40601540800c22101061140101100b212600c1c3c01983c0d50441c542c880c41644401000c0e01410030050b040c0a00035031024010905940034074844c803900ba9145039298005840c04d6980ca5408400c0000144ea40c60596a00380244c41c44c90070f0b0b400030a40d24654030f0049015603040c0199076060880b00d00c4203079110b0390142d000035810244103a0b5410540303849a02c03040d0440344200ca80d00040403008564051060442e201c14032000d00c08008100c1110850810501507505008241c80000412082403c25001e44034907000010005200c41a06203407220481c3d000a00b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 793120611 1250 793119361 793119403
    0x21207180504061805070e1905030124030807060204050d08220509070509011b111305190b01030902100e0a09090c0504051f060e0a0803090d02060c01150314 69
    0x8006080c4c6502c0c0014440385002103116103134100251581824088030329003040340c40701c2c9003035003150002e840e0382200d4068000b04258411064881100007100400c0700c101c0c01480c80800000c0e150034000d1030b0030340c000c1000504054a1b000081c4102c0140441501c3c814008102c41d00f1404596244c5a060f404542c12210b14610f004041140d850008024000340040170401010b142d005500411250b52200c00807039040c403807403406003032065007414554000c9070041c45441ca01d140d544986030241c0030341c41010302c00645c41008007000d0012031281a04060b1039404040043e203a181802150913156150310344031000002c203001c06101242d120b06441800e00c1328550101e51002140c50a644003502d000c5400d07a540003440090724847e05031102c0720300c0c0c041000a4100c0d03000030711001120381203070110b281c10781d03a4210f142c0d039000f80a99150f00513045000761006107024002032022981d988001328113141a103032100001c603002d40c001d0b82c03458041c42c00d107140032f44203000c02d81116031181c034100a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 793121861 1250 793120611 793120619
    0x11032a1305071715030f010606030e0708033405010b0411090105030f130c0b0a0207050a0509190f020c1c0801030314030403030609020d0903030b01081b07020402120718050406 77
    0xa145112600031240e0300201148502c11640355201c0c4c108405400c8807154011801024005d00d01403040000091400c4110110808041840c004554a07400110304100144072405002c0c41080c0d10411410440a40d01c0b1440346000c040d0400f5078020000018100d070300806120039104490365070b2511400400031810181e8000040e40d820100310310100312a680c41030400d40c2465000700f006440300143e0040000c01c41c1e4840010042ca666130743c00d4500b01a500c0090051000c10350040729030144011000030110072541c0d46c00c6020615283d0041411030403041d18804a85c4551141c5c10642c0041c42c5100380b204030300d10012440b2540785401310302c941c0f4640300107160300c9400c5402700e807030314000010030240340c802d80000b0040c0101190841d0b03141c00c404c11500c01044076507000c4002c2818681e00d409158000c81056129043c82c141d42c94000c8120004102c00c0c0d03100481c100c0c0c1c8980e0a028040c4c001084840207480f03201151911030841c1607031165440203109079440140b0550501d0b800384 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 793123111 1250 793121861 793121867
    0x903031a15031801051801060b09100f020c10090303090506030906040803070e100c050f0d140903150c03010608090102040302030d110f0a2108010b0711032a130507 72
    0x41181c4289001d94480d2546054000407901001e4200015030078030043c03203401c44403c1610b03019002c01e10003c108036076a1300f507040240d000c1c800040764000580400e039480640112011307460300c40380e4410340c0c0c00c4441c02400501c3c1e41003800307003080001d105a42c2c14020584c2022600002d1700040310224158034140fa080b41da61000180002c0800302d001c000310782068010f03c1d60030480c55000b4a0340210b48440c41c401020600c1421098401e442400c0d1280c030413901c081900c1ca08191b140e40e0700b400d25038400e42079894070340c0000c07040c4d5010b100710301e401035045500080c0e9030300898039401d03c3c580d02d52608170002c1c0014409421a1020303481000104016a00040c4071080c0c0034882c2006081c05001c1e282c22410045d9004406889002c4c03500c80100700f01c10f043c1a004034981c00003d041e042c0b500300004641c403090034043c03003411180400030400030404110b81c207504100000c045414a90410245502c02d890000014900201080c14961039280001c002010036080300010002460408801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 793124361 1250 793123111 793123129
    0x515030303011503111c0f14071e11030c06010503071d06010804030309020310060509070e0d080304050304080f07180903050d09110a23030606210712060903031a 71
    0x2402e050f0f0300d14001c0d209401500c15155103204500c1c2e00048076106d0b62138140074120311011200c0c0c6524109142c158102102c400354010090b60f0b4400342e01d0740104810400c03c1074610390347c405028401c2c441d44200d040402c010004140103202030041c40d40350500303252910030141c000039010504c04400d46000200045242d9000d082441c200510f03440d1414154010001140041c0d01401804c00d4440d1590094000031b0441d241030382d4805040d65000802c4424081c400c98003944012070341e4801700403c07030350400703990418041ea003560720f01640c0700720440c5808801425042c9030341080104110050308107058110020a00390180700313084490707800030114410700205118032507841d1809028848654004980c440001e01410a06926450104400901c43c000c2c00ca540f054403c00300034908001c00c1103401454050030f11b00c0001d1003101c001500c81280081c809a51054a50008008000c04003401420380503910005510307019040042c01d80300401c0482c0b15940c0d42d280040c91585550440c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 793125611 1250 793124361 793124399
    0xb0a0903120804020907080c130303020606100306080d030504050f0a050f06011d06060310050909010914151b090d0b01090c0201270c121103060a051b09040e10051503030301 76
    0x34407d00d0b0796401042419001e0300285910125010343c0100402d500024500d004031011650061a1620b10400302c0c01d0fa0258080c0403081e40002a41d140880d00079040103801c1485002550503901d07200b41802d107010503105055a10fa8082c00c40d01c10008828445180508801c5010341044502d20580489042c0c014043d64011600000010002e600302080344002d040300038060300070780c01c2c018001da000c0d09000009454280300e180e160006100d00240303140c0d0044a441c800300301995110302099400e4002009004001400c00c05001c040c5d03903202e2800c031010702c80d4182c00403a504040601c000c484004020b281903a2414090031061009850180c100354480320104011312020318058490000070b900a031064007100500e00704010310b860035003e68000541c01c40c0c0b030304e5850348012002d0356420b440101050030002090b180403800b0130014001c0f9000600301041c504207500b0042e103010442542c14003c2d9070307290305000b80800000420004078804500440c150b5061110042510001a80c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 793126861 1250 793125611 793125617
    0x20030a02032220180c040503010c05130605030c07050f031c090c0b03060a0305100e0c0d20220e060703110d020309150406020408071211190b0a0903120804020907 71
    0x105801080d80c40700403404d0340a442d206911480e0600c01000c43d1940c109004c1d86200354200001c0840061085045c0d2300c078140144501c1c80078901d841c100390f40d81d50001e0000141a0400c00be000003255080000c80c0c42104c0782030007180d0758507900560400700003000c003e1060b99400d0103041710200d000d0a001806840001da0010b6403900c503040080c04590030742e07000a00d140908240b81181d0300050303009500044050301521004045041000504802035000500d0500300d00c8014030b448400f02040003800348050020440700304003107941c2e003507050005099003469407901000c1c14080070a008850b00021917050500c031001d04445899a00c0c0940420100c615502100040c0a100708000000c80b46c00710380b040004504003800c0101c00b96205028070101c41c0310384400040c2049081c2080b114880c0c10544400d60021908100000c03882c05a08407141980d0b42d500129010031800c3c000c009551083d220504002d1551516100d0070030449034140a00140104000c0540c440004d42075001d042d40c9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 793128111 1250 793126861 793126913
    0xd0509060d05060609041a1212030a0b040605061c06090501060e0103091e08031605090607080903011b1205060303120c130305060f04060513030f0320030a020322 71
    0x1c010030024041c04281300d80c0107040147ca001d00405041407041803c00c2540c1e0760000200300c0d0300340ca550341190410312a44000800009803c989564098284160010008a019a6541c000030066086110311200140c11940c0781402800244034240080000003404d00056150100103050101520001414552117442840400c2001c074210070080c0105008240030321094248a01c068008440740c007031007145140b4140380c2c580030740240c0e00c100303034014090f41c0f41c10b41d66660032243da000200703103c0c1c1540d228000500380c84022820b036020140c142e507036404408081045142601c40207451940660010400c500c140c56070388402c168440c9840300401d81c1c4004035142c3c103812000b42da20291150048a084c02840320521041c1d03401140220021700003a1620208001808034a15004003c24090042008407070b00a07003050000c2414242c0419640350390003203c0701e45600450b52110401d40c00810000811071041590040d0013000134084c19500c926075502511908000034030325161402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 793129361 1250 793128111 793128121
    0xb07030b0d020a180212010909140a05070303050a11120306180f06060913062c07020706120b04020309010905060c030c0f0912030a03051501020d05120c0403080c0604050d0509060d05 80
    0x80e4040b00c00451b0745001c0d04040d5a50358900a0090810100c101c444151101103035011180020b00740f061160440041d010b224035658085c0c80c0b940c081002c0c9000e00012846100040710203001e51800910984409582e03031500804102c443c580c0c4040515004000b24180b110b03521500809660201080d60000ea0b104250700026191540b505001c001c120300f88080031076880d454100d11100e07016210b413800403002a025030f214500c1404c8400f480180d100740740802c8407a1268204440c0c440c3d201100149818208010a09a0784110342c8074030580c4d110304950007000820001d8a0b4000702060102d070860600881400461249080740004101c01141e1b02c60259588089100f4605c0003104480d5180443c48014015100440300580910101c24401c155540003180b08030076440c40d0f0b0b03109881d04210464000f20100050080a08080184004000254208000c14a158858004000a1a1a14185161210b5000000c080040034444503449403107006c1940c00700e51091202107001c0d40c80b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 793130611 1250 793129361 793129409
    0x1e031a040c051201090b0a27050a020c15010512030903100c0210050103150605030d050706020c0f07080616051c021602151209060603030306120c04020301030b07030b0d020a 76
    0x11501030f4039040110000000f8501401d40c002e441a06040d0352400703010340e0b1100000d08060034681010000d00070740e0750141d443c038500c1e0b100e02d5002d028040010300b042c1d10880d4070b41c40d03e480b44041041001c000f1006008618103d440c0540414180b4025403600c402c0300003180d22440070701680a095915101f5800c2d445000380681c00c0078076050003041101c4d6940b410b00c080700e00c280c2100d8520041c40d00002059504012900c1c10350000d10b40ca0f414580700455a5140c025849680240c98500466080150b10318040c0030b0f820040000400030300c0d40d41490724030303604401c0046080505100041100c001d21000e1542110100180341000584800c041d4007c040c0810401c1c8000b980003807030701c08070240e100d81000501250100d050f4628050703980e01c0342084d40c890040e10155030550041c40060040e281a10341ca10032500c40800303445441c2d03001c0010806980013a0012100d1107580f00802048503498481c0500b074580460b405118482146c011828884240c0102c00242c405080c1d40401e40714 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 793131861 1250 793130611 793130617
    0x40f05090901230105040b09040503090f0a120b060901090501080a0204110c0708032106130c020a061a1002150a0c02030408070305010c031d0d050a1e1e031a040c05 72
    0x20264002203d52200311100d020465000d0003814851407400c00d6120281c01c013090280d1107a51b02c00011841c1660f000108000d10a140040341e9010140c9003022981c4220342820036002480391214a00c1403c011080004802d016003150305445d15040040111340b5000500340704c0d007501681e000481400c84120740305144142111200c85201d44c5000082e20300c0c00000501846125031101c1c5400d80e9401c080e101e02d69426140240d00c420b625000b80442000d941c40400718045134011240c0115050b60341e102910403401c00c001800303400305048801400c0c0550308055582c040d10162603040a20b0303104440ca04000f500001c4c0840d910441d042216000b0000c40d00902100320840703c446540e86801c0340607140d4990220006410100380102240002d40308084006a08028101c0c1c1c4140d410126103903040032015100300020801c5e40c03000c0e0500750485040c5044680d5409100c9500102e0140c0f1a200c403035004000c0501c0c001c1410300c41d401d65000c02030a02c10444012406205480080351940 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 793133111 1250 793131861 793131881
    0x201051303061e0f0e060406020904090b130c12030c3c050717070605031b0409140912071b03120f0216061d040e011104060e0303040f05090901 63
    0x2601c0e02c4080301c0c0100380004100c1e8081c4403042c09101c0a1601e810139020f550490902d203a0390382c0507401140028400350046e00c0140005000060145030b41c0d120441500300a90f0f1a40c00c1d031210006040600c40004403010190040400505a18000e03a400402010720f00c0c0020b040303d0001c0c258000b00a4403111444d84080800204018101c842c0e00e192020140340703001151a0302c951503000074415024612648013250113005011400e24115003a41c1c640d0004014002c1003c100c20038009030390141c40580050040302000007280588041c440800007005410702c42c00d035000c40360042041c040c1d50f0072280c450381c0c8038082c20041e0300b2900d99a05c15502c540c0009010070b10301d0f803c00c05180d60040b07690030000c109900301c40407142c0f010ba007008908804c1c000c40001038130017000001d041c0d0b030446410001c940080c0000410b04c41008034903007101c0c40c89500003040030000030100685540545100390700d4004401a5141c82e03e002120f440c000190700c25180600059000a80303480420341c8012181 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 793134361 1250 793133111 793133123
    0x10e03251a01261209100504050406091d070506180f04020a05070c120b0c0f09030a2a0b07230f060403170415052706040b0c070804030201051303 64
    0x5961900d0f101d0a10070012091480000301d00451030000300000580c58070408481c40749180b40001c41703c1880a4440640d1750b450a1010070080040c09456078801c000050401e04000696000c0002e080e000010001c400d04c501a4000c00c02400966a00d800721090310f10703400020310746a042e00d07011410030107501030030790fa02600c00701e21481e0705c54000005044030340c400c821000c017058550280e601085420103014110110354400154014058001010701d0040101c0c82410104104000f91a0100c194400c49104184240810b88140440030008100303990114452459040c0805007440d402080b2005c2d000340010341c1c0901d6114000200c0c07040801d0b07280165031014844440040d40c0d4102a2000c80004543c4040c3da0710400400c0c40131401540d105500c240d8003107030440300d500a0701c40640b40203c00500080c10700340000605200c180007404200281c907840c03825042903400020b004281d114491420403c400003d8804000c40b004d4a60900f070594030741d0440740e2000680070300da030402059 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 793135611 1250 793134361 793134413
    0x504080c010e0307170a0c05030a02070e010b09011403070324030308010b0304080a1103090a06030e100902030d0f0311030a020702031221060d0c0b0c010e0325 70
    0x500001100410400410030000c0c0040201120120740c0c078414200c010b0406a501c0d0010980600a0002462010030398903012540f0400c41e1216070039940b150003003d02580c800007007000109240b000a900505c1c041c0109030a01d41080006040041030210610301140c8c000009080310f4003c0d0f01203007290404186285596142c42450140700b44140401c5d00451150000003500401c8401201d11450388041c41906024000a0503605044a04415030b00d9001c2848121015211f0381c050300020050380d0340200d440a03003a41304908244c2d80452800c51141040e40c0315015072000250254030700c14502c1c1c0030761000c05a03081103005218200b001140002e0000c280600c0f49510f0b00a020340c14021019180355910810b904101c1d48114003412100000700e000345200704214001d090341c450700280942c2c0c40030215598504440700070380c001c4410035001048191a8080034840d40ba406001c0728003c43ca0305c00480c01417144c10b01050105e10100400100c010100001840300e184004048120450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 793136861 1250 793135611 793135613
    0x915030921050c100c1403130b090106091b02071502071203170f011a0c030d02040915060908030d0908210a2003010302090919150501090c020705130f0504 68
    0x10441e400003901c903440d441035403407110452000c2e04c20001e4602c4036403580300b81d00054011b101c05c2a04001d0071420041001d449030408600c00310032880c03081c0f81c00c000000b032103420403540d5000c6441c0418007203200714409200c040447e07000035408080d20440030107081e5220320400200d183c40c445400007852100b1805056080603000442007600902281205d140c0c0d40d078400130340007018824440c01640c0018103120103070b1070007a9001080d80d0304810060700d18115038030404005990242c3e0208184a9036034103100b030180328811162014003505d180030442d00340340c07101c01a038901501c800c5491407a91046010100010441140c00d0400c1c0700c601034051005c0d04002d64800001120038800700350404c0480c0324114981c000c034444220070f10b00103c2c00c40c1d0840c0c003400961a8010030b6000d45110b8550640c0e40001c03482003102c200e905c0b846401c1c0e980c51a071076451041e110107900000000c2c4c00c1c060459042c0c0d4000c2410070581d141507440d03114201c1b21000d01d034082d114030400584d0307061410781480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 793138111 1250 793136861 793136867
    0x61e0e0d110712030c030f0201050601120b010c1407050901120308041113090c050406090209032a06040305100c0516260a050324090f0910021c0605010915030921 71
    0xf10745e003802a01ea8001d581101a0140d081c1c52080ba0703040d0016400c10302c00c441060069209040c02c40043c582045022070607950051001100701000405130701c2510f0801c4189810405940502061504411400303400d075000b8040c1d0030041c100030800c0340840380c13000140d01d038881152020008248240011404c1e0304110a45074002e0003401e0040c2d081c0100483e541d4018003c5030b4291030050001d25444500c1c284506000541854041080070f01407041c042641da072901400195004030301a00107204c0100359141181c284608500a205e000d02c070a500a80c2140d01d000c100c0c035000404c40d8848070301041203950062007401c070191000b07404540304112590040c05140b258140e850381c0000c2c401c0840b120561400c03240407590340603191000103181d80d900382c00c05641141080040b18010705070703e80454241d800000c8141d00365128024030102b500d9050147d40f00410081c2040701100d42071004006c00150b0039041d550a041d141d424030006c008000c20120091040702da4100c1907030000708801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 793139361 1250 793138111 793138127
    0x303090609110a08030a02100f020d020a2105040803070302070516060207030b09010608030306010c030302160f060f0b0306070c081b071a09131e09061e0e0d11071203 73
    0x2d280a80f520341c8002c1000305000088460400d1150020f1140c0124041c0a43c0a80142404d242c0950713000c0c03100714104002400036210040154444084089003007403081404250001c40d00a07283c200814440031440d1001200d03000500380c078016075608660f0038031510f041044002a1070142e01100001280755001c141441541d1299031103c204da22181542400d8030468051144903030400c00c0070030295030203a488190018807070309026041c020909046103250505260548006020070203480802a0602c189200c00c01c00c80c0742004103014200100e90f580900030321140c1806040280034003402888411380b210700c12291003a54200c05000d510030340b600c1007881230383c0f039100c00e1080d400e400d01e01010642d944442e02604042c1c05e0302c0b00341020809448200c984031119121142e9612840301e6174011254114040e020200f50b01e01203800358070f2144000901f42c2c11a0f840c106007078441041c04192604a22007a16007500301d4130503440414100080d41e4001042801441c5000080503005608 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 793140611 1250 793139361 793139393
    0x8070c03050606120a5f0d0c020103110f0310060f02030406021b270105010e030708070b1803100f0b04090503070f03120c050909010b040b12040303090609 68
    0x4141d00304c3c1e508070740540c0d290301400c0000c10381c0c10f8a4201480042e030300c00c040e60b8203003c00103940140b160048000e800811421b003a84004c03001c000e80c40c0c09058101d00420100ca1a0b8400605400b086090024084844180024105610340d0100c540000018080e21070403207100041580c0c0e41002686000c0e90342d680d10800c00400c401c2040700c09040c1c004000d8030200e41807a00074180640c0f00f9213100305190710803000700d41d03c0301415030b2001c0800c0b400c255034240700d83e501502c80d8865051100160289840c040030901c20740c071a410034130a00d103000c11942c0c115400401c09070b071103c031a004644140354400d50f0881c2c240c414408107003220f0f5100e410416424825071020400d0003e51000e1105a80044c400078003e03500400001c0300050010b102c15034200d010b4944650b0b00c00d07000c0da0000c15142c01c480b101000920208262a140c41c089507001d0043c8616202d00b0f1901c1d20b40000501c0500030a0a038084c50002540010145400790300144031071544500304200403212484c2100c0101b0b03100304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 793141861 1250 793140611 793140619
    0x14010204150201091101080c0307081906090c021005102606090615040b010903021207031e031815050a120c17090f120c0109080c0d02100c05070f08070c03050606 71
    0x82d4801c1c5e5501803015540107402d800034551841d5640c0790195594107000d0080100900d45c46050040c008440c41400098051250045104800420f00900d44612051170050741d07854802072000122840d4004012101c00712005c40c28011081084140401d400c81c0344651402140204201260301180d020300c258120300c07012069403c044203010450308081c00ba0703408200050414000751805465006004045a0403100e1440c0c8981e0381e428802c001c0c294000342c0c400354546420030160130011940102000e21101011070703180c9400022040740d8000d041051210000c0c03400c803401d100d9401070381280c0038889c061142010280c0010134000402510784819201c80380807503222200818850454010000240000c040c0f00e4000e0a2545c403034003c4242e603640e103d1509000643c00d5014050400111001d03000c1c00345109030203420520480114420306182c0081c49030303010381241c2558000d81c0c110001008060061814613000d100340311029011040c91140081004000100e252003050166 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 793143111 1250 793141861 793141883
    0x6050306130b1315110d0b06070c05100513180b0303030603060a11040302031c031b020a08030406140a1a030a0206040b0c071502100507090509041401020415020109 72
    0x400e4192004030200c40c0180400780540220780c412101281000800d40103940034a101d051081204040ba8001000304008a801044411000c200c0e0f11030a071f03140b00c040d1111031900c4180e545032104800036018951103031070310564620006104030b058584140c06203801544aa494421454250402280d140c0b80d4070b04140d5004c00303c1c01c1c0442900c0c0a90000740041c010f5031600346580025050307118682044400a2000002503a4100b14034109150f01713900003041441c500d80c000301500c03100c1c40d81c41030120100b80c1c40210340da0b0006070305070f44d950420318543c2c513a100c41c13900c8000b8103602000041c0c8200c0220511010204550040c16200d445142c400010001d0340c0616031129200700c0041e40c00041800100a80b2031500c1c014507840b00f200d0162091103440b243c01614040c081c020b090b00692020005102820070b034800d071600f040d0103050580700c3c5490700700003611480c40100f0080030044e0a01001c0403d12003501660007500035074038102207820380070340028003d00680070300340c5010b4055 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 793144361 1250 793143111 793143121
    0x602150604021801110309031005012c040809010c2001020f0f1f0f0c0908010f0605060306011227110901030c050d0309030c0e06131a0f0303040509010906050306 71
    0x42c4200e800c807901d140d0004a001c04110010344032842c3e901c005201e90b0004001004896605110b070150804500c030002420394105590078100540c0081c0d490402c100c2042928440b0a40c41c1d411a4041d0b4401503040c2c1e10704100300100c4040808100040007103a011021641d14002e180b0120304892003a822524200c0030841d0007a80c866851400d04542e402000c3d0f110383d07040e444903030f83e0303100700c0200004601c08100540755002c60301242060030000b1258030040c080d844080c05402c10b0060f0460050002c10300f4000021818880900f0041c1801226600d400d85040340d030b0400549521500304880e04110782d05088108017114600495000d4400100d80c0324505d0300140d882c1c1a26000101c4141d41401e100621040d041913034015418030020820000c0092000296040a0450000b0035181e070b061440a000c1e90107681c0400c0d40169041440c2d682c00c041d0301c2400d00070351410440c0c1c440c40c150f02403004607056124035044036420989200c00814a43d0042e0030041c1151016001c9070015556 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 793145611 1250 793144361 793144369
    0x902070605100e061507080f04031203060b09090a090203071401030e241e0703090c080a031d01050918042a0e070908030a23040f090c0201110406021506 67
    0x1d034002c980c01283d505012488a0820000c0785403001040c0c092186400e89a0b280c00c2c0954020034014164090005030600c100803c6062604110082d0b040c10303c00d0ac0d08100e14030000340030360311405010700b84150008024002680252048a80103001c0d50300c203544030300c459003040c4c0d466071840d07011070b0a01018003507050000815020840c02d0f400e0070700d8040b90301030381802040303805001040301e08031080400041d0391031825414007800d03060300c00003514500391401c0012601d26902aa0f501c5d0070000054011907080880083c0030b00320b940c44c1a0a0340301da00c1c010707075440c003030021299042408071110480e407503c50b024550007a809000322060b03000c40d0804503094824214051542d00d00445c404002032040040310907089480341c14200441500c1e0207049182da08440862400a440044032804c084500b01510f40c0002c0300d009624901420002e10700c0c040f440358820414000c1e0b8131280c99105900c00c0d8446105000c40140b0b10341d40e1a940d110003036407800d034042650b444151220100d03505140c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 793146861 1250 793145611 793145641
    0x6050a12020d020f03071e05010210140610140a0324060c08090a0b03191b140706020405040618060605120604150902190908120f0d0f060902070605 65
    0x160080c180c60340b007102942444402d00c03400c40d003241c0501c1004404a400307005000e0100381f101010080c00d03460f0b494100024540b44483e904081c1d001d14040103038000111540b030782544000300f66007a04400000b0401100c041841d0a051004448085a02c10b1140d505800503218030f1284019200d200c800c40d007541000480c0c0388035440108014041020004800f0406002d500d6802803039490f403e581c541032081c0e940d000b22900310201410080032085031507036100d211000310383d2907400102c00d0360030480900074044480c800050400085968802c106098040b1409020090414440c02e81e5903202511003c0c0300300203207140107040507070209902d0301c92419200552040c8180c84180c1d12100709003c01090020805400031003500804542c484040c0008c000000d10341c1c1d502049809104030040515209400c8242035421080c107500300c1502e8881518901d601c81540280d48001c1e02070014010010808503141b91030801500260300042039001e0050103010341c1041c040ca0351500a0045515 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 793148111 1250 793146861 793146863
    0xc0e2a0a18050120150c0307030f0501061209050c030d0903020a06050f19020307061d0c1c08220305102414010201140f18120a0810030f050106050a12 66
    0x3552541000044a90811100c0040380c03844d0203940c0b04005e2040e11036004402254803407110000001400f1a881d8903100e168000326501c1410880f07941000d0000f0040c05605850186480c7c84000710000d001c010700c480c40781d42c10001c04035903140c856040040c01c014030741e1100f68440c46105c08001000e600a004075040a840310144500c0d05100706110000c10242c600c1260442c4001e0103c0d1001400c4d611070413604509080c40c0c882410320025041c2d1a007907030803504074051200e0150600813101e07680c00c03000341c081d442101d00380c0b03d1802c070100c6101c9900051074800d02c400c2c0300c00d0000038041c02241d0000003040502c0c0520841c65040740409000080205051040702c4c0c80d402006285034404c4921012041480041a9109425400480c000094810305072021000060203c0b504002c000450561540b8002e844d040348c84103500010341c010f200c80d200030701412500045000707001c450380340061070344881e44400118190424500804041c0030705409108629004100140040b150130552 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 793149361 1250 793148111 793148117
    0x906021204051e0907030522020d0f03140a11060106090302030307120216081e121803030708040603050a0e01150b0d0b030d170708040c0e2a0a180501 66
    0xa140c0b000b4441e6079000c610100e00c98140501022080d540d444691601404883c1d80102e200c1c00c0c810013401040c21280400284112644481001a217600384004000e603003150407040031250504056070054a100c1110079106400500c550f030041d041407103c1003400d803010480301c40340e0300c0310003c1e2441d00440c00040e505074014400240025511802c01e081e00c2480d00c1030b1500500b070b00d225030706228000d8000441a40207041510000d100340c440d10b40340b89440d82c0050011160712a4101d200b849214501120844400c81c2c00395a5101003003102c1945900c559925a650380c0c07020020010401900c0c5080590709001403216040f905014101064008003541d80084d071810440d20504c1d4824000391007001d480d08180c540760343d01840f803002142c1603511600030303464411803000c0d954900100380d4420703c81c1c050305220105021000e108181c42044d009000705803111800d5a503601160703407081c40c2c9031700d902c0100c205641d40403016001002c15500c504d800e030700c0074170b1a000c2d003c00980500303400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 793150611 1250 793149361 793149367
    0x80a0305040b03180f070924051306030b0c2503080106051b0a1b1d04021005120103120f1707210501120c0b0705060609070512010e060109060212 64
    0x140c1c0007039000568011340c0c40c010654801002c0d01d140c40c00c0200c4d00c04d443d0319a41114504014413006030041082e041c20039160740b00b0303200300703203a9080c1e800400c0d00039103004030707291881c0503000c45030341d03100b40040c542000305e40609140941240703940341e0010707620b00b1510700513540703a161002450001030f1075503030715403503843c1160b00b0008111481e8100d95004156104121807101041400344001e650300341c01003640d12010103c45041c00417030004c030f03803040d03040110000011500b1400380a0058016504135034105118022083c200c1c0c40380180080040c050801c5c00c0000108040041641c0b56008142c83e101d00c1c1142100c1d00f42c6182224801c0f20103807a1100d0005041c00c0d11a80041b0a02c0d0307003c0c81176481641101d8124002c0b02d40c00d0300149041c8511541e0790303044c8a08a92001e008260036200d1a02e0101c01d40c2d280c980f101e00c06810b0f1400390302d121010540d041d00034804d607012a80c004104014070b6035107003a0780c51140f200b80d9000380810b000010220307010b8030109401d048018640c400c90320b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 793151861 1250 793150611 793150619
    0x1b01020c0d03150b0708030406151203030f020d020c070e0a11070609020135060a06020a23101d0d02060408130312020606041a130b0a0e090a050601080a030504 70
    0x30161140f0044181c090001c4400420010304400c040d041c3c079802512010749914003071078a041100c4c1c050520101e00b000381c4a08200203484450030070000c960514000c94045809080b04d006030040c0503010304e001c2d001041122000b4000680c40c0115140d103058862035481e0341c1c1024046a803031817180161411300700140c030040b40d9240c00c60504148103241c81c50b21068461121a040811511845040c500b030b004d45540e28881c0806040e00103008650940030704e890203c000c0c5d603402090700c00600b0b1034101b40f26400748151110341030188900010903600090b2100c01e102008107800c00c030307a44e002051111050000d50001035024070601c425001001242c07266191001c10b5000040c8855040d143d9080203c00991618490703440303c2034940003450641401d20401080c2c40009210b030107050300c900d100704010b40e591903000607821010600060740300240c2c0003042200e481074000c010b40405113000d0103a04000051080c08040c0220150350300c60341c80b82001e40e103e10700000f014000500a002c280 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 793153111 1250 793151861 793151867
    0x19050f070605060303040b0f032a0703031e0e0a0515040807030819090b0f06010201050421020a05160e25050c010b030a030f1106090d0c080c0a081b01020c0d 69
    0x16000f01004046904090340c814200c042680320410600c08003c0101c00c0c000b40046480d06814151a03088401c880e5059200507004c039401500c3c0c000e8101074640344d40002005901c2441c12202a40a6090004c004240701c681e60780c144528080b28144160000c100ea040c00108165006503807003401203213810801d0303d04680c4d070071020b0007829552402c00394070051040030384038543c21680300700c840b83c502e45000c107010022004028055815039040404103c0001d10340741c080c109050324030903100381085102400302d00c0c1c41102c00f001401441042c2603240b01c01c01c84000c5004030344101e88008980d648e801c2500b4060894500180301c2c81502c00b0f001c1c01e4550107000540b1041d16104000281480c4050000e032502e0309211040c2e0104408034081e41c640e5511803030410009059000400860400e50540c0d5580c1d8003000c03034802001a03140380c5104009403007040303036450800031003110341101c02c03401e152a03658405100307007090401c50300e810021100d06009440b124403903a0040e140c0c0001d046025 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 793154361 1250 793153111 793153121
    0x90f01110a080c0417011e0e0c1c050708031305060a1b0602120f070212090a3623150f12030c0c041409030319020909040819050f0706 59
    0x1c491418000e02020454811180c5010320b01c1442ca4000b0903581f41d100030807802180c0041c4440900c5040450000c0840400141511460000d58841d2480b044156881d050342c445075030010f04500071208000b49103200040900b40394901c880803100303007a07503031700c100002031103000210404103e9500a0b0240c9652607200520901d00801004d454119100e115409808003140c096401c03000030814030003050b40c1001407204c0940b80c1000245445602030024804dc0c02d14402c0e50042c40c1986840c4c821b0702d00c000002c9403403840f1070361400217603501c40007900068000c80da000040007040d108600000d008203c03a05000f074004a422800c41c1300040d05100300c9003104085079070070442c0119184240b074020030080c01d40010450280040d0030380340c000c100aa80d80440080f05000f0342000303110703440c54080110f030740007210340200243c50744001c0105d0f00a409100000e0b80e000800a04100030b10030344500030015000002d00c0207600c000007190680d900e004e0000c600085120901c14034000402035401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 793155611 1250 793154361 793154371
    0x200114251803120f030605060c100e030904140106080c040614030403020a020604150305130206040b070c08010c11010f0c1d0609031b03060c070201050706090f1406090f01110a08 78
    0x80740040648a03102d810040011680100004007001001551306038075220f0040545030441c0c03a9850020300f0b0391340603500e00e003000d07a0b0071460b9590000301807a203504000721203034078030054420300081d08444803d200e550710910500001c500c1c1c0d1000680c441a40d8011501078848a40310046035100f0001a03010540000304220154881c0351480c1025135181e1b0003400040540c1da0001801d1602c21720000c1c1a07a5010740300005c086500c0c0b01407001030f902e44003604c0903070b85141c001607104d02490410300c104540940c030080c665441c11b0110490190f006074a08003d010744002800070341280750440003100c0c1440074820004c3ca080200d900104200d0400d0300803c20011f21090900074000002030501514090110380d220344a88502c000341420b20941e41d120fa48a0311903410810207400107071285c4078014004029558503100d2a04125102c0c0c4620802c030740150b104090040007010b619500e10041d238100b480c6202d222518a4261014001d400e00c0d0709900300003504084ea01041910303503030381c0640 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 793156861 1250 793155611 793155647
    0x20d08070f0807180305070504061a0f130f0906051c03210e030d050403031413020103050402040204090f0510120f1203060b181302030105090f040320011425 69
    0x3c0c08419000c1044e2400003d1030003040507111745860007041108803045644400030841142c0900c0c0c8140f0818010b643e803a48603041d00c1a55050b10302c88150703150109400c034415412400d00041190072081d4450015030b50150b9031074249095283c10000d5041d03600c84010001200090003080440340780c10566046d55110304085812960309499604640208805030107241d6100100814107038076000b0440d0f0b6505981d0024458106810a070001e480e2080e00030307041c580c0b01c601245c1151500e60489009191144003000800d45240c0341d140541401c2d02c500c19408074101000c503401101901004400350b11485107a09643d0a036940c2003030540d540e02100901d42c1d03820b0005021140100103000b0b8501d11002c200400b05100100101c44050300505c500c0e191040c0014461303a101da95005820140e8400300e038016a6461038100c1c1c5150524004404002d100764a100b04104150088580c0080719002c00610360b48401c40554500c003204200e60803000020f5040044501501c007510500407285 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 793158111 1250 793156861 793156877
    0x3306080a1a012109060b09060619030507140315090f0618060f090c040e0708150d05010b06042909060a0c0f0b180c03060105031b0112110901020d08070f0807 69
    0x4500242240c4460b0010740b81551206d400ca00305140c1a01c005510083c00c5444074102469003040b203118a5071403080e46d040c0365a84000c922400d00800148500340d002d100c150390350f850813100c954030364450061a503010384010004102e56080400b01107100c0c0b08c000d420f40025504c000444000d82030058205500019545078081440d2900e95410b40300d100d0725114070303545603d800e46091150100501c410100720705401403040042c2c4c03d030904001181c04a55140a03849241810341c0140340c10400c1d41d034807210026000032002c552601c0321040c101d662a071428100040240f640d5180300e61039413158014001c21074034017044e00030102000c001e4042c2050381e41515403580c85012054054840403013941d18074003518042d9030300f0001000369207400d038050031403945401e022960712400f68210288a078441741c000545a403081c512900401c150031002d01c02d544240200303200d294440c2a4030360050080064480c3d819003ea00343c507004101d20343d50341040704081001242c11a0b00035102c441003010300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 793159361 1250 793158111 793158167
    0x10e101d0a0f09052202090403050c160f06090f12080f0f16110f01020c040c0e0a09020705070b03070c0f0201030216110406081603063306080a1a01 65
    0xb25201c2001e06841000080c050801c080c14205411005810940540180c0400401606c0d40c44000d41c110358503062640d211050b0050f5541012441400d0549440e02880000b5801410074460b8003110125140c02503403503210304140e00f54000d140100c800c41c1d484400d030800000c0b50507001705044240c1c01c4c10203051030881b520b00c1700c5d1035014101c003041d081d40043c121030038040400307401d00741e260080720240d204000f101e0000c0e469503104040140f003242d45110b00c02240d8004c880403034607400010541c4c241e20b41c549210304001d42003e141502e040c0b04a0710b010540120000850b80149201e4680c02c888802964928180942c00d0790202d0415409211030342c4944841101215035030322400144904649640030311040300d000d07a202c0303100d560081c103120750a4003e2003034540c1580d030071980219801e60441d0903186600c3c0341100804258440c40d4507a4000ea000080d00d10940d4000c0e80d070020306407610009101550103500746008802c0410311424119800b56250200f1030b562440903103d000c0007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 793160611 1250 793159361 793159379
    0x70203030403081c0605030c120102090a0e040605090723030a08160b0702060610030b031c020a1101021617070506030a020405040506040212040b07090801021305010e101d0a 76
    0x96008884a20000c250f0311401300700880c05180070420201d04200c16881c000000303695549810901d801210b400b000390810603000c2d01100d8007048041c1c000d800a40d5070344039800c80f0740011141956214a490003007005140d000c610301c011145d078044012617100c03640d0200100c01c855401c519030b0500c200c02115001800e014050f0609284902c00f804001d41b090400c500c44001c0103116104540140040050550300c442c02e04600307215034500000c01e011104082843d081d40901c0015400d9a00d50523140302ca0390000f84080307402e11940b40b400b2928000c1005a90318540240c040e0889a581141800100802c0a000b21295424811546619650804111140d105071040750503103400080600c0380d424180101a00500181e4007185000592403148688031005032004200e0109040802c2c1c241c0e100304100405441090001c540d14140340c0150200d0110034030405000c03895480c5180072038135180000c4003000040c0d855242242603c1c01c102c8890701264010b16900c1040c071040410550b030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 793161861 1250 793160611 793160617
    0x130f0209090708070b1801020a05060c070f0204090f14070b0301171005090309010e0d020a090c0903080a0509040605060336010f2f0f031e151f1e0507020303 69
    0x3a4100d04aa9580b00080b000c0c2c01b0941d0200026040d913200368215070000f4400207010b030b4012410000e59840da2501d260800e10541c0810740a0352090030490408188a100c0c501c090032148103546a840d40302c0349400e51070302c40c41c10b80309220b42000c2c1800104445a1004e1009419020802c10b5410022540000c041107032030940f0460181d40c404111052156000b034802c00b0030b00d600321074180b82890741c0c3d0700003204800d1a000d2240d4480d21000700141042c041d0301104041d6610922075603c43d81d102000810540154180500c59420b240c0001179506042c2c08680c0a09007442e04c542c00c145029061012415526100d40c00880160981403072919080c800e603d50603040300300100e500320302e00004e6441c2d0704150030303088000042080e10581480d001c01c101d030700d82500342590f5510380c1c0e11118181c40240c603030107a04501c1001c8104006044100c00a04031900104880e00815011880030304c1501420001d88000825508000c5640051240080118210041c0740080ca400325541c0403070b040d50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 793163111 1250 793161861 793161869
    0x1306090b100302010f1403011a072411070b070c2a090b01020321151c0c08060601090611031612080a140f06012a0b130f020909070807 59
    0x50700e124418000c5607404440e000300c1d0502890150f0f54842c080181c600548018826408000d52284100c1c0e20a2820b10a81c1d02d29074112001441d09600350008190050b4041a841c40d258580a04029440c00c4002521342080e085658815140d80e02102600c2170b440030141940c9144504448071030451402403042140403c0050180d100c0c0d243c00000f100b40c070302104070541036410600c04004043c144094800d02000c00c01030341140c40d00c1d81401c170b0300b080260443c86504611904400001401c40c440415140c0d40301d43c1c040d801141c1e482481c583c44440603140c050000e4001c075010007000e80f003203041d10406048001079a282880d2900d2008141d0989201103540c1c0295800c0002a640c2010900c0c2e030145038060148002c04c0303100144841900000e0108007080d40d80004a501d5034800c1401c06949890340511664a1100d100c2900a64200101c11203008840c8400100c0c49078520661020040d4440d0f28000c00381100e608018640000400c0c0300c0c2140f00c1e200c00040c600c40d0401000b0010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 793164361 1250 793163111 793163131
    0x40b040204080a0209060a0b120a06151e08010e010504020c1c020d17010602120315180105190b09060c0f03042306070b010e060d02041505040617061306090b 69
    0x303014504c140220407100405442c850300c03040c441000b0b1001031008a8203243d11000c9020810390701d80e101c9100600448c3c20100485007445480b5028a411406110000c1d87e20704900d0701c040444001200d03006800d00030f4051069180c0010805414150007408103482030409545600c1e204107458070341200ca00750241700680c00b4030700f1100c00c1c5170440c0d11000307604880840019150306002010f036545c0b181c520783d409003540020009100c6c0c207000328681c08640c4010946080140e0095210b503800d60207029003840740d20781c410240c0090b00e04008640841d440200c0d5a0b0030141510304106082d00f0203c4108200e006024441c40701660520042000e1b1080e22441d070000c2c211040d80c205002885052140640401c018101c0480c1d8603d0701c80c1d04460102003141d8065a9440100e203200d00c9941000f500641410001d0b840803808624640644200765802c209080d5206152281245802c4409455401084c007040c002d60241c203104014502484001c40c1d00c840d9980d40c6080b1079000c5071541c01c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 793165467 1106 793164361 793164373
    0x5060a0806210a200f030c12030717030907050607050a260c0705030f0a0b07030f090b13050d1d010c020d0803100f0e150f040b04020408 60
    0x29140210283e8103021802c0c6002d9030030482c445445002e40e08a443d00b42410304114402d201d00031801001441d0400500090050200c000294041980800c0165401089a56144003a981d2441841c0340c2d492600c44412030521003e030700258801c074810000c0c00082a000038401c0a0540c201d0783d600c1e4000261501c50baa101d240b103211000c1c508000c81c81c5603690401086c0b04088a03000e9040d50f01e42e40c40c41c0c1d400c50300e403954100000c03c25000000802d0070309103e41e00c07000c044a260702c0700041000c40c0b80c44007052590210340012090454942090401400703020480780c91419043c565410002080a40030001100090504000410a8103400d5645c1c038020100300640085c01aa030702e0401041c2503002c64030500900110b21004000040e1040c600403480e80301d84001c2d001c81401c0103203039003080130a03900c3c0c080c495032194440b4451103803640c440c401440101024002008 = true := by decide +kernel

theorem cover : BRFrame.Cov 792985611 793165467 := by
  have h0 := BRFrame.cov_init 792985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 792985611 ≤ n) (h2 : n < 793165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
