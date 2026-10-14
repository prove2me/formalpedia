-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0023
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:24:57.663751+00:00
-- url     : https://prove2.me/submissions/797d322f-1e6c-4995-b129-0f7451765691

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 3956842 ≤ n < 4136698 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 3958092 1250 3956842 3956857
    0x31303060b030c030a0f05070308040b0c0c010504050f0904020406030f05060405010c052119060803040e06030111040315020c07060801090b01021605010c050f030307090302010f020304080d080c12070203 89
    0x1085038a07048030506079200300c0c422086400d13070701c603603200804203d804803540b0105100301d00300c1d100141c0b26520000c070b80c0c0040e808440d0981c0302103038040994900b44054a0a02428a0003900706843d25001400680940c06c00340d001d9090798001c60309541b103a40004002e540c109071440504199458442d6881c0350480b4151002c2d4a01310400142e54800c0d811150140180c8990b80c00304603219030401040030000e0020401c200c0352140c000311039a0b20340501c00003060510044c58655103003092103040b00720010140c80c426403614081c007031020204425142a42d8100c14015040100844070400900c40d4810a01003840341c1400000d40e03aa100c122a03060302c0690310309100e034001c1c600c016640c1ea56403103680510603032038840c03d000c0f0b03502c155150000070703005d60116154004038018a50442e88284c501c0000200c10540510640d40c200b6004100c03010603100941c58680b60814403921b864284044608004030100030070b0403450300344141c9400070501440c20382c050070b0000c1c0183d43d9a01900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 3959342 1250 3958092 3958103
    0x30c020109080a020105040504020a0e0306070306080106050d020d11010c1704060314040210080702010b060c0109030f050f0f030a06031406040c0b090109150309050703030c1a01080c01030e030408031303 89
    0xa80402c038a003010030201c030a140d043e1034650605041030304200107034001c98003190820022880050b003580c3c0401c000c60003030710540c40020b1003905103d0f190f403d449058100c0790080740118074080050b200c240c1c0204085401c11002416003070f01c440100c0358082030301e201501020b550001148490418402402250b00c02d031070401480f080e0101000d8610f01c102e602940c001d001006007840c10b401051016031242e0301c1d200024000340c4072400280e994129500c0d0f82c1c0181c2d0740e0701000c000c254000030001907803021410b00b6401e040c103c001901d8a4401c0038002c082c44032020002c83c0728010f0325041540510340c40004800c0040001200c16559801194140d43c00295240005002d0a08404441d0044410f94440c603101c1d081c0126100c00d03200712101c00303080568405198021810078018900518881da0700c1d0400481203080c8001310240c1c02000903900c1c003117900100305490f0000742800c0c140d002800c0100300d105103808614214059503101c51503078000003030105940608480090290b84c440d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 3960592 1250 3959342 3959357
    0x312090706030c120b01140c0102030108010c020313060e030a060e030c100c12090f020a0b0c010b01020312060d020a0305070602012405060307050705011e021206040c08071218030c0201 81
    0x2058101c0640f140c3c229440c0106980c000480d070390740c8064010b0100820181007140000b031800e42e400a55030310829400366641d50210060010020a000d8402d4074001480110300b045031030701c00059810703c0c0f0304c00e000900190329101c030b1441e01d003840702500c200d400007070130800c1e51040518651207a2201c941c450190140015113004402c6070320a44d20b0391510790780c0381602140e114295000810380220305441107120043d640005035103000c500c074040e241d107041464031107142050003400e40e54031141d028117640003400507410800b00e800c1e400707074080c100702ca290703a03501064000f28410150f01e07000607205005a1001280340f640540100150b114010550030400c807854028011600b154040d69500800420114407a03a01c02c8000c2c1031501c0c09000001101c14520f14010a80303c03282042c0801c081c0c0126405109003040302e0700f10f5000b0700548052141c01075003103000708a501d005105c0014442200c440707440c044201c0e031004e840c400e40708264501020f1541409440303402500b00413070005816 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 3961842 1250 3960592 3960599
    0x50d0507030f0f02100b030f010f0b0901090605060913020c0610060207060503091902010203160605010e01080a0b06060d2004050907050a05040902160203060708040209060f06030a020a03060803120907 88
    0x407440d1056814055025007201440c900717440c0701030310300e0580665151066252215a9801c20b100d440f40c1851410400140000340109000d41c804050f880059101d150040401903500c4260480d1030f60b41c012500790581e07900c0410044000d00819403043c407248600310400050700e06102c841c0055641c44d400300c4001d0350b51040221480d00c800c5070310705141c0e000940d0300c0017080d12007641e603055a841401500e0800e00d40c1004015100000403040d0b4505840390010000f0300d21412429014150044c00b82043d95401d44a00711540c03030280515002d2400028034040c984041ea104014500c00395085103640c10414604545903003041c05110311078010310000c40c0306280980c084410119080e02c074241041d10b440707258030003500110360103007521600c41544001a60301f07100c014860169512048003504060052050b0404000e01090041c26035549060300340d941c840540c0d90000b0383d80001b40e0f4607150002e0460140000e58401505403201158200c1c103070321045200f51090780d6890446140e10307503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 3963092 1250 3961842 3961847
    0xa06181401270507021212010609060f050304020d03090f060801080606090906070804020301020f040e100902030903270406080604110904030c061d030c0307061104051503040302010603050d0507030f 87
    0x10300c0540400c906002c582040c07081d4095000183d0080807801a1500e42c0c0040c1001803265200d10240d0207440c2d20a80144143c80d040f070240d4010381401d2400e549580c2030300170f02070814800980040c1c442d0071110000c404145c8184010005002074650b80380800c0c2c7d03100c40180c5500070a010720041405a03200050107030500d4010300303102d1891500100003d8607420810384050320007030700c20f0b60555002c01400e54495004d000410007030802a01048203440d00c0400c001ea2811280c1000b08441c0c010070521400f00000001c0d01d07401c03000c00784000400002008400396141b0051803064109041c0080080c0b04080455085d2140d40075440c0401c1c004010070030000350700812200100810130340c0c5030320800f10b40140d0084007040115102c804003042003516827482c0d9000002c90740e8013079100041c02c4040108a025000046100c00300040c20076041c6030002c7c13041c005070325260710500c40100000307050610035000b500c01942c208040d16500700345440c0003815984501c0054010901c5c440d01080740a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 3964342 1250 3963092 3963119
    0x2060c0c07060507030212040e04050d0c05030d020d0f050403080601090e1003030f020a020a031415060d11030307080a030204050a05030a03020a02011d0909060115080103050304030b0a06181401 85
    0x4800034003401001d41002c10640302a0040641902180304d600c090030006000ba400810103440207210070704451506e49130140c03074003001c00c41c004200801d05440c040059400016180d000021980150b29070090b10b61150040c00c4820200c0302d00c1e405d00c010b02c018150411030441c000c0038203071703142c01c1e0301e584800a07003402890588441460050341d0380d00f000460f11032001c8070048511441a2100d0355299000145040e00941085d40c0b6002052444541d00c00c0400041c040000b910400d08078070700e0000c00240303101b040090301a002046804039201943e90510407176030306030f5020320342d5a210514035000400a400c580551805186c010f60301050301e1900040340703010380780e02d0760050584150b1580115062004820800d03000c42c415681c140c5d40b0765800400920070540e40b402002a5858121440e800010078045a01408110401440460b5000c4112011b49800c08442c0c0e0140e2502d180190051500b0340c0300c030b482d03900408203200c2c1c08151071300940391044c03c070070001d00180d80340d00f0080000e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 3965592 1250 3964342 3964357
    0x30705060f0306101b0b0702010b0d05060606030c0427060b1204030c290405011805060103030c030203040504020a020102090405060303090d110307080609030703020714090403030209040914010b0102060c 89
    0x803001880043c01c10f18109400b9112101c0a18000010142501134800c03649100c000886240500d0030400003503981c2449202105402180c108031280c0e0640c858645130a4041e020500504001002541c280d20340d601704c0b401459041040400320350b10311901c010607820780745c80603134060500000068104411054031900c41c0300403400391540d00c90755020794411002d24400c45240d51940c032800034024800700c00040020f20062000c10324500740c6401400c41d0604100092000d440725040404076500143e003d06483d0302d814808401c12050905910714025075100b50752040c00000c202021070f6064015215284068800f4025511142c003015189e0007860103542c0c1200030002e6000c0410241c41704060940b80c041d060743c21564844800d241000011541500707150f00c005058001c246c0d041101100404154110140f000600f5001030f0200001a101504254000c1114402c0b66036036880003000710343c00804480058107440c240e9020b000001c0f06c05001d0b00800e8001003400c1815030032500c61 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 3966842 1250 3965592 3965617
    0xc01020604031407020a030611040905011d0403050c01090b010b0720030c011d0901030f0b0c04050306070c060b0901030b010f0f0b160c0e040803060a05030313031e08030a0b03070506 80
    0x10349070800103c405504240d03c1170703920142405000000c192248181300f0340c410802d4400d0b0f84c0d6428118514140d810681c0b05032016011280c241d00d0551100c00f02e03603001541071400c01e50310400c1089090143c041307207801810010030000001130510b55a40145041d0344912105510ba0030106410000c2100b55a840c07501604802040701e559072184000140d20030030175800d00d07014022200400c0c5002e03003d8108403144210036424400f40440402c040d68031a5240501510746400e140100c0d4031880c0282c01c4a0520144c02980010094540c00101004101814041d2030b50380d60705000901b4038080c41013941820b6054404030703c94120580c46400c1d0750302d420020f4541928030101c4a51145612000d58004000400202d42c0a01a18019004d98052801c00391281854010045a0b6600740e010b030303100368010009500134481c24500041140e4202441c0e64a450700c2803210035280121080040401400104105408119502004e41c902d0260100d90441e03072240d060144030301c110f80003400ea = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 3968092 1250 3966842 3966857
    0x30e060c120309030c0601080a05011812030f0204050405041a070e060405090c04051309060c05040302011205060616050303040b0c040609030602030c070210050304030201050c030c040308211003050c0102060403 92
    0x904001c0140103642107801041142d02c0c0c0028a02e0990900342c0030f0b0401c40107a048003241a042c0072090042c000c01d510400b072451070005407a0359220007112911000814161035451070021042c1950640c2c00409020708288201d00d0039140041a81c00f40c1c10340000105583c901007010903100315030000181c10050103d03454681420304110f00e05e8070040007050268030810020459882e50350880904a0000c40c01203060501882c05d081915209400301c010008103100420140c7c0c1d220041d14483c0c00f10b400001142d48a410105003d4840c00040507004480d41c2d0b032207002c01100200441c86503020305400515502c030180c004085110324491b050004010f0354044c40031492a600442c1c07c2520b03c44003915003040c7e41d004c16445c6076080400408142c2c04001c11081c0341c1c082c0250b561203036601d100c0c1403541c50510009a098001c5000c090302181010850b0b410081802d920f00011100c07600b42e81800d0f03c1c1010500c010180e0a02007181c20b1701070390b4208141035000180050080b0b600d40c80c0c2d9170 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 3969342 1250 3968092 3968113
    0x10e0106050915090a030503030a0e0105070807210203010b090909010c05030c0a020a0203120403030314090706180b0f07030f0804030206070305040f12030c030c0905030a0201031e0204080109030e060c 88
    0x4801002c5411510820401304806651a51001030100080d44100041c5031a46885010325044402d170381c00110041e410003080094003075020103e103611800c03508010300c00000d403d801e1030700c020707409044a01071840040080740b14480349015149130303a002c0f1340038195030b40d81c0d40805082c0c5045406000110344240003141c004182d0b14040c2903071003a81d20444810b01403e800180c40d00c01a501383d140400700c0003030f091007415490702a0302100b0360081100c8101b800d08144003981c0710554418142080000b5501148101c04c0b504503100030155921940d403a041c0076100d84006a101d0a811008600c4145012040c0c13806001254419a00764014081b15036841100b60040c080c014000c84007042c0c1483c81c500040c10380d100982e8041d096a40006104201070f80160445a11028240030b00000320001c208035580040d42110250703080c079010424440d441d200417142640c041d03500c03000500208000c18000030540c4000321050003943c40d05c1c04440c0d0300d010f0003254131a40d00e02e203003590480724090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 3970592 1250 3969342 3969349
    0x515040206120112020f03060907170304050405040c06020105070c0c050f010309060504030c0c05030c0607060e03070c0e04050d030501080307020907020c030d0207050a0905090601060e010c08030708040308010e01060509 96
    0x1680140041c2415140c540e8030341c4514001c440981003041d00360382e0604032006504080303060950715030042c0d004002e241005141559070703c80b1303445013091000400350f0303981c1c51384e105206450090a0241040c0000c1c1030502d84a9921003103802640c005600e000f0018184038841d40480c940e0a42180415004070300708014440c201e02d1084000d030505440c1d155440020740c0034490035208502a40e01d41303a654072140360900081d15940e109911070fa002525100050741c44004948803654840000203903d601802c48500314020018041d1420048000000321030003c07110341031140d442142a60b540e8010b01c0001d400f103410a0288084a6205004079001400c0030100642c100e400b9004a0380d0200110000901e404600703a003d40050b00600c1c2c08010b03d0078103481040c0581125641800a4688481181e0b0344040501c1000c0412000410080743c0c1d034000e815001c02c0c1ca40000486540346080c41015010041c155402c80010762140000134210400c0c00d41e003810f0300c03241c0c0c1c3c0c2c107850000b0140c00c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 3971842 1250 3970592 3970633
    0x3060603010909050c060315030606030d050d0f0b0603100602010f0903090e0405010908160b01050603070203090d03140703030605010f0c0506070f03151716050904020904030309060608060a060b040305 88
    0x1264070303115408042c205591010007640c42214030000c032950829230700003414200000507024601a0380100d010240d403c2d080030544042c59040680090803d5402039100060219a180f0940118000080c014004045d49444d03013540c0c510b400134070541405a00036422954406070140020314003141c24000340341031800481d042070007140003041841e200e499403200f592118080c01c0705813610407184402c002d084607a16004010440d0482e0035845c0c541c001035280c0c0300d000c1606129408241c150407c240c001c4d16042001245415143c0e1500c03400d01d00500141007a005503030205100b15402c112042c40780160360040c5900c013000d04a41c0d141d101c420b40301050046c510342c091544501e65101404240720180b00282921002c500741c030700700d581d0f42d13905050f041c40d4240300b0071250345414007081e2900b0002d207400c0b903030644036a825541c60f814120020070310b00790000c240d18100f900c0094000000510310f409544035080401489548001404092040748801807054001ca1151241178000407003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 3973092 1250 3971842 3971861
    0x3020607050f010f0209010e03070308030406050c0d050408030109110307140d0b0315040c0e04050309100e060712090801060e130609050f0303040308060a030302060a110405040905030717030606030109 88
    0x2c403607064240110003420f6640c014162289031360f010031152071540e400544c3c40c890303503000d802408016046459122051100a0010b40640c0c1c680d0b010882050341d000440d184401101ca01b0446400d0515000156901c01e110381c0482c24140300c15820500c1c0c14170300700e9001c1c05d883d855030010603040820a441540080d44001039580d03460040c40c10303585051102c0e50141001e14804403079481c0c18074200b800c259258012500d242c000000b0080010030020444000030400c480000f108417017240700700c80f886144100580c1000001c1807210800c1010060000b4084460300e401d4095500d4911050032a0220312903114400c0c8054081540034034041682e031031070703409120080f40c0541c494964502c0c00c4030011413100c0603800002000140351740302c0711071504140d0855030360840c40d1454078001c0d1307116400f508001d00960788840300700e1482c844200312001884040c00a215801c0c0f50f0600c40e8507a04817490945002c0080455044420307048811684241130042c07400d400c590a01200c0301c0244103111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 3974342 1250 3973092 3973103
    0x10806010201150906090c05030103080a050c0712080307020607020d0c0f0503041508070909020a0f0302030601120f0605031b0108040b0703060801060b0405040f0515040b03030403020a0303030b030f0a050703020607 94
    0x181c100b100007403400314803c040c041640010400528002c001d0085030b030000f40e41320401009000520005800b0800c0b0740000e800740c80d000d03071240b5815402c281040b485500c221510b030350700b2111000b00506e41c8040d43c4684082e40a8176820340d509501139888003011411040000d0700d00c413540c00010026001d41640134041c400722030601e512181c0004e40d0507620316491012445950400981541c801c100c04043c00102005506002074564040c08980c10388180e0300c00c0c0340d0040009189c0364814003c1c02c55072aa840d0f0b0521589810000307150040001c0d0103040d01a01890410200c494611202c1419410060b954408c85a0340c60300c0d980c000540c0030303101000f01030301c1740380c0020700740024020080600880134420740d603607103000200021030348001c03d039078001400d040c104404a030408500c030080e007105440c04200000d21000080c114412600000d600c132700510004018164198002500300e0b41c1901103900880c0050100f0f07030790f0111391324010042c1c0d020034800e00060400c0806000d0052081 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 3975592 1250 3974342 3974351
    0xc050301051903080f0909010803070507061b020d061a040203010803040b0a020a0506150108011d07030c030605040609020307081008100207020a050409030206060102010c11060115020c060d0203040c0902090d02010806010201 98
    0x1c0d512a051603000e50740170800e5060101d150481032801190050040144c54000d5142028640d161500c0d1080c0d40b03d40810b1051104010143d66104030703541c0c3d42e6560003024501011240d10b081c03002001c20700115a00c5880c0103040000700d0409108682c1a660810000c2d070800b46401c04514040e4000741d0500114024514424001802040701e40e000e545400d0280c007600362890001007841320142c2c4946400300c50380d00c03c01004007048820b00d4100c440d03443c2c007003000c0112120503006003005031301803a045440e00350f001517180c0080d070140d80140c10540c0c0d0a4440d0310b43d07940f0008001101c1c040c055007600f007224420754032506503005149242c4007410622802c0e13903400001e41200e880e01d80580c052b800400400000350390a11131407003800c03028100804003000a00142da614003050140310500c03148028000213041c000c208090b44050001d0449549281190340c91000e03410680f4100c46604019502080c0c1200500a5580034103004c2c0807130300107200580044980040107810141075540e035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 3976842 1250 3975592 3975599
    0x1050a03080711030304030209010b0309190f1101020f0706030b030d0c02060d02090a0b04030303020307030c0302040f0b030a0603080408030414040b01050d0906060503010f0c120c0c030f12060f0e060102010c0503010519 96
    0xd142782c1600900640c91440d8903494901121410606481c0184403243c4204015200140d01c01000d0802c0c1904081c2d88280c42410707100517490401c2c01102d18141d4440c00c0d80000311031342d0541040070307801c8007582554014416603405484407002c000000b07611110510525245100a90151017020001001d05031025a40d105854807548690400e07070029400104100c0095018000d034000d12501c0c2c40c0c2146800e1410b80343d60030004040c024031401d0071000001c0745c042d540d150060000f8640041c00565a1960340c1c2da81a607070b50041c0709680710841903000e90074462a2600c111454288181c480340d14000d2049401c00c01024203c100b101c016a54610100791610240f150008441c090640003e0080714808054605030010074a12201810130410018441d4000007001140c0d034903003000700200b90305030390544440880352810903041d8644400020030201400e1008201c8840b140d540c01d43c1d840d1103004900360741030542c15401054040004100b181888a034008011406d0002c1d645103684 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 3978092 1250 3976842 3976849
    0x61b02040f090506100b0f070201030905010c0206010f06050307080a0506010c0609050304090b0607020a0b09030304030605040308010504050703020c06010b0c0a0f0c05030d08010312050307030603021804060501050a030807110303040302 103
    0x41c0340440300030040d5649400e40403c4000c100050704580c000000c50300981c83c1000c580c096100d9038551941155010450b034003107900981000c20025070043c000c1c4031544113881c00075038840091040000341d000e00c0400062290080c01100c2c000c55080c2e03550f0416541d0b9040c8440034002c051720060401801a544070081201c4c0c0c419601014841c0e005142d032549429840d80503600140c100f248142000c01941005a0b0303070010070022140c03070750340443d110209100083d04500580d41f02420941c281420482010f50103e4214140e0b08222003c015507110b03101c084003280260041171510394802401407002010300001707403201e54110000c888107000325540b040c41c41c030f40a4104035420510750406109a01e400d0004022415003803504003829891512501c8a6040501d44402440800000716444500ca50044409590045c152020140050b596640e00c0041100c2c08d0b540305242c84000b00d558540650f03038404036074000380c1c040e04000c01602c41d00785500c2c031448050390510081000000585 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 3979342 1250 3978092 3978101
    0xf03200102220b0406050405040504060902060304030525020904110402190903050c09090303040b0406060302060a0c05010608011803110f060709030b090105240a0e09070303020c060a0801061b0204 86
    0x2100b400300300501040300407150300741c001280c21210041d50144010700c06540e01409a1381290f82c221804070742500c8038184130008203a50000a9080b510000422050542250003845074007013a10070445255070754980d14136420f900070340c0254011955404075005c0317144289480005400240300502d416100c11340f0b0344a0b00c81c1d000405002c5034101c2810024000140044511180e050b9200350349480c0030b4a017142ca030300c00180002e290f0318a44002c0350601041d80d0100c0090f40d40a02010369408107804003602d2002e04a07421100c2d0b41c00c00d000819000d606004076083c0700e01010f0401280da04540e000e91b0529110010601e1764030542c4050054000204003c50280c480c5840f118007250460134500c81c00f40004054652076814041400070f00ba07c1d20241f98035109141254800b50100900040c04909183d07011446c0d849100c006e101c1001c0c800f14081045034407036001c07100d950707a00c0014072034070f80968011000860703c0000100f065500500e044248507500c44c240c001d6500d910303070000b402c80307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 3980592 1250 3979342 3979357
    0x20c04050901060e010902030405060609100506030106050909090a020603190e060f07020d020c010801090c0507020907051c0501030b060621100e0a0b030a0201050c10020304050a030306120f03200102 87
    0x50707443c0c0c44100800d44a445540d40508043c00c000c0d4914075154940c0399441740d01408660140c103c1e100012124070910702100068038004005640d2541d40ba18000e201b6080800b07110b1141107a04d0115035031080005010340c070254090405410342d611041c00380f048450b0700207006001a100d0f603480f00f026a0034003006204080000c4060b02d14185044000e1402c2c4911031007a0a550000d140c0480302d85e00b222125044890301788000c03815601988046816001d904402900409520b050010306508500580400546075610051a00c41e28140c0800d59100784809000c50742d10501103070050404e840141041d080c00002c1c003220150203901c0c184100001c41ea06002c20015001c00c0c08601c600d80030554100056400501681e0610340010342c072044210360080c1803140009e4241502c5805001801c91002141d40854480c41c281c140540c48101101003240007914202c0c000c500704142c0641e211300103800c40d4a06101010603641680c000c6107a02c0d040700c108542410b41540610b0900081000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 3981842 1250 3980592 3980611
    0x501030804030302011b0207050f010c1202010605010e0406030b010b0706060305070e070201050117060f180d0504080105060103020a0909020d020f0a0f080721020f070602041d060a1202010c03020c0405 88
    0x9840ca50700f802801c4488034011001003c1340c0c45c00140515130b0004000b8140c0d4000c641d00001d040e21900141d600c003542240041c9060303000d101e0382030099010b41c003200c11034000f0303214030001d65808410801100e4003070000030121107840005220504e4400c0c064908503210306000905151603807202c5181c4411540809540d035080400c0114a0340e080c042c0e079004200e41036481d418820980101e6442d03a00c0244030b411100d149038001540f910000140d02004140801500c00c0148142e8001345150f01c68001d03d401e660070310000c60019440f034804c88001911582e070b615482410218410042d610000c1c000b40429024049a12505000c000404a10540e91100e1034000c4500380007400741034004149206021287d540c3d1710304640307225651500c00b20b8142c00140c3d2084806007010142c000c642014124910116000c02c1d0f1200c218402c8030000b100001951840d0707a00320070000c40c0c44142c003c442402c0c071174494280055004070540728000d446070043ea007042480c00c0110741110821102e0307225 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 3983092 1250 3981842 3981847
    0x1030f0c050901030b010504020a120e0a031d0306130804090c0302041811030c0912070306200306010207030b091906060501170906070e0303130303050a031d0703080a030605030105010308 82
    0x41026810386000105825118009198034603168021071140c14851140641e400060201c4018400c101c5a1001003038a0401c000e40300489420941c2d4802014048010455081c0c041c11400d00320031a451320210001d00a01c0c0c03035944c0b0007002011000843c1c085840311414400803409401a000d0114209460354005031203c1c070b40601c0a42d00303e4411420403402c0e107010302ca5941500080100c0340d011030b154400c5030740d42000c02c0210715030b0030061019403614082c001001c0301b0402d09800142c1c0102c900703c01075050341c2005400104512060b60b146016a00c160010400a41300c008050b60109124040e1f070b41d00e8610308650070103000800c40807a03040baa9010140115a0002e224041c40403d240030300c14140303407114100b90781d103d0283c503c02c03e1006c01c24030004259010011282c008810245228071103907245406842038204840848c0840d0030607940f040c4450041030140d59140c00c410080003154a1078641d10300c0da500c41240d42e8105900d858011034292004d000d05c500071442a2001ca5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 3984342 1250 3983092 3983123
    0x509120601150f0804030207050f0609040504060b03010b120607081005030109060c080106020a020f0f0a080d0e0a050d0308041716110f040203010305060f07030212040f020a0801060b0d02160b0103 86
    0x10103c4481e0824503042c0001c1009010120b0340c00201e01090340c0058840e600302da4617810001e8034a01450b10104c0d40b103030600040004204443e0800c0e080450f00b50020310900500c40100f07d003014202d010080154443e0000604451080d900c958011344441a0314901e140c442c4003103429030310070b000306482e2103868680c42009243e00406550042001e40301400a01906030b0000da90f00d5040c1c10f60030b210f030100f0700c00364040780d688041000090400004035121407045402c050104182e020754a4840c14000400145d14200600c040d62115450b40d200310680e03031555103005020b082ca011108406605000c100d604080a0020060365030203109481d0444d8419070400c001d400800101e0307401b442c0103000410018500151860304604040c440011a50300d40000710020300800c950481c1c1440307060140b100b48030b01001c0c2d0010072070090310810103039525241c040f401c0c0d0700e0314403507000340c80700c204200c80141d102c0ea1302070302c100788410410210f003000a8a031800c0549080e0401c0e10211800036519 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 3985592 1250 3984342 3984347
    0xe040c080609010b0903030702041509090c03050f060106140a0e03030a0201020d27020607030203090402070f060b03010c1d120708010506090a1a010c021306062102090a0303050912060115 82
    0x2e03004100d030b00b1a2500e4170314004082500d138010100024080d07902d03460610300030503980c1c15003c00f51000e88000c21451100341011100f5032003c0c401034800d80900b0081c0388200001043e101d0503921642c40d4070741200100501080c043d03104401c032104101c514040361160307a070140000e00f010000c0d60f00140e1107801850f480421190b0b59107541004000a40d101d071444d11503031207880c1402d5012100c186d183d81c55030809908611900c44640ea00c2071000410318100603807020360b218000d006440800841d07103914281822504911560008034881c0311501c800b0308418104030314090b5000d030050791a9402004203a290580507003105055035100d00400c941420843c034060380c4650291014410b081d4087d003041c60b41443c00c82c980f4104200c3d602c141d000d64403410113201d80740c03001d5a01040465a1200000c00c01e00d89409801110051258505c0c0c0f0780d0300728002c3d60003900004025180a9107113036170650b0f29605c90503259800c100c9070308641c42c00700010301009008119609120408520f032a000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 3986842 1250 3985592 3985609
    0x3010c1d0d02030a06020307050409060b040306050903030708150103060305030c03040905090a080a030b0a03050307050a03030b01030608060117011806090c051818070506040305071a1c0203070e040c0806 89
    0x4441c041d2502111240c0580d900096009038542c0201c4c0c0103070751340c580350000c48940c842c60700410f100e2400d05100243c2201c20300000c00489000b6101002103444107602c007a104c1c401550600700094680c00414204c49080c3c4180c01024414100007410740e60340d030384a60568000000152042d04086401c020351035103800380719401705060b0007030241da18140ea100c9100e4003d00482000b0542d60340720441c080d8492813100c0000e150880100d94170360015242069860b18000c00441c0040d0520907450203550090140c00181c5043c1d2000e01526030030300010354000c1040000d90420307513481d000311b1140740b18140c4200900c2400744402007144c035018107041c849483c840e4030490140d090440201c2c0d011440719080f5811054a076015030590026100341407900065801c40341d84400005000810802c00040a600703d94005040040076513903400e50020364010310310180c1280d01c2105403013940b01d6840e80115030041c00303410240300c00c80040000c54110383c250001039000c40c0c0d10302c00380030035464000e41c2d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 3988092 1250 3986842 3986897
    0x111f02091002030702150307021e0303090d0e06040302040506040b060c03190e0a12020f040e010212100b0306011b0f0303050708060f010e0d03090e070e01140403020306010501050309010b03010c 85
    0x540c504004c55010540b10383c0d80c001514050310000c408980d0441c03080c0034004116030300c0c14100c0301c4541000702d4240c403039005603201c1095200b412503450030140100450842c6500c0142400c0c103062541d0280005000c00a0400b54015a01da84402c410303950b01000e0040090401d009684901e82e426280b5107032180e840c20b410a0281d007485d9001c090360340c003401c40140ca040c4414404410440e00c04603070764249040e06158070908003049800760307030b40540c0904445000000c01c40c007643c44920260a03034005600400c42c490904000244555005500740aa034030302d075002c060301080c100d03101c2c110404420682180040d481e2000d010761181d00c98055074000c1000c541d0041030032440700001c0d024204150055000c1e05820b5020700c285030141d200c0e85c0c003c1c240072664056a2400b880002c0ca07204d0000d071000e0104510b110b85100341104501628240c0c1e07400380c0180071513420140151460340004100701919902c074041038040703460a0040e00c50b85042600c81020a41c100d40300a03111440140c1d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 3989342 1250 3988092 3988097
    0x102060a090206030c0a030905150a06060507020d120908010603060b041a0307061b140105040203120708030106030908040909150506030d05030a0504030c0b0f0406050a02030106020c01111f020910 86
    0x4004000b580da4403084a420010440186548000921064016080c280000f80560180428880c002d08a54441521030340061004114294403600700340c2e05401035850181d0004100340c100390000f010000d1175400c1d0101b504010a01d81c1c0c0d00c585680c2542d8541e002200c109403039403403520301c90620780507610300710b00810030400ca64071012001c00d550340e24038482c0d01c041042803811602c940310b04d41290410640c01800164400004000d8680a0304042e50124040e12818880b030254185800c00d60b070342c042e8042c3c646803843e440d2850440c003401422030150f0f0320200802c40020074000d036109180c141486041d000d40a2200205242c00310703000180258001d4119034804841c45500804a80e80302d0b0704240b0002e042d0725207007021100a101c02c2001062400c840007801140fa41e9003034100d02c180d11412040c4100d540c9d09a40034140c1c00288110400342c4d10141c242d0f140d560155608000041c000000c9238400020140040c9040c4004e0111000040e400a800d040300c1c18884c18004103283d450 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 3990592 1250 3989342 3989351
    0xb010503041a0a06120506010f1202030a0b0c0d0609051b0405060f070807050607050301090506030a0308060d03030e030a030b010314010f030b090a050105180c12071503020f0301080a020102060a 85
    0x1620b829203082c91030845012480001000615481e0030b5900210150498070012003901419203031040c6e0742c544c28001c00d00035000110001600d000149185815264050003130810346a0b1a83c80c0d0200d03500142400a0301c3c0424416480d69000c03610030f05000700121000130a05082200700c40f082c14404044c1801580c100b000180550388030740c0100e50350301c031702020241d176204000c0c1084070250080e0704c0000c0590103904207014940d90b0000265050b550b03e0b40c8200038070b4644500701030f560102e0410080c0401d02583c0041c1c15490282c0090300c0250003410042040c4d5100e650190450380010303980b4001c6641c0f42a0381c4d000c3c2d41e040c451a540c4a04480e4070303130004d50406680413100f10715440001c04d4440c40c113000900541042c0040304203294440002e02c035a00f0416410290500180380c03018071442100002d40c05442c0040840e14503500301030140096900306040b0120a5520040182c28141c003082040a00c0d072201c0f00a50081031404050990740b5000e00c00203080a50207407407074801e207081 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 3991842 1250 3990592 3990601
    0x20a06091a070c0b0106051c020a020303040506010609050a030201030b03010e0d03150905150f12010504080405090c070c0504150e040503120708010b09010513050303031302030105071b060c0315180b010503 90
    0xc1e0b150b0b05446e05400c2094803201c02c1d4502a02031140ca4403466541800407410045480d0004007850150b0b100340c081e5005a86ca8840072603061040380714596202c05000020009540280e20085250102600202c1c0400c44070001c0d51514400b210402c000030f41e40d0701c4d24503141020002c0b15019000d0002c040c0300764108520b610002c1c01c07005103042e11460b007081440009907940854400c0a4001c01c0082c040d500d02030030031171941d030007522803039002d00413a000040c1150b20317001c11640c4c0306038400640d180d01d50401c01480010308100705840070800c0c20650100d200070f10203144922603803198008640e980a2080b240c503000c1005810341050168050051282004403410b403a42c4030420319001c1d8540800b038050070007001107540001d4140c040007061206040c545c200c924520390003503009005d60b45441004aa09840281c502e602c10b000514404000a00d83d821412406900d4075010901405690395529014144d40c00200c4107a02408802c505034030a0144492444003401c105085251 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 3993092 1250 3991842 3991853
    0x110a02060103060b03030405100e04060605070206070f03140d050a0b0306010501021c02070b0a020f0106080c010c03030b06070602030705030403020709060b03040605040302010f060801090c05030106060e0907020a06091a070c 98
    0x306020040078951203203004242c544080007960b00a150040003030100805d10503014107284416856030b07003d1030900201090450140c0204c030f6a90b58040d024625160742030310b60f43c01813031041a0031030411544801a0282c07156402c09408030188144001802d8100703e001c90003103c0448810071f00035003001c1c00400c551303038004c1181c0b640d00010b41046d0115100540c4104e042c455180c100107048440400c140040300c1c2c1c00030307041c030510300c058008010b05500c42a4569444030f8501c42c3d54005000300000c3c00000784242c0009881d18009002d0b641004001ea070742c1c4059800441d49a000074034040108024581e0406c42100100005881001080c0c2000700c51071a6220080000e00304548540210f01018030075030101540130b80c0725908001d0103468902843c0646118142520600099607010074146010300c15403003141d00c0c1b40c440900040e803c01c02d029941000508407000e600410000c40080307101ca000724240d182c8202c1000803000d41c1c10001108201000e090b4400300481c0740a200c00151 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 3994342 1250 3993092 3993103
    0xc04050a0b06270402070c03050c03060c0d090c051807081003020310020304020f0a0315060e0603060406090c030b07080406050106050a080f060d080f0a110a05190201030204030204020c10110a02 85
    0x420f0300c12004801c90550030424900740c1c07440c0c90640007480082c0341010b00255200c00f03010307288290162001e490882041507601d16061316003500c802c004025441111126034003280ca450700c43e4407440c078526541c0300068a400c828051109000100e5820010410751180c07c80d944a0041114420218110b40109030b650383c1c408031424102d540080410107564034800e40040024000b4403081c070300c40d1685040011649001240f81c881420032038041404111850386d24071600014000b4046035480b07407a0000a41140034054845100c0400c010021822a808491049406803078581c554101482e00d8412200140d00c040c04110007130140c0010340d607000540e44e801011031190407680703454840c0011b002c8024013100514204000440320441a07900c0040d1203030341d40545414900c0f17144414244c2d03c621440c28010500d400c140380e05c13007040c0211446422524018500107060a8036030340407904990200c1c00070201540080600c1d8142c01050180c0d950f1070209144040c10b20380348a50203990303803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 3995592 1250 3994342 3994357
    0x30302070b030c070f0302070905060102010204081f0221010513060608040b10080a051b03010e100c02010b06031503010c09050105070206070203030906031e010b030f0103080c0703060e0c04050a0b06 87
    0x5601c0040031071902c0208405840416421003001c59010440b4070f0041c0d42d640c0a03126401000303092100141140d070040c42030f1001c4940d08000b610b80e0303640a0080440d240902003000c0c41071a4203220142c0d503020700f650030185000403441090703070b6035041908001c55005189441c4003000d083c13880500445500c500401c3c2c0140e0f0003c0301c0b100c141c07680300701c5203541c0c00c158004c004944a0441c0303440600c9400180b6a07100302120f111214103410090905080e038a20840c40c1c10254401024041003044076030004a032820341e40300005007520034600203803050f1710030b980185603542c100c1100140780c5000c0c405c074065220b450130b1110410b4034080002c3c003503000710f40f03010b4450840031a051044d900c05200b01c03120440018030095591801d03600d0315400216030081e00025400e800000321300e017a14903040340e0046903000b1018a41d03a10f140c0c2d50701c41b180c0c03002000c0315050050000000006205005040114401e00091b02103034800409110840300b004007403029007814032142d905191034080480707030721 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 3996842 1250 3995592 3995609
    0x8010e060415060f11010e0a2d031d03070e0601020105160e040908090904030302071401021c0506031501090c0e0102030415050906120405010903031404031706010c020307080706080603030403030207 87
    0xc0c4c0c55490015608a46400c00d1040e540d401d110701c1d45140100440d6540c0841d100d00c05805c1c40c04034a080b031060101083c07083c892601d6003d110040802d0041503505007100341012440d10f4403542402090400b80503500c100d00c900019010b03c251980c0a0041c40e6005907419808402d041080800030502c012400d242c6000da81d80e0034102042c00060000c4842d0300307001410060450130140f80081c0254004041079981503201e8808a0482106008880718103840d03416011541c040c0c1d00d0030400812001d00406da1500c6600c40406040e801d024400b8000c1c07489480004881942e00c82c098406404040580c1c11074004010a0041940007100000403000364503140e41c071805071030041340c2544039030061824000103c070100000c00005402400c00244031b07036424403445030502c8034111010070aa8000740400e0400020403145d03031400070880c1c0c0c0f10005141880803064a90042400c0c1a040c1e00140300c160400f10041c014283c000c1c0003035400c05010f60003035141070f00e10f0300c0003034a0700401d0281c07401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 3998092 1250 3996842 3996857
    0x1140606090a0e1303020706020f0303010506030a060513051005040e190c051203070309050114070b040302190b0a06050a06050d020d0f0f14060603150405040212010c08010e06041506 80
    0x80d031145000b100240804161068183c18007070780c050034020b030400f4200e00604c82c0c5240801c08900c0441c0086d5002115001142180d080008010310303900014440d80c1c1961f998040007940b617035001d09460071513082c500000780c1030815004003080b10440d03400039809107003011114942942c0018000f80810508400204aa5034526100850403020b40c40140d02c0f0340c04803086030341d500000c001050311380c1c865180c13441125986da0054498074030180d03185921201c1480444046040c080000d60f11510070b01c1950060090864038140482c8000003e60f070000e40030f020041d1a0701f00340f0030760001e4041101c0d580d560b5031610a00420710b12034a91800107098010518803408ac0c2c054105000b040003000d001e01004003403021890040c030552843c900e01c103c00d01c2c042032482c281b5000300c0340600041c80c0b00409102c0b2140a00c4003500f40a08100c2c0c00051a0140d04503c18081c450488604402c4d910803c2c2549844130303100e56120040c16540c03155140c04400c00c0240014141141204c2c0181400380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 3999342 1250 3998092 3998107
    0x9100302150705010e10060e0118090f0215071a01030506061e0916030506040605030c04020901050708030108060105030709050705030601080c12011403070b04080703110d0501060806010509070201140606 89
    0xd81d1401500c00003800c642c24030042c079065a20100300070348600200f982c2042025551704000c50214070130720039051618212507455081c07405503003040801c1030282543d206500800d84c0452244080e0342406102d10002241c00410402c1030090f42c0240112004148034a504544602e600d941d00a41000d100310201c401e031842d202d0103e850180c40d00c200405016861500345007202c904021640c41d80000386c03410000411620f41881800291003000c0c00a0144540c4942840300079801461618144081448404001179462000754045e1030702c0750141400394505030925203000b00d43c0e0030600f821030170501045251b03a840300643e0f900000910f8091041e854041d52090548541200c442c251402d0308004201d07c805591a10304543c801d804880c40c0550b210321519050085014441d800d41082d4030401c0450004414510010b03c0180001d42d0151180c2c3c034907007103c0c8a50701c283e18542054004128a00c1c000000f5035100840d400280102000140010050301004204074458103010032102c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 4000592 1250 3999342 3999379
    0x901091508030304050109060b191e09020711030105070203030c180a05030a14060106020a0201210b0a030308040b060418060504050c03030406020a0b01060504030c090207080906030703020a03060509100302 90
    0x100000415a652804c3c035041003400392000f20340681d1010706018400c019401c0404c0c10345034a103600c00c04000f0305401c002100c000d0603641d9600c040b22195207003000c996508503100030866644035003503200c0755000110500d8290f0b403009140100f950424000c1007244d43d051001c507010f00c03034030036540f40d40107015400140c0d6820311504a203405201d6051070404009145038202042c0405d407007101d54aa990f01d01c01c81ea181511180240020b107090032103141d480b029003014800000b0181c0104541c0e140300003041100c0308a03070017030340000c4042040c070082c000c03081c00d86a0000310644060207500e020302c4e130ba605803882450000782540d5039600020140b190501c4001500c4000605990f40c580d42da0344d00035a50000498143d03291001140001a001d00a40c102c1d01229130103001261494502a105002500608400d8500203005c0001601e117030780d1040294402c02903074030f0050312a8280c50005080b01c1c1c031500014014524481032207880d03c607103880b1314101d81c1e040342c04001700516122803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 4001842 1250 4000592 4000631
    0x11a04180903020709020a0806040e010b030c190506030403020d030501090203060d0803041502040807060912110d03050403080703050a030b01030b09060f010504030503040b030105010f030204030209040f051f020309070801060302090109 103
    0x11700701244085241e1218903401401c0f940504001c41d000e108510401c40071900f02d5055140490341684048000380b464140101849480603411001402182d9640c01082140e80100c0e03003100140c20200c0c5810200390035200e0302e409003229000850031031408101280c840140d02c0301c003074520003000c40090104107400d101c0000d08600341005640319985d0700c074810369440d00c1e401040003007851284041002e0380991810000150041c0d03803080b65501d82401d015991103060000d9040000c200008404208a1310041405520940d03405540d80e082e4540103003184c14042c0702e04c0c100f5003800c0d203c5805554004c202c680005c0203c5030f202034a02d4405c016219842680c4c0001c20381d0101040c0042c10840060186040f9002a00c5d080105541020708604034860341c04001e600a800c54042004902043c0100819510940841d015030041e1620b07a00f80b00040f650741c4003040e40000812103051000d00003c002001e030f08000b4022182150700041003500c0500030741410f199501031181a50709069107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 4003092 1250 4001842 4001849
    0x207060b0a0b09030709020304020901050d030507080a050403020405070c0f0803060f040e01050a11030405030a0e150d0e071208040b030a06030804080106060e0d03050702040c050903010c0206011a041809030207 92
    0x2501c585250784aa0072000303600100011407084c0100d010004c1c90900740d000301c030300c5035a0051000d000d40e8288400c01540fa84034800580c1004414881c0c60b001889480081c08844240d4540f551075624510410099070401452407003000383c00102140001c0840510280740d580c0300420719145d990b02004070300c035036075002901a070040c1420580c0c484004103500090140889403000d2081d5910360b5291010f030f11007501d0041c806e40c820003130a0f600c541329840015030b21000a00031007040d19050158511a00328a0005580c240d50340e103c00d00306001000480024a01803d585c1c0c002e4946031034a0b030703060151f0b11407500a0b445c0000010401c100a42c0560f0195034800d020700c0c0c40e00c0e103401d0024003c0a15008180104a0040743c904441c034003400d000440b0381e40b56072050b03d000d9241c1d01b88406440202d00040078032005120038440c5076000c1c050701030320f809a82d0080801e9031406208064000410014907032100c41000140f21040b1f010728499085129a0008500252646400c03450191181e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 4004342 1250 4003092 4003099
    0x100c030e0a1706010609060504030308061302180103060611070509040507050d1202010507030b0d0609030e0604060e01022a011803050615030d020d050d0e12030901090b090607120207060b 82
    0x20021a401c82d00c4070302c80702442e6485084844907a01ca4401782d808040500820010400900c01000040e01c90800030341d0008001d40780c444002c21040c443d006030303000012003000d40000c1411900455070f040c402e1900405903454112250000b880382151603002d00d01400707015000e4600010305020703003004408001c20001d0400030000074941000201c2c0c00c0080c40100040d420712020030b031164841d0080c2d121030140102044094040c554655000340500d401c22002d05c2200d05a401c020350714000600700a12450700c41c013248265084c00241041a01044c0300301c0f0207400007030072080c640003010417030314420300b07080800104422003550580c0842c1984002c0842c811803040000d42d00c0c03600002142c1001c258121405a1907400c001d82e1178902c1000c2550008034140590442c2d4101070b0004c099950402040c0c1ea050340c1e8281e0700316030550044a010106039168641d1408000004c03400c590300030a204041c0106041601c001171991281d468443c0400742c003c00d2400030b200c0940e00c050752120b07006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 4005592 1250 4004342 4004359
    0x151302030c031e07060e10050c1c02030a02010c05030f0f0402030a0f1208010e150f0f1306030c0b030403080708070905030a0b0702070801020405030c060a03061a07020a1202100c030e 80
    0x55400f0310074521070f1035a1040600920f000003441c01e02074103e08842d11402410130102d07500e00c04080303a03da000074400c4002c901c50043e10007401415560603408072202d55014540d156580341c0040c5c05d4804400c80c071000c2040070000c0120f01c0c051103200b0754010082c0c0c0c0e803020381c9841d1400000d281000011001c0d02d58441d804840c000c004010304440c1034561107480e0071146a90315000c141e5060411288448440d04804000c03009281054080c0c200401c010500e08003081c00201045500030542c00781840310355190340500c1400011500c1c08010028411900e2840c9042e03640207100c100b024000c0c106003d96580402c1d4810f000d41483c40282c6400f4080315074461407801c0400b0680c0c0140c90000240c0030b0700c0400f088200c41802220140d50f000703001404080d4601040c4200c96000c1681c00007010360310307032010505020f00700d03907400d08054490b50305882d50780a004003d02012a90b00c1401d00c0c0c00c02549103001a10380b088064030415041c14101c0c0822100e081c1174070074410007884d407540079454 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 4006842 1250 4005592 4005613
    0x2071109010b07060b0d0b06040b060d0606020609060109020a050403030e040207060e0303040b090105010602070501110703050105010e090f0604020a0303030e0c0a060309030306080d080402150409020d0b0111151302030c03 97
    0x1001c0c0680f01d20750240c0c03014003a010701001440f503908003a4070042c0241c80c0c14400500507007420f411040c5a44400fa040ca883c10749449401001c80b03800350001c41c01070304840c050250221003002601d0152620400c11807402d00c05210243c0706114504c4010140030205007044059921507040d1441c5a400c00810b00030103d40d8030700140c599008590880c1c3d20303001200440c44005051160b070703050345d5181c2c0023051224241001590400445800c5c0c0245108440001c8006882802a28020036511032500b000342071040c03806050030005030b521340b03003980128204000360341d0b05941d2900300d0741c140c20000742500400380f00b10b091a58401d556600001c0d03e000000c0c2c8294181e212151035070182e60100581c03520f55510300d80304e4080800c402d00203100721010402614005d414018024090104a0b182c681e8849062081e600325081d2400e200c3e80d108261465560090761300c55002e0b000101900441c44103220100c8075290290852800e0030116120f001152800c009210000700010103c407524000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 4008092 1250 4006842 4006859
    0x11103010618030506010909050a060e0609060705070804060f030912050306010e030606030a0204050c04030b040309060305010801021303060f14010905060a05010c11010305040c0b03100305010e0705030309040207110901 96
    0x1e2041c0710000d40b5030210b020a24500a04880980e41d2050150119905e06121040504020403041e0340b68090014400d000031520720440c1e40415a99020f060076107807200000782041c0004000109200041045500013013250342110142d0b0560b0500e0300741c545029030f04400501d40000e00400b031038031003030782d5040c05030704240503511510003640c0c2c80c05107486d200e0516448070303401e1b11f205030036611469440c0014901900840d521030003460900d42402e40d0fa40f14540180001d0b182603001c16050941801166418061780f805040020000c3d8684108010801500703c1c103444090843ca80c0c8039880c0440c5610f54202c003c000c080c82c0000902c5517145e40101000707140c156220b9100341401c2400065039402a0311114400743c00c00200f001340a07208d001035000c2c2100410440740034890380300100f802482c5802460007040008422a41a41189400b83c2110103406101c400c90703018040400c116900001144c100740c001355405038440c070951505d54001e8847e10707e065840019540045a000e5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 4009342 1250 4008092 4008097
    0x9050411030601061d0609060715050115031406010f0201020d020a0e100201060806150307050a0b0702040605030105090705130209040e1f0b0105030c03070e10020309010809070605070b0a020403050111 88
    0x400803025101d191341c0c1c0b0841950b8208484002d01040f0303c20500d407814074644038000d040d000102818441c13502c0c1c8940c1d00ca0300701c00e150109006845580f1001480320342440300c1c80b503803a0051401c0400883d00101c1c10394000030f000500c40c60412201c501040c139154800e406076031010290035825501ca42120308040e0040e200e4290385c501500c049072590b40002d205005a9040f0f6012801820460301c3c0e4560300b2000000a041c140c1c4c040c85810300004483d1102c04c038000c01840c02100c4103031035a610340304000645045c1c0c0d02881c8a60b05080c00d2004115000c180101100c100300d900706006d000c01d22228000c0c0c09a0481c42d94418602204846c8007400131410a520348450103080e804a0036520b844400c64007071001c0d00740000c1080c400202d0125240380156004855400c1c590000701e00d01001905c06100503030200010382000c103078481d0b5075170840340858000600030060074229061000081c2607014118000d05036480c504042811000719a040703c01540c0c21a000b445540101042001c00e035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 4010592 1250 4009342 4009373
    0x6030902010806040501030305040501080a0e06040c0e090714010e01030f050907030201020609010507080604090809040f1a0306010308030f060d0c0603020414041505010e040623010206010b0c030d1104090504 91
    0xd40c602c0009605140510405040e0b940c16103916052034149001100c1c0f1070f00c014002129544e81d02d0441403004010481039201e6441707620094a101e080c41c601c000c03404030142c03030b01c070007030303002d1a01803120303c04030441c59036000d00c00e00e00400c1c003003000303801200a00400c2c0c20072841d440c6820309005482ea008110102a40d00070b800b100e10b03a89035008010f08840040741c02c0c01c00941444041000c41c40d19800420400d03020b1b1100c542040d4400c000a001c0b03c50211600b00340a0b501c0035460780e405000d1139061f40b1000b00304c1c090002c0b5172458813450300611004041c560003401c08800140310365241b960212105400482501c01107866080c040d00a50241c0a00711824024400400d5585130034090904201d030000721140306145008019200300251203d510f80c482d0f103400d008914400040b601101c0021102c00f181e40c210444c01c0003a04004040c0c0040d14629410804c02012540000c1110a0360805a40000d60f51801c008840143e004640020b41840d0034542400706100b64000c1c0b41801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 4011842 1250 4010592 4010597
    0x608060402100503070806010f030608010e01090201200c040902031204060c1110020a020108090c030a030504090606080c0f0705150405030a03110c0706030e12040807060201060603140c03130803010603090201 91
    0x8100c0c0109a5044c04100c0d038a400040136880042c1017035205141e448070740030300c0f400c1c0803500d42d445858403403d5660340101c01d03106a548144d41415980c0c010300703001130b604d00c58a404024100c801d82c1a52241002c142c00c2e40607a440f81d500c0401c54408110446485241d01710340e035141e640740c1c1d01c01804910644019242c000010080c0e80c200d00d88050594503084081d0010180c0140ca6801901d2401c4020004802ca00506186030096201130080750030380c911076034600c1e42c0c5505050f8103501b1212182c100104100c0c05004000d0480424412542200707100c101164072003400b0702d081d51910340c0301440d0100b0341301010180400c1140010240801d0246510103100110103030f40e05800f1f6000d17148284900f07a00ca11010444180294460804101d114060f150340c2d6070254403180142d4490b81c0008003544c403040041040c55828419100500707480c0c42c09020388140002c00320010a00074080030b404c0d00c80040810032a014845040c0446944910069207a40e036521019005004ca250141e02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 4013092 1250 4011842 4011859
    0x90607020a03150b0f10030b0102160b1b010507050417070b0d06030b060f0303030a0e0c060f0406020d03051e06010e090c0c010c030e0304030b040305070b01030b0105010f020a0b06011803060608060402 88
    0x145440c0d0300550903105c01406041c0c00c20940700040707000d04040244035056005e09094205400e10500b2a100548400d00c0160340c5c4241035030805400f034034406041d007540c0c0d02d13250510840e039600c0000c0303e040755014604542511104512581009019803140e0401040059400c84042c00e6401090440340207001225250b034aa1050191600d0075240e0141c0c0743e001000000c50600c01035201c8810943c140d07040341c02c95500903021541c40d50180c201004402c00c003043c20804d15504004d02c5540c060031745014400c50400d80309400c00e20f2030380007e00c0e05100494001641a9108914203031110000510030b030254100a40d910541da80464074000c0135500780f000d00c48240340a401038001b000022401586800d1554075900b0582e5006001102002400c02401001c1051460070501850244020911552420340090010510a800c500541d0042404000465850b9030750a170310100c2820503030040c249008040d00c44003011b13000103004c80d00d00380011a0a24000480780e00c07842c402d807139006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 4014342 1250 4013092 4013111
    0x40e0901051608090a020402030a0605060304060905010b01020a15090312050403030e010605060406080c030705160b100f0e0a0509010f0903020102070b0106050c060a090206130311030d050a14090607020a0315 91
    0x1c40c2e65000304d482011591044e51170b01c00506280c1d0085034854ad04142c001501034443c00091111350040c0d4040e0340190300c80310f4039001d208080c422011101c0c000d00040180c40404e170760f1211700c00f803080d4050310300550701d402503414580206503c5550b0300204400f00711920b424900a401080c811605481562920002080d80d041510466051b5003490325080c06076034406003002d909900c001d01120030090180045005840100e16040229125524040340340c606032250340b10403000c987c01074440c0b003c0d1140c10003030a9080007131907405c0340050780d003c0355940da980f8210740503007008180103102d545400111024076a0640c054903550380300741514141c03070340c0c0c9540c200d440c0d000f41c044600150300900003190b00b0001e01d0348032100303851004d4036040c1030081c0c1d910f4541c00b014160f03100760f0340b80c40b44100300c0c14030780303418021090710b0340540c20070f40d0900824041c02000803034000200711010900103145181d1b41e448005a03010a80e005100001ca40c1c0c880c94050b58841c4c1240c54403000d44c2c10028441d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 4015592 1250 4014342 4014347
    0xf03091401050405060c0a0203060415050f0103030e04090201020a020303040b1201050303040506040b0d14010909120201110301120201050712030204150207030209040209040602070f03050a0e1c030c0305040e09010516 95
    0x14000c90503901c060800c3c0c28402082480c0e40b12801c02241d500c100340e80300b80180c0f003d00c02680700d64040c0c801046034005250340881a0b590017013804401e5440e00d0014400660001428001301c403082c1c4000800401500c01030b80340018005029501d8130010400080b01c501d01402440d45035003895050425980e5001855520700030b50103901d900581c14003080c0004c545000c0039044051448030041003080c00c00000da01d181c0800c0e002090b0007900c8042c21400e002c03801541c2e00c0316030f01600c000c0103854550003100c0380d640818015401c05241401c2d0030000e41e84203034152440240c00c074520113040c08000390042c2c0254001d10400d80c500b0b1025890000150021503100202c0342c000e065000e180d601c42e42002841a001001203178a01e500303101c500c1c04580c4401c03500d52040d00c04d8641030713a1841601c1002d015000342c2424544103016010040440d0710038010282d8400350301d8209117050f0f51503450107581074003c64003c000039410300d004111502605400c410300804403a481204143c1204808 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 4016842 1250 4015592 4015619
    0x30106030203030d0203091005090c091e1501020106170d020f120d020307030204090218040f0603051002030402040b030604110901060309050303150102011803021006050405010303170619030f0309 86
    0x6580b60300140442d881c5092183c00959005080406a40301c4400210001c8203c50043c0c070903074132640c01400c0041c0d09040180740c107a00300041500c00001242005611401d514004000d0207650510301c0ca0064280d000f508040050842803443c1e00c070205109200c41e91f54040303010850018441c500c0a4802c0080100380301c40f00000243ca014038240e10341d8001d0010f5440502900c04165081100007223070074083c406068502414406180d0080c003ca08010030b0350301d581c16100030540f600608000188002407210a2401c900c1009a120380e0b42d400024000e04251000d20380500506041100f08452910b21421f0020111800394883e45c03680401c504a0f80d0558004009500410115400d0043c400754120401014400890307107901c0c0d14256a4042410442100980d01c03403140306901e00500d01030712001c1d110540e010019580b5546008008a0100100c10000000303d408585c21b43c440c030b040c01c0f0407a452003445500055491420381c0302c1c62000c080560019210b0240802c000ba01c143c40d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 4018092 1250 4016842 4016849
    0xd0b041505010203030a09021503010617061207060c0501090f12030c05030c040302010c0c05040c020102040602060105120a0201050a050f040314011401061409040603150507090b12040803090a021518030106 90
    0xb1805e50303a440c14071070018000e4076426644004203487d4045609250401103000e400c883e80e8000044403c00f24100385800042d08803481500b0410410110a00014841007100c00c40e103440d41d003410303050419a00501c0c01c004003508483c4e0300c0c1d03404002d0100440607040314141e9a1350030000036441388000c48a5002c1171303030104c00c80482000200701541c820000b0b544014003d40c0300400140e91600018200ca1540c1e8052025035000300742000034130740500a403401082e06668881440d1074800072540c442e2003001000b0b060100100d922181e141c13141e000d540b59180000940340d9103030780ba41007800702c0c400c9045510803158203288018541482c1401c09504076032507500d481e100309010019810302908103100280d00710381d940b41c00002003500c100c1d88401c00074076941c000a090400e401c0091150405400c2040001c004100c0256050b180d140072503030007900031820343d460751210200315080800c031000c040d50210076454011880d0000c4001000075203298042550700c5007001d4145401e0310051711 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 4019342 1250 4018092 4018097
    0x7050903060702030702090f1e0a0501060f0207030b0708090304030813030b011d0a0209010203070503130f0602070b0306190306021317010908090904030c050a030903050106060806060a0e0102120d0b04150501 91
    0x1f010544500c5455080d942080d002c800080340f01c500414040b1008500719010038030b1030303200c03001002000e4010350b032302b0703007402040c4050300610b03045444082020750050070708030800c000c180000c1c02102e021310a0700c016683c080c05055441ca01c40c0584030075200580410354080c01e4100000a001c5190b100b401440c1c09540d0303094009070b4815184400135009404044e0644c001008104001101400103101c42602d0388405401241801c0154101d480290008401c4d980301040030b0005100507400d481d4440c5007202c0c424040a410034a80321082c800f6030004119600200ba030000080141c1102d400b0703509500c1c102c1c1340c103a04d00074203242a030700014006421800c04204410345030030103c0c8501ea110b07000b4105940c2c4240240d54862600107001c400b540011503c160034400c2103401e000b41d00051503186081d44003410311100041d9644100b00c012011701c40d51300380c030240c540d00a00101c24603403200015281c0303400d10448884090140d440a55125038500050600201000440002a2541070703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 4020592 1250 4019342 4019359
    0x20304030c030c110d050f010e010b011704020d0807030201020a0f0201020a0f0503060a2c0703092a0f06030905010b06040b070b090307020d03050a02100606050f07060b0907050903060702030702 85
    0x351016100352040440590342c09000c0207218802d0b443c0c1111710682184128000d280344820b000c0d13034508480000c2c00c00d4201c0d90510003d075a82c1e0380c0c0442d10081090300c00d0701400c040d403524030000d41a181d10981c010000300e00031030300e8018107406601401008840391038030090800c80e06400c0f8202d1040d900b020021030000090117401034400c0001d0b5901003c0901003181c8251a50f800884003030001005210b8012150160805000c08203d9581c1108407428280f001d04810303900c00c2900740c07442c408120b0185103217090001c5030b520300d8440d000401040c50404200c50b02e5403002000b500d0004003c1d0366039070a10602c8465420080d080300d00702c4180143c030320704205071a500c0c0000000050a03a100c0b0b40300c107000444c050f03603c0180513440179120f922265560000d64002909040d0110a5020b05626040d8104841030f0000300316200c100c2e064008507940c1101d480e281c0000c0040006594104080707000700040d079038000d03004140140b01101100c5040e40e6900c001ca980744102d80b4025005982d8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 4021842 1250 4020592 4020617
    0x206010503032d04090603032003030c0703030b09090601050312030c04060503060105040b04140414060102070902090102030c011a010305010e09070302040c0e0d110a0b071a040c0803040306050a0f02030403 90
    0x24039400040c511204640f010001220495100454225030050194595117400800806070403015102503600c2140115807140c44201c001616400005c0c5044420340c0c002440070105840781d0311000030b8803002440c20b842c41c00c158400e40e40c0c45109000d407134041c1c1b00d01c410700c400b00a000d20a070391092101d48070042c139150402d0000ca585400207856541402002e10000c240006024050700207080303400d2129021524000c100800d0f0303180a814101e1094880301480480d0343d0205007038040e038900c5403002d81e403980e6100c0104d10307610880050012a52030303e0040f010144400b0074012003000c0999090184d66240c9444103207000080d11755000d2644850000c1006007890b40148090b5a10340c18490450a0b00402080f0340500f1100e0403202505100c00c612500d00d81100f2038800b428001031090b04217001c568880c000d07005600611440e140360000002c04001c003d140340000707051b078401070344d445590303900e00440038042c180d52840da0b06060481d241c030168114401c0d24404d907015941d02142140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 4023092 1250 4021842 4021867
    0x5010602011107021c020904030809010b0d02090406090201050409020a020a050c040b01080f04031709030306010207150c030e040209060c060f01080a03050f1b01020301080a03020f01020301060801030b070302070f030306080d020601050303 104
    0x10024100040c42c0f03055505e040966524400684241e000fa2600c52142c5403201480d800c40701c0da41c40e414441c40c20781d0200c10158642341d51403032344150300c00320003d0030242d24001a9082e005541c011800c0a0000406a1030540c0c0422a195414071902c103d034074034103a040802054643c5824400e00054400d40010145100c40341d2858001740031303060140c80c40080340e140c1e5040b02c40848013943c4c0e641c00082070010710f5034100860310003041546803011001101ea1401021503151800250401070542030001040da520b904460840c03600400a0740ea4003042c4091684a2004980d8144980031080000820310b0010642920156266460038070305070700f00b8043c1c2030726003240482c0311150b10955104c51418400740300446c06400303250001c195409080c40d00a14003942500b40c134074a03034010310040200c541c01c1020a410f6030751110b40901c180c0d0f00c00b207084000740200c240141402c01a82d18020501d5090b6018205407400c42058598000e29218160b94030701080c0320300b90301940108018036a885 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 4024342 1250 4023092 4023109
    0xa1d09060f01050a0e03070609180905120702031009050105010501080901020c0d050c0309040509060604060914010603020c0f010501030b01050a120f0b0907030222150303050702010309030302070b09010f0501060201110702 97
    0x14140170b070f404249600030a1624000d034000740003140c0c580a05014919550454a01d604103e000c280b102d40004d90382c07242c4400701c0ca041380c1c041130703808148401156424001c600200c5d040d51002c004c0c10380d0608055010304020322409011811000c082614090103000311203100401d4001800615011031007220700740e0052088036010f000501100106236114003e00f80a00d03110b0b4001d14050a000c0200b000711081507005020700383c42d003c1203e1071401100d07405411600682070040e282c09074038440703a04003404940808003951800c4000f00800c111044501e050360f20581d040c14140f41c48402580c0182540103020340000c03190480100000c0d15801e130958450105030640e44c065541c2d901140040c0d01e0400180c0081d142e089210301c80b10740e240315154a549010742d41541c81886c42d1000f400604c503213500603040548401541050502903011100c0480d4019910b819624060a00c10300038503a8281d07142c0041e007400000200b5030702c14021501c102c03130132066051400e01c0c2a420002da80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 4025592 1250 4024342 4024357
    0x30d020a030e18040b070305130209010b0901050408030a05070c050a050618061c0b03010c02010506010c0b0406022709060f01050d0b0a0503030304030203040303270303030b040f020a1d09060f0105 86
    0x50780c50b06500f100f101c40403020301862250091910301e013041a00a01500c2c1c0042442d06003404004002d00965203406002e41100d840d210308681c0c82000c0401201c2510840d0000c1d01284000140c0c0b0f03c109500500a0254900503100b4441c999120301c01c0001c0700e0701300d100f043d60001c0c00380211540c0341074817035a24404030002003169140519242d52500b442d90740300c05a800c0503540b08034140403400c013801038841c0711045100030030a92804000117403124001a00c0034000b0080400014200701d4154115580d0000c9101030384042016001282e11018113041c065010b410000c0c04aa003504006040c100e0340701050310f500d4100941044030b4001001298091584201e68600008054030b05100640c0201c0c000da018503642d41c19030038060805c000c1700a44400460000882400241030f0038580000e80358180340100e805104200028040c0c22380316003031405d00f4800100c005c0f4454101e800006150b403400030403040c64048004110038988200c0384180c000d4801165401c641d07210f00010308070b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 4026842 1250 4025592 4025599
    0x6010506180f010e0310140f0103050d050703020c04090b1602010501080c100e0402070606030507080607020309010f02010b03061006030b01020a02030a0b07090306140703050105030604050705010f050702120d0905030d020a030e 99
    0x10f504c40700002441c10b92509000101c881e0b07285c11941a20104420180e070090004c00103845039495940e803203980307800c045100310400a0205801080520a11003407900d000d000780103000e140d50906040345a4441603402070480e0000288604500f4018082c4030b040b1071000c809040c00d40c480100340451000510703900010000b41074105200e90b6540c1c030250003044e01510700041d086046242251a140407604408203540c4001d0420686035800011101120b03001e103080c001d0348070750600680c05841880c1030158140140801c203c180f90705508103500310792981d40c0c2400b03280f42160040e40c80c3c16036504044d401d134019000708400300300340070300c40e9401401074501412541c0da40e03203d04c000c5401c02d40f4170300c105194000a1184003541800340b203000d00b4085001c2d00103410f06944036a60364145100d01c0c2d041c0007d031424942a940607600f520303856a0042c107400d0640e421480310070380b50070400049001041c4501030208050a001886244e02c110940060200c0a03482e18262942d0007100d6031309a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 4028092 1250 4026842 4026857
    0x102121608041e08120f07020a03021206040201030b010c0804030b04030203090d0602180a060e040504060b040f0e010501062606031204060201090201080a0506030a030c080c06100806010506180f01 86
    0x140c0010014030003041030f51569285040c0486010401d03000300d50103004150b000103140354051010700201d43c079000906000360344c0c807503c620205118271342c1e60340041c0d0300c00d4000e18408010030021494500c5240300340d0342040781c1c0d5050401541c0e4a0186ca4010301050410302050001640040810781c0117070080c0100e80c2050385400004002d00c461110485040f13802007110403101d40e140045000c0200c0459041c0c1e03005081c80d2006009910741c1420038812501c0340c01181c14090300327502c5451481c001038001d011100300c20701002d000d4500e280a0485079840c0c4400001c403e885800302400c0301a01080285c200020030700030b00307007000c4c02500855045c05894440b010401c0301000030401000340e900080345000c241e000240078a0001095180700302d080004000b01d9a5011640d007042c076034182001c02e0841c815040014060164925684e8548203071780c00d0200b80a902e07081c10048982038130448110780c0e03d450521120b0702034005280002c04840000c9040c1d4540302055a403418010300d041d08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 4029342 1250 4028092 4028137
    0x301020409051e090706050702130f020a051809090604030c05070503030d0e0606030d120c020a08070501090b0a09020d060b03150a0f06080c0d0803040c08030301030303050a050f06010212 82
    0x40b95403d40d0002c00c280a40c0e06407440c0080506400da40c0301e05100c2c040c003601351601c1c001030000c0c450b00800a10906a020500403190b000d5444000d905500c801c0464888002c074101801a5000c261125107401083c000000d251404074811407190010f1009803411b0340f900e03179082c0c458a030300d0b4a0442d420b010310100070070a0b45081010b0a2030042c206d85c013080f000818801c3c1410104081c11640c0030782c1200c5130400007181c103c0004401890b01d4000015035500c0b040d412420300c60301d6500241002c2c000903c842c24484150072180036a8024014609951541401c081c00c5409951009402000ca0b004d10408100d03690303c10502d031172001d4181d801c11b40b054141b44900b000100c840e510110b80c0c8004040c406901442141c01412440c4014130102c3d210200050070300c01d020f0001414010000001000c02c090001080020031041c0c0c200c035120b50f104d01e00a0081c000c1201c03607905082c036100004070402e0308131140038080c90040e0080d2008881e500070262941e403051040001c650501040300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 4030592 1250 4029342 4029359
    0x11808030f0c0a0b0702010203040606090c0207030b0a0204050303040803090901151d0a0302100206040302011a0306160e0307080307050114040803060d030201020c0318030c0105030f07030902010c0b0c0a0909020a020a0206070203010204 103
    0x1394814030a6a0005075245446d2801104039107580c0c0000301c82620b400c440360011a00060410300b0389410910002040d82c80c1240300000c1d00c201d8001da070700740c04040340c0011134540000280049550450741b0027116038032459480c070454102c07043c80c000654032013000d0001d480000c501450402c80034107030718151500d80e00421915076041c1c80040050344114200130038558203202d402d075403032040c1c42603103080034048001030340d1442e000d00381d0b0100036200202400d6a034080c0b130441c1c0b44403c0141c01e49030100d680d60f40d42500c03a0807003002504c840d400c2c00070060a040a00c81c14921680d881005241141c5440050041d840f40c2d03042c00b1015594200420414a00100050080440e0465402c00c44042c114249410300c01541102e030b050042c00c2c424011003c1c0260550f583c81411840c0c00580c00c861030004a807510186240502214402424001d46003403100041030802c441c0d407501500203030707204000022071003400b10520048e0030505000005180080080884e140010000340c00c2c142c40340c0c4070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 4031842 1250 4030592 4030613
    0x4090603030503090d080114040f140103030f09080109020114030901090615050a0801020a0c030804030e040501090b01180501080604111b060103050d02030405030706050901110f010b011808030f0c0a 87
    0x240c0202e070001c0100040c9100400c80500310011a00e40300140b54500180002081c0f4101800c0e4445c0e03071640040200f1185680c0b00d0788101c5400d20144623196034070308000d01030920491760800003a0f000340740032692034414043c070403c596043e1b44203080b00b01c4c1d5410510403a000034086034140c0d520307904002c000c10030341d016078440040311101d551240c0d485c1904100000345194003c0c1a6a401845041145a080b50380540c0050b010704144103070365914681110201e013401c06050703001d0710f0a0000714458080f5400050303030500a0302c0d1905c410100c0c07600709a40172800c3c86150f00050b85000001c099080c00c0d00304003684014650010305019580801c4c114241c806012040c0c0d55001340010418040104194410020180040d624103418800465141c021901809050000c0020011641c2c2d2080185c0c1c25450300100c00d0b50880c140d00c0a4490182000810540c00501c6001c100c154145000c2529021118030030000d62030004561070042c2250018580990940500c3c940c641c0030a80c1802d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 4033092 1250 4031842 4031849
    0x5010b031602031c0204140a0509010504020702010c050102030a020706060e090601030311030c0a060f0b09010e0c07080c010e0a03020c010201140a0c05040f0612050a09030203031306020d060e0115050f16030203040906 95
    0x8017680740c6003000c48010744095464170342c038400c3c04259003c02980d22014a10b41c1582c1050b14056541d090b01d00043e1015a0a01d1009000350310010800c40400030a07800b0305022441814148140c599071003a00c03525000a507a02109030308840010000a402280c0d550341103145c0ca41504c0c100009800300c1410041c81c410180da401c3c0d00d40074080d0713040380144a034941c29141107502810a50400118090001c001400c3c0501075000060040521801005070340d00c99542500a000c0d60803e44a0340e6258034090398110050310448070302810541c018061258101c01c80440c3d410303e9590300c08140054859440c42c6008c0c81010440400c4241080c00010080d00c03c9844030210014680f1414040b15001007103544c1c07a03031400c220580029400300440b6040711202d003160ba0301e45002e09002e00288102c18450001d03515080c2c0014003c04545082412a1031420490140c80d03c04030044d6980e118910701a201040b0030402200a89910f030a042d10207802441203078185502d0b52044411900d0541 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 4034342 1250 4033092 4033147
    0x1306080f06040b070c0c1401020703080c01140606030606090103051009020705030309061302090106120b030607032003010807030206030703060b0d060503100e060121060504030c0b090105010b03160203 88
    0x4041005000760080f210f43c0195151038848031107480c03034030b0341c0600d15003900a41030402d42d69501c441d05a0310810200b070103150020155aa6080c4100c5154000c0207840035030850510782000041c2507150100660707200b10000713414a4582844d903c01103000300302c0142003c068003060a8081200c00480c400340100900c100001c641d00d05080d890180b030150001d103003031282d204031000300c001619105100c604454290400720008a03401c0c94482c0540360740403a80350141300b98800c1240d1070f03038503400110511048811181d1703908207074899811188030034007500c020b13035200c15000c00060412600850340058649800201c0945440d41458540d0040c07140303510503a01c84030284902e1505002555181138104010055164015540d42e21a0070510441100d02c51120001a40c54a04012403243c00c1e0700c106e0800c803a00d41454041c040302004501035a0020100001445119052141505071103490020605645d2140600074034280200c3c403039011804107000038454442c43c0340d4995201029003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 4035592 1250 4034342 4034353
    0xa0c060207030503011a040305030a0806060903010e0102130b070507030b06120307061505040504030e1002010603020303040b030106110609060402150c06070206010618050f040902030c0a030c03120302040605091306080f 96
    0x203801d1070054843c04200c0d25107106c1000100b001482c0001200d0325040141403d8040b03039580070002d43c1c10701484245a80550810000c0080c41c03406600500c0c00000c10944005410748030004080c842c001c0c15030062144d48035420a1000c507000001d015400a0018012a8000c40912446042d50000710003295a16100c800d01107090340740e0b2810201520301910304020500c3c0c40d840c0100303101002d400c074a015020341401412103920030b422000103550054200d83c0d40f079642e00801180d42c0e0007441130000080305140d40b150b4141010407158083c80c80701e40144900e840707a0b020840344580322034a84d10304c400c0420152148450600060780300341e56640180405624042d009040008985000003880e0703c0d0303c0c014040d5a450918040c0743c00c1042d100041c0440d40c61011a00d0907030000c0301250b00800e0480c0c0001040094a10b0505507880703880941310120346410260180c0c052400ba000204005000041303075424940300a04406a0100700031403001d43d29260182031003800091304070180c100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 4036842 1250 4035592 4035599
    0xf08030901021009050102090a0e0a140c07030c0503040801020f040e0a0c050a0509010e100309120201020c07180204030516060207080102030609010b070203010b060301080c010306080d090b0703090e01060c0209090105040201140a0c06020703050301 108
    0x2840b0300c0740d400c3301c24403201d5038509c3c0400310a401807007075404c001c092020003a150801c3c4a002c01c00d40d0054402e030002156242000c405401c41500148a44280c1203c040c0002d4804099170103040d18440351911258204140200c05aa61703400c14400b841c1081015001c8034090b81e1a1030b0304000c002c1e00b0b501e0000e4508003e04080686680034141201035a00410a87c000c00b040010384a080302c1030041d021f500c44c807107001118003078440c0e50300140181c403d000c401c1411640c501664802c0765483d401315030340c199482000c00d091303020443c0c01c0c42c3c1c0184000010000b42459500030050540b0041c0005503208d02c450009005030020381000720039510910300c400c855605841158042d01c5480010080c2e0b0403410740092441440e400b13040074600c00443d5040407d405140b014025101460b07080c0400e603194032000307010034201e0301c0c2a842a20460b0200b181d155042c0301c0d1070700070b58060396030841080d010b040c2101e482d44401340900801c4203105100d80424043e10241950780c0c42950f88a580394907 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 4038092 1250 4036842 4036861
    0xa02090414041104090510020a03090501020403051509060c0306010509010302090405010b0d200405040207050a0605070e09070509010206060f0d0606030b090f060c070204090221070f08030901021009050102090a0e 93
    0x304040b149000b40d05e000300c1d06010480004045503110380341c15000d40c0c0c0d203084080c224090610031000500560020074003000b000300208460690140c100400c020503640d07110107076079462050b2101100300d4020808100c15500c40d00080c50900070604001d403420000b4804103040320826401061811000700c1c805a002c0b006010360920504681004440c034000015035040703d10843c8110b500c541e0380000c1c406c082280900c942d10030240c002d0340404c101c0c80d114034050241030008007820707c2620214001541c45008100740c8002007010f0b4014091569400702f0300403428801d180455001c00d2007900c5000054150041c1d00283d84984a15200c84c140350700745a1034190712007413118180e00000201f0081e558400705881e02d1640442c0c02245c82c0740c0e1800410600c0f01003203106060102d8034a551005c0c41000070380310044407418400c140b0a241d4031145607840780610390f1403a00581143c0780b40410250035800070224180100d00051500c100e83c00090f01c041055070085a0200300c24080240045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 4039342 1250 4038092 4038113
    0x10030c110d120b010e1306060f050307020a0201080403090b0408030702150403120c0206070204050702010b0108010503010b01050a0302030901020d090c03060e0303070503040b04050c1c020405060a060203040e0a0209041404 97
    0x8040c0c4009000401c600d00300500002580c8403420395040d030710701d01604a0b80c454500701d291028003400500001c02c0c124080c00c054240740c0a884040742e0041c100740f00052240c03049030b1080003da03010f460111240c0d4011510340380d0140040c3c4c10840340c0d040215100b0201c0000b00000c1c0b00380700046075140c10703603c180302c038251090210b046580e10900007040400c20314010040d07000280d03d0104512803031032001403414050314030b01a422518050800060346e07015801284451403d0301e4040702c0303030303030715400c050070794010901481c001003040c006134640c0c5002e80c001d150003000107000907003084009000315044801c00700e03094803840c030180c40c00c20520085c0e200d40d5200c07400141c042e601c5d40c9400c0c00c2c081c04621001d08001c180e45403c0001405201c0c0903c0000100c2c2c10003403021408440d0000049013440362500c0c180d101798907080201c0c00d10710700a000402114210f40296050502d4402d1b9000000d0b002442ca85085408208508581d82c0324454a260628500700300c02050919080811420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 4040592 1250 4039342 4039367
    0xc01110a05070b0703030e0303010e0105040506030606030d0509040204170304061106010f03020d050c03060a0501090c0504180e0f060f0406060806040c0e060102010b1504030b07020319080c070210030c 88
    0x10381140340301201041d00821180181d4041e002425a25070403480c048008003047d412480090001200210380041c80307801440c100c40b0100d5060280351101002c05445440584907994107034403040b012580680100040c04020360010f00040c103190f50342c007050490408141c58000c103900b00282c02d21206030010040881d285404008211560405010000f81c2486000180c030800c15400c404040140401041720a14001307826a6802c0c1000300d9902d000e05020300a0000f114141490b080d0f00c10321802c259001c4030b400400703509070300d001c144a46c00200032015241e0460700881c284021810f00400c002c9000b0144080885044c0c03400303040000840b00c3c03c1e04400001c1c1c01070005c1c007010680701c0072008281e4900805c030465540344c190050f801080c03091a402c1d082084540e207106d00c101401c020340b040304d014a491000035510884200d03101e201781615414014031084461000511844540d80d100d03003003044e0300d807a0401c541c001410251040800d03000281c0c444d0ba00c1545260302c0300041090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 4041842 1250 4040592 4040627
    0xe030105010b04060201110a0c080304060f1401032009010302040509070b0304120f030603030c02040507021606170606030103020d0803060102030405040e0c010212090d0b0a0906020714120403021302070201110304080c01 96
    0x40c0300c123005008042c51030041024245810120204003400320b95400b101c1c2805100c00200110411f00140200070b442c2440181c0300703c1c03401c00b840e6603d280c07a50881c44444100130140311341da0f030840d800c200041101400300042c5104510001c00c41d0030b200c2c2c004600a602580720030a81090100c0010483d41007039441e00c0070942004401c10001303400c2001054015412a00492540e40c3e4030f00c128a006401c01d100075040c00c00880c00504145c00c05910304060040400344505d1355984420300446100070301c0000d42203401d040305c4a0215502401071600f001c01481540d03d0203548000050a0f81c9400056525540240000607600d42e01088603441003d511002107050a0320301002030807804a00c5400f90001408a000038602801ca6001e1011a40c3c0070004540750000c5042980c10b81c41c0b510302c002201c1c46100b0344002f1707680824007554116503000340070301844450020041c2c0a5008600100c1c184000680651100d4206102034005051000300420095104000040c980141000782598 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 4043092 1250 4041842 4041847
    0xf05040c080c0c0f07060c020310050907050d08090604060e040c020a11040207020102011407020a0b0f040f0201050c0118050102090310090210031805150703050603030a0207090b010e030105010b0406020111 90
    0x86a00701251075403103054074a80e1500c890411000302c0c2003003181c140030b40090084d0b40c40818116048459400554003c1d0101c0c0c0d003104a00007828100ca1090328007100540c840c84041180d498000e040007201c40c840c8690900300343c82c0401084881d046600030b10040741c40c1d0048150103040a01c1121584583c03803000713102e2030000b9120080b14015003085c49001e207400098010669000f50010407004d8506846400c03640b40c403c0c8000d4940000c0c00d0102d032034162000c040f5403000a6403002e41d005581005003402c000d41194010742e6203920424105206549817030001e10a179102010590909001e1800940c1d1054172508142c10010b08114500301146030076841c0025031a0140b0a8910103442d080c005840008510560b01c643c14420b001419885100c20200044684404460240400303807400d0040da22560304058032401068260030060348205403c0007a560550042301e009001818090031003000100403a003900c00903004148001ca000400f008a583d09207d040748004075035107140d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 4044342 1250 4043092 4043111
    0x30b040c080103020f0a030b090313330e0405040507080c0114090402091804120305010501090302010807030c11010c05130506040302030601031103030d0203070f02060a0e0316051501060203040f0504 87
    0x4001c10418040a4060400420a42d2403900e81d20500ca015640040000d8858903028001d10350782e9011800540150604120001d001480107004070341d0940c20380c01802440c00c080e01c10001807030303100c405941013001001a00384036440f284101802603010344040d25425003008403652814811001850400c2410001c5101c15180b503019101c2e4644221400360303442003000c000603039151204000c00da44105000c180801c2050340c080040c03181c60390340c40a2009a0ba2480103640d40d481900c0003901040c0e2840002c1d200c0c61280d44080140b00c02c1d402c0604501030440c00f0326084588540210000c0b40c80042e40c0c600301c00d1f080355110700415089413498940f6065602091310340740107100060100342039490000d030700d50381482030b2200407455000440d00c0780b41c10303c4018488200e082180c409401070f0004118803004901982c41c500344030400540ca8000700303a00f4085c000c0790324141505e207401002c9030b032000b10b110192414002d0409600441d03c0700e007000103520b2007000313503440184113614202485 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 4045592 1250 4044342 4044347
    0xf03070305090d0b28020906030604020c0a0b01060203070c050319080307030207061401140d0309150c020306010902030f0709050102060103060908070b090105010611060603060402060702010908070603050403030b040c 95
    0x6858040d4507160440c0c6801e140d0303012880704000c129008103821903610401140b24464100c40d11906901c07a007560003091403099041c03c900c181d11a00b500501c0401c00254281050307002002175503180c0c401c96420740841d494541c50741600f81c106600581000034150103102d0300f815244054030302100076156201829200c2d440901e5400c100401003000800021030b114001d50642e01d2003600300b60700340f011141c1002000d041d85000d00076205220411407080c242828221040030b100c0c0c2e4107031603287c1c0e100c0c140445401c00101980c00c08042002442011b030058a090016a0007003015401c05a1a810403080e200f0100c0c100a00c608100541c100c000c12050703034001121411a034009400140201607820900480d210300040174002036030103030502416180550059040700c0803907072440c01c80c2d1440e0300556258072054451641c55840000445c0c00340c0f8040009105c102d1050401c02c2d2010f90f1003a5060406159910640c0403c0d41c50040000b89900b5002c0d042044004440800c9083c02c8214003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 4046842 1250 4045592 4045597
    0x8010b03010e07020312010b0702040501080607200102160b0403090501020307030203070b060103020c010c0801030203010b0f031c021501030303050106020c010c0b070c0203010e0312041103030301060f030504150c020303090f0f03 100
    0x91006038030380b890100d401d042c020700031950141c0100d04d071b002e202e43c0c4401818031a5484038070708a0003249400f0000605403000b03c0d6050103808595182e80a050301020380c0003400000c10482c0109550801007004c08080718100f01541d42c0c803c14400c602880d0604014012040ca81e1190b415504100a4080002c2d4080308444142c0c0d4806441290ba49490f00100c009010b500d9002c2c0d030541c640703a400016240c120b1402d0381280c0c800c400074490390f9000001e004061845070245605503000000c0d004001c0300d0000440c54a0341e81d03104881500940300a042480b000a83c01030b40440d5850f00180311880e03042c071001710181020b003040580046541d03a04094903000504400400c00d00d1b044443c215503080d048010101020000c40b43c0310300203042c3c40b002d94507080d2011500c945d1152031807001e505000c810b4a0483d01c154461240460b503411054024000c018012201010350391a10740981c05188642050380351681c2c010b540302d150114415107007425801d43d420300e0b0380c86080d40c0310302100d00004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 4048092 1250 4046842 4046849
    0x605091503060415090f060203040506102909040504080a030b01080606190903020603010602070f050a0b0702130603020d060204050108070801080607321c060501050702040e0a0f050303070e0108010b0301 89
    0x445404c1c0000e41550080c00380d0038004181e070400d00344110038404030b600510b00880c003460548141e501c442da2050010b1295100d0311127a132150109000c0751010350203c080e8602000d03007a00d880d0910500c00a01229000c44044502c1d42c0c01082d1142003990603c14203a5146e03080c00c00c0455820400002103070382c0070f0b00c0308008007895250303922801e9510888008000b564050301c041d40300c0d6100c0d40069240d41090003a060140c10030840020301c0e1070550b04620488004d4a1800d25040558007070180c00f854840d207107040b080d00c0b0480000161143c1601e40340300c0703004540c0140c5039030801d8001811503002411303d404100e90030300107000d00345d4085403850b00841941004581100349444c200d51503000060707800071989680d915505003428800041841c0550303400120360015114860b03104450042c024140059030510440c1d00506040d03010100a461400484068540310f070303202e070a121503104007200e4541021090140b4240c009441c20140131f02400d0403c0198140101200c09000521 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 4049342 1250 4048092 4048103
    0x109090b01110109150c0212070b0c070c0303030204051309020f06030a0f020301030b06030f070b03010608070504030f0309030c080a0206030402130209030604080c1b0f010c03030209030106030606050915030604 92
    0x41040d803150b80100714820800c0c520200902c43c5001c40c0c145003103101c04000c0308011407070a12030321032050b07480490f4040d0360003500940f00d410035056407107a800f40c440050003510018010030442c404039240d1042c01000b14865a070250f619810203040c000c0c000d001207400c891641c00c12940c1401a941d20942c20320722101512001e80b290703030b04080700c0702800c0701d1000c03101618800000403040c407101c490301900c42c0f1f4058044400907211651100e54442e8640b00d060008841072006025040c4100c03155508000c06d0b14045003050303160b0700d500a44180c640d000301c0c04940448410408c0190030710002c0700405904001d03100c00e078020303000300385c4910000f00300900c00d080c0070003404e10b080d1071a0f050314402e0300040c003141d100745001e281c00c0f005c542c001071070310307600d4864807000032780c2c01001c0b103601640c005010f03082044c10a407220064030b0307a403401c4104406140d024040c00c0d0050300c2c248100c0006601401010850305e02c2e080034020140c50250080100b0154030001813816100006c8031a082a40007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 4050592 1250 4049342 4049351
    0x30108010f0c0f030b0103110c0109020306060603091c090906090b03010e0c03070603020d0608061006030b0904020f010509030f010c0302071403070507050d05030d02310807050d0302120706020c06010e0105010909 93
    0x120018041c40c8c03a17110031100c001c41c0801200105500860f5100e20980844055865075401c00000380403c4540c00d0007544a25050205840209904402c200d504d080504010761100300c0c8030b00356510740d0080d81040341c1d03034000034040b07150900502d100c4e90b05a02c041c0883c0082040400c0e1600b12a00941007130680016a4804007401c65000030001c0407031005032146410203021008550042d0b11039031001a0030700030825020f1821071141340c0640c0d0f00525524a0203064401925541c10060025070301d8007030305000c2041c0103002e00614010303410503500107035110545c2c87c203441e03100b04404071040700303a1081c003c1700001007000985d0003d03210220f401900401180c0392044c42c502c500354244c2103c6001003100150301c0441c007840c000040440844040403078868400880c040c94510451010740d01004041180d410110464501a406841901d03040740c818580041d8551100c82c0440d0110390024018400c14001c0c030005000d491030110b01e041c0d43d4503140000300610018001c3c8005a03948 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 4051842 1250 4050592 4050611
    0x7050c03040503100e0607050415110109050105041b060201060b04140d0c0602010902010e0f01020628150306140702030316030207021305100f05030307060e01060509090102030108010f0c0f03 84
    0x2001507600400009044400400303401da40b140141c407030502c0b0305110703118010104078514091025501640d000c0d00c02c0a0103d6070010040310181901c54100c0099580d0301114000b04100b0b000c0d662080780901c80402c50612018101d40382482c11f54040c10840e4075000c002d000c071188003030844048400c1400c01e01146255a000910000ca0880c0001c010440d8000000f07000c5806402c401d171158003d0700c4020b0300350f00480901043c9012141124011303001400082c1c0106c1c220903030400c018102c950b04400c1d68a654201104450f088500c80800000001040042055500405038803411544050403903007041c60029580e8000541b60300b4a441f060414090002c0c4294181c84110341c00130304045184504551100c0200000c1e0750044240c0603641e07012504011401d100c50032101c0280045180c01c141e62070714001050f02445030300965484031400201f980e038110010f4000e031007000005a40c2d514090b511821111050071071f604107130900d05c200040c40e0700b0100c400031806003401c0100b01c2090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 4053092 1250 4051842 4051867
    0xa06050403020c0604090b090105060405010804020103051f0e040501050702030c0d0807021c081905010b07020103020903010f060b030906060d0b061306090c030e2103010506070302010b040f021206180705 89
    0x1005100b0760b0407107800300d0b000801e80320903000050302c00c00a40b0403400f142d03252b4060003030b18480da0251901040c1c05001040040d4440c2c1c7c8207903400300341103003041c2c114555030001400ea0340d45c03588501e100c0c40320309050005021080c440d490700901c41e40001c5242a8842e09840c0d01c83c03081070782c0c00c814080c8140006440380d0090080d0424002c001c501c2071002007554078083e000201c142e505019440c8440e1107a2034401c00fa22500781031f02d0f07500b4001428520141c0c011006940b0503010107805541310841401046101c0c0102c0c80a456000303010382c0c40386445901c43c0e24140380200800c0c401c00204200202054031b220050741c00001c1a29000d810100f81c0384120040d20003070b800008442d14185058075031030351540c00140466244001c0cad80b01ca52179480e000d60317820032140d50100301c4541000108107600e0408001c101241c4a4000419140c4080c0000340884103e0712280c05041e4001401d1600458501011540314808482144400e000103030440c1c4004001007600050010001e0314400001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 4054342 1250 4053092 4053103
    0x40f140c1c050f040b07080c180402040b0309010b120106050901030605040303090219091a060301090903090b03010906090e01020a080601030507020a0f080403030f050c030909040303291507050a0605040302 90
    0x24000080c002c80c01c0082e10110340c18811a030a035042550030300404d06551282207194060040f8140172420030711641010840502c0340b07400d45070300030b03402c020010300c0c0112000950b208450100001030858455800d000700f6420400e0381820b035914289052003180e480f14107c6064079040040000c16035168542617004001420000c0d44c03286911114000b07120713004141c8400e5039003501040c03104000c56031401c42d60810b040c50003648a50148010300c5120b91a40c807803200b0501031310b000c00c10555a56400780456200381c120314000c540700d040c14031508015000b040342c0ba40071031000318a48146020020422040603140c01c2c1019100d83c08201031074820800040c065400c207a40900c4e00b04589840801a4094401100800d42c600c41c2c0b040702c54011700a561141203014003461a200c201e0040205400c002401181455650030107085165411030350610003c0303000108811440c400010070602d10450301c1e002e80c4018040200030005240031903080509030b40311201080c6910341740350036800c0c80d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 4055592 1250 4054342 4054387
    0x30207030e0306040605010302150a080f040c030803070203090414070512150604060203190807020a060c050f04080a0c0503120d0216020306070206010e060114030708100b1305040f140c 81
    0x503c00c5100b80802d000785644584e0481c5c0c422145040d94131090b0b0540c003001c0c007444c120702001c00da694000441045100c141c0641c410300c072301c0702c010700680c980da030b0080c050b0026241840181d20104d4604164142403003400300201210cc0e44404070f151840c0014a144030ba0903022031007190010114940001c441000440c10324018446619035880d644000d5603900059000c1c0340c1c81c240140484d00d2036003e110500c2c0140d4803a40940001c89880d2200380c046c0c07071003542c2042040300400c081000711114802510181001e807001c1c1c04094200e04145112006a81059101e074001074030b454090290f8904666407010702c128096182c02217096504010041c0c110041d401d40100c8042068032a40420014161074003044400d90503190603004680640d40120108015241040850790b5540920300c030300d41c0a881c0d03e894040440d2100040251030300480d001c010041e41d18102405146814060030341e034690304010070000b19500c0d80301c4c00301a540140c18407002c0180000c22007c640607000c1d01203000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 4056842 1250 4055592 4055599
    0x302180d050c0301020f0711090402010206010b1c090b06030f07050105041203050d06060903020a241d0a0807090c0305060f0105160f050a030f0203090102150603100509030a1e080106030207030e 85
    0x103444106c40f21600540c44500b0444680080d043e144943d8a0080c0380280540e8040e030003014183e0030400c1c040704680c031400380300001c2800c000304441088e250740250010544a29400c48042c20320500307051410402d44811b01c4103410030807003848141d030711406507421910032410b2692281e6882c24181e91620030403042c40d029901382380d03020450b5034028240b082200e1090701c0c0c8141d0681d40303013150502107200020003a0a150a00e003002c505071300c20320311240d41031140c84034030406e8089140041c0350b0304e0280e400510245c110354820000c520071171054042c8440c29050134062450300a00090030019140000790510174081500649480ca850ba51120264446040c44030046603007840e0f40d9400304c024040303000a2428000f05645440401541c80c3d0240680081601c0c101c1c100b504a5010402844160580304038036042e0301c07119450044030300510140000c2c40c0e4450520780010f11070310481c161000780c2000d070605154107070703401002c50341100c84500e80143c4840240c5002c84819802e0a0070551 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 4058092 1250 4056842 4056847
    0x102030108010504020f060315010e0609060c01050403030608070503070510020c0303030403020102040503010f02040b030414011e0e070608010b040306050c1908070201061406040b0304060f090b010f05010302180d050c030102 98
    0x550074415440700307000714002c50b625803c0e10428400c015aa00c002c54107128855111f412919a550146000b580303190801014142403807010b00110b0096000740754000c440346e440f00180410303d03070180700b5500a03100180240420b603042502207540c0b0003030f03440307000e019001703007403420414034801d10800310a44401010340c0d0b40e0f81403074140207010350400c1c0030786031181d403038100c0460490343c140c400c880403181d01d00d4489040d82c1c0d90344c4600c45285d1441c031000f0400d540307400000380c0c03444656201c2c8011445001c030016000b410070045a1401c0066000754003800071910060011003401015101143e600c0a80030a4507550505812664090b24003240c0c00c2542005400c1001500203860620030b02c1c1643c000c005e0180c0c0d504000b1803265140b00540d400040422080c00001105001917134824002c41000c07400c480b0036580481110940d81003500d90103501c000510209090740c50f408004e2400f4a0203500300b81c00c01c141c2c002c0c0d1049123008684101200f000303107030030000d080c08050350f0700c20b00800854 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 4059342 1250 4058092 4058099
    0x90507050a021515010309020102010b040609060311060405061c0603050307080a02010c080103020a05060a0e090f040519020f0f0d0c090b0102010b0307030b0105010804030903060213030605070509150904020c01020301 95
    0xd00a410040d0400054001c40f5642c9402e20101c5407950721520264034a03840c110f0165005500805180000b82e0441d503d4643d65013181d01c450180e40010045c020300099040c0c51030a04000c0c81000d5003070b00c0d00c01d2500b00f00402c411342d07840c015a01c200e400110643e43d429003140c444001450b00382d00c000c4c49800b001c0341780814131040740080c0400d640107800a1080b410080000c569002e4240002580030b0706040c1d00b400745081c00c802800001c101410303c2e5442038800c00004100e16421500003000b10315103020001040003e0202000920b00f180c4030340c0f503440c91640000c40c5041440b6071240517042a491042541d51800807905405412400c0b050718192519070820251440c01c2c5000d0156003001480c20752400d000441c0412242c001d03258082076420440115041c240152054003000041d0102201165041c40104551142811114071140c80c620380542135032402851042031000034417400003a5101d2828400d030000b4001001b0b9500c0d624207001a00a0140814040140d8800700020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 4060592 1250 4059342 4059347
    0x109060504021816031d0703060204050f010c0b011202060904020d0b040608030412060c09051c02010e120303130302031b01270c0605090a03060504120801051c02120304090507 77
    0x200d0207030340241d0b2440002901c030f40d800f0000d0801074810400c2100d02d04404049148a0b03481202582840300395211b0038448100300c1840c141190300700743c0c0c10301e5000a040245142524590109200a0824225204441e02c8480100340144a03400b94107880c2440d03c0115943d030310890b02411401007045449d81501c4001d1402041e101c890315000381c2c584a40454142c000000351411264007440d580202d4440fa60307500d0140c10104661024800d80c0704011903c2e035541c84190611103801590543c00709031600006101030301039041c1a001d801c1c0703c030b0030a51500b008000c80360b0000450b460305240b01d0061600b03d1452003062030b00d4841d954290f02108203810b040d000250802e5110441d41c40c00076200d000d890001d4102800240113410f0082c04020460044010f0841c0c0ba000070400c0900e19625180c2805958045400f100c851480c245d540542d44e4000601501601c002e4500419480d200c1c0c946000040450401921030710185100001190003042101c01a142540040c4001e04248802 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 4061842 1250 4060592 4060601
    0x10908070807050c03060c220b0301030b0406060e01050105071b030803100e0a020c03092101050403050a0206070e03031c0209040207030201020910080912030402030102071a01050a0504020306060d0e0a05010906 92
    0x212000e0103144d410070001d21300014007500803010840000d2414850004201135001c3c1c86044680c1540c007104000380642c842c07006540214007442101200b0301d880c1c5080c0007100c030306421500c411a05000140f06599020302641d001ca5849100d0314035030720a012a00c2c0c2007201a610041040704000700704018a00364840740d40850b40c84d610130941c66103400f03e000080e4010403641344960703401031090284a00e04081b00e1442041060a908a9480b650020b5802e441c000c0302e055010820024014110700d0f03040085944c0040d01d440d051440b400d690f070000380c4910640407503000841ca003034103034443d100c030340e904a9082c05002002196034040031701e0064080d401100b5418801d0f0244a942c440107801640400d10502e0341c5005001ca110704825165100e81016000ba40c05660034000400054040201200030b40200030071503402d50715010800c5490102c83c0c00c801c0c0105c0c018818840302d602c840c2c1c280c0c0d03a030360300212010031400d800143c41441c00d40801d001a00715803d0940880601041750b01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 4063092 1250 4061842 4061857
    0x3020d030c020114040b0c040e040609020a08060906010603020310180e01060e0405030901050307030207060e01140a06031a070e060307030f050a0903120506040213030320070602030406030c020109080708 89
    0x301032081800c140e000781d00300c8a4000505000c056031000090016542000d610b0b484010010424282074860801001c5503200300c40841d032480c0d880304610154074060032404020003c00d002840907161010426807a40018400c4500741074003c80400c496590000c031550140101d131881c04812040c1c440213401034150b20261050a51070000003040326a20360403010707c11038221000711f190403041001100c00d580028076250402d5400c2c0500c0000858600404904810f10b40001c9902c640890026840140160180d02aa171400c0020800209444010100c905030604000c02e69a1080c2c000d032070b40010301c40e40d150701c031000204010245405920810746480c80e0a800c002d295506110501281d41c20600a004151a0014100b030380320640c0000754083c00145c800f5040c000e01840386200c11042d0740086002c500c0d000254000c80c06c00329913860035030780c0f43c400070100e0529041e00a51203120324043c50080540320f004032800309000750842e0074200e0340121400ea941c8150f0418826680013400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 4064342 1250 4063092 4063097
    0x140705100b010206061c030507020604030602030603010e030c100905100e03030a0605060406090918060c0c050105060319080c0106030c06050a020d080c03060402070f02030d05090111120a030e0102090d03020d 91
    0x550740215520001d00d1074456400541100d141c00090710030481c0055040074200d0420008000d00300040c0c0f100c0012740700541c401c5c3d4002da268240ac40030903003501d810200c0b4551903070007070204810801e40040c00449404035640001000002410210708210905800c120050f00b007078102c5040c072400100440c818030304031408100c1c0907113420810a103071150b441500009941850148071910041d401000c2d0210b040c1c500091a1a1030b940782010f44031550300034804900b0400c000d0090080c01e01840f94003823001c40203005202122a0502c0d0a6164050040c181c0c401c04514040c40d1362003540074802954100020000e000d580f4400100076074001c0030081d005009885074100d220303006c0c941050240c14080304150170b40d580c0b102880025000076205982d19a000e03141d500142e1030511111401d5041560b905a4540c14040003400318040b001c2c62103401da12100403002401c01d9002a140c011130a4a0046031b8003400340403040c0680118400c2d20740c0881300314000d070b0030160000780b8401d00300b18030b4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 4065592 1250 4064342 4064351
    0xc07060206010e07050d090203011109030c01080f070c020102150f010302010909020a090b0c070f0803030f130c050904060605040c2111070609020604030f03090f0504020405100f14070510 82
    0x4190481e01c5440030300c59000000200300228040ba8024405130406a0061500203020055600082e003525034000c560003003e1b000003007010071810309101c40540d00e602803c18045600b401409600c41c100000c2420040100c00d801e40c00441e0700c02d01040002d408040d440400c10705100c00b846c80300700c0081c8412030210780e030000d000655288034026242e40700072a44543c4080382c44d000ca0008142e021121558060050540118502907002880406400004000c5031685016108000500e60140000c2c2141900e0401c600020703046030307020001e880064a0101c4252135038074001d0003501c2203030001c550041c01c107203084403103980c40400d2441000101000082120142441d0380440e02035441243c0502810803400c404201c036508a4400d01d813000c2e200c80e1034540c3e6912194450b07120480300328001085a2030400150241850440150008803000c501d03040c070704400030b80e031710340048000c4d0240b040f540110b0703444500a19000c210380c1d40c401120342c0e40f10440d03d000c5031140540390460b205149030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 4066842 1250 4065592 4065599
    0x6010305070c0803060f0609040609060504150302060307050f07081b061f05060c03070c080303010f0510120506041b020c030105100302030a03050c120a110114040305030a020d020f0304080c07 84
    0x901d004610090f0041c40461071038075000240300b1000402048940c00c074408104070351141d160740c820600185070f0781c0f00009016040008100a4820344800700f45190030b44a82480541e5820084075000002030500c50351f9030707070396584a22541c02240340c0648402804917040e0781c900e00c50081020940644012355405991f0322507030b8000d001d901950b4246010b00d00000b03011508008000b0100107c1e220300300d0f403e0940a03a070f040180341c00380c1c0044d501c6400c04001003014401d88540000a000f08441868400c46a40390090903004042880314880f40c0b1a404558140c0702c9901000400540d290801e000d208861406035580f16600d0146000c0d601c5c0c100000d0030f80e4144c42c40c501c15203a00a028103a00307409910101e0705500304078240b024601660b10707020403440c1003500410300750300c040c0c4420010b0141003140c80d0031114281c40404907141e60004100000b60701c00c003225404100c0340e00043e150304001400c917000f401341c10030905000030004244418000c1403006010b15854420442e40743d141c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 4068092 1250 4066842 4066847
    0x2001030c110d030903030e0601030606170f030a030207081606020307090b0f0405040203060102030409090f020a06051606020d09150603060e030703050703030b040b0303070c060305100609090203100315050601030507 94
    0x845507080031034204400c1c006a107846500410010f502918011800c07040d1031440505240e02a40b0071a03620350341d050208014100c03a849889280c81c840701501e50389900808894a81c0f140d41110000c0550000e074200810186405a803040302904a10f9040c01c0854a000d2009500948000b00410040c48001480c2210441121007410b2100d64240c00c01d4a002c00b408083d40011349507c0c1540000c2c080421030100d140b04110a40d8081c41d55005616410300510202c0403943d0001030810070104001038807030034011140052150b10039001640e40f0508284240206800ca070300800e00141640e000e62500601d40090098030f00078003040041c40c07440139505549229404004010850a00101001c207000c4e60000500c15400342010a0704081840000c1c2150302890088501c1507501c0d1007804000e034103108042c0d20032054410790060303600301000503240c4407042c82140d0fa600e40010000e81c41005000700c1c4d90045920680007011108840107800240100300c44050020385440b0004030b03d1031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 4069342 1250 4068092 4068107
    0xc08100305030d0b04020f0a0801060e0109140d050708030c0705030705030a050a0305030a02040302091e010503010c050708071104020a09030b060904080403020d0507170a0203060105030609060106080a092001030c 93
    0xa5105000b10301c2e000c25041e0500141c520b200420b0b901c180e090100e40447c1c1418001000c000341c8681d58000d0075810918081d02d8042665012410040b920310140b0481000031300c4c016006400315654100d80c1e1a601d01146800c00e10340203c40c45000c00f2a440d64008000500c4406554080341659030b1503440d0414503a42c3c540851028003294410051400800e0040380110703005a8240301c003515040d22078011510341710341a600c51a081006044269004c00c42c21b060502411088000b4802c001203194003c0c914090020087d10442c00041c402c801c101c40e0f40f66600d200702c000781003591141c3c04504041c06c03200d107610043e91704102e000001820380c5450b0303a00500c0b856109018a0815045030244102503110f8a02201d00340706130a00800e801d44400d100a0031503a0090081c094010284141400d0107010383c81356000340e0015090000e41c084c045242c50550f80c842ca0882059070320041048050030314441e028140401500c03440000504883c16082140400c0c0c8044c0664060500700b1904003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 4070592 1250 4069342 4069349
    0x60c020708101b05070302070f030c050108100803031503010603120c0b010801020f0f0901020a0c091e1b0c170307051206010807020c0103020903030409050c0903120c07030b06011209060c0810 84
    0x81c0c2c00031095079030783e9004038090000c0d14000e00c11107000e5903c8580d0402030100e5600180d50103000340304100001d6900501069119105402c0c0c1d00100c0d00d088420303650f900010b0061a01502d80b80c1ca51200f68501b5807042d801507030000707041c1079840130380040a401a00c10505c2a00c030f0045050000c03400e03600500880e8811420306c2500e40c50b200741401002d500d03400c1603044904500940301c1d010b000c9082d0426074405400d06140c0041d885403076000494040050542c03450544c1e0402c01d0f540c20610811007170b408004c0c1e043c101002105100c1c90401c2444c5071455241c91745e403401009100d4203a030301001900e200f036074900c1c1c035100940391040107451140b81280d81c03200503803000c01103260a5210b034003d040c096101030b00f00d038203054030340301104250760080318800c0c50500045240600d502c1c042082d250340c2d0b00100100303494005520a900d4a07007249010180c03840004030301041035a40303e24048254011000b00c100034100d958035000f0054003048400d07000050800e80443c460707480a03800030088 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 4071842 1250 4070592 4070621
    0x7140414010f11010e0f010b0a061704020a05030703030807090608060303030a090501060b040605090907080705120c1e0a0305070203030601120509030c07030c0303030f05010308040e060409060c02070810 89
    0xe450038000441d01020741d80d04000c10000400c40c5604441d10074040c0507030071000c0c1c4000d006442040b040b11821540400000c0340715071030728042006001d800603440301c0b0030001104002a955294000b05242c00c8559001603010702c90101e0000505a01c001f1242c0600c44c01e03591003034603507528a0304603107419080e20682da040e002000450480c41881c1d0013955214440c7c4008031b07805540c0d400010326508543c1c89400410400140c0205a103030082880c1d5000b030190400000a042c1514020b06034060301401c1d100000311030740446d9550050205988608042c581407070154043c0c0c3d9200c4089400c070f540c0f0100442e04000c00705c1d0006002105407440381034103a440038503950401c000e510190101a000c8981404200203081c00c04030144890700240d80140f500c503d9542c914071b4020101c074540c1c2c000400c0b4500e032038010b0000481c184115421290103c0301003002c0e0f01c40400290060107282e60041c651440c110700c01c0c00a0790042180400c886440e4150741c0c1844a0b0701a8006035203100c04030940303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 4073092 1250 4071842 4071869
    0x8070308030c0c07030203070b0a030501090204080a08070602090303030414010f0605010f030c0903020a0303090e09030c0307020105070305091f0e040203060a050d08120c041503090c050f010c08070605071404 91
    0x40780032032000743c92100641011140131540c0d9801107410442690018641d051000a90807031a0383c041c01180d0041070059401c5103001d25100e007690712916141d50042070340030000341c034105015003034040da4051070000302a00c5c3d030303403c081c50100d9159604d1082c00416500b130070000201404c0390b115080441d003040c2c491044115003010110020300e0745100c12000d01c03234850310100140e00c0710040c01018602c6a15426001ca040c04880315112030024412100d591042011403001d41000c02030710035490342801e1680c0c503906240750075101401020742c126006020380000e910b58203150f5229684080071900c461011100d4031043c0816031004070b6600303421404c0010100124202180f5000f100d9004e100309600f0001c482c190000011070a9450605184005c5001e210305000158107400d01043c0e81000c1240c01c2150340e40500c40219071065901c60b6004d0180740348964040c01c600c822244c2d010042c0307660381e902460007100034502034458000280042034841013041c007480484007624080744d86141c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 4074342 1250 4073092 4073101
    0x2010905100c030e031002070503031012030903031808010504050109060e0a03080103020609030304030b07030507081501080a0506010203190306080c0103050f040602031302060705011406040618020f0403050f03030703060807030803 101
    0x13100024210b26003a0188520b01441210026501c040d00c0150720800c06980d0700d00300502d40005007015034020808686066546000103600038548408903580750030540d058618030319006038800303020f9004100c65400c21b01000200b01041d841140ea043c0310b40010800e0300440070703103595111946072008010038550750042c409032628202414204178000c044a140940300ea940701e640740c10075a00d01c00820340311001c0c86803040d04107803242d5100005101e404040618400001c26130800900041000303981c0360045245039209200700d402d03980d16040e100c10301c4103884000400524032842001514090f410290030340358844d00074140114400b134000c11440d2100c0e00c6400082d800a840e0101e8402e1800320702d00180c8502c0041c10880d80900c000140788861740c00d54000c00c0f0401000f0f103105500d080c5d028030508000301c3d80c20721075005000e4016101c464464003401684141d80001e40070b1303c00c0c80e010703c00c02240000114030442c003c2e030b0140509039403000c489543c0c0c0003d00000f0241d110900014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 4075592 1250 4074342 4074347
    0xc070b0a05090f06040b0f04030c0506070210030b15040b04090e010506030304030b0c070209040609110909060711070e0f010f08030c0c010507060b0406060e01110604020f010c0302120c0105010302010905100c03 92
    0xc1c0c9040e60044c02c8a00d02a035130314000481d58015005032428440c0401c0420911908000180c000c0c0810b071800d40c5400d0041e40044d1100c9401c00c3c083e028190340d0840c80703840340c03160120b507000101a082402c3d580c540307c0e00849400e402a1040107031032414040340392441401070241c0b0780030f000081c004606050559452044440000340058103004083c043c10015a4a508503103020303e0040c0e000007040102400c2174081055041c0005001e000e00605101440c000028810740c0000e05181c40c881d09500c0700c0034541031465580c040340203c06c401042c00604455071078240d0403603604800064041d69a0b41e105a16070050000e1070304103810103007035101613500070b00042c40007601c2440c0001d072000000d0002401c6a506420203000108038a42040c010350704601007141010240004010b00d26143d030002e0100a0041205810070440003158800c1500800203a4556141410610345800b200a2928001c180c02d20080c0d00061004400007190305048030301c83c1140000317a581c107000b0300c02038405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 4076842 1250 4075592 4075609
    0x50103020a020f0a0309090608210306010e04020c030a1803030207090b01030e0102070606031104020f0f0a030207080c0a050d05040312030905030c1006030209010504140714090909030c070b0a0509 86
    0x200254011043c09002541090101c030f01464070a46444803054104181038080310082e801141c09a4086481c2c1da402070400410442000d0f030012006a0302d503a00703c012122441c42e001200d030040d0012030501a141408005080c00380020381d01d16004c0140e81004c0192200d4601c0082c2c090303088000203001d12065500242c54645c0c043c100402c03495100e01c080c60032a0b02074607060710f20581d80c18091041003030b8034800700e140310000c8400b941060803006460006100e1101000d50400f40043c607551010301030b80644181d181c001480980762501c401c03e464850070100c5049420380030b0341c44001c0301180150150340c00e0340c1d08849581c0c00070320b103110203a005181400b41621184414004217800c40f004002d6140d882042e540b001c9030183c81c600c1031100516041c0c0040f4030981c00d00c52000c0000e184c12100940c496903610b010a041404038400c100320703114582015800c00300078410003802c54000001031055140540c21100819590205030031280504040e41001a50800004040e89802e428 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 4078092 1250 4076842 4076857
    0x30105070e0d08090d0f0609051002090109050111070302060c031201080303190c0c020306010603020c0c040209010e0108040f02090403050c0606010309020a140303040801051501090608090309090a020c010c030f230105010302 98
    0x140070550b6086d4460600d160f034114400c445482d151103001c01048424030901d030b034103441c3c0c407802e506103445070002030304682e00c9003da54100044003812140d030700800c100c00340041d9009800d0503034804a2529040d1a82e1100e0035070842d41c440280001b03064040001140c0c4201d440c1109130301040003841c80314019080c0c82e0384400401c0003510031003003d030b0707401e0004c0f600078412610016074944000100c207080000d58034a40d44528414401c141c6a82d0b04894030010080017442c14040590b80c1d031402100c0800c035000041d411088c020304001c105500078009144440b400c40488017166a084011401d448810400035040102001c04102d0040035051810b06484010207a0f801c0c0390710341141508540c0112242c407200e1900310049241541c01c014024090003140c58088010f182c1300c16105d5580c03045030a6107014031100000585090695415a420008000024000511405001409000c032241741005403858416100c4160300e00c1c221051280791200001617a0382c4c038010055000350030101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 4079342 1250 4078092 4078099
    0x4020a090b0303190f030c0801080601170a15050609060d02030c091b0304061401050105040803030705030c040503030a02060106030605040b03061305010b0a0608010e0106050a020a02130e07030b06030105070e0d0809 94
    0x800c060620340c80804d00c3c03a54a59568404040070b0520008044c0e502d00306940041c04a210018010101d020510f681950b261400c0d20280901c084551072a20f449018094040e520501c030103041418550003c13405040103e07002009900c512003008035214100700020341c181e02c582d814100a08040d10450f501001c0c0c0d0034440592001c604082c0029801210211000c0d41c0e510458103030a00d00c000f02c50b000d003c003031034000c1c201410560303550b0340c0b840058820800c2c070a0100025947d07820210440300070f490040c0649440307014610b07010b07544a20070302880303000c1390501d40302098900782849100300e1401c0040003006152125541e0710141041d500e4180c030295201c1d09140c030192541c0c1c5014000700f080d5520300705c0c123625000481c00c2c9500107130400c2082100c100000c0024542c00a071410806404903020224110745160710001001111251403940c01a90000000e01c0080c02400b0710a0b1002d81c001d110590700c81000711002c81c503164009138805461554980451034007001380441c00800f4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 4080592 1250 4079342 4079347
    0x80610110c150301030b01140303030109090203160603050f07030b03070b09040e01050103030206090d030b01090b0306010c23010f020a080112060204030c0b030601020c030105060616080d02040f0302011704020a090b0303 96
    0x20000b050350715842c026100c0c00e4800000c010001c00800c003040a0040150b0714852000503441e400180e00c9100c1031143c4141ca0b038540303c6c1340d0213655040c4000d0f00b80c880b4044295404542c0d6880c041c020345000c0f1030ba00a1016400d00041c08507010740030315241010020082d00c41941001860000303500b200c0052604180d40301524a13802c2c10034480c140c00707036000b41c005140720b20b402050185052500c100f16010541080c40c00e00c1d070b1ba6003241c8680c1c107440c440c1030f101c0d40780d54503600121929200c0b52409000881e0704002d5950660010303030b42c2d0758880c2100d0002e12600e150b924110040c1d11418186100140c240001049001800100b15607894443c02e40986000c2e5680c4038001c500c40380d5000108012000014046c1ea5030f01004000300382041075000380141d262010008105000d03c12405a40700210740c20002000000d00882e0f00304e03c07103160219161502e840d9480b10110365400128042010500c9a000004014518a110301da0007810800f059080901e01c1001e00b40291740365405102c20b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 4081842 1250 4080592 4080613
    0x708120d0209120106030b0c070b041104021603030b0f03011407030902030f010c0203030a050a0c020a0303051008060903070302151003110a0308071401050a02090f060a0c080d050106090608061011 86
    0x22440c1543e4103240e41800401d201d421030030030a0b20f101c00174260481c0850100889400a02c1c1302e56074903485600944019954032840340480c01a1084034030359000b001e40440071504242e010b0b800b03125103e800352003c624100715581814201c9007004144039900101000185505210b904400d51640c4041c06940c80306070b05581e104d0a41e030440010b0f00240e040413003000610196071107800d41c8006108400d1100e0189200003a440e980b011a01400b099200ea001400c00b9036481c40450091140c10f0885001385004101140c881c0c00ca14000c8005020b0044590044614100100e01840d81c0d0400200150700e19a00e02d0900d0300b00b8004203400c4640040004080344510003d0581d550045100e83d042e00250803180b801c4410050091609920500034221103031148500406001d6041e50302030740d524014803040d101c1542e005001000d51000003111101030361650040e604840b019111141d115031035410a035034842040b200c2c241c0105048040844075841007450f02d88400000742500c461038503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 4083092 1250 4081842 4081849
    0x1309031404030501062102091306060f0b04090b0604030b01060e0409060f0b0a050a080c0402070c05100c05060610050703081b030106210c0c0803180607030b040b030708120d0209 78
    0x1c150300540b4035965403282000f00e188546a048454013680c10f904d00003040e10b90000c0d41c0b0036006025260b42e200c12070a050100041d5030b0006026040760840205520f0303440c070301000d869015014216155091400b8491541081e00680702134070780c060300041050382049030072191072010605190303115490340740c5500400c81d2442488070085548038082000c151401c02c6c4124480075502850084000c0d940420070700b80c000ca1040c1c0071020895002d40e40c0c0104c1d0400c2405d030326150300310720740c170580d01040c1e20185900203030491216482001030b18042e548030340c2008040e005154009002c694100003134000684200840c507400780c070704400d00d2054100c460b40c1081c02e400c2608000040380c2250b8805640781400003c0ca1130404010303200317210780001c00c0e030020b200c41140032000f0702250010000c0b40c80c8042c1c40340030302c40c0c0c034003540c0131102c90340740000c40100a0941510700d0781c01a031900a0401c0e95040c080b60f41c00995003203000034104010301c05140506503200101c3c40681507400d10000324980e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 4084342 1250 4083092 4083097
    0x902180127060f03151203020c090708010603020f04030803010f0e010902040605040902090d0b0903030108010e0c060f09030709050a02030a060b030618070306030b010b04080d050301140103050a111308010501080a0213090314 98
    0xd00d51171101e4070f586c1c061901034504216440b40a100d100200c080001c3e05500003a001e056070554940981c0300c4145a605084d18025a080284055400300c00441c246050155650803901240040240b0381d980e038940d4422441140250303070004604100612117441150020320000c80701800440000c00a51682a40d215080e13841441641000004202100c400d00031500115400303c0a00714118002c000201103218000c0f8130041c07200045031240040d901481344078000c1c490460244814941000c2003c0290300880340c207400e0078640000894141092019a0711844002d080c0c5440318007605484141000300400c800700700b603100d0001000090341140c1982c001c0109400598840b41401c08407800c0829a0810b842000302c10702c010070480c00702151242c0844002e00b4000f030541c680e5084100036001d1081098203483c0c0000b0807015000d10390b4800c40803205d08500801459072903050300394482d944000040c6d841018104502a240d00030f40c086010544242070001c5031091701d50b20310400c3d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 4085592 1250 4084342 4084349
    0x1090c0602010b01030606091203110303090303010501090e01150309021c05031803010b0a0902030411041b030b0108101406040e070801090c02030a080403030b03070902180127060f0315 81
    0x498804404124154090241488204003400e0511005050010060080d1072a00c00d01c5c2e8040d4607684188145801042400d2401080000ba6550392030680349982c1c1ea54070070310a150010b40501d800041d075542c0c04204138162016413a148541c0030302c215044010744005542a0b900540c940341c4084044910604496000c2c4110041d43d04c0304089142280f11402446e000750090341005030801240e5543c13011203050321400f4200580300e40311810710300d00d0009071390503440d000f91900d054004440b003203208503502c0b0319032590248082050b01004440d841001c0d20607402100320305501f44000c40303040030007080c1e80601030052800d0581e141101c40b10844250b07400c0380801c0c407000c01400401c800c2c0c021400c1d8081240011468281311040041c002000100040e08250b654001c011403076409000401c020201e0900c10354841100d64900c400743d035055180c06000c6080707003524440401d031501c981c1d03525000c40d40c218010180341c244160f8030750031a007144000301b656902a91801210700301e03000307024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 4086842 1250 4085592 4085603
    0x60c0a020405010e040b040b040f0203150a15050f0103090203010207080409020304050d02030c0316020111060c13060801030c050603090703060504060903030c020105091011040b0408060703050601180303050901090302030109 98
    0x544206005010803030750103822400c00d074401c28080002013a05000f040d600315500c418481c915039103030b081c5005a2040032030001d5260080001e0351146145845c0801d000324007442042010445400d01c1d20f901c0b40291003420f07004130301002e40c545598081d41c40030000a00180016182003000d80d5000141e03441604100380965000c420f000c24003c0401c07003c1078801c40c1c0c0c00218941038412103c5980c900402030b00350300700c2105101500859100e44600390040030b03044110741c0541044925a040383d002056420f00300c808040d00051024440d0320300c141240e4000c0c200c14002810101880303d29800100a02014441c01c0c10020014842e8820540304500600c4c000422110700e20f801001e03140f00c201c41c9421a070600e401e02c59124030120f50a071303255038946d90014075028035400b00c4a1900441d44010880c00700030900007240039000c14010720030f50190341d0400032070340c0d000c0042d504110001d400a072464091082440040c0c0250000e00f1a00f070141448814075a0701d50000382503500c1440115407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 4088092 1250 4086842 4086853
    0xd06020d0c140406050301090b06040909060504050d02070b030f0703020405091305010b040203010303052a0d03020c07080a03090308030910020a020102070c060302040506070605181c090603020f090d05010b060c 92
    0x940341d0b00404220300c20024200a9181629116005045000c180200103203070313690328000324043d66568200c0d8028042e0710f070140080080e038242a002040215400d0f1000d0244408408680e8401700300e07402a103000001c900d086848040c0f5010358070030010010024181d08100100ba40e81e81c0703420300c034400e0729079564082c0b0461030303440d1080c29100c4035000580114014401400000d40003030940d0100d85000740c4a2400b42d008480703000c482558804c080e10709000c0c804010003820381c190010501840354330708a80c0025510b80e8829592280200e0140001c0d1000106000007600c0500440d00109000203e50032040c00f014120201d070b01a0960301d01507907000505404000c08915400001c0c1143d007400c509252402010442d24454018000e00e41a660400107000000030801014944007407001c5807004910304100c0f40d00380a80b2030710040824802e18002502c24468000c5542c0350306810461405c1403100001e01039092203480302100d6554076912407504540341c61020300088070f4036100a0a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 4089342 1250 4088092 4088111
    0x13061211040921030f02090108010302100306090c05040302031204030203120a03110a0503090606030703030207050d060f02030f04051b0a031103030c0a05030319020c0604030f050c01060801020405100e010804020603060d06020d 99
    0x401701c130782e1002c403c50003e0041c0f008100036031308050283d04494040c1e50189106010000440c002c08141e00301e00001468420720a611581c031602510940c0d00c00c0d011191428070094110b6024015440000e5043c0d00031207248456103440d901030410f100d06400c020944c00c0c030188000170a50082440d900c0014000700402040e600c0800034550482070503800350603d43d0650701c1c002c0d116030721030094900402045418404214217a4401c0e001084104411902c80c2002d441240780e002080d942a50f40c0d11502d82c1c25120350301d000c07141e0541540000d10307042c201c0d07145a0345d25a004503590255a4135000c140160441c1e40d10a0001c0d40c0c00c14443c00243d5942c1c03401d168411918130705070392001d600303a105000741014a03500158158115400d42058400b003c0c5820040711f07980700d1040c4403013541d400c01800040c0d20a05402800a03550203c07070b2034020b40142c40c42103d514105028181c0020204000b043c00b6041203001075400600207091000600c040780c91b00002d0741c0c009040c05102c2592491241d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 4090592 1250 4089342 4089347
    0xf0c030506010618050108040b0604021c0504050a03090f140f060403050102070f1403040302010c110406080708010e0c01050f0901080903090316081603080a110c0a09090213061211040921 82
    0x5138060803090801c21410700301174403010315140008100c00e00031b42e400919107001e18000702d1031500c5c4020191090100c0d160031300e051500c4c1c0342601c90403408104c16103c007103070300008801c040d429100782513a0661440728007420450960401e000c0700d03030071400400010004c00d20070300003091411300602c584540815107140940480c07038404185403154005020a2005071382c4900c0071012a5002000c00315000b8203c00040c4c028402984480b0244c030035510300103540d00c0d041d0091540495079400f0380e143c1d90420001918240311f0300201017502c0104001e03400d0150700542c0c081d07410145110071281801d0101010034940000080711010186030404c040000040c104861660104100b02288030503181d83d0303458226006540d090303014003080c1500c0444513403080044c60754030344000b0241081107589405075001045018416805290104a811400121030050034221008040b20103d04c43d120344454400c51542c3c11010380c00781d1a00308002c04540403803811181c800032100e0f00d0b1035240070003101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 4091842 1250 4090592 4090637
    0x6050112050f010b060a030207020406120b04030f030603020609040c21062105060106110309030601030804051f08270105010b1207030902010f0804030201140109020c07050105070503070f0c0305060106 88
    0x1c0b04a070b030b8100005910180c4902055908884c01c60a0241e1100d803648001800f0f0b11071600400d9201c2c01100c0102c060110140415006078001d489030b09100c000300c201182601d850303010207500400100505100c508041c2d201820070521450481d00064003403005410307030100020712283d02500c506061110100144032034030f2000450b00521040c0f1410b9807110b860700e074144941800c0c40601c0f600c00d41d00e02018004c944034084000c00b625120342e101c0c90100042d030018010203010b0080c0c1d60140d00c02c0d180d1306040b00003681c49900c2d01101d944d12040c00c0041e0311800e08420520640c200e028900f241003d008503070280c00744000c00da44800303c03860584484000102490200340c2004418800360b60820b01044c8201e040703182002c2c07141e0302c03420164090440c245800380e4200316800001140e4580e503003c1c1c100307540c0710b5050b00c100550380c500444260144900145c01d81d00100041c030006907485031540d5400380320740140710303c8582c1c82d2902800c0540903400391011508501c00034400b8481e00c6071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 4093092 1250 4091842 4091863
    0x12050103111503130807080712020105160206060a0e0a0b030102040b0901020105060105040b0412030e060c0a0c050d05100902010e030a030f0801050607120c03050c0a0f0203010501080106080307110105070605011205 94
    0x252402c624000c4244c0100c810380c038601030003050b000169030f014003400700c0442d500c49402c0b01076142001c25128001f4000c140c00c03a1b244070f14580c89148550701510100703240c1d00541004002d14402c505041c5050040c03203020700010030443e07841c01d14011544003800500010415250900e445036400300019003912401400075041010800007030021740001402c1e1340c155a0f035400190655100c0d07180994181c0e00c0a6005c980c85940403da0b001200c20005a6880c139510036420620300d90ba0b00c0302844805204000d004040c0c1e00031410020009c3e59940c00410036500500d00b05403c4517440d0f001c41d0908036002c4040e0001603000c201349180310b40112070031b801010207a404903d4010648c0b500390071031541404007030402c02d004001005142c4640c0036644594900000d5583e038488a00d4016429040541e00302d001394201000040c1695040c0b04480458030f005001d98a010f013a43d540100d02c0100000b054140041071100d0f802007020b500c1424080e0100400822103240c09007846403030840300c02d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 4094342 1250 4093092 4093129
    0x41119080102070c0512030f03060607020405090a020301140702210d0501030507090c020706050706050402010c050102030a020d150f15050c010609020d0f050601020709090c03060c080402100306050a0302010507031205010311 98
    0x1080b64400d0310000007114440c15103003032394680b01d864420024007240b1071004042c4d8080e08200c00d008090304040354410203984228000c0001c00554040c1054450040302e084016803c101400d101c0070100183d00b01c078500c1d00390504d0b03151034001c03030702002260001e1f00251811b60000005200c200407a10070360815a409000030281c0e0b0345006c2e001411842903400080010352203401040c00c59016083c010302d4194000001d6491340b8041200350000e41107078242c802000d0401490301c0b00d1a0006141da002c0d180c1c101d50312014582052100d41058050701d54210400000300300c0d0030648070313084c0b28103030240010000260369a44d159071442c00742d5010310041004c6c1381c501170a2001070783c1c00180d40d90480b452804080f6148031142085080c2a14541c0050981820a00d4041d0b01c103900c821154800c5108840351146501c0340641181211414010700381c000040c18010b2026600800c05402618071038a489032203e40c51442d510b095038000c0e8001c4558403100c107031030b10b00c40c0761010100040c0c61014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 4095592 1250 4094342 4094359
    0x906050403080f0903030d090605190203100b03061903110f060c0c0f03030d0603050307030801170d030203040c15090302090c0c06060d05010207120504050406090603030206041119080102070c05 85
    0x54481c2c2040d032149480440c04544002800c12264038140183c8000030b180701800c11400000c0d040070006400b040301e07401200200d00d0b0320690b0640280c400c0e03034000c15040c25400480c500713000c419000703030307101900c025482020001d200811a840450003005103101d1510900001448814040200800103085110701c8003072242a00159000901c01d5003a6008c03101d444010581a020078110f104510356203e10904020f40030080c000008000c158491095031003e4207a070381c914001450241240c0340f100107400583c40380c0c4c00f451280d00507580140c000c6900b0a419551108101c0b44541e89120900114990b06e10420a525000208a40c48510403800c40c2c542010f00328080c1e2220801008540300724641c0300301c48c0621034258103a825103a40103038032301c04412894401400e80d0300284140744c400da080200214150340360b40290300c200c80d0305400814082d2a10755940ca51000c1d8444484c1d041440412000000713001c10038440000d013890b200060b500c07401070601c5034200505400a900800a1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 4096842 1250 4095592 4095599
    0x60103090b04020d020a080d03020c0d02030c06070c0215030403020a02090a05070e0114040902040b07050106090b0a05090a0b0604120c0806040b060d1a01090c0e030c0109150302040302030a0302010203060109060504 94
    0x250700e54642c4554101c41c41c90100340c0390310001d170121440b82c009007807604c182031500a00c141c040d0300070321010300a4000c680310b240030864204d940e4030803228081c07807d40150010922443c040d40d004081144000d000240001070f800b130b0f81c0210b4204950a400580c0640000d40c103504201101b41e4126000700b2051040e4030348118040c20030892000c1c0769041000c603403940c16181d59050240c9016100d044015940c0725131344c100c00d0030f0300c1d08420801e40e45546050000144c0c08900e01c41c6902d09000a4000d100703040ca00b004005002d000200254103040c0c8525040c10300795118001403000e4100c04001e0102c0d5160303030030303c51115081500f04c0109640141c041c0000f14a14440c660340c099401c8820139645d03251844c102c1d55400705003214858000d44030001150446568101c0103410755186e882d841d0600c0d8480825584140d6078001c10b010985000051014103208050404107640c64113001d0714282d601d50209140c0312151030144c0c0140d501100f03004040da03000300790344020446843d02a060070b08 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 4098092 1250 4096842 4096853
    0x90f05040503040512100c030c020f0313050d030c0f0302030d11040305120708070c0303080711190303180203060c07060b090108030d0207020a08030c0f0105010902040303120b0f060c01021206010309 87
    0xc3c0b4025244150b256404601c0d015004000c041040d0440b60345c24410455041c00c06805800420414400340c020401e07900f00900700002515034515000314030402281c0340006105001d0600303032050f010054290601c2001c144140043e0b001c0350710980c02140d40e2100402014100e84040c002d00c10100420441000400c0e030005902e618040d90400e510768401c0d0a24100f02c00d4410394000070100c0303000e01000800e254011038054841c0034aa00c845d6400315400c61340d03d844030303809007107550b00f400081e964001103446680180c10919207000001e500440303c0c0c00003858080201d444120316080010004104030560050030140c2c542038504c0c00465061055041e184d000d03004003062602e40c0420310601b03550f00c4904442c002c0140c4401d803035a0307507100c03500b107500d40d10041000704040d82024000610341d10180700b19412241c050340c6005030180d020101001401c0184c0340302d5400842e0300301543c42d580d510002803140345c0030389000682c2e4548007100c0740400718000f01a24107040c500b400b183c01190 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 4099342 1250 4098092 4098097
    0x8070b240105090405060a0305070609080c01080f04140313080309040e0703020607061503080409020a0201060602160302040203090709020c030a020601050103090b0402040506010201060b0c07090605060c070e0c0702060f04090f05040503 103
    0x1a03088602017125551400132889207c0903910203012486213103c00242c00c0d400441d81001d50311120140d441440104005580000c1c1c2039030402c0d400392a0000140220b940301044d01c2565101c2c406480c608036581160081800382c5070444a02500000fa0301d603214505442140100805640034001d290315540009038240121600500f40b55141d5241da52800d54100c9041c000d158091980e58545880e810100c0c000e4001c040c3e004090740c078001000c610f55000003550211820000d400201c0c841c1940d09000103900090101c011520691601107042a9140040e05060354513038005d42c0c441a25a4000740390003410b81c0258141460720001001140407440810350254040c4c1d8042296113032880102e004041d164071a04e83e5420108000c030300b6010103c0c0c81400c403103491a0900c52191101d0410142e03104420010080e41c1c040d250422041c03903a60f03561036111070100041424800560040b8009070310071400780010390b400040c1441407030b48500c640c0c040d000c50f07000104118546a03546507582d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 4100592 1250 4099342 4099357
    0x23040507080708040c03020402031005120a020303040923090c030601090203070f03020f130f090e060f0a09140304030803041502091e030102090a09140c030f0a0504030c08070b240105 80
    0x40c0f140c00180c01e010131440100021603026100715aa450f110001e081480c1290240303611403805800b10301e142c00307000140c0c10035098004002e14506072500442e140107001801d1000c0191809101c2840c21000160280b0310420500c4081c00c0002850310804d820b014058000f602890f1051080c007000c1075004c132042d11000d4940c180141d0711409120108142d0244001750354070015184400701300558044046002c50b4584035051050070301c043c07801621900211401c22522440200184c8002e00350b8008100035070081000300030440e111400181160300c207410a41c1c2e07581000050104111035402e01000d10a030104046080409210008503c099400d0f0316100007649001c0c0f949880d030b02135040b6007105000500a80c0010341d64040803010740340c01151840075820100c0012003286041c1e0849203d011130502216030b554401c0c5078140203020180081e070401603042c9100001440281c018a550760140c9900c5041b45408039000d00340c65503143d20b41003080010703280010166088015102c40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 4101842 1250 4100592 4100597
    0x613030b0c0c010c030e16050d0f0f0b0f040201120507120f06050301020a0905030c010507020603160504170f010e07050607060e0a06060e010e010f0f0302010f0e0301020301230405070807 82
    0x6480304010003406000d44030b802d510725441e00d09040052901680b1a10340203a088040d0b40080d8840c02d440c2c0c422840d1481aa41c110f04c03445140c0340051209203c03071030070601c910161002c03502191500a020803003140c0a244d0042440c0501044d90303045035508900501002d800d001600c0d0401c2d000308507082e0709507210441030300e1b55540c60321212150880c80141602400031510b5100c0090003c00f022018420700f4041d0068148a01c10740d4071410450b8105a0080c0886185854607030200002c681d00714642c0040080a01003c280c103200300702c00140c00ea590318003c080400b113603200e050844000c03030030041c815072044104100c00d031071b4041620f44c05a00b00300001a492500402c55040c1020300c02c00034030040c0b90034004208a40b10728001c605a070285105074989a80310284c02c0442d0311603014803116a11400000c000640c4a203480d81c08080091804401d003940c074034042401d9800a03005030104080c3c60001d105880c0d1481002c4c081c52508641c02d1005081052000d04040b501500880c02c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 4103092 1250 4101842 4101863
    0x30703020f1225050103060801020a0509010c0807050a0807140a05060601050a020717060702060a06060c0b09160807080c03010212010311010504030f0b010e0603010c0e0f011701030605060f061303 86
    0x310b91824003074120440034101160b070700040e104024016a481500549000c03a181041c0844c90650510a450b40f0b00000d40303e451402c0742d10b90040d03800202e04181204c440301c041110030b001034404d010034482540307d62410303512406e1500c0d014500c1101c0b00da40100ba60722030f8504c900071072800202560860700070b00b060781d5150f05200089040c00455048039001d19046030642d80501000503241d48150129800d8130b580303846c0c6440410036a40c061294038002102104040d0101e42d01700300981d000505074044070f00601203d01048108005540301703441c2c0b5004603000300483c00040c800300700c4402c01100210710b0300115111840b4242da040c0006050402074021074030041c1d005904a0b006581c00000c20790303241c1e200780f0f050000300c002406800150540003000c20b29605050250381221445916050b24100042040c410082c1c0c5074107034a030420051240100100750f503003001d18040c500a182c04035207803410801380300b403082168441c103000b40c01c2003100c1c0d0000c482110411040d01e13408001a030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 4104342 1250 4103092 4103119
    0x60b0309060a0e0c0312030a061205030913020c06040f0501050a02041d090a0503030a0b03010b01050f180307051003050604050708130b09120d050f060301050903090f0301060906060203040311030703020f 89
    0xd04d001404510140c1510131212418100319070038020f103124499500c2c007407080c41d44035040c2c580030940c03d800052103688144140c0a45260541c0c424006400e40c1c10018180780c00070341c0007403804006440580e8040900c4c142d00b002d0200078052294800b090b10b00c20752030240381040440403009201d40710040c0e400c2201c0402c01d00703071041c0302c01c0d40080c4c0c024048a4a81c248250528000c0110285140c802d610301040c08440794000c206444e401d91000e1444e500342081100100405030300001c180c3c0e89030141c1403002c101c0c1da1b01c00d00e140710b41c1409644c0011b1149000014401254000f80c4110284602c020821407180c01c0d00c442d490b03085902c11400c0880382c81b50380c8158600000c0e40000b00c0c5503240812800343d20754059210707520450014940b07107240c0e128801494220341c8290b41d4848650010400d80407039040407a02e1000800c00500000703030b40f503603801c1d2602c221038481d0007000040e04005420014803580d80300701c80c0140e0f021001b44c0503092070342e4000350300001e015441a0250401c09541c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 4105592 1250 4104342 4104371
    0x7060605030102070b10060905011d04090506070207061805030705010c05010609140405010b1207090c050f0408030a02070602010c080604110c060403050a020d020c0904030507050f03040905040303060b0309060a 92
    0x500410000d03000755200d11360341ca0400d0700141c0442d02600040e0406c00002121807041780c00008440c81a110016945040303030065800c0303000d0614080d003194841d1710b00340003c1e400b088001d100f032030540e02801800f8101000105007a81e80544141090f424038014040d6540200d4003d0403103600f424040071802103850010702424541d40051810b0346440503080704980c06400d241c2c0b280e40b16100030003d80e0985070070482c0c0072403000b40300302e41507200759418000710f0503d50012884110a0402034180004080806580d0340a60005119500301041d110001c640401c00c11001d85403a0000380060010b03c000103000c01c10003002507108540b1582e1008610b0300690480d026101844191050340c50603041c050000d42c0f00c4004031005101d8032002c8071a00388041400401c0d2103004003003035000e45075901c0855090700000da040d140c60003040c03486a04004200000c000038400d043c1d01113a64074190901504407000c43e4850b800160041040210858003c03446a501440b080340001c0c03c0d0704004042d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 4106842 1250 4105592 4105601
    0x30c021203010602070302040b030a0b0109020903010f020f04030302060f040b0a0c03090204020705011b030207050304050904020105130e040b0601030c02030901080c04050a0f0302040e010b0907080703090f1a0f01050102030901050706 102
    0x4508410310010010070300340d90209204065a0081d6414007900042c07000f40b613034644803064058541500340005020710b809540042200300c100400102d09088041c0c1605e0032039210032141904014009401c004041e0148840d50340722000c5044103006251a403929034990200034a0002c0c066a070703610902c038042c000c0c0e2025090a070090030441d100d19603451302c54000c2500750501d207c1120b02400c4000341911900071200120390041c0514140ba14100c1849071070403002c0c108905001041c0701149441c585441808000c101d40000c84d07405003050300b820801080094100d5040605148083c4038054000042710407040003882c090005903108103003006a40916000607500c0450b81e80700007601700b41d1844280540740210b074100203070903014482c2801c0703489040c81d00340c004d40c3c04400100014010141103501c01021300740400c03a18002d07940c3c200c040b00c01d90360490b420044400380750041e81c6215281079218680520f585095410440040c0d42c0b4002c0d900102e040110001e401410400356810 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 4108092 1250 4106842 4106863
    0x50a0b0a110c150c03060d0312020706021306080105030102090906010807090314010e0f01021204020105030705040906090204030b09010b01091809082a030304080d240b0a090501020715030c02 84
    0x810740c1c490030005500340e155030a05410b0b480d16100c0c03d0218205030075680880740921001084d042c0a120550f9041e070309488502d5403e4a620303824410500442d8840c0000d00c00c001c1e1081c2a0a40d080c204800030780030f0401078111034082e078814420f250182e1a8101c520350080002d082101e491340e84c0200898100b403094200910703032014140070f4001e40300150080b00300c1c000036500b03480140d800201d25908038003810300c07000521240c1c0008034000d540182c0065800610600d4840d140603140c1821106480361035100f00381c0d03103600140800074818006841504074565400a012016940000070a64545409491000b10750708421008001c3d4540c040c075a02540200b043c0e03220703034903000345034151411007005840702c414464070f107110400c010045901c40c80d4002d00c01030030008070200d4080108442d02d50021a641c07210744c01e0911040340380c00b460042051801c0c8590301c040c0c40400510100c0180c0c081d0341550702180c0c0602c0f9600f4202d0f0020303202c034a14030340040e002542c010124600480a007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 4109342 1250 4108092 4108121
    0x8010302040203091c020102040602070e09030d020f070602040602030304020906040b03060402040209031603050601080f0312130314120402010311090a090b0a0f0803030103030201061502031c0b0612010302030d0c050a0b0a 97
    0x5c44040101c1d01074018108940ca05d409450340590390300540180c00708200c80c40c50740c90f0001c000802c40d003915640a040b623070701003500c1c01c1e0818070310343d036281d04a80c000d0b0007030400750b8000b000308000c516000780c0940e4428000c0c5d400b0300500c40c1e80c10200f0340c0c0f000f016000070720854010642144070384040156038001c41038124000007450303076420030507212103080c001c00c41140100300d10500340220000807034807010790381c140c801d003245d039081405000c84603048001c9080088400d4180c45013a40c0c5405014100300108003450075040c02d00c0050110380f0680700f044030b40c0b4810701c15118140d9030300c021740040b290704020116007012440d001859411042c0c101500705841c40c013000c5001d06c4004051416644250020400c8603141c0e0300181d440a03e492040005070300410003445680b120107022801400c1074240441c1001000001504a400101d01d80350712030440401003081d883c041161180c43c541c1c501303046024241070b88540742c0307c000301c0e40003810a120340004149905040e034000c0d0440c01c03a00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 4110592 1250 4109342 4109383
    0x1080c0d14090607110a03080402010207091406010201050601020f070b0708130602030304060510050a05010f18060201090201030b0406030807021c06050c0711030601080606040f110703030606090609060801030204020309 96
    0x80700c41c041044060710080342620036680007400f00d41c060b600503a03103030b08810001d101001240e5411201e4040051049045001d009400074101c0c6c294020b100240250b0400782a85203000c01c00282121801440141103600c40500c8080000020605e4070a540c2c43c020f0f216560300a1341485016482034045801c01410069400100c0c2640400590301030340c482d6030188000c0e150011a5600d11109000b801e6200350003203410465507000c4c0001009a40380d03420700f25200212b0780307049a102c0c078907076000e8409030751192400380440d83e040c492550300c1c0c0c000302d82c10040c0740e085440ea06024061020b000f80100c00400048250004404900107441e5011030207000f07a00c1d00700b1188015800050301200e0766004402d5106491901003020750585101d40014040c40c0d480004002c0a0210042c1c40200190b481c1d6070516520907420040a6803030003a1000f2644520f0150000e02c1d0b0000fa901003c10000008410302400741c4c4a2a00740c11260100c4015071240c40b2104080e0915440305c80e010030704c400e0b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 4111842 1250 4110592 4110611
    0x403080405010206070c050d03020c0f0a050616020a0c050f010c080a02070f08010c02150a060302040e03040806010b04080d030c1403070903020916080c0c0f0a0302060f0c07020f01080c0d 82
    0x1500003801550002c1e4203a07138013500ca408080c2c0f08641d60010090481d003217080020000c43c0300b6030141c0301d07041115088a4600f0061619a0708004020760103039002e4010f88204519444110301d01c810131032080c0700401404000780c4900c40840c00a008240c410f01045c0082403250b03100e0140590240d40000b205a514000c07034001070355402041c49840c1c031401c001c4000080030704040c8100b01030043c960b0050040030980c0d07070b261204d40c2c100404c51503044c0d0b900e24021000da1918400c980110480138000d690321400c00b80326600d003420503444545044000c12051211040214003000d403030400742801f203825881e00c5016284401034126030b050051000c801c1044484c0d116104000b201c1c0256456282522056050b4654043d51120348000c0741500d0049406031680706d004054508c080c401b941d884910001c0342c142811014001a8016070001c0107004214803c41c00041d041004611000d00e04a019030125003117007110b683c83d42c144441140001e07540780000003154110604064108400c01d00f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 4113092 1250 4111842 4111853
    0x1308030108030a0206010f140405100b070602030f13030f08040f06020324010306060903080306150f0a0809070e04030507060b030609010c02010b06030f0606130302030a060c02010e0a02010819110403 87
    0x4455040d0f00140314403000026402e00d85a40c01081d1002e0741a01705282c100c6000b44005048094101e10800c840424002000d4a40d94041c0c50b03264070030903000d662801c000011200d0880003604001140d180b04c401301d0300280d0000000c0d0292191801e000400741c0d51424204000080c49001800b20b0380000304101209103c0c9108890745081302e03003940101c0081c000114105c0307000340950004070380354000500202d12510f018550011001300038080000601c2c0349085a40c21801c6040303000c18011888185050308134909680c0314105400400516103845018868104058005001c1c801d00045c800b0130b0003065042611003103c040c044038034900303203c4640c5000340001841c2c41c0042d407801c00300c40c0151915104881c082c180b0301c007603041c0b280c60b81c9080011603880100b0695145041c09000030060b1814410544e42c54020440003c4140c0c40ca84007134299055040c08406a40040101c080140c0e0400d500790b810a10156100d02c03146440c048010081441d40010f1413001c102140000400c81d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 4114342 1250 4113092 4113097
    0x1a0906060715180c0e070f0e0d06060302030a03030603170702061206030313060206011502031303031407050106030b01030b0c03071205060a0803070602180a0609140d02040f1a0d0b01030605130803010803 89
    0x1402d804038174250b80c3d03810608582100d00300c0e10100001c0c0160585810501c0c00c900101784040c060800015001d5803517000901c0d00c0000c5d070382180429241c2104000780110800450700b9034101c80081d61030502c1c903500050262185040d640400030f028000714242c0c2e14104143d41c102080740c0c40801180e134417081c0c0603644105c240306608001008102c0c0c0e0006520200c00d94100c48003800c00c01301c40341c0c20b542d02030740d07401141841c001c243c100c14000e49000c11801d014502c001d60080f0b40247d95541142400410103000130700040311704004000740104541e1045003010074ad1156000007606448036000140304090356400700940e407101140c00d20610500c4e038000c08541003540d1200881550326410708c042d101c0d0612030740700896044103003004001524402007002102c000e0035580b1030074150340000e0486880222030764600c0d94803000d010944a6401d48000c40710300c110f4080499407204c1e0781d040350007401408010034054a40380032a480000b012000800c0c0c6601443c2c0702e49035a140d445065494 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 4115592 1250 4114342 4114349
    0x14040f020f030703030e13090503040605070c0909080306010e030304050d061a01030504020108010611010f020406170a1505040e0a021002030309060c0702060a081305030406031a0906060715180c 85
    0x1101c580280392218580090b50300203c983c1a22501c04110f021400c06c02d901790041552565030f61216050400504103000400c094001c60311800d40720011414202030b00c411a4005500c0d040c5050303880c401083c042c40a032940f000003407905c0b02c3c482c0020008030f4114000c80e4802504407035004600b030100700b17094128500102410301c50801e1090b000c4011415128103031000b074007040561005105645c40f601410341d0300a4440c00100b21504102d46c54012640150b000da000100000a8807000d018646203042e0407010701c4c04280b10850000d0406045040c46204d200d01c106c0e0794003101c81a50030148140c80006400038088000342e0b50b2400003944a074401c84901245026600000b1544080303082960300281d009081c2d2801c0031a012001d5507036030030103414504400c24003001000050740800040c4043c02e8540e41c082844c4a04005211002200ca4429807088100e4401c01001d52215030070f9803c503540041d8032039940030860024500400541e190260910111162502403118550a00044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 4116842 1250 4115592 4115599
    0x406060f110312010b0304081e030603010c0f050301060e011206030309030c0e07020a080703020114071101060b0306030307080a1205010801060510030507020703120207050307080f01050105030a17030a14040f02 92
    0x145001c10460742d49038851207140c0000c0780006401808a48644409158403c2c440c0610318503000c94461108042d020f0484403e10780c3c0c00020401401d418203000e0350304441523505040b41c1450300c3c640040d1050005020308001c20100f40c150161980c480d0b00c01c0f000ca0210f000007006259143e0900910f00400c03808107580150300c0081c0002d440694041c035610a982a40c0038105070f02542c0c0d00c1441c039078080c0500b54215901c90a0701c18103a29a52265400b0301d120380c681d54012090a0003642c251441948000354015061081105a46004c01181d001c00c9e40301240e19034072140401c050310424110100c810341d4918002c0049200581540400243d60303080b544400f081c030050104405854007100ea403c01600076281c10400210004008068034100d070055840050311400400d180030181d52244050f5400224008132890083c46160b02401090f80a0801604240c64401c0300c500c00f120340e00784044001002a980300c01d958484096403030f178400000d001d070030a428100740d10345640e2401e074031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 4118092 1250 4116842 4116857
    0x3090a06110406210204050618030d020d0206011205010219090603111602040c03020904090605061002060709230d03050304020103060b03130204050a0905070e16020105070503010b16020406060f 85
    0x20207556581c00d441c2116410740d515100190780720855490b980c20042c415004a400b0701c008980d80da5294050490400d4820450340003445640415103090305202d812802c2d900510616003400350301103034460540d03c3d0720502d0294203400c0d00c0c20900910030162a0303102202260130355072840380e20071002d8007216507903a4240100403084019150901c5a011507196000c1c142101e8401170815030010f88446410b420014140642080440c0564081c60030072a02070303644800300706581c604941d1041d086039151005007541d2030b01c3c1201502412407030184500c4562070310700c103c4002c03902d0500c0c94000e1070040e05024030503045190181541c1c20580d030881c00709013006c20101d092001407054a21a007040c0c1c888131140409a000d100084c94041c000740101a1516000c6002c50000c000c0c05004100d400c100003850f10740060100b003440701101c0e0420869040000788503045070702c00152810f444010056035500e50130b86400e03e101d210007900c000e42040c00d04d07200040c410380000308641580e5440c0c98004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 4119342 1250 4118092 4118111
    0x70309060206010b090409020a0308030a0b0307080703020303030601080405120708032502100e0c060c060105130207210c020406180609060506180127030611070b04080d020f03090a06 80
    0x2e0716000b0900416100c420144500d0302c0390b140541200d0007103800034040b045265180c0d282c0e5951544101c40041c0d11075122480c00300c4c80d0a0421941004051980103407003c02d040d0703030009441f8440546518100b100010104040c80020f0110780c2d00c04490480a0b0350b01c0c1118a00300320306410455170196a0707004001560541d0550200ca00b104200340d9014091041d03116031148020466081e044d101441030808403490b80e26941c00a001111540300188099850708081040140260901c0b0384103174018000d44000815400104050b8888196034600648201c10104e900d4003030303940041d50240c141400015922050b000c40b282c41140850240300c869120021402911114410550840c80c100b006081c010f08070003549a81c41814985480500114140250320f80c0a01b4010500228140d00400c02c0103400e106078480201230600c001d0800e6010303211412078150052010b0601880081d48042ca05016070444000c1ca4814982e1502d038185012030544d2007a440c0e40403141180742c4003006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 4120592 1250 4119342 4119347
    0xf0601020a03020703030f1106150306091f09060b0d0b010302040b010203070209040b0709170609060708060607020d0201020c030102070c0e010603150b0a05160b060a090507092d0b07030906 83
    0x10001e60160003d044880c070350740e4100c50b80750000070b01c50104a08030354a640c41744000c0c800f00c0d020306901c52201800300e1118040504100018045e404560b228210041000443c501080314000420900003052541c41c1084806011402c50195200c44944103003820496401d03c1c1c0c84c1624000c0e40e0400ca004040d6005a940340305d03520000e0741c02100c0c2c00005000a000345000c0e640541a45005010141e450408040c5c80400301c12800d01500904104199540b0030043c241c0d000da8186000e50140c140b410104880380b18200001c0d0050007110600825a4003c02c4000b001c024082c000315942c000b1ba040c9003844003030038000c1d070722400c2558000180c541d1007800b944840e20340c034150181445207808511403d95004521941c20b0003418014882400c004401c02c802c0103020f00c00c1e4101620303040341000030f01c10407608050985850101841041c0d5400f0103170320241c80503034104101c0035050006030303808001842d410310b42d500401c02021400004603009800041d07ca501c50056094407040c05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 4121842 1250 4120592 4120603
    0x60103060506090607020d0203030a050403030f0503060a030609060605060c10060905090607210507030b040f09050d0507020103020c01020a0c170301030203060c0901030e07080c01090b0717030603070f0306050f060102 95
    0x1003503030055060000c02c4291528000800607144020b1a0200c201f00e694041390540e0881c84800012900c041000c0080c503401c8403001d00c0440380761a0441c43d5240c0440090300c0640607000140c10655180c01100030844103038401c1003d484018401034480590340c182695860801d00310304155410124001402521802264050325500300905081d07a691001100d449002c110304007a072044c000c259440d010010300c605030003030407965000301344002200c050000b40d07802c400e20004030500e004440fa01041d40810030000141d854034060356600901e0004a000e40101c458021a5500c006074815101340c22045044600d44100402c040c2c100482003042807a000912010750035412410001d0040d4407030100900d46e111050400103038141812150f180782000c250885606a40b0410407484d096801024000040c0b0708030344c410789000156594044144185041c02c00d6200c80400400c0341c6642c02d00451010b8800628a580c0181d40c9007000f4000e031106440d025124010800460502d500c00300c1d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 4123092 1250 4121842 4121849
    0x501090e0d0305060604050d0201140c0109060e0a0f060c180e01090b0603010b0307030504080c060720071d04061d07060806060f0a1404051801080d02030c1c0e0904030c05010506010306 81
    0xd018105440c1109200c0600c80f011010ad0400c0491000c0380c0b0822003000c00b40c511100b42c036000040d0031241d480d1003070441d401c4181002c0e00364080c0c80d00ba40000ca0036908558410b510100104a103024101d00741c0e10344200f800390210b00100d1a01c00701e88000d448984904a4000400c14452580d504007800f000c1e110038090041100300401c005240d090280d0003054000303101d02d8200d0b160034a031500340c2e420072105a07054000030340c0d03080b410340c0d0090700c0245000075424440040d00145140209103034102c0e020b10340170160519008001014488954840c2960090b81c40000700316118a1100c0d0f511907034140943c5010460074404a481d50400c0015240722004900401d4a000e03600758050351140c2d03ca0b40c20020a5404220116181d11441043e0f090108590303403050a41d414984210300700100c1500040031584107214007107042800140d00e4511080044056065440c03224048070045016100baa4004114501f48000c050b4050444100c6a008000801143d29190011020745441c0d11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 4124342 1250 4123092 4123099
    0x30708030d0f020406050a03020702060f0708030403080105060f070f0c1e060f020304030807030302030a0b040e070303030b03030a17070c05060f04120305010b09060f040911090a0608010803070b04150501090e0d030506 95
    0x200b020051fa0080d4005d22980d400180f015041c0070800d40406819885000202c1d441c80010041c4010150080152405458119661402d04060000c00b0645000340d0f9000741821143d5014441032100c025800d00141c4190360303483d141c0203203580035060307148002d104202c0050401d01c2481e40261012081d5401d60340d000e03140b80d02e0034031185c03021006500041d00c440036540c2c0c0c9017081d07030719660745200300110100d5590103010001d02d103040c0a003c4a51066042d0b000f50010044007010030341c002c00d5401d10301050554407a00d92914070003103c1d0300c0d151030001049442800c0902c0070f41c2d542280818400c0d8071441c003203880440c5005088064483c01e2180e140001b0061100320706916183d0302401c5000c54040c020b508142c1e6800e140d1099550b180200512941e00041030001400c00b401180040c00702801e140c0801c1d450400b6183c0d132032181040c044c203410350141c0443c0130040139000b0740c5103a008601c420300880d40c4074003501005280d644ea1002e424403400504400160090150a01c0707820700a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 4125592 1250 4124342 4124347
    0x301030209040303050603010f0c02071404020301080a0609030210020a030b0f180f070302070804030f140a0b06040b040204051f080108010c0c080a03020f030a0204030501050105010e031b01020c030708030d0f02040605 95
    0x2d99013070300540350240000e0780c55501ca081403da1054540301d404140344984d801040030a140901104200e06500400d0b4080c1d80100010700c40c41c28005030342c4c00316503480f080006500341542001ca041110080b01d90510310b0000035185105580754101da100304604540e8007444012a10421046128014003254401500c0300015600075031041280d5001d4003c2c1000340c9031040c10b43c1c4a01c050b030b1051308104d803c40c0965840780c2c203000e440042190b03400d031000d000703201c825240e1322110150361006003240c0c8129110a00c14003161a50f0301038900506010740214001d05080c8100d420358a00f2400140c0001c0201c800054030001c1400364600e548415195400341d4040c60300d84640c507600c244000014035408000310078100411f980190b1191240181c010388a0f800c503d0324500350740040e404641000002500c190300c0f5a000301e20802c0c05200034500d035a10042110040c0c0c2000c80340041c0030b0b030500680100291410300803000b002004283d171000c001c240c0c0701140305401c90285000c1c51001032010b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 4126842 1250 4125592 4125601
    0x80c090705030f1303050405030304061e0212030f070e04020309030304050609010c0c02060904090c0602030706060b0307171509011403060906010311090901020d151701060501140901140c0607020d050301030209 92
    0x74108032401385806440c0c0545016155004a45140d100380d10542c0024428024081e4208281c0b241c50303e6007082d80301520001c0d000003d413540741d02018000d080380f1560080852191401408a2400407101034030a6440e49022040e02c1d03201c1c2c008076020340e050301840740040c03040e5006120302d021017046901c680d00442d400780c0034052250401c5a1160f0040c0c3c0e15081d10020074010300e0140001c2c00c4990003541c0e14a46882c0c0762094442a602480b083e250900600089070f411030242e000307420190002d0075080d030b01d024058423010f5048410380d4100410400100342a1015640700707510f10002e03400ca891544031810055541c00007484042c00070620106100400d2070019501c40e0842c1c0322200140c1000e40d07500c0103c040f10441041c0c0c4465008456080013a0315031034070030a1700b604802c0000c1003400e20b00b20010f003041e03141003403002a00c04d00041095841c0c0c041c0c409503070004010b03ca11503c0d0300854680b55541c580c159042009845440c0340b00d40d600d880384040302e050b42c0d4007a02480103500c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 4128092 1250 4126842 4126861
    0x7060302090f040504050703020310091101030e01091502030a0b06070503180303070605070c12020610050103021e07060207021c03020307080d140702010903080a0e0712020103090804080c090705030f 87
    0x4400039180d801890710b403180780a0b90361801800c0c0107502440103091918658410945007503000c2540014040c203200011012404507000442001420308010a52240c0004403074010400182c0050565040c8000d984040801e54081c500c01c9c10140010864120090200240c4e4007130880000c00b10340c0100080c618001d0041d0700500a00c8010307045a00748809a500c0c0c40540c0e5003265481e0001e81d80074541c005100f100c40d01e400c0c0011840c000342001d410b0880e040a040542d034001e20341895000141136610310003260340048200c00ca040c0c1c1c00d03120112850500003030360042e6016440303060101030104040c01c0002d84090300310b5164009501c2e05e6990b9039500c00c0303034100c0ca62010100d60350300035007042c0700340c405030311440b501d2140d0000541d13031500d180160000300054021790b102c2c1d00d8000c100e03200e00380001301041239482001c901c1070130403c1d034401240604219000144486804500083d40100015102d0948402242c80ca48656603509040760a804100c1e0050511105d8102141d040c0c123 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 4129342 1250 4128092 4128097
    0x5030f06060409060603022101150501080708060a0b0c030903010c0212040e090106050604060e010314070207030f0804210302060105040c05040306020309150c0904050606030112080a02010e010908090306150307060302 95
    0x9100e0311011800546da41c000a5213040a80300120102c0c4914251041c0b480081c0301c2c03001d00381010241c2d00651814100001c2100000400010600c00008040f641560740c100d03103c4000c14414400a548601a0a0361070302da4202607029802503080c40300c0300f86c40034004142d040041141c049180d08251408205003280000600090140e558510010603640c03603010003000074200581750200005070b1030000408a0301e0f281000c003201c84148091250140d408141c28003100e411500403250380e0720505003266548581c2c3e118040601d1020321800341403c07007410900b8201e01a03000d60744140c1c0e0b41c1c01032000742d034002d2801c000024010402480001c0c059400b40d50000c61060441e4100c02003640e80548250007603c20040d841c001152058580c0f5003809050741c03101c006e4400c141176514010312180d000085d0100205203803c04100300c40181c0c404d40c082c540710501f80000380142040382c1008020ac1e80302250490080c00344400042d461040d40708a028a0000500108486842d0410440094 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 4130592 1250 4129342 4129361
    0x50c031306090512041409010b180a050a030302070602060a050903030403120902030703062403050a08031305030307120f0c0906050309010b041b03050106020a08160c03020603041b05030f060604 85
    0x442d035418850000c02d20030454401c02e9112010340b15030321410800760050150320b2407081c0b40308000f00780c018480307900d0800a0325055039212649c0c2d4a003401d40000a04035000d207420182e04440f1904d0000103050740001c03508102e80341c507002d0754120388400b100c0806a400407144844160703c00c00200340000d10440841058600045002032030410300e500003420045954001d40d1115114903503c0700900f12041c003003003021a14204414650b1450395060345404100030090085600800041c1000000f070000b2410503502c5000d0380d50304d280104000c0c0403452000c29042049103407851681e1180002e100d60442d00c2e500342c44092046107841001c072440e5000404070107003552509101030854079179024440421414026000d03894034071410080c11504141d20100455000c0c004000125075200101e581307000c0800d6401c5100400c0d801c210141c2c003404d5100940002c03001080005101a503001c1c1e10320319600000d4815002e40d210201a07135015038000e842c2e05c40c0c1100020480524181e4400c0100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 4131842 1250 4130592 4130603
    0xe06090406180507021605011403040501020705070803131a070b0411120102070b07020303041a06033901050406020706081b0a050703080601051305010f021f060305070801050c0313 79
    0x302d0300c8103010700415020040e882d03015500d58090104058062101648451043e406100928507000000b0700c0d03410354200d039101d50800040400c041c0042074040310b18035504901241d0030607944140e807030795179070007180c1e01d82e01c15035024000b20b8011001181801c18001c00007006091000d641c6035842111809072007125894031070341c1b80001a0310389805001c1c0ca0039090b80010b0312200706080c5103034410401041041150400c100300b100140c02c900401c022400320740440c007007590747c6001003460490401c4400b162401c0039103000070082c1e00c80d01454448010354441b003107a490342c44011740c1c16001c0c0c0e010344805600a11814840148601185503110031837004142000d050341000140070307482410b040000607400110403061580207a803040d0080e10a18000b0b103441107940000c1c0e14000c084c001c1c603040003030701007a02503032030300c200320000b41000700d4001141040324100e1114020480c6102c01c40302d5004260300091803000c10700c07615100764051130741d941c511741d19942c00ea00c0510104908460 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 4133092 1250 4131842 4131851
    0x20f01080603160b1e0405010207030807050102070503120117072607030f030801060807090315020906130906090605030105060d110102070e01091a03011b050901030905010f090201030513030e060904 87
    0x1409001040c80d00600c130000d03070940d85818014100b0001003420b0101c000100082008025590340051074004683e008454603846040501d0700c140a44504030010f0424030010580e05682141c0441e000d0484401201070103917000e040d101c00e42c456040b4840d80842c2030203d038556050244d1517904140340302000b0141c5800381e44a64030074080031001c2e8010f8002500810050110f80e801c244003540060040c100b65900e2440d56541200325004811a08405500400c0c81025912039009480d00d10440c900301064131a1900c0280d401003d080c030417491864100540080d9a0406209444c05210080c0c44101404916180d40500c880c142c800381d41103100f104000211b4165a51070365020b04074402c07020a070f20300c0c2080020101e25081c10214842d91410312a682005010140e000392904181051612007001d0401600200f2886401400d10b5092400802625610b80c0c422000d4134400d0324204620f07140c026120140d4128a04002e0204501b045100001d240c150003034581d41741c00500201c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 4134342 1250 4133092 4133113
    0x2091902040306090201020d1407080d0e0d1701050d1a0709030506090c1008070f0806040e0a0f0b010b03010803030a02030c07140a020f030105090304260a050d09050a03020f01080603 80
    0x20100ea01030350058071280d540714140c00466030705000c05850180d25140408000f0b8407040403554034402d402d00103010341000100c020b00015260408960b140170941640e040c4003003440003510107210a034100d8014071880c800455945802c245d4600c4d51500000280440c00c110b200f4900491400b6040e8000e00c0044440040068401c1100718498800c0e0310240844842810510044520072240c0c042407010080c20401115805034010844d205240b9021f0384c00d484040208000303100c1528280c7d460f0094075513080500102d02804109a4400c002c0d448407030380d03280a80c160f940030a02520714240c000304085000300107150080c54000c150880d01d14a0404250b50300d1520000c4c8174038442032504809200c03020762070f106280300e8a9050540c000e101c80d1800902c0a5102c2c07046004014114588140365600c40302c14082c00c030f81c2d81000030100c030780304007032800c0180da81c4e420883c070003001071505103001c9000e0502807800421070380c0c09007a001c4194004401503c040400509079605886a2000300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 4135592 1250 4134342 4134391
    0x415022d0702090c0d05010506041203050a170903040314030702030c060d15090c020f0c0604061110110316020102040605090607110d03090602010b01030204050a050f0a090203010f05010e01020d0206040209 90
    0x282d0007582c04c01905640c94000c08071100544005911407446010240010800d8410240c0c94111003076052400c950340340425002a00d90700e491603000240b881b9a039003084210900000140180c0b4041c00701950801d80500303480750360340324540009405800c07031200110581800c0b03010f407180c04547c010205034024480d02c0159094402c0d881072071503d8440f01e40800d00d52b01070195410060140b0040c1000001e42c01c04500944514443c1d401040701001300303901d0006060203603e0728150780d2a400e0250003410340c00c00d88190400e0301c8240400da201c00300f6803065401407084030201c806039103449007085070240030080c143d0011740081d02c500c0e09002d11081556200c454034a00e107407007138594407101030600c00d0003801c5032503988549045c14130401040c4900d41d100c0440000300d8004980358000b900c4410085546450300780c2c00038400303a00100010031420038518102d400e5650a981e600a041500801281d0b02c001d5840c0e4500960003a1003c100542007002d41d0341d610900e0104864510004810350 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 4136698 1106 4135592 4135609
    0x20603060406030501050408090901060807080c0a05040b0d0e0106090204030803010311040b090f0105090601050720010e030a030201021b060601091203091d0415022d0702 75
    0x180e4640d403181c102c1000b03103038880c0081c00305052510700703d480c580190f01e40610070a8840008520144580c10f020b1040318941d8921241d81c031000c074405200ea0010030114200402040302081004107400209500018101c2c0000e042402180c1e0500b1200960841000b80f07004000c1000072031184400e59064075005030505020a04030000136000b411071a0042d2742081114040101c010500c406d1181240c0c0181c41a070843d80e0b401004450324842c98a0080c8050034030104000181180c0070076010800043c10714001d0b100075500028070306509080d040740140c3d00001c1912154481c1000084500f811300300419140c10605e0011300301c00558000c04409800005000b018944103140708002080140c015140c00408100c501500c0741e4100c03000c1da80c4c00704002501c1094840c500c00c8461684c14010a1908111440180d00c0d0340c00201c0140b0940d45014060b07040036a03030f900321 = true := by decide +kernel

theorem cover : BRFrame.Cov 3956842 4136698 := by
  have h0 := BRFrame.cov_init 3956842
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3956842 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 3956842 ≤ n) (h2 : n < 4136698) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
