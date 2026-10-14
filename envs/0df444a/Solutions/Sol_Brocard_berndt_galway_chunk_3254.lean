-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3254
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:06:56.824519+00:00
-- url     : https://prove2.me/submissions/ca4c7212-a91e-49cb-a0de-deeafc1bf9e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 585071942 ≤ n < 585251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 585073192 1250 585071942 585071947
    0x110a111b090c03040203070905071112090f0d2303120a0b1f030e0303011205070905010303090e040c0b0f0d0e0c011e02030d0c0207030b010918031b05071e0605 70
    0x800200c1c0120801030b158105030320340440402c0865070f05000c1c2a01900c104a0200f1091411380300c01000c0b100340c0303092194240100740c80c105107100002c045601210b0040c01e0680141c1140083c829541d42c804026a840448540c2c40103c2c8070000010800101410f40151744034a040404205040000b4086502c05072600e101c0e6041c5460307141c01d505204495051020345903440c0c100c240d010b815121509074090000100201f0b5a00701e6040340500e1034000c6040301c501607200d040100845074213000180101d03041d00002c12090f90a652840e034440d210b03081640791985d4940205101c0c2d0080c1600f602e80d628082024840304200b44602800c41a5001c014070004030000006040c00b00020310005185d00b10880d124071030b80c001c204581c9820101c18013080b4401d03003c074000b52254003502041341e0b81c10911000051070790a500840217003c1e916481c1040030702c965601503d403a50010702001c2c002c003c00a1b0b103004240180000ea0007010f0000b610101144180c40c0c0c01c0a000c0180c00100600005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 585074442 1250 585073192 585073243
    0x61801030f0609111002070f0b0301081902061608041802070213320405010507080106090608060a1701061a0c060f060303040f0b0c0d03020903060a0f110a11 69
    0x4101c070a550041c000055507102810420480440c8a07002d903001120741c40f50780d141c2907001414a00300c0f80100300d00016680c031107801c03100501c401c2c4600a041e50062000381c07242990034510030740c403520051005203450610444074155000c0a502a500042d01203001c021b2402101015121603840d10310452074154140d002892207201c9a020303265541d65581c0d10b0009009200c4220300c0c00250b508001c020204081600495900c00c44080700c155090038041103d982c01075000c981a6200c1d52a44404503041140c200c808000c000d01e00c41d8003d60b2610009007104900d888801d40000800000c941c603070906889542044044c1f42455040000b008130103201c9030080345140d004013604003604019144e0100291860244c0d40000c0000c0d08015400120803c001c0010031411643d42c082c0c59160394814020b8040380a020100d54060f0845000161441c515901100d20800305020000d040032034407010380a9a00004030410110390030720301071002488200148034141d610000c202400307101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 585075692 1250 585074442 585074453
    0x705040606050d0510090f02090a0504090308010b130e130b09060c070f06110307020a03020114010315050a2007151506050d0905061e09060405120d020706060e06180103 74
    0x280700d64052004e64032004611007a88400c103005c01000c68083c240328041880c002c82c002907020074a40c501ca84103801d000141428540500d0141c0d07601900c070200300380c1c1782071443c0354194030120500807031400c0000081070041b9006842c40c00f610004800d0141c0c0c140b14907000d0341000001d04804080d50100c0c0c10800e984071200111916141e2180762107880340d00610b800e0014180a43c1c600e9002c500210421014950004018080d503010b54000e20041200080c0c507071405000780400707010101c007014201101622508440c1d0403441605e070000c0d642c205500394010420203010780741c404000c002824002c1c0420801306009220019004002c80d90410f501152181c500d03119803010300501284040c00c410a41d401000c0b001d030418142c4142d0301c1d0904d4190001e11561100218441c220400304035100030004010344a168002c00910920959031b48070b40c82074008250b083e0300c16800f0411080020104e008481c001d02d400300c0030601d07a0030250204200c800b01c141201c203080380031a004002140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 585076942 1250 585075692 585075697
    0x30c030201020d090b0d1d031b0d0e1c030e0a0303081603052e030b040804051c020109060e0a0f03141c0806060d0204050414060102190302060c0c030c1e070504060605 73
    0x640311000150903994166103070305a00f1101f0002c40501010400c179290030142900400000328040655a1400d00d90304280c032603240c070205654204a140b001e00f80c01104580c2009000b40c02803c0c010304101200380000c50700c090b240c02c100c000070808018424503101c802e1408440c0013580c03c1c144007603d45140c5828401d0006c1c107020030862401002c0c0e45810120009040213160404908413a921b41410208010b900c2885650b01444022065446000c8400c00020b0b4030380d03050755824013152400304100c41d40d036050024035a03c10318014000036180d1410400e080150303c40c0c08005400c8040380030b40e50400001000700820700806c41100e00c0441da20a8209500040807100c4940f503401c0e003030301c52000f8000c0b500499041032818412400b90480300308142c0c41034000f40d00b191441d160800001c2c00b18a114500200941e0002003c20000ba22800280240c0342034202140c0c1420744010010b8a0501044000000009501440c4088180520608010b090251000d22405140c508003d0007031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 585078192 1250 585076942 585076957
    0x12072d050717090306010f0806010501030b010e10050415080a051806040305250503030f062202030a091b0f05090f01060305090f0610090f0b030703080c01021201030c030201020d090b 80
    0xc01d00c0e03040b80001646031800c2e2119628041c013160039560f191503803100c242c020340c01850140d1003443c000041c00c0d88203004040074904182d5403006c0e0000c5d0042441051301032540140c092103410302c4042112800d42030041e030a11f1141d65000780c50305203842c0c0d2004881c40607040352070003144407160310180701001505a400660514226603a4038001c49815900304101502040481031703902c803a400d1100000c099070050000d00842c040d00d485200800c00c0c5a28440340052215404110011b540451903001c4d50740000019000315a0540311340d2140403582c41000450016440d0307400c2403000c0302d08480c0d00c4010780b0080c0e5401c1c0007401d1003404100c1003101441503d08062b01c41000aa1a0409101c07041030403038000102c40003802d02c508240300350405801042034840c54070112800005003800f904105090150103000781d10b003161200c00321603000c081c0d68a219074007008104402d0400040e0b1500a60140c0005460301e41544002818402403c1d544400c20a40c11001c2c4841e16003002100d450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 585079442 1250 585078192 585078203
    0x506190e03070215030703200c10050402030c060d02070c080a0b0109020306010804111f02100c1806140c030d021206010521070201110315040c0f0804110612072d0507 73
    0x300da440300d1089002d88002d000c51020b050441c2031b401440c01c581d00180c89270381e03c12810b880304421447c0007403040f03400407600654954840050083c50303050403c000c09600040e008094640003558907120036401d02640500390f1a8010031a107001c0c406400369280c09840c030380105515500303002d00028454480940080e0124101e54201c440603554482c4410040303042c180f0445e9107401e404000794403032000000c40900b06040c2a40d00040728440c000c03080c0302e0301c03961601090440c1018001c950f40303100303240c24601c42e074020000910190020400707001e180480d6003000d40c3d100a078801c000f000d000c02420f41c505010080c0b240c007010301c04041c6400c000c000c002c0503c206036550b1000803400f505241600c1c1c400700f1800424404c0010b4400c00c045228041640c00340050000000e049030b04140c1101088002101c00011500041d9004038a4002190080c4071a0070325030004ea68076000c9500f503403554080780c0c0d03494482e00e0b6117448407122103448008030f5803004114030801e40a45030307202d5407000501 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 585080692 1250 585079442 585079447
    0x3050c12010302040b04020409090b1005010c0510200c03030907050d23010b1009030b0c030403050a0503100306050708060405090601060f0e211006080d1209020a030506190e03070215 80
    0x82035240d503410352300100310201d4117110b401560b01300401c01035002d4030340c107500f549584030104440d401240f4000c40c0c0366103c0010a4a1400c0d8004800103018280c01e12404083d500c6014a1a00c07005c009482d041001001455413801e004802030700e48866a44091700450706000100c02003140c203401500d29900c0494003054580c213202e415401841411100c961040319007039100300d0030381d1101c52032058078419002003032142c13908030348103449010480d0010001481000b000e680681301b4006150405003075903001007080d0b201d0b03503403205a54044a6410014600f44200041450070b40590350708080329001070308c025410540c000b4180c0b20b00c2421082800200e581d400c8694076041000307080180c141440f006000c01144280d510340c0300400780001030b40c1c18104e02240c07510020405606118036038440009052610340004090000d03d401603038801c1c1c103140e0000c080f500600c4000c0c81020440203000c02d08510f11034070002c503003044900c034000c2d034003d1020000507120035186030490780388201c40c1d58 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 585081942 1250 585080692 585080711
    0x4081e2d0705090901060311090f060d05210c0c01090b090d03050c0307050604140601080a0b0a0f05181005010302060403020111071203020c18090a060c020c150a03050c1201030204 79
    0x9203401c07032075800150010070500c04c00010540640c88642030360312904450000d51080d034100031624000f507580d1003800301c4100100b007041c909220350080c624031500c1551012000502000a03030900048a460402400034004200d188240503809100c0e00034204a0101380c20881c90081500801c0d0b98607000e240040c25580c28540a5000c0c1c850360501e503030440e607942c2c5880c5003203a02c645054404903a13560354202411440240403408a058840701001000d04035a582c0380e60b040e1946c00380c0b40402aa40c0d0702021502c40c00507002c0e852003091181c40c1c90805451440d9142d00d13102c0110900d40f070b80d601d0328005000503a2244210340491b40c09281c0031952450001d407003424601158041d03c160292040040c04042c0c0100340d045140300f044074100c8224140050300e030746083c0e08031130204854014034261800101c255000c080c00b602103104941e030b92401c4002041c00d646024651144896010901c10041070749801043c2e030010346034010508080c82251010702c06001800020302c900d8991b0350741c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 585083192 1250 585081942 585082033
    0x20709020d0b0d050106030c061115040602160b0601080105032b0e0d06060303030f0504050a03140408010e030d0c0e010c14010207060f091106042303010603020604081e 74
    0x42951103006002d41043c1d815403800764000c1c025440101d030394440c404c0000840d03a02401c100e000111500e00548082c105030705520000083c020300865003075501340b0450650145041450621030311032058039266080440c005460348105912032442070f88030145138080207600004050700c04c6221951030154103e2a00c064074082c511408283c0c00410b110810414040d10340c002d0402c80e03001c0e407010040385409281c40c00940d030049034040c015900071560340001a10525011a085910300501c509107034a5090340d900350b840591205000d80c2c00800d50070250300341c52044d02d0304101c20f410112911007420001901031248918041c040030300300c1c00c2c0100464070a404a42203503900071070410000030080e00703102c0100068170f0192000c01d2400f41d0b004850402c9411a010303a401c4c40704030310b055004c8021100c0303592811000e0740d8141d520b0b184000010f032152000341014044420145c8a2605826040301800c04080105201c96101d1500c402d01c1200c05283c4800d14046000702540300c0700ca07100c02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 585084442 1250 585083192 585083201
    0x10c0215180d020721020a0b18100e01020105060d05070317041d070f0906080a0b0a0b030a0905190201090501080a02090909030a0306060221030403170c1206090403020709020d 77
    0x2031058080d80a010310926808030b44d46003590300c3d50f144180400d070946111520540810f8009400070360210084c002c11220300040d100000d01c0b0801d100e04001c04801082d42e0b180341d1401140814a106448811580c0a0040d903a02032810f98854408085a0300c801c2d50780d10350b41c40040c220403a2015031038041010501190701030603e03c1c010b025031106001140c82c20000c00c40d40702000030080c001e03080d00b0620034441c84080b6a42e03569203540c02c1c0c0f03403041030000070400c0380400c5030b011540240020340102d102c0003551103400007c3c000112902d007030800d00d007003110b2501c104c00c0e054100710340800182e801a10040613a002882c00203615516006103400134420310760120f60080d10700d400c001d0707090070000c010205884552380910041e60745580690b61400410000b903200d000a80c03100e6007071200e40d005154840d010b460300c0303071300c5002403140340c0c121030000d94a20b07410440004070035141c2c11038000c94a822500965981000e403420b9100251250024001d1518298000420f90b02c241c07055040f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 585085692 1250 585084442 585084481
    0xe1503091c12020408160b0c0601140d0b0a060303030b0603091005041a04141c050f0d02040e010605040305061e043003021e2802240703050108010c0215 67
    0x81c03c540e43c0b40c8444602e5521045001d00704800400303800301241c50b03c009025a0800e0030014000c10899080012102c640040c0818540c2c220038400c1450000c140740e122082d02031041c0000c00901e40c2e0842c10700030283c2d00f02e1006035000b29405c0007030095503200001d0070203917541610400591740c3c880d0314044420902202a05150f005140140020f011136080341941c42100c2d1022103120104040819205581c4a00c2c070760003282e002d0225291501400004000140d061072005203095296804031040305001e8001c0000101d010034240f0030807504109560701311080a512076219151a0356600c3d46480092000348910701c0e1040d5001c40c80d43e01c41c10006260240b030030070404240c40000040c0207400841e4002034605c404042d6072420b0074281e0440b00b1a410022050b07142d1590000c40c0e10809041a0f00742d0218404c5410043d0268035005e004180350807030795084c0002d400c101c00d00400760b900c1a0001000b80c1d00d48401038040e65000110780c1000000b1040e1a400360780c4200700070020580c0440c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 585086942 1250 585085692 585085727
    0xb0a0f0b07110f040525020f19060608030a02071e03080919032f0906010503040201052d0712031419061701150b0a0906030f09050a030e1503091c 64
    0x100b40801c081b540202514100c43d09038120740808074265003280da4410b1a04424a1500440c94000e004110144a0828a40200004243c46568092843c61030303104080b5500181c2292006101c11045401d9040c2020500c1102d0708055003103031a0f035405407044601c07941c803502e9081181d05000c91080400401182c121031040c0e41c140d2140040c14000742a14880304014520440321100d03450603005250068006035105800c5036510790055a1691041840e80c440550f9401003055101e840c203005200002c0d030305980340c0c80c1c81c0d00745424200d8600460141062504044078110380032900f441080d40b01c5080007041010524000074400103002907005058610712030303010002c1e042030540210740340703082e2106640340c40d07031b40e44018190030300404224400144041c0303810081c00348243c000181e02440c1c01000100955070781d891500e841000b800480120f405600f100d035440c81c001c041080111580a0b80a1461501322002501e41400c05e08040c0d81ca03030700a0444402034443c07007400b4000d00011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 585088192 1250 585086942 585086951
    0x6010b0a110f0a0507050a0b2502011e020a02272806090207021f1409040612061b0306180e12120603060a0b0d0201030902060c0a060b0a0f0b07110f04 66
    0x80c00e041791103020a001d41400780580b030100003108221071045507032400803404080550070100070b0060903002d010b40103034104442c0600044000b861942000c0000e5000e0b0010b10f14034403140305125103111003440c2104607084001c0c0e8410544000308030030703134021141e220b2210b00400c04030021014441c00003006624500d04000400d00c1c100c541d009004c03460080359540281c0342c2d104031043e403182a2360f05980004241030741349849541c0210140851a41c01007010890544501c05000301c130350700660076203095403652002d01b81601c003d010003086290600d0700f030209034141140a40d84900801c5d0303d900da90340c0d8990399070b00140b080c480c0c843c5041060107042e03502c4c1d00c03c0301c41c182241c04c02c0e200303d4400d025280101d010407205101e904e03506d041c0034001c40c0100c0c0268006400912052209a0300b184080000b440e20860038000d114015200d107500041c15807a4109105d5a080660800040d400c1031101c00e004030f50403135050b60b1045900c0a9202c4c05203407803c01165101d50300c0f0312480d8205061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 585089442 1250 585088192 585088213
    0x90f0403210501090b19030813030f0312060512070b0705011104080d020d0305060f10030b0301150f0b03130803150409030c020f1801120f02031c1106010b0a110f 71
    0x9503080b0a0484070140010f2003805c0d42202089003c81044411505489000300b0401c00030725005c01400807105100310354148207650b5102d0081459102c03400b140016190030b070f040440c1d08144500310207448241d660700313200354040841d00e940b000c10340500720411b00040b0701101000310940140c01a51500050b0645650b03aa040c00c035a10300107100030301c0250050404410615110b81b203a9071142d10010302540328040030700b040c02038040c91400f0744c0c0b0030962220008825500c003405621003070094513403415901e6140480710714141105420900300000c080091141d149054400c084240b5049079600341ea0b5141d03841e40d4621808100d200940250801128000b410713045881c141c40d80c0e0003941c0c0080c800d50110200508000c18815078520700c04094014882820b401101c00c0c030240c0315070003100c003022054000910380956078a01440003400004500700e181e074000d40d82c80307030072100030003c1c55203504150f0000d02c0d5005504e13a840401c80118a8507881407002c100010750600c0d01c138180c48050f0003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 585090692 1250 585089442 585089507
    0x1090f03050c2820041d07060c0b0a0b01090f0e0115030203091507020307080403050f0f0d020d0e01090504050a0507080705040b04120201110d17070e090f0403 70
    0x4141c80070b1a10340036803c541d00114802400c140c1d030784608444031980c428419503c506090043c140080c0044034452203008494031244076101d01c42c1d1046108090380810b80c0344451902c0704d9900708504000f2040303000c00014100c1ca0f11107400041006010408060300b02c012191034238940d210f0039003a480000001603c1003003204081c181c6865080952032030440800c1a4240d10080d1210b02c2d00b43c1c040d030380d458105400c01c001550400101d1054070706e090050303203983c0b1302034000b60400d40380386d0806014040c1e0b842c01001142e45010030076002d02206000071a0194440b00e1484901080c0030300b68540003451ba2003040b803040503110003001003019080c03100402c4024038048403114085944200804c00450150081c0c1c0c04032510355003141e2806040030582c01940208120890601c1341a44001d000b14a0034009440103100c0ea03502d005c25a9180390700c0355040840035290001b8070a0120b50002540c641c002d9207a84000701400900320342e00c6601d400c850354030385103801e501d2200212035040007034003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 585091942 1250 585090692 585090697
    0xb06040306051e04031b060b061b0d090b0d0b1f0201020d2f160804120323040302010503090a060c02160e2203030b03031201051e0f1201090f0305 64
    0x301082191591000c811090212000056a002c4d0104d540b11006601c06c15481c544615018898003011480102c1c2c00040742c22074200a45821900300c800c518100199010000903100d03081c245480c000c41440c1c5240f4448a1040c0740454020544615200d10182c603030700c03450313000b1001018410346c400c20319510090003504662010b50300703d8141224501443c05011354036600d58101c150340d400d00031900042d10300c3c69201c1c450f1440034160403407100340411040b501800041031b03000c0700104131344fd040c81c0041c0301e00e1440d6140c10b13082c080d1103000030760921003005460580b942030802c1603682c1c9402e0b038200d18001c3c2e0030100801c82406c10210709101c82e0301082140e0140589046c4952003501c4864080c1e20500c02c0364a8101c03038016403601000526140e00b808032150090400140b64a490004242507502040a481d40f040482c001041a400e00c000d002c5007050650050712081081003000030520301d56190070740c6c4542d1100c500580d8030380c0c081d404068215404058a92002034500e000381594 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 585093192 1250 585091942 585091951
    0x41401060503101a0a2423070506070203031003060c121a03010f0e1b01090807060e13021c241701110403121202041e140105090f040f0b0604030605 65
    0x300040d090083c13541846084081596016207440c100c0c3e03006c2c000402100340fa24030b041001c101d2080000d81c01000010320011804820003001951202c0c3d50600c0b601e0030304040c00f07090455000b04100180c03078840a05070801d0700d03807000380451400700859003110584115032081c1c000718a441c01001000d003000d1560948024203400900042d010381e20b4020454140001d0607020340c00c2050310f03d00d5a034081c1174810462005060550615484694940c83c125080d00400040703140014005214542501c1d030001844e4010300c154940712584041c503036000c0e081041d180c00b1680f9036941d035580341d60104105111955a1018000059468207071600d5030a4241e0301b58030651900300403038805105182120162070300080b03500c0b01c052044104845131658040390107000c55092002040038901f42c0740e021200825002003403074041c286849210521a4800d0f0325051210402c101e001685500d4240115400110750000744d00701c400c3c0c1100090081c41100d158801c43c0010003000704440d99100760f00a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 585094442 1250 585093192 585093221
    0x9090106030507050a12290901020d140103030f0e0301110c03070b0a0b0a0e060103090f053d0f0204030206030c070c0e1905060103140108100e01020a0804140106050310 74
    0x1d83d900c00038401068034902806d00790303035800341720400821854040c2d00c040e402a0800032503140508060181103000654000388940d400107a40c000e845a14001d50080880e046905135003549150780c0507044000c40b0400d1418440ba010071051b05075002c0d44000811072413054407503614081284001d44070707030102d0402c40b01803000c81f000c6082071100340f14003034800c42d01612841c8501c0c2849604075403400006c20082c105602e81c0141400142103600c07150405104000030050002c040c0d41c0503183d025810403000c0d030654110b641c040800f000101c403190b00c0380070240001c0e07503081c13503100d4402a2007a5040a90400d07400800d0100b0a410034006040e1a07010b03c0c516441d840e1610b14460480303c05581c0c1d8150140c010300c461000850541c404c3d41c214805060020340e00c0d030500b15500084c00242c1c031601c107a402c000da02040140007070041d01c103c05528030085160411880014084440280000d0100d10580000030303200300d000d41c030810251070024101d4002301c2812071000050f04100022111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 585095692 1250 585094442 585094453
    0x10031a070c061d060a150f080c1c020a260c01050301170307171308030a050d0b0f09070201020405030c0603040f380105010f02010b01020a020111011401030f03230a030515090901060305 81
    0x1c421002141d10419586230502030498042000c08100480080b4800c48004d1001c1440344001a5100d06021008207100100300f40340b80c4a0200700399070911025184c60003608403914442403aa40802141c1c103480d0002e41c1040c12040094030b8a145008564004002d4811500003100d1442100094030b085000344e044038201584071140c2c143c481c0100000c080126006000003c240d82180e013001c5110640070380500c41e105001000112960826200c84001d81d60004040c481400d003401030308403503101900e607145581821754900c40c0381c01c220400a030905a5911029000040d0115540800444015070381080c01e1540b85180d060070742841030901103400c0d8191841740c00d0060080c0d8452060507000b80c01d14082039001901d40041c0100c208945560300e1001c0d04801c80903480485c01786008141d4002210a545005042c0c04801018480c0c610403010f081712144e00d0342c1c02103070303d84d030304501d0041229201c0d0080c100b8001000207280f075024075a541006100001507000e0b804581c003c604480 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 585096942 1250 585095692 585095699
    0x415081902210303160c0534081005070302090303071109100e130203030903010204060c0218060312210108060f01091a150d0510031a070c061d060a15 66
    0x70b00407900b88110320310340c106000181c810540e801074540404601d04002844c081680c1c0c0359400e100c1b00041b501c20410000c0c40504441d9154803200c60031891280a4410260421203129030b00d0180300d643c00d54041e2610001041d49200c0d070192801c0150240c00c507138882d0b1441c0b03043c003101c038290708000e4002c1e490900041c0e4240424401c1d90211900341d00204020784443d5031981c82d4410b8020141d81510082041c0703466034500f40b004000810a65843c034499514030b10400050711800c10704050758080704424007109a03000b2a000140e101050f00881c1e607a02c40e940030003140b403002d1800184014002d0000a05040086120f610500c0c1c100e90481c1c0e981c1e02c401c100011035042e91401c140044225042d4031890a010391240503c4038645203ca0410414084142c01d95404072001d50946030030310f60400c02c0103040408803555000003901c9001c2403406480007440a8a100d9024012684030710041c82e40c0300b1101d50201c0700008800079640c183c50100c0404021b0704640c543d0000e00011086e001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 585098192 1250 585096942 585096979
    0x2070b09060403020c182d09070e0a020c1c030b0315011d1005010f0908300301050913020616030f020f0c33030709181a0415081902 58
    0xb500c1032615041e500e1000e0f11804009014442014081c0041401f440d145800c0c40e0562604140304204007c0103102c55824840a12902d810242a07880014018003544084400100c0c3c14103403400443c25400c1c1e0b03010343c0041100549615030803c1c3d0140030305801d00341c7c0d006a400d00903040e034981c074443d101d0541c81da41000c08100d50032505086c00d1104114240318070740c41138044000b138620078038001c08000d0b15540300904040c101104a0215041c407001803540850300d18440500b201880c4d402811903240c80301240d018640204084065500301a40108650f9580160741c00c2155000809401e466a03183c00790414000d0b41140001d407103041c81000031000c000640c84040000a40302410a410076410340000d09400c0240c601010760b142e0820443d0294103003d90b204200a5469030207036480c1c00c201003150800001010091401c1441c240110003441d2a2040308038419140022003070455500c00900030b0b02604112403d01401601030300303003803041146403003941c000c84c0c0102c01000d010180707 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 585099442 1250 585098192 585098209
    0x100c0c02010e0d21050d0e01060302120f0705040203061203130504050606070c050409060207050d05031906082104052110090b040b15060301122f04050a02070b09060403020c 76
    0x810405860ba02d002c1d407102c400c0c2c3c400c00707458103604101c0d0034140340c0c1031440c01f69442020151800c0e95510410001c9d80382644c04491940301d200050184081049040c986078403003070080a000b01e0700000071800d2600e4036060250009641d40603a0341310784800009501a00242c401d062182d81460f02149035880c3c00012551801ea00400c0004902e1170170040c0005054005415584940d00f8080c050100d0810f20030585022010341c0c2c1c10f076481c501402c200c8560042410b13116145482d00e201840100c400082502115030000c01d1100c007012007940e00d5007103100d40e4109030303003040710300070700d0647d03450b02400298a5600810581f1a000000c43d40380080b40c4045601900d000310a40224002c01c2c4405d00013500101d4201189007207842035008941c0d180e0080c0d12104501500001c008140705150340700440b211a000030640e42c2d040c2c5141176014083d04c22440620440e07941c2e0110380d41003400d50480d000c055100780410300600c0c00a00c1251100c808a60907030240c003404105402030301d0300b140b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 585100692 1250 585099442 585099469
    0x1b0a0807021e0c04050a0b041125020a060513030c060201020d0609020c0a1709040c0503070e040e1c030605090106020c10020303071d060702120601050109320102100c0c02010e 77
    0x2c01c6200389030f10070480680381c00b8140000c0256181c03515103e9072154014000400e004c260440e5480700e0701841c1d00d04400500c0c100d44000c034050415000180c2e50602104103d41c40d5141940e119584409004045c0406920080140c01e50300e00000361160107401600650b240345004020083e9650140c500b603201c2c4a0303030401f540c0c004141c2a40040c0c000c3d0360705002c9143c05250380b0306210004010504642e100910b18000c903001100700801705a205500381e60140096130240591541c040d80c43d541c5100d50301e80c1100c80000c80b101030700800d1107503200100a140080c2404041e5a480700060345600c019203c4500903507489000020306400001128064001036030750066116192041c0d08000700110070080d840340b42000b4002c00350b690030620100340481c55001d0445540350400250840d4407950040355180111030202409076850401ca9464400c00d003540a895000040100d051001000c02c3c4184280f9100e111480c450740004001c101d2803003a211003040c42990401c2040c200703140700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 585101942 1250 585100692 585100753
    0x106030b131e020c0a0c0f051221090402090a0b12010e01060f03090c0306021216090b090603060d0b240625081611030706080601080f1b0a080702 64
    0x1e03030715019103809a0080c18003480180507940106059581c400c5082040d1f845070042d5034081c42c1c248074070701e0003c0b80c01c03889110110081c0441203c01c180300c04548108165801625004148041d00c0c0d11203404517080104010040340480b038440c11482d20541040f103940c07000389807420000c0307000c2c000e205500b41039404c1c545900e5035882003424200c014105240c812110030600190020000f40d8900203490188180d07103000e20146850401441200c1c4500000020048242e03c1040a88a0700707040b580360b45016580300c1e581707075540c20104200149201006000903200300800401042c0c03105444001c1104481e801c100c0104c41040040758001c1c00f1800c01c048641c9820300ca010b051500f10900c40750702c6080765908001c0601542400c01c91146810394465502183d500141e10b810f1141801410381d905000c003281c104000001e000c070340c000b01150340d50125480402d104000c03190243c0000c3c1440440583c3d500c00d0484010041c007000d5a002c00580300d00b0a5140038280007214440360f508048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 585103192 1250 585101942 585101981
    0x62101050103150506034b2112090309060a1e09050a0501030903031104080a030305010503070311100207031e031b150209010c1202061b0c0a03080a020904050106030b13 74
    0x480e2007003880e01c00c0a42c8100b15030300c7c841c0a2505000310660b00301d0160754800703810007101040368405080107015400510360a41e02c504a45036032021a043d04c0420001180301045540c0d4040d006142d84104a00590b108002150313040d0240c0d07120040706942105103c01e0340d241c05001c9003e503040a000e00079258080610001841a54420b42c04081018041e15011400303098000312111580e100d03070004852900000301e250141501406143e005120990051130a0b030714640700d6420011038964100e104090f0001005030380c5d8070800c6036002664114214200485000520719050700d54850b045000c50003014100150b074030b081c48401a0f1642001c0c503214a12003825040c3c00a521101555040c0400c45401401040d4084800c0f00e06514030b4004014504208404900300d01101d075600e4400d080402241c0b90321038000c1281e030900c942c54203080700c2584032152428040d0040042c555046032400c000041c48039030603002507a0710007095480b96800a15280c03941c0076202224002807200c1d445 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 585104442 1250 585103192 585103213
    0x14070e0c032e0f08030408101d0102130302120c09070302090d08040f170307050307030e060f0c010b0f0f06160f0507080d02070605190806210105010315050603 70
    0x100005540c008902d82e15520040c840c0900241ca0007101482c2602c0a81d2a8605110b1a80c4481100e0050709820340154207040ca02850960f442c2ca8020080c0440380d2209181003442c02d2800c00a800201d14800039921032440441ca5a00902d051000307030301c2001c0c4118203802204000c40e0700c01d00e0420150611010384e0707880381c040c1c1c00783d882b10484641058202c0f80c640d01107101800034202600050342c410501c5031404403c46d000c204030200b0200140c000304207441c0003550000880700c1c40740c0d15003045001080d459001031014043c00300d44070101c01c03001a282034a074106601000225504681d04d510555038401440240065554002d403c2801044500315002d8100d040302e4405100359401902d0307600590381d050503c803503070703002041e5035003c82400c1c5111601441044007030619883d00d00c8c100340403c0034a46200c5105200b40c000c0c001d002d00812640d0b100d4446011350010b001c0701c0100c410782d050001c5030007814244001d0380c000c102814003510041140c0911402050001c0051105400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 585105692 1250 585104442 585104461
    0x10f0521040503040909080c010c0e030303040b09010f2d0606050d051003120503010f0e0402090708090a060c050903150124030e0d030b011107030312020a12020d0914070e 75
    0x41c000b540c1034401484000390b994a14041c19000c54420b0060381d449a8070404600e0940d035110b01054107001510a008080392400010303242d00075000300d0b0b245a581c40f59510b003401401810924286207050640c0840a4a03007800054107444039410750205c44042581801c08071b508500030700740010410450504040c4942e000180c2061002d00d4040e000e503a2030352490140980c0000384c0340421008401040f000e00e001242200412200024203107925143c1c0c00200752140c01007030502440040000310300321400400a000800d6130000c400c01c0108106030000c3c0664104241e202d209100f05140040c007190a030628904841d03c040003070140d03040019038402c440304140d00d01c0d07007095a52810301804050421034440c8191094900050070322b9034100040c040003d004808036290300030384042000943c01807802d00380d1500441c0060310b900ca983c804031510361101c0d8000760710900204d228401c10f64540d12015803184100840a80d0318040d004c5a0f44a0109101308101a000d55001416152 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 585106942 1250 585105692 585105757
    0x40e1e0114042910170a090609020904080301090b040b1302090303120c04171b040e19110306160c0b0402010306170604050606030a0f020609030703150b010f05 70
    0x21001800030540101040044803030900c014084a11682e1080410880781090310306006040b4140c074001c00d0700e000034420b200c0b605e030014007103031082580d580c400400d0045a031310800a081e8000c00048440c100350504080c00e030428016140d0b02e40c40c10408103c185418420076003416400703840301d2182c80c45074992000940103c01c16a405000c02c200c20141010f10806151280e500100078a46943c140307140b010b2104c2d0208011111548425018403e0035660010300004a00440380801c07410590b000c0c2c28140111164070800c00c528004e0550f0400000d0541c0010b440c0c5c0590841d0340c5561044022114040e00403001808034440c6200714022508101420354054010b040108529607240111203011070302c9004010b0170340180c0140020020140021034106404078001c0045118644030050410743c0990020720510303001408001e140c03424003000006507080740040354290305504101c0041c01c01c14121078000f50640d09100540b902680940d8080038954084d050690341c413807090744070348 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 585108192 1250 585106942 585106979
    0x10b0d15020405090103060c02010b01080c092b080301030b15060d020a0302040f1401180b091216060807140414010c020f060c03070308010504050903090607060917040e1e01 76
    0x1d40030400450951215840c080c001c601c1f614000615800c420002421609a10f40a0741004950f40c10310034003e8000d0280c0300c00c01707400c0740c400b00d0f92a0b2190310030030306d00000300c00110464074490400e018050058040d504032400344148200c103513a5440e8410b4500100c0d0030003948844d0174401c0d101115050382c06080b15510a00f001031516031070748100340716015a58005425040c8440080c009542c1c0714a11030300301581074140040e002d00748200382c0e0450168241081c01810000c450301da03410347c01c000004085d04034911503881c01d03880b468000d2803400300301c07040004500ea2020555140341c43d401214200ca09841e00503c516030030b400112025000c041059030321000359500c400481e038074039004010601c645001180d075010189400703032880b0f005910480c0300d0b03441c2204201b080603000c01110b4100e00200c80d4185c0c1c405036480c210380103001010003d0494002800201c0040d00b1440080c401d480c00c815115001c2d80e110301002059401c01000700038100c08402c01007200820302618032211 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 585109442 1250 585108192 585108233
    0x6060c170f03070516020d150b01020115050d11060d05010f0b09030705011103131e080a08090402070f170d051302010c020111072d0806010b040b090a09050a051008010b0d 75
    0x1c18486800040315000c0d401d00692341000c1180603601c0361102c0e445003880d162002e000900c0141c0380702c5006984d1031503d1203418010704500c01005c0810455218038064608014001a25655040f0700903000340030034040d24084510046002c01c682d8030707010070f4940607000200200641400c10004403100b00003240b104a172840300b07100c04004010301c8240b000250800034072890910350580c2d0581c440f894543d10031403868000445550105842400301c405082e0281c4015a403101940b4002c8003200700204082c01c1c8100c1c035921021480d08080046c1140c42400006001586881806c40814510391800a011407107151840c070040d4003034608000c4041190040c0c074000c55481c00c480071060b03007420011041304180c00703d5041441d407a1142d0009040300c140104940c3d81800c8801200d417080d0300804000f002c2c0800c03401c1084d901c02c980000034005e13850080c402403c3c1595000d01504040d070381030100c443d24810100d000c05051146c1c90320340394020304000803490180c844001024100801c40782 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 585110692 1250 585109442 585109477
    0x40804051e0904060b01020c1c080a18080114061e093607080307123b040b060306030a0b06041b1101110316030f0b030106060c170f030705 61
    0x201a6240502648075901402d0046909021034000a00380351500740072301d1094010700c1e4080750a182c460071300c018550f0311103c103030383e200081ca100f501c00465a1004104441304604081045d580c190440b00c0051949811020151140300411a601c49907502071260401400e0b0400e181d0700e00003100070380017603101c80f10781131450034500d00c03441c8421a40d40c0c1d601504031f2220080d51140007040810700802c40000910304001580d55040100c903805e02c607010130007011560844c6c1c0358170050305061500780c035108540e52100304100c082d01180c44007a031440c480c0340b811401c07015900700181103a00c81c08004001c1c1890f0300842c0c1d40c4003100700024101e19041941c0b00035880070714040000c1c01c0c040500c191030301e02000880080701c6080d01d000b5806901000d400b44107004000102d540c8405400d641c2e800c2c01f00381e072000c0d07000e00c01c01841001081a455800c03c0301c001540c0d80c00031030804419000d0b6007548003001038041800c07401c0c4203403e050304514200304009001c0d28402c0c000741c24102c030080100230 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 585111942 1250 585110692 585110749
    0x509070f14160308100306060902091c210e0d0b0a0b0109030203190305090301060b0c162312060f070f0e0906011b052401090e0735010209010806060304080405 70
    0x2c1c01c923039143c2c10080e14581e000500741c18034078000c5a41d007140c103064640d00704c0000c1030755122001200e0142e00400d070940c1042d1585201801510329441070080502004503444882c206980d501c0030039940c0e194081c1ca01072810949500c03812920055907005130060282196608000624100c0982c007a41003103001d0050340071980d028010507004000f040700d0740752615209542907003070030400790b075601e4200034a900030081403150490800301c1c20300b82c02c0500d24901780000850481000d429513810035000f00009c10560442e00c40000340502e0007a52001031680c1031000c103540c0d00600341042544180100c0004103150320440394070200200311071544030f0460031a661149040740fa011108402d500b1491001e203401034140c110350040c4030701d140c00e005003d03001c1c10440c0c0314945400f0701c0c08901203030b012403829801d03000b0a00c1881000754085005502c4a02c00c41c9000b504200c064500140d110408a0f8941c64140d09a038040c40e00b14040610f028900001c003d140300c84102044140b268002c4844e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 585113192 1250 585111942 585111953
    0xd030e010c150209010201050c1303061d01150602060703110306060306030102040b0c03031b160b0601090f1202090f06031e07050904060905071a09190509070f141603081003 76
    0x65201c10b548090168440010800280c00e50340c00a01040004500f800380c0d804100342d0b072618a0469410030400a29079484480070340d61410442c00ba402c0313540c00c1c0048001c091801d00c10b12001c0307511a07402d855003600c40020480c29640708601c100e603c0c0340184003207032540c034140d0010364008600400040c82d00e5658100b0030440d4010002d4910b5942021080011401000881c3d001c0c0f007080c41905c0d46007030a50000e030542c025031004080c0100001d1070000714280d01565108025080d0005180030042e65540301c0d0b81c2c01c402e87d01040b0301a24050700490003000940c1a21409490001c010b0300c40e1042043c2602d210b04c0d075048040c0c84a03c140000001c0c8c036220054001e00940c040c403000700d030070061424914942402c50340300340c404080c8184500e0556450106841c174940089445403441980c0003c003114402041d0400c541c044405d800384400031360004020145503665440d094841c20703a082002c5030500491000e0818a54207441a00019110f60b581b150300102500d46803c3c500e450f519403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 585114442 1250 585113192 585113213
    0xd060507050406030c03060e040b04331d1e150f01080c1504050f040603050303130201120b0102030f07051e0d1404050a150c050a0c05010e0603060d030e010c 69
    0x100340114000080901015034580101021030341207080c203002083c035000e0b030300304100300080003c0c0c0114248800714040040b640c0c0000c6100800c0c801070074003078034000030428103004c0703040068081030700d41992020303003000300b041600c40039807400090035485a520214510400c0041c4110070743c1e004607001e55280303a075481d0659028090403840d0b080035604102c0d0451500201140d4207226074485a00d50003905060002c44d01030320b40566004d10401444004140035104641000301240000300030403d61054054400410038000d80e0b502c400d043c0802e041c90201d610b40c0e08080e005807c1048207480d0341f00c80380f0080548912800403100c08021004444d0381c0c46200c400039044540005103016242680074000c0a080c20103110480c3c0740903d050002101c020031403085244a812404181c20218011f1900a2260f90000240c622403d03952400c502a10b900d4012240401e082e0200ca0030b8a0070000c06480c03107000b004d46080c241086035102501c41d8405610305504000b0b4150041000840000d80d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 585115692 1250 585114442 585114451
    0x60702151c1521050f06010f12050715120906050a060b181507021f140c061b09030d0e03010c05210a1e06030605010803090a060c080403020a1509050603240d0605 71
    0x540421f50514000805401156000b40e039034200081703182c804a20701055107801c4030144802c5190301149104151000d000c40c1c84c441d000240b8140c0782c0c0c0f040c400d29070011032069000080c100401919003440384614041c0d4810319120002e01c13401031005003000041c4010340c501123020f41e401e0080030741c001001c103650f40d06080510795241190022042d000441c0d01c0361040c2c1c200001e801c010f1a0040142c1c1c81800034100d00070350410101c000300ea07040000c11240c00b141d019041c1c814110441c6406040c0d040d80c540d005000351300c1c01e000344000320320a006075015400b9090b200c204102c04040e40100c000070280a94001030ba03240180c0d15061091070304031025083d0640042030080c074605010080310816480885030b43c1042000700e06660f2400395040548140d0705080c031568840341003452039801a45c000a402c590351202c0844c0c0c121048101081500180c1e4030f2043d60ba46031070a20069001c00c1c1c0300c0100c03400d103480721900305070a58a800f0400c102d003c1c00c5075408207000d84038001602d80684 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 585116942 1250 585115692 585115723
    0x915020d0e12031c3918060e0f0603060d2a080304210b01030b04320606120d05180910030605090705151b03070605010509011a03010306020306060702151c152105 71
    0x50301c14618242110400e5049c94100c81c1103046142c0200400e402c81986030000f040350940048504070144516940c8000040500703518401c04d071141c080581ea607015018a14401c40c0e20190741c068416500302e040d034603640c011a16102c82e442c55481c1c1e001248050001c81d841c030440000420030f08a0b8454400074005080c01c0001c0100c40c0f10308040c00c1183c040d004c0b0b8000c200302d6101400341d000006040d009160f007840e0507550341e0b41840d1105070340820022010741c0900042c081c00011148905203c0603030307005080802180d1152042669142e0541c46000e410401d103003a03070084108208050508011803020511440c0544400b46086901c0784004440403640c805c018041800e01818007409001c4e5031a8a640f215100c104004050005201c002d05440c2c00000181051b1648010b6419455024101620b02000c0040446454012003043c60b440d00c8494000349034014940503100184060040d4440300c41c0c01c240d0100c0d5000400c42105d020302942c0080140000e1040000305640180d20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 585118192 1250 585116942 585116957
    0x210c0210081503030f040509040206040305240108030313080a020f030d2406170709051c0b160903080313170301060915020d0e12031c391806 62
    0x5540007420b80308000301d2070081d032043c48500d500140d94811601034800461b03644030b443c0d039980b0020318544580d42000b0500d000703038070303560581003400341443c1c6100503181d2a0140a03030320342d4040c0f80e89001c02c860000c1c0c2100e80c10191004128100b00a1013814494816112110b03d001462482c5a001c1c0c41c20441c03195480609500305c2441550f0f0000c0d0146894400a205150400045c034140041038003003110001c1d4004207811030f01520b10300c0010140a00140f400800715150b1002c032040030725060302c96401c0d180000d40c11400000c0724400403503043d1584084181162030341100c58000500690b5615400740400380895240c4040b0b0700c1d024a90101203581c0d40c10003100070f1441c6030f95844a465407003919642000c99402161641c81d1030302038a05003100d450890000342940e40b00c03913060480c07800005001e5134401c0e05000c800100c01c007052070600c0240c03202010184103000c1a8000d0101181c10120402514070b034038101d40c254000d03440d041c8440f406440c0d100300c88090b1a48103070b002c528103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 585119442 1250 585118192 585118201
    0x20d181a0711040903050703050913050906060135092e06231c021c0303182f1005030106020d08010b030a0905160806100f03210c021008 60
    0x100d25a806002c8003558240030745401a9800342c0140a08040141031041c04110103404d6192184003070050300919505001900f0710401064883d00151201e44c0080c00c1b0561310b84170403803841045406c60080c031003002d10100900a140c41d0302c40c1c020300341000e903001da259010328803007640025903030100d81c05010000d1158100029000c90352a503000b1190300c28540e05130341801b5041e40740780c0740750030041e2126207907201164040c40381002c1c083c1001358000785840d0001c4c2441c2d1311400c02d03415a4401d80f41005421122140350702d100081e87c40081038400320b2030140040c4412048015862000e0845804024044d500040c000c4281004410300060001c00100160303075040201c229240e106007412034036035040070300106d41480003d010b00a4103888881d01420810200000064a07074060320f400c0e42e0130b031a281c5a9488903400d44501060f4100d500e000f1400f1141c3c0d03054001100e0f0301c40300d1441d4020140340c0000c805114125450140001140c803600561640c4c0c0d00491402c8055072503070001d290 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 585120692 1250 585119442 585119453
    0x30207090c05041d06030d091a0f07120e040b0901050d08070c18091a0412110705041505030d1403010303031a060d05011e05010c110a171c03090201020d181a07 70
    0x811f510b0100400403102401c108610408110b0720000c007020b6030041d0b450050b01164429446215002072a00a41c0c50145034030940c0b140072072121800456041c014035169204021001100380078585d840803015490301c000401103401043c8d0b452050f540301c031807960303640a50721000c0c08403280d80104540b5101640c0800610764040800f10000d180201310b43c3c100341d1501400e041c011800340c001c1c420b2a1200c2e1040b03000401c000002000010070a215100030500441f20301942482014000d01c108404407082902030b41c1a09419001c0208141c1142c0c46c50301d08401400075004101018040d40b08202c1c907a85400e8001c0c0340354801030307802040079450100308900645508850501a03079034094180b007181c0e4003610101c1d003d60011281566101104c00003641c12980394400501091950000740c500c00c0c01040c0c0f00d01a510381c154107000030000300c2083d02501c1019100a00582010100300c220380c1c041d4682628200701d038062402c4407503c410300d41e20705c682404d00d440b41b40304010904404219 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 585121942 1250 585120692 585120703
    0x1060b0d09260a1101022511030613150212130302070602030316030f0f0219030f0b13020a11031803120a050405010503191a040b030604030207090c05041d0603 70
    0x402071246442c124800b03848000440c02141040d608100d00c48440000d000c1c025016070b064811051004400a0042039a040c0d40c400b9002c4201c860800b002074807141894089400c0e4803070b08008010141101440d0b454100c485458080e0111165081c01641c411803248a007162240744408556000c50b02c0504000e40b03400351940c4030700c0071540200308105c1c00881c07802c001244d00700340d41404600b42c0d001d0300e440f0014041c0e444203414140d2001c0b0b00c1100b061a0049506000d0689403400c1044801e0451003034151000002056000b040f00030200d00b00d110240d0080c00e81c07a0423842c15540c05066001c0c51400c43d400003103100c22100408040300610300d4184142103102c001c080032241b6100d4440000361190049c1e00c02c8031b0510001000140722005460340d00e00e00c048445604000304e2600340c0604526a0b0400308260189141540d00080b0f0b040019586000c0d44d016001042e1803403a00d540000940101001c11040080900c0000380e00c4410041c1400f200c0d00b9684180043e16004092500c0c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 585123192 1250 585121942 585121973
    0xc071a040509090a150e0705030f070315020406020312130213020406090e0f04030f090e0a0218060c0c06180301110a021606170a09080a020d0e180c07020301060b0d09 73
    0x25006040c0031000942c420210200c101c854200c01b1480c4140e0254090404031590700240c2c0502558034916200034000c514107050324413424209580c0da284d542c800c01280282c2c0610005a4401c12840c3d80500000710003d03484489a000036402410640c003041c0000d003624145a60b254001c40c1c1031280725000207025001c1c19440d20321206900d48600f0080c000c0a000d0005000c0c0411102d200c011184103001e2031024000c031005580141c28001c005000075071180280d0812401d00314107000152400400300d039a0140341c1c00042070911804130401c091130340b10244011604480c204501d0164500380070b080312514030303840c501d51103100070100681401110040a039020750005801e20409801000f4046d014142c0102d441c502d6a400952a0003848a1040078050210102d030765500b4075400030302d00380c41032181da44100302c4035100f00a10105407000d1101d00c480302d810030009940c9240e000b001c0c05030203000400224010382c2d120340c022820343c41160a2001507072500e420701d0601c41c0d400031348030341c9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 585124442 1250 585123192 585123211
    0x280e0301020a0c0f110d0503210708180c120307020a120b0f0a3b06090d0c050a060e15060d0c06050d0b0a33050403080c071a040509 58
    0x10b0041001c0001d0000c2c84852004016109250303805090207012500c1d0308000c2c1c0e000d4122030003414941000c40c1d0300d403c41d1400704190a400c0c14801440c0007203495a0b0f0141017292504215511a6845010640051011204a441004840031f115582d01c070710b00d400c1070144d101071075454800b070040c01066566504003008291071080705100040c0c802e1166a880b4441a50100458552820440c0038020710b0f00366150b01c1c0d001201e215400c00c00000302494600341e1640c045048401e1070701461700d0f1202250300d00c6480d0090f03209902090b0040c00ea008195124009030703100d20216548800c116055510024281da0000c0442410401e5001550342c100c04121004400402d00daa540703414043c0c903010341c4041100208002170b0980c5603800103000c1c03c00007001030301c4081e201d1a40e800340c6051b0109000d180c403196042580f0064461041104201c0581da42501d1706040d500c0b507007042c3d408640d0101e258882c0007000a10101101d07207280b4010f040c02c08103540c031481c200400c503407144041c1c40c038140f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 585125692 1250 585124442 585124447
    0x20115030203151504090c060f0206040327030b0c040812180d03110109030e010311040518071119060b01020d02060f130c140a080604030e0d08280e030102 68
    0x250b5400160096007106440a98040703640d004501c94036042c145001c660440d04100c4110208483e486110090354001d54803a041c51200d05400c9031798a40680700500414070040095206003092051802400000e0120059080e620741c0c0301d50710030390111000100d15101040034045403200780546c4000302034184495050039011803104240701002882d181c402d00b0403045c3d130323020140200d0071034010303080782d400800c800711083c00d01030821222405003e0004c3c1c60040741c0a0500401c00c00d88081c3c80002d0010344a045103103100c1c298a24001e0b03d00000e01a2100c800986600100000d10f803103100014580c1168030107140c0380040e10100e284e81c82c1550480c84085a950b43d0001c0c030298452003003011611039807600001544814952403002d07041c070010f04408240e801e4481040003e440f001d41d0b00e1511643d503409480d8403200242c0703008000420542c02e00600c1d180c503250784900c25000d250218517040c03a2038441314601c08001b5485400c00c4200d16480c0c0300704d411204500210105600035031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 585126942 1250 585125692 585125699
    0x406020c060a1d01140d24080604020d0f0b0108070806010501141812070e01180501150e011b030206070306080d050405151207081b19051e03011203020115 68
    0x82c840e41004003d0814000ba901c240115a0b00c6480e9210a00031407000c0c00b5a6000c0d00ba41c0f8002030000c2400d50302101000381d214943c40034013821403104450510010389001e8480341e082244100c2e102905940602005842030080781c0001c0045008101c80401810a80d01e81000242004030581c013050511200301103140d0111401c004850b40740401c108a1980307011281c0009a1030029801c030344416219281d408260f098040c10040d0580301c00c14180000050511041016508240203040c140c6200703070310140c84a4000e1078403c1391103070141401e060054105c02400e42c03180c1209826001070780f00f05c2c1409001030b0035110b0100076100d0034001d000d1180032000c0c06440c5108078031415000c1e410b00100181080c81d0b40302034403a02c803403000488200b418140c10040c4a10f0085e5640b4a0314060a110285074032040700c200c600500f10740700704004104101c0d00940c2c00e0b8010b28190440802d0385845400c0100424000318082c10340e000941d451300d002824000d003101d05203900c18401c0c00301183c092 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 585128192 1250 585126942 585126947
    0x1d0108060c0901090314120d0b0f0609060a210c03050a0e0d08070e01120f0501082401061b0f12090f030804031202210a120c0c110303040506030c0406020c060a 70
    0x144d0549070041d140b04007841e8440c03509407500004081c1040310000100e034140c0318903a2500a142410720440721038255407208000c0086920900702810744c441410495040781c04e0103008843c009180d0140b42c60802c00c0c4045949007503520021440c0000390366481001440700540c4100c1c41070214090040001c80c0d040301d000350440303502624010a10a452103100740c180e02c1003840c07140c00c1c40040d90a10105401041880280c4000e003c0d540b03550051020a10307500080d4038801035840d03900010320030142d18140f07080d21004159a1410240c0c01c0301000c034000f0483d01000f8100c1c051080703011005400b0800001024081e0b03a400000e905078140c4000c00c0418904c5003524103507600922026110501c084050303140c6107001c00c0c8506035086005400030b00c800d038070b006013845035000d07154030410021005424044503a89004080400c183c1c07840f0101142030f60781c454060f2031000d02140e1078280c46400180484d0012907420500d0000001d0a1040d5507052080bc3c800035020b440b00c6081c1151001e01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 585129442 1250 585128192 585128207
    0x307050103020c0102250c060203030906070e010c0b2802040b0d1119170106030608030d0b01030609090606140103020c0a0803040609020604091d0d050f03060a1d0108060c0901 77
    0x540381007540210320a40700020030740c121920355540118a00045803a009161048519104d0598107034248040015015001004a038400d207250f201600159031130034015204c01e0080c40d01c550401144002200001c1c010f00d100034020100d5032058120030316000c1040c0815000740c0c501c000481c1c0180800c200400904e01924201840c8140110350380c106c1c90110303465409100e041802400101010381c0c074894100707e02d03c0002103010f40142d09a0303200d21090b0305071031140c82812034560081014841c00800c943c40100c02038014507000c202c160b03a44030348100350b45581034140d070a0741e51440200031400b044405e56241c11000c1c242581001711030305180c1c0c0c85400315a80507090307840000006041048a83c48200039550040010780c40319100c0c0c20325001844034036041e2102401442100c4505140040c80c4d102d07200c059501e0703500d485004038a1002e03a81000e41401c3d0440300f200c6005c6501c51440d91258500c005072070403205590f141c040490f161101c00341c01c202017448200051020390341e00171107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 585130692 1250 585129442 585129449
    0x204080a0b0c13030b070201051e0103020f01020106031b061b020906090408070602030a1b1404050d060b0a170d050901201f0e01140c030f0711030403060603200307 72
    0x807048166624405030212920490208401071040c0342c901208000882905500801c0c40e54020400d0707694004000034842840c050601c0d0501d95800100014505440140301d031a4041c4000310741143c0c1c2e981c40c0450700c0c4070341440e80107004403034071b0901005500010100e2000d8205034401c01200d4150080381749011f014141c64003410010000406008500c41202e807141e500010440d036038600f03950a5402802588034109800841c000d05543c5130307200d109c02c1c0101c06c090800c42441e113464401004901c1e190002c0c2161580d0710703541c409656a0300c0822090081181903102c50383e607980d074500c003401c1488022030341e014450184038000041c3d03030001c0c4000301e42039000344c4402d03455800c1e80c040d403911200c25075181c94180d614501240e100890f801505007044664024420f45003040305803400740c0021074560300140b805100050203030708410340d0141c01143e5420018011645010344c06d0450340142c0003030f2100c0740c50780001c00800c0689025025070b404000384514000406600081d201d080318031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 585131942 1250 585130692 585130703
    0x1505031608100806070207031e02181905010b03040201111c030207021219020a0501020a1104050402010c0b01031212050c09040b0a090e0a0c050d03021e031902010f050a0204080a 78
    0x50008081070010010b5002a0003144200e03841071900c3d4100030b545003540c1c0411030703c2c55215000804107481c40025411081d50040501c0150802c8450209840000a09804908400d0446480c0301a420301c110b5019058001481c0c1c1e5a01d054000545201d402651052081d441391841951100b030340d01920402030742c5850f0240e51000c0d80d0002828010301c3e51070140007400b8143c00180311102c1c165030480300742c0c42641d081c28026507900041e62074103c4580042c2c03010400201805252600e0b5000c99449841418407100b10740c020340383e0011181c000d8000303e50340600c40c502112800d41000c0c1c1a09a401a4982400700f03141c04000004140240d074115409940c880074400180d42d030703111070180540108013041000202c091040713540e9621643e825a0f842c9003052000c2041d0801039803655105806400804094030002d10700c0c1510000d04010b004e05000621030301000c4600c2a00c5030028440d41c0c0c0c008151004403000c16404c54401404110b5094810041000561008100302d07410a4004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 585133192 1250 585131942 585131957
    0x3200c122a0a0b030903030907060311040b130305060c030a0f0501050f103501050a14060c10140114011e210e060405150112140309030604050715050316 67
    0x781c02040001020340c014010307000011041100a9000001542c4151070070412204480d507a0729058044444140342000100b804200c1442007101d8180101004141301c0124100d0f0b590b40d13250f060030044103070307640d11010b003000090000c1c10b4007900a00072514415001001954501000141d103004082822409001031100890420303010340800303000d140001700c0c0c1c00410800e4208004800607200200c18030200d00000120310740c20016520130a54246100d40e001c003500314010416580c002d0001609188903001c2c0c5240c00d03000c18000d03902012084820303425154103000710301c0e03c9010803600300350402c520300b194000d21a48070b8a280741c9060540c20010b048404460480f094115901d41d0004180d040012500302c03050b0006480307209034010425588114848a50001880003c1c46a1a1003000349131020012501a10036484015210303811245411a428040f80c109182140c0546180e00410703410042c3e18030341038464812003a94039140f45140f50071000d032082001d00c072020b0410481d80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 585134442 1250 585133192 585133273
    0x3011503050c09090c0406110105062803080d0f060819120207030c0e01031407030807151e0b150903100e0703080d05071e08040f03200c12 61
    0x1c00301210f01c4000054070b502a646490128146154018810000001c1c0840500c1210f818107101e104e004e984003c0c071103845c00c60051000340e024001d4031401140003551071000000a1405030003842503500300b000c00304e4100603020b04101140c074141d0184801d90403010703102c202314820b5591a076080ea80050060b1074066008800c80c038102d1940c00c0100010201c58001c903100d00001840d9040340d01c00c0c01480203030200c5c04101c6485445521004001c10000e21850000945440300101c0070001948001818841883d50307091001d81054100c50140d0364680b00703001400d2003030400c084400050344e55440c0c4100c000100b40d139800b20012010728103a0314842d01c0c0c5a0345084c816040107680043d56541c403034a40c1484070004100039240300b400303c0d140724040b15a00c80b00b03a40058030509a82c80781c0f14556110b484078404210340390000c40c100648503164010041004460259075007090004192040d0500144040500c03c000c1c024020b50024491002c00510510603050131181e040c07480c41e41402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 585135692 1250 585134442 585134461
    0x2010c110301020c0f06100b0f0a18061d2205040c05280e0c120603010e1f0513020f010c030c0609030c020123030c0f1c021e0301150305 60
    0x12560039a50715500020b8081c2e081c080014502c111208004107980140d2120084140c0b0019a4491602c502005112120002c500707000600440c0e500d0381841400390785c2450415208411a8000742c0105031400340c41c0c003080c0d0598803c6000d981c2c0550300f00c04040c4400140d441c1401d0090003141752a81c40360f00080402200314032500007040060881c00c1e0010444070070024010510240c0362480d07003100800140600f2100e01c40d4020500c0c100c0062400034844182460342d0002040170340c1540d200d240213082c4813010458501c01801070081400038031150440c0c841580c03030140810041803007040c0c5420260b41e841070b00c0400d002003400d0418000401e803405503000c120804000c2d0146150214007014150440116500c05100740e0300c50440300c2000303240c6d01d210860000c0c1303400c61020900000310314a50f003c000f41520030424074090b0900710103540c8195820260301070140540d40200b04012818540040000b00d100c001d034040341958101014500c04100001b8030303004054480020820041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 585136942 1250 585135692 585135713
    0xe030421050303010e16020102280315030b010609080606030d0c0314041d060102060712180f0503091207030302060403180b031305060a0b1804020a0b1204030219050a02010c 76
    0x40d0301c03078107503900c9694510508004003012181d130403103ca079802c0f10b02c807518410b03c00c031003e5020744030ba05090000304460500719401001106414150742e40b8008039882900e2110708003c40c400c200384c0c4201e41c140f007070040c0720402540c00b042080c1d00c50401e00001d44c0d8081900c1400c0c01841ca0b01c1081c1d2402d6090403644042c10514034070780028006004541c19004601e210080c0340050104c0d49685c40d0f100c01282c0e501002c580900010704807030703c0001c1d1460b60740c2000c403020100c1c010f420540000790300c41c0450322140c8401181c0e550700004e4102000d0800300106002d80c00000081d000300d9145072006911500300800040c1000340ca42d00780e0785014094454280541703841884903848c0e18207003c0303025047c1203813207043c1c0e41c40c8138020000d020048a40074151b03030120060260a200c243e0601005945000030f0022a40102401000300d00303c80014090a02d0036003816040d0001e042a05001e81805543d6036403141c4405550400340100b0400143c4280d0107a082c0b03407441703400c3c855051206406 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 585138192 1250 585136942 585137009
    0x50d0f08070c0506070812100303170903041e080c12071a07060614030c120c01030f0f0212041407060e0108090c150d0b04180209070905031f0f0e0304 66
    0xb00001c5a21000d0120000c087d0031041a0384503850815183c2d02d0420016015510000b4001244c0d1000081d5048540c44a1750700001504101d03070605444003040c96144288a451002502d5030701802c02501030208a40441d411701518030002c1c0c400030042d0f0701e4803907202e0b004003c807164240d01852907001070744040300d81d52604090100550b94942c400103036010640a40c0364401e11465458052529154442c04803002d035440081003400403180054011b00005030204c60003596500502d0381030025400103001d0b001c11590510310910b494508141000c08403000300c06941c1c007180050015541140313285241c9a0242001c949036518403440e20701d0704010620440d0012611360005900e40550005041c441020700c82c10322942c15084240011640c280090403609000e54255a015003002100340d40c02c200300c2e1030718503a26510303000401d00c0c080d03003040050204074107254416011041c0b0300c52103074903400c155002d2113a4400a600903035070303001314010540c010480c0c041401c81c2040d441302c42e0001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 585139442 1250 585138192 585138199
    0x207090f1a060403030f080711120c010506040b06041401020a0f051501170a060e0309130c0e12070504050c0708030c1c0507090501050a050c16030201020f0a0f03052a0a0c050d0f08070c05 82
    0x50724900d0307808000320f2f04498150b07185d560138100422520700e0980960303016800050f100320f080c146440480b2118000d610007440c103501070401c2c6a004030b402014062602e0380a04000c0c02c00306942511401c4500d01641b0103000c00b410b00540e00031134003010865914440e080040400c0c0348c1c02500240d81075105162000c0d9000352544c540b00347d880e4182e002034a110801d0303200c1c0e00800141400307000d80e2004441c010030854116003824002403800c0c2d0300c2580c101c8101416603040105540d11316080380d00a88034103250060120700e444400c195861001807a501c01141441242060030005e0104009402100d040c40030109000c0000b520440627980c3e480303403240031961f03140c030f14184a01681c3c0e441d00040e401801203550512822000041c0b049445a011207441d4421149071000c4541d5080459641d10122413852018003504004400c201d10071140000fa104200603460308020f0343c2202ea22803030141002444200200c2c151030884598290820b006550f01c0403036250085019180303410040c1e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 585140692 1250 585139442 585139453
    0x17070e2a09040903020c03012301030b10050d06050a061403060a0507050c01022709040b07050f12092b022806060e070314060607120207090f1a060403030f080711 71
    0x341640004d1600007106d041d0001c1003901421080c41d40c05400f802c041d5401c0f0840351b03004200107a03c4164642e807002076002081401e54036040081c505403c10030b000c1e200180c4400a000c1e211000e4412070004140c0c14480c401d00401d000040f81d19a000100b10151640d07681001445085c000c2085403010701c40c2600031550f42840201c0003011010340c07142400703405211100407156040035404240210341003e041915a5101d12084038198003600c011082e480042c421701300c1140360045800c1c00380041c4400707803000407041d001034042510b4000c040c4078000000071100284540101c0e403418901c1840301e05101c1e00114036010020060110360050080e490035000050000c20307501d07014000c0039140e0f020700c80a00018040030000f007040e02c0641e84980d003000840002004c1c11150810710702140140c0d07608541d40d000510840f1010400711900f1a11501c6d000e0442070882030340001020304903401341c1420f04607180245100c07a0f1803215000d00610501249030385018002404906903100c0c1180c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 585141942 1250 585140692 585140711
    0x1201110d02040e01120206190c15140915010b0708090306130b070f02070605070524070e122d0616090e090607120e060117070e2a0904 59
    0x10002d40c0070b841503c0e0180c1c202c10000c40c0807082509001c0c41c0a40091486042c890300c0000440b24502015421007841044810400000da921a010202c0d1130b0311580014190203908940703007030041c0100324111f030b40c0128000342e5000b14410038190541e013100c1c0c0b14544902e41880c0c003211078880e15400c0b40c3e15100c0c0d0b20400070400a1540d0340c020340c4e8840c40c8901701c0d40d19045000d591031190300403010096003100c0300a0040d1403080000e4a542d40c080d0782151500b22a90030a4650326a00c003420000fa41114020000819000080c26000740000c0d81e21503c040c03c0310085a8444813107104400600d4605a1424003100030498002ca0031900e050554620b400e10401146036400c6a0b019100403c00003500003035620040c4031018400c084200c05032025070f079120710450301c04034805243c0002e03d0b99214030820600d010030845029106002ca0303001d01c2c0c100000c09510308003140c0d01034440084e4880422600d01e1662003841059811004035005100d90b0031044035542c0103600d84190803900e0304034003c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 585143192 1250 585141942 585141967
    0x801060e010f0501210b0d08070f12020a0b13060b0a060905010e060306010c171b07170102030c0403060b180a0525020a0f0204200301030b010f060c02120111 69
    0x30341202d0b01d244181c02c40598442c010b503561400f0715080b90415441c00000710300a0300d680c210503041940101a10302800c01d581d90050f03582c020040548180703184807414010800341d60566480d41e03450f400203120071b40955480d920110402130a0418501c42220359104008668000003030800c0c000b07203000900f985840c0c1c0144070100b240b25090001c1d4000b11141402e041c03800031a40150810307507a46003401c3c0e890720769070b0707084140d850270500780001040030f0711400403030b40502c1e04082900406003101624042c09000c03a05c182e40e06003e2107034410410300ca440c41c0004100c50490b82d01504c045145000c0c1700004030509400480340c1c1400c650700042051201c21079114911400500c4a100c25011880f50781060610780e42110f800940d1100381c0036008200c0305503454441e035200174404a403581900c81c071202141c2c2e44611900010702c01000500401200c0b0301018054007030360000c04182481c0c0780300240f0003543d201010740540064041001801408c3d0001c0441d242115078250781d076040841d80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 585144442 1250 585143192 585143219
    0xd020307050d061406030c1b121209010606020d0c0507090204320f04020d0b15090111012a02160305030a020106080304031109090712080304020901050906090a020d06080106 76
    0x241640c031031502c40d0100d01a135980c3c07884101100301030946421070b601d40d451205558008000044200c8142407501c0d10800100200f0303007000d0b044a100c1340c841d001d40c50308418102014004494590601400384100c99000070300c0a40c020700c524050b04800c00301d040160070f1601039000040d845000090104824680120b07141c1d4074070352034a5080003191000300244e0905424041e42e540182080c2c585d203411724007500508000c580014000079031034980c00004101d03001001c0100c00c9075002003204042d640e0405111610005000001d0040741c030240b03c4002e24242645051500610281510b0401807080100d43e241c0520a9180c001c440c0d100c0c10304039620f4004c00c950400540c00c2950120320014084182c50403a03601119400152500c04100051a9401400c55445204404002484600304600c8010b21405400d0503036032414180180311301020305802443c045c1428000748600b0380c850081403039028040c00c0b80140c94021b40311404000c4d000a600000a070340c2041c02c081a0081407820 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 585145692 1250 585144442 585144457
    0x33120f0103031b12121103010e0f010503030a090303122405030127120c0b0a06080606010c050a0b09011805100501060e01020a12050f2701020c0d0f080d02030705 71
    0x440f5090141c0302d40c544068407601c418000d20848880041a41a42c001d00340003001d0079460b100412450700d900040c4074203400c01d134441240e00300c2910038482d2106004040e54054202135024600d00000d1000182880045200080c00c0107615141446001c0240e80034020810740d0040003c2c1350464601034a42d60b0004e4044e040c4a5440c10706481140501d480e003601d00002c200e0400c4803c5c4150341c5484001e03014030b4000d103040c045821050070001c1c08255007144140400390340080e5080c20100f4551400d0300c01003105040c00402c01d4480040303100040c68810a5900002d603544039a64401d00c9409448050140030900d88407041010400c5004140e040343d110089004002d00d0780d8036070040707480711060100103016810004203070021031a050002c03009555103081031490066005658503a40c2d004001e81d0164140c06141180581c00e950b481101d010024401040c404d000c40e0005880000c1d130182c01810381c41e50604000421540c1c800b0303100070149001045403286060f90000d40329500c90350 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 585146942 1250 585145692 585145697
    0x1d0c030c0403151d0c0d170d0e030307182106140901020c0c03010b0a050d030302190906021c05180103090b0f0f070507030c1202102933120f010303 65
    0x3d81c8107883c60002441040344407000701b50601c0611142c480c1003643c0400d55000c003840300c0400c41044240e0315405108156028003006550740e20301200001c01d091500202500712441c0341004104071010208044c00001c0f030307154807900f0340f207561510320300820306035920440b481140002c0000000065001e08081e0040e41e0a942c202109034080500301c801190034507505c0305078540d007840241829860401d025102e801c00526041c03294198581c0300c01081200c000155040d20180161079060143d5455000301e480122400040140c002d0841d001c3c02c1e5440111098501c592002684a038215501e8a0341004016106c6e090821840100d0791045469048501c64000441c620521030360803110010b8055441d038204030500d03aa01e074807031b90341c07201454214452134a04a028070854030039020881c052135484640c0c20051940b0b82d1802040220710352150740104602030980038081100320820104981030f0b1900c0d44100014a46406003403000001c00f007418040102c52a00352944a060303034000d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 585148192 1250 585146942 585146981
    0x63011031005030a02060d0b011209080316051602060d06030c0e0610080702031804061d0f07030e10050601181401030b3c04020f040e011d0c030c040315 67
    0x38002e15130344440140d0001d401007820440340742030300580d9200407510340d01450000360b00ea130703541129010780d800e0f0441951701107000800e01062426070180c01d40303050101d0905a040500c10342d89451501c0030080081c0c0103090000312200300314456401a0095a444002000c050340c95086145441c441160300714000c010004038100d105d40140507140c403500035a030042d89402d041c40c000d030200c403000700301d2182c03c19164500810201c1d04052001c0c8002140d14001411b8644008440070001014209509052800d10015010100070588508021500c400410309440c0c50004860b503001c0340d0720000840d0000344010030784940c0c5005004480c1801d0340c00b0f020150140c0c0c02c0003a070510110259100f640305203407a040310402a0b101c80c1c061284d503209403095044000119091740c1c403101c41e6042d00c80d80080c05100070000c0e050018007408210300c0040c0c4c46100441c00c10000140a032082c000100040006054000544201c6014540c4104070030a1741022a07071100181000751444107042440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 585149442 1250 585148192 585148199
    0xf0a050c010b0105070c0b0c10020c01050a060f140108190e0a05061b160f080c0d03063f050d052502090c0c0a060203040b07080703060630110310 64
    0x368103440d082e60b04100c06d20340e1149007944554240d0f125800b01d404a0240b514015010b440510242583c4c03400400042081d140103541d0404071622500101402420100c0034001002d4030000301c3c0f00d114003801c1502380c54885854443c0e00854000c00e044034070b420f01292160392074011030225243c85c45401112010340b200d00d01c5140d04039522085002c2e0600c18010f4040d071000310034000421038003890303c8a45640300c03501d8218440e88420340030a4143d0100b0300e1410200e60500c205001071940094000a20001c02c81101800040d0300da0843c0c00d95482500f403003030b00116040c00c99080c0c0d0120441704501140500030b849600180c0c1b103241e600f000c3c16035001003c0000c6803a513031440d074001d21048495888003048172064025a1044c001e611071546560b0000d94284000c1d8041d50161441c1e000d1890402002820383c00001d00007403c25080c0441000b03030942061000300c40108808001140700c0c042001941600c0720b14401420340e5080008030344511085400950040001030017805136580c0307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 585150692 1250 585149442 585149447
    0x20a0b0c0322142b0804080703030b180108160e15041104090e03040305070b0c030301141527010315090b010315060201060801140609070e01050f0a050c010b01 70
    0x402c45100042d2503406401c0c00364001558562000b0501c5905800340440c400801103280501911030390701d1203c1541141105500050000700828007545040d42640ca4075075100c0c6406d00503031800409064a41000d012203076a02104075616031072011100201c0c0d0303901c00c01d8035501c512030001c1c40c0745540d00381c2e0041107503054840401c0c4144a0450540c404242200601000f0640c0386503100d4010701c240008031301d81c48035005010f40d110401d00150385490650900d9414248250f1001c142e454080050f401a044040305880c1103900001c1007a00c0704040c04003042c464882c501400c9a01503000a418526442c040c02d410705402c1080400b100703007040900150125901e1451200c1c40b174091040400c011159030704500039090b070616003c1002c1d6407550b210200c40500d5000100541d441700014041404244201c071080c0800c102d019109042070320129440c14005072400080011060824040764003541c211075000503401c8215030303a0300d0503001c010916089401c10322100d50829035200069807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 585151942 1250 585150692 585150697
    0x121110080a0b0d0506270d02010204230d0f03020a0209090f010c0e03150a021306050a03050c071a0403110d0c0302060604020a0509090406060801020d09020f0907080115120903020a0b0c 81
    0xd502000900440d280e000112034019620101700058106d100084017006105020301e600c5a49550000340e1074904000c407031040c10103017684410419403001c50380c0800b9651854140151500700c009820921200c0c00c4c124205100c25201941008100d02804604440050075a101c4078400c40200b280e031100060803500b9048025110b03900d6031224101143c21404a44c0a98105800100051411281c0004200303e1507003503000c03801007040850708800c030700d03018007803070742d010103914070b254a8408607580d050210000d545c42ca081600b120400181014020086403495404400c21100c0c0ca00d210200180300d58090b000890041c05500d0110341e90341818000d60b201e642c1c0b191261303030810038000f081c0420a4402042503881c651508400240040c00707100070484040f0704c140128840056005205091442d48641070080d4000d6080103c000da01c2580c0f05d05440d0200f580300309150000101f02d840d5490522180e640b00d01d0310b0745000c1055000507c22038000d00c1481c244503d80e642c850201105e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 585153192 1250 585151942 585151969
    0x20306100311220e0118030504060215160e0118151b0b0f070522050f060a08010506092403010501030b100807050a09080d0f1b020a121110080a0b 64
    0x140030200c0050b83c142d1064000300c4c074007544d42d4000222081d1030359224160420382c110650120300f00040600c00b09a05000787d00040b400e442c0e502080c0d00300300e1a04130742450707020440b00800c00b42001e00301d403980c031404549248401c82102c00755115100c1000c100d1113140c100010380450f4000000140001d000480c41c84855008000c0b0815a513541764550a08040201140b0030030100b00318040b40001c42840c4400300103500800186514200300074013212103c1998003c0c862907040c4002004036038031013031480c1907903c00c1c0da1060b202c900002c080b500c080c582d6102050072010550065002206580245040740c0013640d042c040e400303e4000f4000010000e40080c030005810000154046024000501d4128070ba0700c2c00c100d580741d807118030b44d0800000c0c11004c0700003201301da4900c488540c00710100180c41c002844042409540b5030005645094600ca020049010070f078282d418030078078030300102c0030000160a29105a90004000f8400001210103160f59071411140350481d041c01c072034110300c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 585154442 1250 585153192 585153229
    0xa0606080118020609090406060519140906060d0f0204050612060f09011a090f09011205160f0e1314250308070602090d0c0602070f150507080a020a020306100311 71
    0xc140c80034042c010388a000501c123503644c5885000c001030f00d803200543c0000c580f01100d1201002030a150b1040e80a4a80b00081c41c401c60841c13060005030381d03600d0100c41c461014040e000804051140042e40079000d1640304030350207500490b8440005c0b01c012045031107a00d040b214800c1081c561410004884002e00441c2d001075141040c00301e48804440044c95a854000d0106032070016880018001c044243c110710014081d04244d0f20810004020700200d241b0aa51031024860400580b44412a418412510418107060218241d000317031600174422941c000c405c041c2085181211b4590340c11a800d0014540303a480c10307522a0395880501e98206980c0d00c0352046250140e43e49406000c1e4101c0581c075603100751000c000c8000224150407810003803055401600c100f51401e241000c0740c03462548080080d25070000d010403002c0c0c0c8481110886a800000140c642c042084200d26020115000a402d407085405010410300c0080ca044206ca00c10003031300902039804418825004400c5600c40038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 585155692 1250 585154442 585154447
    0x3120a15030821040c030b070c11100903050a0534060f03140106080108160302090c0c03070602030a02090a080f0c09180102070f12140409020a0504080a06060801180206 74
    0x150042d4001c141c0e81c0c0c03441841c0500c411544400104400341507a04441804d4511000c0041251309000036034060310500f021a017200b0207856402180c02694070041c4902821403c1c103451500814111002d0b5811400701e8810505515106540320320b0344080250401e490725105143d0060044894140c10314200900f04680c5026010b071428402d80c1110801c1c55120305440400d01d400c210032500a2502c0d0303460568551401d0700d01d0703051a64188001c10f1a00751580244090780320001e0241d044100c80d280150348910b825543c82c19070190303d0700142660f0002003400110358054000d0f081d1458121861300000d030b40c89030b446542e0401030450003c6900715403020b035201d140c040461944a0b0642180303c81c041c2203020b18a003280d003c804100d61411030440300d4400c0c40301044650150300f10320306080300843d12800c48040180614402c900300684c001442500c0180710343c040e2401002000c0c22190350281c0ca160a4001d010039000301d03040d541c031b0055459100000d459a40324100d8002d48a180b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 585156942 1250 585155692 585155699
    0x1080a03080615070f02040f09020d23030a030606020d0c150c050c07090501260601231807120b0604050609060f04030311060c030c0f0918070203120a15 67
    0x11a1000002d08090307110f40c41c41c0300310a80251810003440d26a11644400401c03458600c104001c4074041064400ea42c0d150109480058854040e0f11000307c0e0401d20514035022412260f00354034501e005a100c0c5404082024800309070103401c110186c40c02a02510111000c04004844000c011100900500e080c50440004e800c002d1b40104000405441c1136890110800d46151426050781c0c040303441c2d0750740d580041000013908a00c41e03812100040d41c2c8425082e1814029540d9501800380410600e0b4250081100c142c214060000c0c1c0030000c0d1500c5d807802c1d001c042c007103102e00d002c581500215507402d5050080285a22484e081f0794401401241050f007000d0a108607030300192840d40d0840700c104807260284904c44090b10003540301c0e40d00c906410203003910741410080090080b20059000744240018206804252001041d4030703140c46460f4803502000407403a01140d04440400000c04040c403003103950120003803507512200b0b054800240c07103030090002200d03403080c0c0340c01241080050a2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 585158192 1250 585156942 585156947
    0xe0a0b1501050928080c01020c0a08030f280c0210030c0f0509060409050f0402010f02070501020c120319021015030b07080426091021050711030d0c0306050901080a03 73
    0x184128206265040008110020320b10204c010a801001a90788060711a44407076904110b81481e02030295450708106140c084440e42e80c0c01010310346004000d010848844502d41180f5007038001d04811302405085250101c00b070409a0951700980c021504011072a800d80d019004a20310520941e98401180c060070000312240e421400d4400d0748880304000001e80c032100c60140074020000425444610705003032001501c0303904829200415500302c21410801a83c010134400c0c2c0c10340703080e03c01074080345031a502d803400c0d0701c5951013000801c3c2d54a02c2844103d540040d02d5203e80c00314003020007864480c120005040b03051444001c040d9555940010101c0d0b1007010f410360030a21903025101ca08045048418141550400342c03a2081400b280f94051450020381500c403040700341c14036080100c41c43c201c03030818142e0721007460a03881e01d4502084036244910810001080c100b01941c0e19540b41ca100000a004103050f40c40009050650118092402c502414101e0300c0d00e0000701060317078180e5001d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 585159442 1250 585158192 585158209
    0x109020c0c04061508100609270f05100801020418180b010b0a081006021903020c031005160801080a03030c031409030d0e070f05060702040f0e0a0b15010509 69
    0x203800300740601c5100d4909502e55000f40d070054005100e5404a240401d0b000401035a0002d00c4450b0081498104101098211242000366a42284d001d03500b0001d800c58100300545414071079034140e260007170b880c28030b5440c0c0c0c3c0100c8c0aa501c031500d103800f10780e441640500380c0c0964001c02c910300c140712420180f401c4090740107000607426082c0408401030f8948444121103026803159820700c00014088034407039444040290b021503072105400c4028200350009503104d140e82d0103144122041307440b29003458000c2202080004005040352080b00c04000880003801050b10501c864010a000901300c036401080400d0503215468018182141d860b02c0c1100038107294030040c0203040e038582e100d811401c82c0f070140c50b1050301440015aa40c43c0c003c14003404035100307031242d2811a0081d420a0011a04883c02c0354120384d0110345007901c0c1c0456000060013044a02446200da07442d003140300e02280350105154003000e001300c5202c051540c4803101003115007100104c180c0011002c004443c0700c0d1520640 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 585160692 1250 585159442 585159457
    0x40203040c030c080d0f02010c0801060509150d09110f0d1704030f121715120f060a060302030f16150e040507020c1207120311030d060f1517010902 65
    0x70600c0c07982d41c80d100c550506105400030f59464006003843c0c961290030651341c25616809100805c001d10304d60b00d001b440705030103020344000c0010000d410070003503940d012006141c03400c960450b43d41d00c400c06022002001d5840c4101d84c40456400d224401e45800e2690411002014201422440712603855011079110345286503a080010f000c00310100e01407581c85440b041c418003c01214440703010b000f4040082c030740c0815001174540c02c10051400804041c803074141c50150707001400c03a403250006504050007003c041449200e03140030891603a22942003801140e00903020799480c810600303401c030348800d52032180840000043c5010004e980c400c0d07094212200c00e0386814010715082d400040c1c251401a59544016440b10300d07c081c05203415000030361040300399030042400515201c500ca44101c1c006078013400744544051200c01904050044030265212084108940da490341c0c013001030050386010740c4100341e14840d10580420b004040910050351a9408034004e40c1c60410004069804404c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 585161942 1250 585160692 585160703
    0x90a0f060f140415021903020a14030a0212090a0819030329060d020403080703110105010803041412010605130218010908031804111b060f0712050702071502030307080c090f04020304 80
    0x20b4a040c151441c0040005506d4425400f80803100b07440d0411003c1da2000502482e00d5401c01c004011006400141c0e03000c480c1c0004042e00d40320644c0030009044144694000c0320140070382400d102e20084900160050144642c4040011000c034a40401d408207000b46071403800503d0b2541d4203620300d450300107001018426180985400e4580d650f0756002e4204500c1140810088118200000803e003d820b0160060700019401c25107000c4100040032001142c0500600b8001c15601c0c1c40c101c01c5d0030140c040d00000e008401e00b00c5614858400951000604c040326941c50405400d0030362103120444110f6040310000c50802c4002222906036000c51000c0e95405682d8894589450400034042d000481804600e1804982501103031800c24078024140310324030005404012a0310b4010040203000e0110020000b550f44d1002d105a183c602c294012103003040580d42d981007042e5000000354807581e00350f95520204e80300c21a401034030b4090405800e60106049035900609d05140e0f010b9139100d0b0003503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 585163192 1250 585161942 585161953
    0x1503060406090e01020a02101a150d05040f03030b0109030804030303051504060906052b080a020f100603020111070503030307051315080906070905060909070302090a0f060f14041502 80
    0x400503002203c040d07030500d804a9401043c03814405806001d0b16256144e51758041c0501d81e2800c849140740404140a00d11906c807242080f006032171000300359040c4c02e080b00f000300000c2c1000c0c202144100403100080300001d0801b0004000d551080d1040000c60b0307800485203040504544e819406040000e04144010b44201ea0004150307541d40210f00080a40040003d8501e0906041c428820b0300c4850030640316502500e19085240d26240f01c0a031290009281900c8500400c005c9040203800d0045402c0d92143c03049044982c80103a00090440e4800d89900034020310710001d00d40c403080c051003800c0d455081800081c0100e0302a80080180d01c290880e01d12419458210781e0100382c008080c3d150000d1076034010016100001c0100e030f42c01001908107080303440d2504001a000e4070a501314280110640350200704000c0c06601602c0c0041c40c0107104410381c0c1c0d00c5114411003000c0503c10000000e40440c07082d0412400b60700039003241054540500c0c5010309250030300031101800c080201c210701c01e5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 585164442 1250 585163192 585163199
    0x3060e0a050d11010e010b0619021507050d0e012d1518050121020103390801091a1014040b0c16080d0f120f0e0613021503060406 57
    0x92241010300750b120380b18208260f00c0d0441d0b403400c48203c011101080ea144c40d0503000155512415148245000781341c480c03d145c0c020700201d0034030001a0105d00c901500c1404d002907903400c01c02414807034240120410601000c005400e00783c40c0c0c0e029000219640c0d4800040301c170030500110725461503090304042120302c0e07121301e1111285410361182483c04201e65410300035a426000d05801041081c141500741003006c110041d17403494400c0000c0c141340d41e55454030090592001d01041c01918040c240110000203144080303515000c806620000c0c00c46000840e00c50f4541c810000381d082604003500140e034403141403000b02c000c50742d0082e05003d180810718074510115070050000e0320300c0b525580d49484940700c0c42c2e4540b400562901025030b0710100d09100c0300c0c200140c5440d0040251403c4102ca0070140b4040c0c1d0700c1045200c080403400c0c1040e90003030030380d10107800038529054810121000d6540f2a141d80d48681c05c803c1c802940503203851140b9402450101c00b458006c40010800201aa034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 585165692 1250 585164442 585164453
    0x30812090c060d050603060a050606040e0910060603090c0510210b0301090c06140405100f140a050405010806062a0f0a2001082503020c0f1f0204050a03060e0a 70
    0x2101c5204030f00142c4500400c003a600703050200035088484c0002c00d1009040c10000940c0501440c0108440c1800c1d40c80002d20203442003004030003c101c1c0300310070000b00b61a031500401909800b84141d550b002c1e130400c0003540d800c02044005c10311078540e4030a0016100624400301140d103908181c0131240c0c5505182c4803590f401c2c0305225070303581710b40711102042c0c0c9001070241080501444c60400010305100400454030b40d170600500e2440680b40c00da608060500041d507003116200703219100148081404591160020001c0007503c50903240c40c21295280700800815121f03558404480c64007004011009107008403a015041e0500000e903080c9240160407640b92201c1403400f076424510a407134032901758100b441160b1aa030020f2800c0051840d01c0740c001c0030071b0080b4117012034000b0040c03104441420b100754151400c030556141614000003035903042c903983d4a090b81000c1c5100700d013418003d080c11102d20840e002c891000e04410041441c50b240c0b403000b0695039142c50a030340500c101107400901c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 585166942 1250 585165692 585165697
    0x433081e0a050706051c0501030807230a0b0106090f0b04060c08120f010e070e0f0f13020d0501050301060501020f1005100308030406051617060603060303040803031915030812090c06 80
    0x254540c0d0b501e4640606120140e4801b12210000d4001d901d02401800802c804008840c401c541006402d07a4260280f00c0035041c5910314481d9104074084c01c1d180340d08200d140300e105030494100d990b0f50082c0548030044060010342c0c40c461102e806d00c0400080020a0140d0603452400380200d0000d030402e440d4108081d842d030000c46800c000c800301e08005219004c0b000f10501d401064074942400540c5810011501a4540d80d1070f99120348111812624560380d502c100d00300c0c0b0000c0c10000c1d0f44600c00080c02102920702802050302c81c0d42800380100356544001880001d40360601c009000c8005c510781c040000381000303080301100341940c22020000c11138040045000b00d20519000940d071400b41381d80d940b503184034041101000394071180191210728295400d0b4016904640d15956a2100d1001a18622a5500070780c401c0c00041304201d040d142c160808003000801000c14440107205044901010032180002000c84505210703940000b01c04841080d4048020411610005840030000394540c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 585168192 1250 585166942 585166949
    0x6180a0e0c1003290f0d02150c030c06131a0a0b0604032103110703110a02091006020705030d050a0e181f091a1e0433081e0a0507 57
    0x3a03c2d2084842c02101410000a10f501490303420b200c100041d0000502901180c83e401b846120072581200541da140d000b2003443c031018160f000d0352541c1044619450303801601d000d6507180540307400a044403081034010881c4036032002d42c84d10706070781248200f83d1800d40030300001c0d0180d0b62900c80d1400e6442d4100208080c40c01013003110b00b04401911092209400310703200404160401102591501c0c0c0c200584020685c5420480b41050914444c9840e0544206020754888803c0d01482900304a01c40004155a0154203880003507480d0014569a56040304440c8000354003000b0074600d082c07040043c408c2e07500340242804469524a822017681050641d40c00c1007480c2c0c00d045400309e501d9980403038001400d4486c0d09201682c81030200c105511a01103501e40106805a02d48000075070f01c0c484100464001001048000c41444038000070820a05001c00c104c003059148801000b076503031440084500b01030090500341e554a40e441e04003407a59101c030155224240d400070005a00340f00c03d6014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 585169442 1250 585168192 585168197
    0xa0e13020301210203100905030f070c05011218140a060e1c030608030409050705160507061106450d18060f0e0a0305030d0506040506180a0e0c10 64
    0x103a50409001400d946544800312010400c030b0503c1d80c0068502141c2c082000c4050b40e00081c95100e035041080c214810180104d8103801d002032181d0800c1000d24000c010b68000303030f0341e18003090702030405501202c00901d140c0004c522130600390000901d4607203001c424440c22406541880040346c1c0e5540c00d0b0307641005003d00d030390045940c04070749910558180b80280018034080c01014501001951a4801c5006501100e5280c03000908024001d00403074600c0701e0107001c1003000c0030007410074603101e01040c0141400101d01d00014420720500140304c0b0700a0365001c120611403120443c0300507500c1000b04131840c40040640110212140300d00246140340d00c074a014040789815048020042c0c400290245c40700c90301c00310240417035030b4800e600300b00b042c2035420620400048100040c0050010b83e000910610001039400b021003c5904118000d6505440600054030359000300210303000b043d640c0c0c07028640c04100003800c1143c00d421416100d003201c429100051040d20110f1108040c08460342c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 585170692 1250 585169442 585169447
    0xd0507090b01020c010804080d1104030f060b09041a330a090501080d27030317100b070209190c05070b07020106051f1205070e03060f0402030a02060a0e1302 69
    0x21001207401075072100c00003403010b0403091900c8000a04030110140c4017400c600000310314104c0341e5072550301458500c070342010426222071b60f038901030b8401062000101c4141d8109038030040e4604040e5645402168401801140e5010b003188211203500010311078028031034030660301588002056100c0c82403030000500400e022254206012859069502124000d49007070010003140e48086a80c240402179403600703030074030007441c4d5001038508503040d18a504054445000810560441304504684680045040940c1c1d15080c1206d900c9500c0d20610b070f0500d0042041c0b50040c680340710070340d500ca00c401c1041005000f00800b0b1400700c40720446110040340000540605108043d902e03c1d42c00390300c620084c40490708010110345030420149141c0b0b192a500b810407140d06008608080d65051420801c0086151060000b824803560082c1c2038007a0140c04089040785e5003208030240b11f10b802030f005224540103036003400b1050b88082c5680c03082000c002d8200440d40c2d503a104407400ba074030381600980c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 585171942 1250 585170692 585170699
    0x6090509100b030609190305041a04090e1515060c0f0d08090109110105090303311a0f0318030301152709020d0f1e05070206071d0402090d0507 63
    0x10201d8202142140c402d070304c031070204001010005519100302c03c4c01c0301c0060342580c00f0300e4140e456000740c1c2c0000d0410200b40c9032800b5100c845001a000300c0f25459402e00c030044c10400943d848141110492003041c400d50002690b85107080c071401e01414010313041510b4000074082c071034107054030303014802056002822500f04483d031006000e500310300d08000800c40c3c0d4119642e1491440300d10111141841804143d40140f40c0c2c0c00d1007a10a404a603003204402a000c0200a11800000401100c0300d070361142030100e0029807540c2d105094103c800846440d01c9250000702010b500001d007100c55901020a0004056406001860081544c240034241d0300466500107401c010554102c80c0b1a42c6504220001040e000c011400c04c0725850b040040c1d940205030b118a02800c0040410714105d82000080f0402d619959141642942c0c40c0504002070388031840d049854a00a40e80d03140010210801c6007121004003803000d9600000400061400b50f0f81d201050345500801010342d19904080f0080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 585173192 1250 585171942 585171973
    0x40b0702100212072304030b19020307030605090a1401050607020a1d0105040f0b0904121b1b060e01092d09020d061403030f0304050703021903031e2106090509 70
    0x10004007183c07041d10090244801c3c175030185001d030b44006003600e190000403d61700c52640c41150b0b00142c0d0007805542d03a282540e0701401074074440c42124041d0224000242c99220f0910039958a50300d0400801502d9280900f080201d8005d200b069038449810702001407054401a144207106000703040c0f0344519071600013040103c58120359400302c3d107401d1040c4401c49980701ca85059020781d001c032803020402c2442004070341c80b941c002014400c12401c0e49000d400d002000441600105100b440130001a40b114400c4030b1003c03101031740c00d0118444100a200c103040a04920f0000c4012018401400413010104144540c5036404901e81c1640040d07482100b0f05640160707030181034159582001d04d1010f0f004030b6520310070444e40e80321418020011400b0401d051220300010343e001400c01410a880b101262010050b0b4030048022504018161302c10141005214100611585460072480100c42116036111041c040c070300140ca90351a000300710964144103290003034402e0802003000c0310906006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 585174442 1250 585173192 585173207
    0xc060305060102070b09090403030609020a020f2b050c032106120610050f0f0406140a0e040f03080c0c01060303021e03070213021608190801150206040b070210021207 73
    0x105811900444d00070300901140c1c1c0115035040c6000d8600c0c40a998881c241180217000c1608080e0000b4000034803505030a600290140700d91a44405a520f0580c10248080941d005070b40450b130494400040c8264a60081024000484482c020360b441c0880058691344500e4903c0201480c440e080b000780301180c28580c071038007001034041c0000c103141d04180c1c1c1546c08100d90761160380d11806424241c00030584494546c0856030300060024011603803102c161060b41d185524074207000310101000042ca180c401d044c4240559000010040d13148140c0e2000c03540100000c245c10007081d4200070380198124240301c1e0070015402030b80a031161a03174074405030400000c55069007245600c01d00c07071200035a50f03a40010b80d4000404600603919480e10001c0c500c5203140300c50142c413030036006c100c00b41c1350b58424411a0aa80c3d00741d4031420940e0700c407451101442e01d111900301c0140d002000040000b0341100c0b07d05d8004542d40101d03450101d401125605a9000c40390b00803240d82410180210180c000c6403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 585175692 1250 585174442 585174451
    0xc0c0609120f0f0e040e07030501020d02030117030a05040b0d0e1507020601090b0a0909030207180e10020403080a11070f03290115080705090a270e0c0d05190c060305 73
    0x203007072404541c00741c4000e00e08403081340c11358841c6030344652041d541401001b5400c0150b41c810025034444420030001310007900309108a01c051a01c0410388001361070040102d03101d00003203071076950402d41441141c04141e0410031a4048a5543d40d0450042203402c200080562a032301106034142d01d0701c01070080c1010b006901500c9041d0920010015a56440b000541130312070b450fa0019102010341012858141154815001001c680340c2e41030340483c854110240400560084502c0c070301282c54480700b2032041e4440038140d04418000c2e000c52a101e10804031800307036244115010161501c0e9101200e40840d0300c2103540401c0e104d44060f1480d00744884414078407011103900c22943c50312480340b05640c401e40b42c04082010b20000107a0f96806201906e90017400034190300c591588a01c12100c064042d4500418030313400807200b8803004581d40c082c004454500c5406400d8a10f12781c1c0600514030560141200c50340101022510446919125800001d01074081c000c480ea2a02c2c0b00603084650190 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 585176942 1250 585175692 585175697
    0x8071121071a040b0a0206040507061704020d0204090804180605040501050135010303090512011104260f03070b1303090b18030a0302100c030b0a06030c0c0609120f 72
    0x191202640102046500c00c988456520b0070a0900d41041c1e0a124422600b001d051040c0100d11440c04c10350014034103105501c10301c11201801c1d11818150303116450100740c03650310004040081d006041807280351419503c0544007054a1201e0b0703a608000f07412a0304804404d920f00d076050b0302003071a580100001000150b03020015941880b000901d21304819040110701100c0d6074215030f12900460308206000d202442095144d41c491038000c2911000d84650752055030b6241801170125810f120307000c4503103016900b9a02c0e2034a44007000804088042190f8000c15200303035054406c850a11440c0046081000038666421462401e00c0c541d85000d005a1103d0004400100c0041d030801014400e0b1407209c242c041d120b0103800340c04010548840089500750041034602c004040c0c0000f0012000280e5090500508400704011400c0325420400241d0003034071807408000c100d02a070b100c161155401e180448008602e9107a01c81a619584804c44041d07140d2640710050035441114294075030080e1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 585178192 1250 585176942 585176989
    0x712180206030a090c0e0c0909011e171f02070c06050a021f110a030e120a1b050304120503120117030702010f050405040c020f010b060f070305090a03080711 69
    0x260082040703408014800049260b440d00070310f00744504992014020301c1c0c600310868141c0390200030040290400407646014600714400465510b154034040349034a03d5110006040b1880d000380c00f0300b0300c4080c07030b030103081402091a61310424121029500c1107910b8030602503500c681d14900402c0442c029406142001014800c00314456404500f0650010a0311000c6224020402034000101225a040c1400420000d0070b2208284c164100070034819441003614200d580b88000b26007684204041c61001030858165441c15803940c0881040c3d4a004504a0b410301e0f4682500c9034801300214004d0705c2562002c0f03030200100d5401207009014100814801c803142c0040000a83e44e4090102c0003411b000070091200c40c1d1611a00c107450007001d0040082c8a200740254029450f107404030301c003403401e500b804008011030900340f00725a000c106000d000c5186c4003042c3c60850700341e0042a44242d201200000020104003840054070a1a00990708841003000403c07c205003110f42c030900800d8060718 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 585179442 1250 585178192 585178241
    0x20a02010206130812040516090501060f180b07200102030901050315030111030c12010b13030b0702012901080f0c030c0c12040602011b050415030b0f090712 69
    0x106155410150501c2c4214184034a403800700e0f000d02407862208601c1740004100803d026000814105146072661000301050725001e80030300b640c40901a00020480702c0c0c00002109204c2c24400410300d08406421183c651514140c414a134850a8280c2c0c80301e1f0044c6816006280600c0394581440c002d0000318030300f2559a00203441c03400010501c50b05061896209440b45d10203400241c5201c826490b580d0f40c0b0701d0428600200c541109499903045142c0c00c0010070400405800c442c11103e030f0002c0b810f5090b146a98114800c00010603140842d525042c645040e40b00d4010490310862401001e05000080b020004202c64801400c292540c4d10324004d02c010b103141d4808894011103504525035481501a506c80d207490404c0c07680d40d0101c68000f0300020b00503419400034101c0f00881d005558001c1180c24202d0300f5004900441d4044100310031400c0d460790082d400080ca4550244c84c54115004200019210f1281102d48602150200d9212011008030f80700d088543e400c2420f201da04500d8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 585180692 1250 585179442 585179447
    0x10b03160e0a0306020f07020a060914061206061b0610060e0f010c030e010207031502070203061e0a09030905030f0d02060a0c020601030b070c1401092f1005040f12050d020a0201 78
    0x11544800381c04d0720750000310704900a02510898120540240103103000540d140c0c001801d5000c18450b444041810712140101c41c0742c44021112a1801000e680015440c0d480400c40076034042c890a0090392030303440c00800d41c90810b00402d48907150108000c4140c3e894900080d1102040395140780c4034003280e04890089070303003101c66030b00045d4142c0b501001c645040f1005070700e00051f0f5003018040b40002000a00d0040894004158803803003a030a48a881e00c0e845204032804d0131141c10001c884021303c00081c1014440d42c07040301950300a01e411a000c5980758003080c01e14404090184450308049601c680058041010a0700000b61600c100f203c00c0e01090000e44400c0180001040c010040c0c3c003050900c2e12944000c2c0710b80b5044007021840e2425122124024917a000049441d03150940b171034544c104817180c000984900c91801c2369100078442040000740c041c03540c0300505018080c40041041c1c80d50014078009854a0140446144014101185001c0c01c2d068103100710750000a91000503603 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 585181942 1250 585180692 585180709
    0x30510081e01020903070807090e0105060a03080c0709141b160605062808010b0f13020901020a080301151806050901053402130603050303061207030b010b03160e 71
    0x90022150526074461000380700c0c0a0b1040d02c2020f07a05114148000c50403a2012420404840245030200100c100c8400c403542a02e5040b10401c0d40f04403041810004580500c0c002c0c214045000c0a4604168441040000321418003072281072071030401040103400e443d07441f00e182d0403180850405040248820041450720010034008201076251408658561512080d110071420301700280f003441f004070192f45c0a8840e851040c103099600380002607925040c002c060080c5044060140b810920003508424080d620410807a41103101d8402c01b580458003600140d400303000701005402c822000c0050040c10344561000c41124258400820000c26400008031550f400013801d1140d1588210f45103140428500c030702c09461820040703140c8420004101441e0403262080b2099082004504880b0782201c0c50743c040180154400c1000c00e195191942c1035010481c00d190446d0200e588070350b50b200003c00c0070791140c1000e02c2d012050000c10034045081610180d003d2400d0704801002c500060520f0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 585183192 1250 585181942 585181963
    0x40e060103200a030203030304050105100e0408090103090f2f0f0f0405070c06050a0609050c0a0905190513050703050c03160f0309062a0201060e2e060c020103051008 73
    0x450100420b11081d032a051400c01c0216001000e41c0e8aa140ca030401a000c1c00d0103d5401d490f0105061000c0340c0c50200f640c4150003160400503090600142e80015401001030b80c0b0140d40d4125a030101d4800900c0744920b08190312980388110504408000c40c488c03800e070400078058401c01032a10450b00720b40710345c480d17036203280c0d002c8801050030744414105030b410030311101c000382001c4c4c1442e0410040120720703001101200c07580001089039a6440f07028422500660000000007107000804000382d113003c140300b001919094840c0811180e484000820814031342e0b131446040f549440c200070300182c040c03080a43c00080344906a00d1480c01161038040d072a013000302d4030b050107200e80300c00205c00d1287e072201c2c180d240e00031010400400c96446002008021300300e2828610300801f2000505032042c0914011500c2c209442000f68480c0202c015080c1d030740f1082d9000c0100e1035204040c00c0c1c1c000c45034010082c107080d01c038940c004015000040c1540c3c8010b10020101c80300210420803803c0004003850300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 585184442 1250 585183192 585183233
    0xf080604091707210f020d0c03020d140912011a0a030506040303020c030f210a0e0d030906090203010504030c0b150a0b07030903060e0c030609210a0c0c14040e060103 73
    0x243c61142c40d10982001c2c9640310415841200101424440d420480d400c03a16880780d02140c12000c2810030031602c0710300240000b80141c118602040e01c030380c021800101c01003981000716003007142c190085541e841110b84110400ea4450341040c10307151181803849003010081e11440f509504584915981e00c2d00644010b040590000300154009014026510780c1d5900003040341d40c2d103000602024003070324803a00c19503001e00e000000c07514500c00f0384524401841c14001500d00541c580b9010b80c02804c1400f01560120b460b41e03800c00c0103a5003032080ca0711841c484d4072861382000107824583c3e50900014030b804483c10b0104031410036a640d8501d410102c90f12030200c0e643d205080e00d412211a1b19a40c0007c1c02a41041140c82c0c006801261124250310103500301d4406a0380c44d0310050340e030300428003401649260781c0312100092a807000240b030002040d04014071a050243c1c0d9441d81c1c8403031540f088000a6041c0d87e40340340b918081c0540c651040c4bd45000348100d50458071003641c2683d406807201135 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 585185692 1250 585184442 585184447
    0x915060d02070b01030f03200d0c03050403020a0609061d010e040b01170106110c01030510120c080f03030601090b070201022d012301080d0e19090c0f0806040917 71
    0x440c2220760100d4080940c4100c44103650750b900d1510b0312240302c0801d011000300308007450114290300541c0b034900320550303a00000c04c010100503200380d5038042ca245049e01000810080440541c940c60740910003030185a403074082c080c2c0740403402401c004910002981c0b070401c441c1d1100e1542c0e0f0001255035410001c03200007400d6801900141e81c052000f18510200300303a400000910b00d03030804403508460f44c0c2ca005031144513520b10011001c132070003210340c0105a55022018801d4031300003a00e40403c140302c1c0500c540950b450300401c40c0340c1820700100c03000c141c0c0008100802c65038404115030084c042004818240f018540c0082d4690b43c1e41c82501d600d5456100038621a03030101082c61243c000390f80000c0003210500c0c0381d9441c00500361141c0b444008610000090180d500007440040c0301601d541d4410990b0700903080200c0c03911800c4008a40c4034040f400415070464521400b051024291242d00348400c160001410303d03e801810f0911440c40d0541e9100840c440b400003a0300401c51600156 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 585186942 1250 585185692 585185707
    0x4d010f020a030203070809120a06140703020906070b1e01080c01090b070503120901230604060b03040209071407060e1e1b06090a0b030c04030b160f0809011d01090c05091506 76
    0x4400c90180c441d50308e440c1c0b0414070024240240b035400042603d010f2480e0310041d598000054007603118021803d03822580420820000ca0f0200c2c520b6074005c0c03030485490050078142c422220000c0c1081e0803880c0c0c9074020800d03c4002c1d60f00a41e2010040090f1074406041c1821610303041e850780690303004014024261400600d8194003903000d002d03612a100041b0707008001086c1c0c5462400b00407140c0d180220318005021903001103840649105640c018003a449503518500c0c1281d0064828034003414603881440b5410010300c19003d81820341d503014000300600b5a000c020313102280b860b2024552150009859440034022803c1480c1c03889006a4100d0340d240e100c030340032030501c0440b58400300a502d0f0100074040301c8041000104105c0303000362407800300780d00e481202030a4554104c007924045040b02d45007801c01406880c00652150200000160036400c800e0164180920b400d68018241d5680301d0010400c019a02c644020b4501982d41610314a40380c0c6005e05c080100400c0c15115080100b600d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 585188192 1250 585186942 585186949
    0x1509040312180203011e0506060403080a050f09090106080f060d05063904060f090506031801020d141815010509180f0318010503044d010f020a030203070809 69
    0xa45125400b5008204204070850300009041d24101211b00e128204004a00949044404d490580740c2260303007985071220282c01034456a10034206a80e9035441400807080c0d130341d01d01140c18002e001c1c0d61910302e401c0ca000350011011180040c2030903c14018070380340d00e010a100160b820f034071403200c44c070354010030201a424654609400074080d50002c20080e241030000780343c0c0040d02c125040c03902e400788103050700901920715240c580a8150048014000140c02c6903d41e0030020a20f1081c100061415034103445050940c0c2c1040034280d184c0f00e01e2001e01142d516558504100080c0203006003000807999100915403500612a40d0b109184010204075a007403441004000004040700319501050308440701070b126040070310050402159007403240400d5004504591085070701120b020111444004040c510140d071503480041101030382d040301c00c019407c02c030007803008500818040d0f8240d031a00004150b507259940d141c0031900720f0314100000a800106841c3c48903406407070319031269800ca012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 585189442 1250 585188192 585188231
    0x30207150b011b0501151a0f13030204020a184109040507051503060319060f091a07020106050d0b09010b0a03030503070e0303090a0e0c0f030c031509040312 69
    0x214030f40702c80c4007003106041040540c80740405002541c4007001240e5030364041d2486203489801d00010380e0007085032001c02500c290080181140358003509280589940100e000c90300020b5400c0c020031000c4880100c030a00c3c01c8600c40007050719506400b201c000c5012500042510b034408a80310300c030280341e000c3d9840b50090385421407181c09071003000c8900c0e10307050640d61001907100f5940503034030101072483c4516104d02142d101e0328002d801401c4d40340b090b081c45d0b071414400c80416141c081e40d030301091110f18414091b0038107aa0150503051540c030300d0041d0844032000c0162445056a00d002c004000c0b035219200313114035180d040340c11487e0980d65288a00d01620002e0300d007076803105134a0000310806400401441c01a4450b54803000036603103000506a41c0e2040ea000a6480690a0810054208014482580480d8640b405810300c4004006040305400944d0b80c181c1c3c00d4404000c000c110401a801a006540200c0e1007040e0340c189510702030054840390f1111750910b030310707002000059000c0603003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 585190692 1250 585189442 585189467
    0x15050703200a120f031802060d200c0c030609070e0c070c0b0c0c030a1106070302070b0c032104081911062401020f07090c120f0906050601030207150b01 67
    0x540e88110000e107001e03060320708260b150343c000c509096248402284244034144070040d40e1500d01100c03084680801036a43c0020f215040840d0f1140c0e01e08038206950110910a40f21090801d038454980d0440f0605000c0b00240300760003544664100044200c00282440848409070381e078003150f8a5110b035006841c40789001c090000c14180b080020703400d5420700200042c1542a080c0c411103900181095140d0303a0310000a0701c1d0a40c2501501603d261250040444a1182c01194141d03640c400c1140072541103100344000075040840c900001040354400c00d80501c6c5494070b14000c0b4503142e034600000d4000c0300e0600a5000c201c8900040440c0140703c080d113500c501e1402c0740e0503403401c9051080c0d184480264914414200c1052503d95400081c100b282c03c074801014200040c01c060081c40184010204a000c0003a402149030f0318801700d10540c05c00d10401040890044140c2c00c0a00503600060070540c10180304103c080089848219140062222584080303420051100106c0d01c000c022078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 585191942 1250 585190692 585190757
    0xc1b030f0601030302100f0506010e09070c0f08071202060106050a0c03260610050702030c040906141f150f2708030405030f0109031b17030106170115050703 69
    0x4800d00d030700000c0c1440d103031b20040000d1158010320407520090f03030020344215000c02c0c0402c034629100c0c50300c0042e1643c083c607540b919640c44049034480c502c00c016503840c01e55904100058000c00e102002030320805035041c0f8001440c5c254504803009029202d580590300800151003800c0c0300309445170507010211181c0d092b44000c441900c032110744413102c1c250307241c921554201841c12130450080302981d11403074008018000210b0f00c40d0501020305010801200c1d0241e40d010b1110351080d6880b0441c0c02070039042c1c00010400e00342489040f0b80400d5803c61200443d489240e070740c1c610b902c09100551032450b460040c00c0410110f03100c0c3c40c10000034070030301800c01c41c511003c641c5503000800750048880c201c0407145814001002c160884003035200c0980042d102c2c9000190110000d2130340c007a0144101900c2e010100554000d902035002a0072281c002003034101b240d03031200d94000071580584004450b025803443c5044010708140714410004083c0482003040381c135800b044101c0b032542070000c1d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 585193192 1250 585191942 585191953
    0xd1803080a020d03060603063203030f070c0e0f0c0d15060c2108221a07031a0a090f02040302030a0c0503070603020412031d041a0f060c1b030f 63
    0x200003a46648424a00d04006880c02030000707070180c81303802008116851050020540c90762000e00d160164a503000b4120f00740c038589c1c600d82c0c80f910100010301c40b401d80030300d94540b030b120750f1315142c00316040030b03400209080f10304000c0c0038607281c041440640085044143d603130b40d1402e00196001030410032a50b0301c0600720b880800242c40c1e820622402005100d807218510b41c0c0c501c00c0101414009070b80c04680011017010000360081c184404041e58900000d1a40c91a0600fa039141999031141034900c21400c0c1d0040140040b4507018060f818070040c4030100f65a003040e440e404900d00c1002c0348035103800f01d074440c007580225100310b5040300e0246030003500355500381e080c0d4180a03419124600c1032501a00c16094000341c000e2080c4282c070103941515140760060340b69500c080f00d01c0c103c2c040130100d4040c040d240750f081e2503071b5034401d541643c1d51009000c21504d0700c0404100d203142c904581c645c003880081001c0e41601c1808a1621a00a01c04060002c0f460794180800d2919450b90000d01051040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 585194442 1250 585193192 585193207
    0x16050703030531052206260f06041209032907080702120f09092406070c0905070c050303010303091a0c030d0c0e041811030706020d180308 61
    0x220040c01c00142e85112420b0f01c10b0310303840c2c05842c08002040410310f010440000d20040c0381030700424441c071036100044c452203040d50868100b05c40080c0d1140c085075040440902c00f04040184808044130994042e00d040b090314003041d9114079004200801e04210103841d402024019003c0740040c6070000400c0e648030202100c50804240d55900c41803590503810f0000d40028481ca450703a2242c0e0702035016040281880703500401d550890382c400780d246001031100000d69240c2c4980303641f044001072100011a813404e100c103100900c8203040240204410030600c000310700854a20800c0321060800001c096031750200c1100c100d825294002c24900000000100f41030703126100304195034004110011200ca10040c61461b44188080c05c60a900306202c9030108801d030342e210000c014814148028103402c1341c1c00141c1154401e9688900b00402844001c3c01e200c02410544d0700c801041e4010b016250a101010f5921424480d40380e08100134401c0e00d076086800c0c0c5147d10000c1d60b10441a40e21020f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 585195692 1250 585194442 585194447
    0x1141303080c010612030903150b131409010c050421060c02150906100b03060102070302150403030e06090a0302091e070e0102060703060e0105010f020114090303011d09030f1605070303 81
    0x4401d81e140c41075800d0030000306103402c090b200c00503500c0c0d050b240c0c41f0b5000c0c915540e4140001201c0070013030449903110303103029090711015180300d01907072000e42c0025441041160721504000103403c0c402541c0c9070400300d14000703422604490580301b2000740500c0c00d03c1001032180091500600007031046007401001c2c3c20540c1c002a0010400450610440059039401c0d00c40e6500c000c01c84107403034401c4a0010030009954480000c40d000f49041c41a41c042c2a12500442d44100d20b0080d03111644900140800505501001e13a0b001c48a04840d298504000800014109440b90102a209900c0d00c4049400c0c6003910786140d214400e0143c0c0581c0034948414041d0000c441d0020b11805401203800144001c4c0c42841044240c8400941c0c1e135560740d0034180111000023011410700e00f559680d25054000c025a914050311844086009580c0e03581408074a450486160034000c071f0002c084401c2c4018800080240c4014881c0d2594150703e4203040301100100c41c0721820043c00c64010580c0200c00d16a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 585196942 1250 585195692 585195697
    0x7120b031213060e03030712110d05030901060e010b3f0a060608100608100504240f18090309030812071e0e0d02062503030609020304050a020114130308 67
    0x5407800d4400e2103280d0307203c0c2c0640d800760501000c107506420411248000807068070780c40071034191502d05020410101c49089291141100b600e6010910100c104261580c00f400342c5001390010030840724040d4500580c0d44014002c4a00c1d10034046840c08465150300e880400c10308282002c00301c0c151010b01d0640781004240406d84140d0740e1942403801c0402c40034002c442490040c0c0513500f006e100c1914050b8102c4881c00c002c1e05031500760411201c00201030341d0f1800341c88642c03295078800201d80e103038000740b030b2100c0740c1941d02c20300d83d0103515102004035802291607072440ba44640c034003043c01c8200d40750841f00c400e200e4100034a0b1800c0413401c0b0301050101d919217441010580c5510b0030600c9150608015014101198400114244004a1541040641c01000707900c050100d504160180c540c1d4038400b000d401401d04c0b080e010660305000d155041c00381c2d100502401c0011859420291166600c42d004044080d0500032103003c0c0038440c1141e5400c80d6042038602e5602042561280781505095 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 585198192 1250 585196942 585196957
    0x506210112030e090402090414100906020c01051b031909150b04050709080c01050d0b03030a020f0d030203010e060415080f24010605040e07180f15020607020607120b0312 75
    0x10303c900b40c906034a400c043c0ca42c41d0140b6001050fa054540e115501c440100c8030360083d0586600901d103003403541c0d130b0769070099480b51481120b0241e140c90032601b580742100c000030712812240e0609284005074030b40701000c40380c002c0000803100541340002003a44026000c40107006020444d966207278007001e000c641c00322251450844081c13190b6100c4200c126155107250003140e01c1d0f900010706084296000b04014021554070320004104d078031151001034115085a40d001c405030300041d032442c880c801c0c10b1101e1002c1c1d805c541003c5045504144965160140c000c0525028980d640905082c03010458016002070414404403074018841030030458845158000c1814aa00003c12050400e00c6c0700401c5410b1398400e42d1103a041c14541001498411400351031141801b0a42e09920007545100982c0d0014160728494030b00590300c3c284001c2d035401c146e414444110740080d414804066030128a96400c455140b03004140d0f40b484001c198018924110f90941c94840c01400340b6461411030f0241045 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 585199442 1250 585198192 585198197
    0xb0f010602060a090215070201091d090d020a030c1e02030a060b2b0803040f060c05090f040c1d0112060905011412060105150909040f0209060f0901050621011203 71
    0x1e60f201c1e403074020240e41070b0b040020b520059a100810710140064080c00e9198014545040c58640d1070706c0780040e00b2451f180c900f840c020788a041042c484000c00050300400b0a91004000d18511510028480428007800602d0079445c90341d00014407000d811601e1f00c4a40003002c3d0b4803020420329140c8020843c2e070101c14011400e20640010003000e03018001d401500e100015001085a96075190b007541c0f00030002c031140090214120701140b0b44e441150f001c140755031110390740c0e04913441c1085050440101010700c500e04064000304210780c02a201d0440d0201141080d03400d207081c07401030742d510106032064280c4070701d0a01e000407070301074076003125048643c0100301050340c03045442813007407160003481c004e0a40d61255004020034104100f03030900060300d03070030321a040000c50300000354400300a48060b5400c90020107014258038000702c2242d0052400c17a602403404d8640c101040c034000c014864136100302804201040007401d0f40b10300e48100c044144a200b1550786806401c603844440c0c0105400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 585200692 1250 585199442 585199453
    0xc0903110f0303120702030f0c0601050a0b07050c040905100222050301060e070806060717091912031404090501170f011e0221010603090212010203160810030b0f010602 74
    0x16818001074481c400714015000c0c1d440c010990910001418001c5c0820b000c521041000d40b40046250f0068016035541d0006008107515004c10003030040159044002e0b500310400030f690000e007000a0190200e00180c4001c0b40c95582030400500341084541101d00702400001c1d500c10400000104140f004007035003080e10526200c0d810305080310171a010f0015400d001d0400708400d0380c0110305007540154010314891624503141c1d6444842004625500500346c00424810303214038002540c651080300ca1458004203514052002102242095020b0701303016407a52940165486441100d001d001c203500c0c244040d50f594008c10a007910204000c14483c0103090380607401c11010f001e07007041049040c80080341c02c2950201e240003988a103400740180a0301c180446551000b01b02d00500a25442c2c034002900902c074018000c51074030640381158141d10400800c0b954a04400010200030340d07528242c420b5650b101c001000b00c080c190005030075080b0030000c0100c01344124800e01d0598210343e0940341c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 585201942 1250 585200692 585200723
    0xe0102120a020f041a0408150919050d12020405030706210e0a0b062e0f0c0210051606050f18010e070e0703111309061509120804090c0903 61
    0x1002ca000d1500310040c68401040308014020701110048640102d0032a01481c240d51038442c47c0c074040e065104070303100f860003508210b402c45081c401403812144081e62041c00c071005655440e02d801020003401d00303102c0380350089205a9031540c113550140c540581100d10003070312000d000d0801c654059200c410040c002e40513a07118a11801074282c80d52202d80201021a629510494180001403005801203c0c00d800389145d00e9110b5440d82d80d09640041004409101800c020903950000e0002c1040c08281e000c400016120305442c41c40307504181c501162515090b40b40d0003841c3d4003012024080c14200030610464894500340c89000301c81c0b41000b10280014296010300740c030108400481c50ba082071743d04000100c0720080c4141e20528034980058100c00c1e4503800c15240c0c000c580c2088081e8030004d018403600c0c0c0c961180c1c602500d6640c401c04001c0300612401420101180110b002c1540c0b00c0e511078080140b200e040e1005002019001c1c06113400e0078900130000f96040c4000e0b03c1c110340005018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 585203192 1250 585201942 585201961
    0xf1a0705070809010e0103110315030c06040308040e040602161118060306060d02120f10050f0c3403030e01110408030d150806100e100506070212100e010212 69
    0x25031000380d202c1041400c001008005480343c02c1c018400b40e0505883d0702ca5849006d038403c00643c0f052a0441035002d0410790141414540a4078401c01c9000c0ca40422091010a113508180d40444034444540d50040da19032420300040d005a000e4841001c07440510344080100c007038440c011106040d2401c404c0702517041c41c88425800180e1750340c5c2e015000000480c0a81c18911420600c0c036002a000500b1782c0c1018180c0340c41c112800003a600990042500c0321400702032405504c0d0883c0304040042418208004091040c1c4569121001103000d1900e41008003540408046901185603840d50030019560038040d0181c00503a111000b99441c01d10340c400408416800c1d10240c40c1030700011810845000d4030380008052072050002100c0380b01c0c8000031900b80410480b841106400100381c900c5142c00803042d2044400f4110b50340899445034140195142c1000340c03101940c04403000004815800c116500380809042c1822009081c540390544040054000b070054409010341c4003d580d4401c2c2d0341 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 585204442 1250 585203192 585203197
    0x1d030f0406121a01051602031605030c0f01142b0504031e020607030e0f0105071107060f0f1d040911011215030f170d060f05061905030a090f1a0705 65
    0x10810414943e41800d0f030a500c40c0003c0d00d0640b54a03c80e00384901115000a41303400e0540e60b0241814441c1c180501c091704052041e4107800382c064034031003502d285950020348419426007911540810219a68000c018901d0032012460a800008503190450303034408030240008941c2034002c210035114904243d042980300b1800195a40d01800c800d8542a230224040c21104140d040144120b41c0c0c00c005a010a100741401003103a074172289048130f0210301e2141840350f65801f05040c0496007008440954112041c0d844d40f00151525070042000e0303644150102c1a8500b00d5600316151100311000c1020350303004155288800d03206c0220f82200b400d5010240d880e94000c0c2d00f464260054104001040300c1d40716009180321740110b4a80b000c981404584030303000f000c190310b003868448004008103445607552001400c0280d6096181401d092800210405010307031500400c0000000507000941c643e004910381c0e076000d18015444449030900031160f154210440511494040c041840d09004908 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 585205692 1250 585204442 585204461
    0x20a1103031e0c0a0b0108010504030e0d08070303050a1b0c03021e0307021203160c1d01060203030402120705060a050d05010b03060114030402030703060501150207090c020a061d030f040612 83
    0x1105002d40d0003806060415003081c0b0600d0742d20703c1100c1498000510108805001c0c010040c00014035190a0400031b10200940041500884105d1141c9001c03540e000e08884c030308e03605030034081600d4450442401c010003031241011940700c41301030703c96019a803041d80100128026421107160070b102003484002c0d000c410342d000e07e0f140e00c204800c1c001814050081d810307801486082d0790410340c0d0709103480000c0c861250b003200c1d10711074448244506044040f80c0011900d0203801034142d0740c11300c00007a54a00c405040039202c2c40f29032030f071089a08405c01c00e140107404064821611054440750180c040d401810045c0100d60401002090f00d120060540e44a00c078140c0d92021825112a1403001943c0040e000744c2e010f00801002001244050062500074500700403100340200d05d8201c020b04049a50700402035690a082c0c250f9006540000c0c940038064125000283c51001c1c2c6030607a40c0204003900c2c0c08001d01000c00c030810b000740c10a01070400c541c890344130b0800d5140802c0342034003181c24120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 585206942 1250 585205692 585205717
    0x60c030b031e1f11160303060b09130e0c100c020406050f0a030209150a1d1003110f0103021b0a05160b07080a050d0f0b10030e0613051606020a110303 66
    0x140f0254218420703024150316861107040000e0302a07040b00d43c010859100302e000d00032030440350380480101a0700d88220070081501415050070300808100003105854400c43c40c0520350b0f00c0c0c6140c2c1240c4102031003518000d00c0000c202c80c4030112032580141090040c0642a13220f14582000000c403410030001110754a0001000311068504540c2041a0008040c00c82c0622842a1400394940d45a009503074001d0000c8070381c0e01000303129078403041121840c01064402d2620b040102000001d030071404903001c00700c04a40b034450320b05039840101c00900441c012000054a1100c1c020216840410040007041c000d0042e42d9080312504d24140d4032f910340e4451840944d00400480003c14010303805041110700781d14005191105013080c0b40192403440007000c065039035405600303034685040804400c04440328201132040c4107407114110b4407208000d14010041c0e4540e0f03840c00c01c010090103031800c001c0140100300805604c60074003e68924420710103c980d02d13038074010010280b6000054440154218 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 585208192 1250 585206942 585206953
    0xc030b0a0b0f07030c0606060c022e031112040c050f060a021f09050f010606030617070306110f040815070e03060a090201021c0e030d090e0103030507020a03060c030b031e 75
    0x60ba003880c90f5001d14801d800708080c40758003600044070350190500602c0240e84284040e000c40c0100a01003260444910032416245d8140304c0a01222201019076491410001203941483c440b03203440e445507468101345003124008200400c603081031501c0640c1c00076104402d41044000c1404400c2c030030300c0980e80c056402880c0c035000c40b0070040c1140074440317190030000c500c80c0f005507030b214074000d081a00340c496039450b4130f41404819498130502c002407200d0054820440d00102860f40c603a511400042d02d010349594110246c101c2220455040c0002050403a036200c2d51036203d1601c81c40d04055180b2000649804985034520030a00001c80440041c060000361f101e03844100700804400a0480c150302170040260100310800e2a9200d1225040e140c1c15070007240c0c04105418289841c0c0c0040502812000a0003000c044e845580d0641e903040c2410742c2d8440c65400020f003040c4071907000410060070443c83d0358030b5503407640100500440a4040350540b54801c0031213400b0a050411b00b03441c82c1c2c0036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 585209442 1250 585208192 585208207
    0x160203030c180612010e161d0d0602040b0309030406121104050f011e0207080c0a0f0315060902040f051008010513090201051605070e0a02040602070e280c030b0a0b 72
    0x30326030302c01641c4002454149070071014400d40d903a40d00c003680040b00380400c0701c0400aa01c0344007032000b482d805451401e0102d03a8540c2c030f242d10321071030418103080c0102c0b0001c0426080014990450340900000055151280750062032580c1c1c03603210780120b10005020360344008451106004059070fa8104107200d50030309040c94248560108081d28250402042203608028080c42a2200300c0208070399000d09202801e0401603480c00c980180c441d0f015520310f041c20007203000d0700b00c180340c1502d42c07001441e080800ba0012500c00740001ea00304c0460584002000149060700d03440300c030704480b0141c0c1c040e402010000e4090791009004d00c074564112440407009118050643d111070000380c4141407640c00d01d01074184019985d460401c0844103984844400d221902c44601c126920590341c640642c035282c1000b50081d00e0b17141a200e280c05e03000d040008941c0041c0c024a24500190000704088541e400c1d110409002d8101c1c200c03080b0210740740c07507040c01403170900542e40429a441c60301e15030b140a14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 585210692 1250 585209442 585209467
    0x3170909010923040c260a030309210206040309061b02060f0708030a1a120a0308060604090905010c09080d1d0111070b09040b060306100f050c030c0105160203030c 72
    0x721000c00300040790403c2d140110601101d03901405140180711a650103800c20103101440c0c0d200c0f0000ca0301c080e81401e990070a00000185001d903041d454503000c1000c9441e40703040b2850080b602c0d40a906900c00d01d20075403610750b0005400c3d10940c00b13907a805c44910341d203520580758a07904604a01c18041031880300805410035000901d11201c0d81c41c226032411358180c03160380d0b1607081500c039824900e489200c0200000d10302c500e0401e56100459400e4030b20522203a882d5983d150781c003001011f1002c10400161030b80d840c0c1080d500103000b4400700340407460503450110b00034044030501c140414006540800d51240001d0420410816925a9500038040d014108941c42e104442c150420801520f03090401c40e003031150b03400a20504400e561184050000c00054031440488180214018010022207958403980040c0c440030a040c00c805040c4410710407039440c401c40c040f10505200c00191300a080310150b104521600c006140b4100400300401c040b6200d200550f012940800280518040a034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 585211942 1250 585210692 585210701
    0xf060916020718020c010c02062a04050d03080a1104260f03040e070e0427050c09011401080105060a0906050d090b011203110c030618071a04031709090109 68
    0x500303801210040c1d035540d1540000303015103c03121080a600810749100f1044240148906040280040c01e02e0b031401840b02442803000c0400c102131701d8200c0303104180d43c0c0003a10071100900006050303030040264074200607000b030b4001d40f41c14a40c00d103440e0340d0800740703d10300c003d4900307403281620044001d0f04000048440001040400300c03139406580c60302c01001e0400c0000704010b05080220305924900240050120540240e5240c051810121642602c8210300c03075481d403204041c44040841d82e241c1c1045454030754503102d015000132103100007080c4140c402c05040c03004a402d03a12030145a885809002040c000c3d4054007020442643e8203100300703030264000e005540041c00000500e00c2d001d803592440b0280aa12034880000d103000c4600900d0b0b4031115464260800c40c0c01051149840d802287d900c3c074004050f400c403620303074849041c001d950500060380145030750301c0e071a500b031420f40f08030055a07030061008544000ba90340782000c2d5a00c2000c20f442504400500d502d805a00c1d102d10140940b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 585213192 1250 585211942 585211981
    0x20c161406130b0415020f06011a0a02100f1e020f07030318060c080709080c0108060f040e0102040b09030c010215011203110d0e030111070c1208090604030b0604050f0609 75
    0x160b2400d000480d030980c400000d00300401c03c18401d442640000d41c406414043c0d010865249500442c00500c00ca0f510840210855000320116550b1644540001c90900060814070141c44c1e080c80c034050960f0b942c68005505c03000e4418082038121400c02d845000f00d200360420412200c205000d60408079000c2e0b0b1090041c4c914042c0d0030428031025a84410841c0c444400d8440030406001c10300104540c020800800b400041000b04a03c181890028003801c1c00207004c244641081c403041ca41d1900ca5411402d1007000c1c042c0290f4a594403404040d2240d00102d080c0ea02034880c0c60003c0c0390a40c80000c5101c203901c560b4200c0d54990342000513001e03a44506c1b08080d030611000040340200000304104502260807103940b5100e24102c0a000c06095640b002074081c0c07940800e000c0c0724049a45415102d040f108003083d5003640d8412441c00d003246d40210000b0325403160001ca000002e00949910301da01c43c403000c960803c4565500002c104448400fa40d0554029407070300000b0b034041d5101011004103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 585214442 1250 585213192 585213217
    0x605040f05120c150103050a0605090f010e030408060609010e0c03040602130303020109020f06180d060902090403120f0603080a03050603070510090614030702060c0d0b03030d020c161406 82
    0x40140ca500d6581c9408610b11402140c00000903511102000900103882c1c02d4040d00840c0e41d0651441d00c5040d9185900305010301219602c0b00803403c4000200880e0220b0700c0004001d200595002e00d81e02e40300d400900c1840d459000b8500000d03964505004ad06040e9a42c60a000b1101d8858540312411604010b0007110025801c101400022000c00c0181004520035800840c2c101003c0c410f0000070201d500101c0d004400c14051021041c8500301038482c00704040d03521100b0844181010760280051020203908140490280014154003120000d20242d20440c28800c03843d5068151080702c25500c00901040300c1804076401c01c6109030405e540040700223040300d01040d19080020307400c07081c3c5800c01022840700c10b002c000e13041c0c01c40b02420b05560004600341c214038000130301a4480000908112004c0c0700090801481085d6030f016204036840501113946900010301c0cbc46000f9805189450002d00c078040b1103102e880a200f0407841a11100f9144406e115400010b01c55150402e1850000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 585215692 1250 585214442 585214463
    0x1014040b0304060c1e090510020a080c06160c02010915030b1806131a06070c0308040e0103021f0c0605060f0303180a080a030c030c14030d090605130f060504 69
    0x303860103400080c5006900807040000d0010103541c010b070400007507000000354000c03a0201e607900709400070001000c40300161002200c000745807004904150041400800403280400d030f10310a80b00000300c403031055807200340b8004c0c0d400d075540c0c0584084a07045002800200301d01d600740704110701c050034405803c91500b404a40803210b8400146419107000202685141f40c008101e2107103049500d0013414096040c0820422110f85055248500254581c41c0110350003d95034041002482104000355007100c0c2098960b501c0c4d401401d004102031106030310480e162507114007460441200c49080507440d46400040302841c2e501d0001401000307102c10b0f88280b4140c5220b140e07840c1400100564400d20000d46541a480700400052080c1d81e0000c511030350248190303400081d000f07441840d110340c060403c01809513171071400320000ca855544500443c000810300501c20041c82d006800300511505023800785940707040205020700d0005001070403040c1100001c7c80400d0566118581141c0241c02004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 585216942 1250 585215692 585215699
    0x91e0d05090d0f030f1b020a030f0f080a0c0302060708011d06010e0d08120c03091207060b2206061803030e13020a0512061806062d0711060702101404 66
    0x104000b0682500851200e850702500f686d031240d4030390f002c0b80d020b40d40301410103025004140001c09a01008061024154100d0240940c4004d564095640b20481aa60365000711004002804044049002d40719880200307050a00400440e4141d5001403036400c419040b0110f040f1f41c100c000342146060005a410a0313813240c82d42100074500d076004203d0242d56103e400d004a032207a400400e40101d1030010300601c81d099001140681a1000d00600980c0b68030700c90511000401c0035072540b55220a02d405407400844410310000c040c03201e4007104000103550f58005866500310441c2010710828890000c1c030010380114680c500a2601502c41c0252f401500340c4030303080f41d00001c85000454004a4090542e0030040107650740034405a400030341c030903a0740f05590400a0040e0031513109250119000d040d22510b0740c1320140340c00400c5000c13407080801c4003000301143d00880e0305452824030072107183e1090802404581045501074110101c4505a5100f01c807414920011022031950810000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 585218192 1250 585216942 585216953
    0x906060302160f0c180c090f0b0316031407080103060f06140d050a08040f05130e0a08181011010f1103010b13080328020d0c02040218031203091e0d05090d 68
    0x102030001c440400561b0b0800801c002c1c0c40d4030180d0344425030810714100144860041c850a0300d40040d012070380c40301d2400c90501d0903800303021102c0f512184c254001c0d08000c0781591080320706040341e014030020003160740c0340358814041da8454007800e4105c5048119410b202c6c10264550990f903801001650840c804a54500d070707096100e5030081c0141e0200d5002401107142011a151400884007001c02000c01030b00c441c980c40e11418400946001c07004107040303031280441c0806002c41c010080c0303848034217031800030080c003080c03c84800341c0c40640c601a03214443c03140030b210342500302490b00f942d503041d80c3c80c2000c1542e55a000b0102c0031090042d00c0700001e08404200060145415019400e03000080300000c2072400300003240c005411584404050003c0b03940100c2985003580d0180c0b80941c1d180682580024004444800e0720f400d882068107500c030760002c0d60046c500594420040d510210364031b006400300c2410503990403100341c11206540403884e0140006003080725014113400d811b000e40c1d03241e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 585219442 1250 585218192 585218219
    0x702100509010902190e1605071a0a05010902070f02060304021906020307030206070813151509020702270a09030e0901060512010503011b0c110d0c0906060302160f0c 73
    0x41c1c0325160344a00740303002140741c04405c0180300404a40501840c1c1d250002d15032402c0c002a10540c4c547c1e03201c0120b1b0a1072481001200d0000350002c00020b440d0030f01140346420903104039240701c08940b030b05001043c40440ca000f1544c00d0f513001100840110b071140c0800209610261040342d10006585040350307a603d556083c8001000e050b0043d649480d03041c1006803c1c188028011410050200c0070040c10640c40040300c1031403500030707030304403003d048045000f002840110002041401c034072100040d0490250000c1c83e0b0b0760b00c20340c0e00009213040400000c1c0d0b442121401551100a442c0001c0d42e1622645d02c200f140301d0207803400c41c51200b10800031460010003078100030005940000d085662841e80441d05005201c194020803481600c0164400c5042551104a0400480110070818813144292030540d01500800c10300403d001e41c501281d8004081c400e040800d0300f40040024042e010380b007038940d490102102c0c01080241030780c3e01a846000344d142203a600302001c0c07010841c410342c940c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 585220692 1250 585219442 585219451
    0xd0e13022101180b2706030a15020a11031602330702030f120d2301080a0212011104050d02061603080a270303020a0908030d0c08010e1e07021005 64
    0x10f08120910000e041c18090710a2021168007610404614024001440700c10800095455103400000d40340d0700c001a08244204030042c10b000d002c0d80300d2004403081380d802400c6a4038943c4501c90f00c0002c1c45142c50b1280103001c4110140341c1c1c001e2188000d4100385604030b07024a0112aa80c82c1903201c00b03510309954041c03407107505035031002155060440c1010440d054800300e00e0002400c00091010002500307201e10400d042c4015100c0030054255000061401c0914404188582045d0303107a01300305985001307542040c0e11458000e05020354415040c410785141c41084802a4a8a414602070000441241c41c01300d0b081042080200da920800c024044200e5100303a491000e28281108281c0544083c410700c11840c400080c402450101d440f6011500c40c0e0b4141005a100c080d403441c1904c52038000c0d40050000c0c04001541003182920342d0020740665000c1d20ba0300d10036600c0b51208003880710202d0340384068043d54060a40880c0110703000c0c91344564188101d41002c0070b0380080b80143d400a45 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 585221942 1250 585220692 585220709
    0x5190507170405010b040509011401060f020c0a0803070c0b04121113091a1e0604050a0b0a080f06010b090607060e010b0607140f010507200a061a030d0e13022101 71
    0xd91103170540307487e0280c07603004581807000788a181e007030800420080354188680014094018540614140280268803900100602080b841e03640e07403942580384d80c0204411194003150b020003085e50410748040c0c0e010344a200d001c40e0642c80706c503914075180c41e11000c0003640c0003401007924043d840841c019440f12a03c0780070010700d404041c0d8446540030601601e0b603802c60203003060314442c2c5030503800d40b036034018000c40d8041510384920800d0340052010452a5401c15441400443c20000c005010041c1e455040103c95090781e0300c000c1100d07140251107802d42c2c4100c04010f050089462500300300030200f04000001500b040070b0340021b60a0b40461001c03507440d0b0280007042401a81802004800c164501c000d001605d850790005252404a007030b424100c051100794907441480401c1240380d00c43e0f01c0001041604040070a0000441400c012244607201d801d0103c4041c1d84a00e4403196022405001c04400210741c0d030101010790008902d0441c0808492050700840345401801d42c02451042c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 585223192 1250 585221942 585221951
    0x6061203090f150e040216030203070b0604050402100507331107031b0f06020313060b0d05060a0f27031205280e010e0f100519050717040501 62
    0x149000781030140c2039440102500b0680000300203402c0d440203124550352840c42d152203141c49240014009002d100f6840c071203000030103602000c2580000080404500681100341c15a40700130070041951403c039402900441c112101780641c5001c0c401900610b80305e1a03a2500041e8083c6600038110081d050185a2060306a15400c403000c803803240b504501d001c0d00710380346460540e0318040e184e09031200c0280203070700c8240d40840601540c03090001c101680300c60309640d20f040a030a22091004a00300a540003881e0031440c81d1a460818481140940c1c40000b0f800300d9900e03902580010714a2000709456261280240d03844522812020341980034540804a0940c001d07041c024810b0403a00301140071145401c0910084807810f52070252115944c6400305a080b8080320058040d00300d001c2000350560030403c10005003400400c02c11894010201250341c142c26802c000c01c01d4540655158100f840701d009106040e00b0981c012a9000015081c4809405030100403081200320840703050740e259546 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 585224442 1250 585223192 585223229
    0x50f1203181b060c0316110909030c100c11030705010203040b0c0f160c051309030806041802090411030607020106060f03060e0a2408030405130603030f08130606 71
    0x400018001450500014041c4042c40940748204030001c0c03034071a10a400118120003003060401c11528070810015480d8103d40003854140802e60840c911641302c0c481b01000603428410000c1a216645100801458005450300d00d000060801e1503800741082103900110740800710810080032098441d1000581d43e00e000e0070505d145040281412123818410040c0b8600751003a031064500c1c4003010040099607080d6032401450501e06544000d400000c0b44050f25a15130842d4080350321640645c6505a15966030380c20802110440501d130408101c2c0340e242a409818403008503644a07102d600f4420f0229400d10010b4903100c0100c40450051b03440300014010341e0b6200c140c01c0d0160300141800e100882c00d020040b014460014132900c0810b903201e0780c5030710047c00c000110345200590000d0450741e0f500c0d02c030345640b2036100f0702580340034210f0104007080c841c106124402c220307a01076035140c80b0080302c090202d89880000c0c2c800001c2014581c04a804035081d4811000200191030088032070009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 585225692 1250 585224442 585224461
    0x30a050105030715050a050424030f060b0f0705071e03030905151b102909060a06050d0e0d0c15050702061f080d0c0209010911040b07050f1203 63
    0x201604414003c1d0403502d0100078200100c2190501c08801d8205039450f0022190100c40707600495008800c80d000c0350740c9001c1d602c425452801903212550b0b4045c4213120f11351032140c0555806128462061000b00000d401d8440c0c83c0000d441e240384914159100386903521000c1c108800a0011062030800b600420420581c102c0741840007418181c9004c0044100904030b100e140c003c4010b4407101403005189150b09035000c2c003000b82030300a0250108820f80132103059070414201a00740c6100180001140e1105140c07500c1c1403441544010940b0f411142480801c495641241710881989612020500460f140900c851a800a80b582c1e51102944d80f40c2800055109549a600b842034030b41002c1c080641c1d0301040c0942d1001700039180c03410030075170000166166141a8040102030050b1007900000c558440c81c1a60348500840704040d10781d03260300c4010100d0b110903002002840041004028804180024062042c052030030399480e121000a07172810540e0007901c51408607800420444150b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 585226942 1250 585225692 585225701
    0x80a05010609060e0f060301090203090f0a020f01030b0d12020106080d0c0507120201140d02070c050f210a0c092f120a0605100e10090302010c08131710140702031e09040c05030a 78
    0x403904000e03b4180341580110f544000030307101e402d040544944034003070207848103a43c6210305540100c0001c0d9290400324001c0c020706440c02040303801d00501c00140000d9100f1094103420542100c081d10480d4501030f10240390140000e4224103011a40443c40c03030501302c00c0c0150900220062001d66524080d1030080f032039242c181c126030710441c500c1c003039403d860311540107080342001c10031205d02d0417540d074051881c5000c0403190010a264524080829100d600790405401081c04801c50210305800c001c3e004407807202c0180000d0081e4040c44074a950b1181440b05503003080381c49400103065a250b0b00441e000340c1f28600c10f00007261180c4094690340c03c018a0800c1aa01c95140071080c19045900080c042021100050441c030404118140314080100b4803400605840b100c1491042130140f00d01e80320707041580c0c2c449280d46000d8110001340b52a4010038400d06042e80614070340003544154000c2150b4400a040500400f4003c60482d921030b48560b0400114540322079480340703004281d04040e00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 585228192 1250 585226942 585226963
    0x303070f0b16120507120906061406072001050f041e0b03100504020f0d060806010305150415240902090405090f0d0f020c03120703080a05010609060e0f06030109020309 74
    0x12003034580303194216403120007100f20042d4244049070b01e4848040c1250407061880750502024a81941203003008069489801120b0600388500100e81f0138a003040402c0c000c890001c2d00c00c0b00503040c0701c0c1c20509803001c41140c1c1c540504003241002c4420301032503440c0d0450b411030600030045c00102410781401e0400600105207408070300c2d203140381c0111601010022480380350f001c0c540204841741e121541074150380704c80303494002c10032075180e0329130010303540305400e1200340c034a03010f41888a10110800035086104680180748400d01440c0c0089940040000c8072900c0480b80e00003044155071044800910000c10780c103c405a203c03d90b06080008856002e404d10490794841019010061008a143c2410350185c1c00d01080d408030000c070907800c000004041c0d84c3c0c1070013501221221131084030701600308a40642c4e00c442155840c0414601290405e008001c0402c030480d4041090504c220b01074004690007800d501718441c071803004101183c0086e040640d5140c2c0100411607003010401480c410b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 585229442 1250 585228192 585228211
    0x603151321110c0a0603024e060f010c1e0501060504060b09030604030e01120e03030406050604020304030e09090a06050906010311060f0403110f10030c02010f140a0510050303070f0b 80
    0x1849101001420318084d82c440c070024540c012500806504540c10a114040b0340000e04c0c5c0e28400c6840c80784524500d00f001c034a40401d0650583c0c0440c08030b004403580c403900d40540078100741903e0340010b480c64611801c0c102c8541c5a400e50a5500c03030000320240741c021f4460000480c2c8981400300704400c4d110550400080e0b0130003881101c4d055540041c419030001c1d01030600b101d40407040300c012243c500000d0000c3d5441401c1c011030b2100315100000543c802d40c01880100710310b44400c01080305a1101307940c058001001c00c40c0031449803820519803504240010211500002245e84d94070031b4880450340c80c011a0007440041043c03143c00d0f0b04078a00030f00100c5043d07207050400c2000e4601d40c090f601000d040c40304041001403560b210010124207504c00207044000c03410300010020040c100002d1404010350910620380042e803840c0c0201d505401170100740c04920360303a202c03042d070080c040245000040000500c000995840510003001010b0240d22140d02d108140d0608528008020380b44400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 585230692 1250 585229442 585229453
    0x120a03200304090e011d1506010516060e030c0a03180509101e17010f06050901140621010f060f080c0a05090111120c0105090105060315132111 63
    0xc440e00c0110072102501c4446800181a101c20a15240105070305101040d0305415100540031910300001c5400c07800d00070040305142c0b0b0381c48800441c0e00780210b45038405821010315080c80001c40744c4d00b24401d4681208112404c0004c0e2050031454501410030a0b00442c032490100c1c082c0b4045d0500000c0076240036285504c0a08110303004111106d094070482c00342c8651190b010a0132540764590364003c01a1074110703164040030041c141c1c002e00030039280744545840c05900042c1418a5003845040f107100c03840c00c0051951400074020303542c0c0508a030b41072080e010030548900b0420070013814040d04020403000015401c101001d44150303100e0100d0703005d000c6401c00f0042240074a00889590040c20f18084c0e449910f4000162846583d03040d86010300c1c025400384a43d003420303000282c040002c064000340026185e0017103182c02c80701c094400e5505500101141c12030007030f980c0805a0040100381e040c444011441d201c1d0341ca034800c01e07448070751b015106c001d03c1c000c15a0b200c2503140c0003071044c801812 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 585231942 1250 585230692 585230747
    0x10f0c050a0f0504080a061b0e060906130504020304030906120506030703030f050d05150a06111b0d0c0803070b0f190c03022203030908030a0905041505120a03 70
    0x80540c0904401c24041010002986803002c0c401c0041d207004020703400841d0070f01c0342d041c075000c0058400b04880048107400d060994400034481c1442c5404070602919032440c0213090007c1c0500c541c0400c503e101c4801094000203640c1e126031004612560181d0b980d001144e0811400411000d00001c0f048101c9042034140407682e41c01192040032a82e03d802c090034036a40c1410309480718040e090382111041d140100300f02d1082d41008444900c06021100e0f00c04c000d44800c0c0c20b507006120661042481d6200b8000f01c0044400f0f050004004400200240c00e5407100d65261603500010f038003c4402a0800300d181000c211032039046603005002c0236429221f9140204a006045c048004482c400c1500c68440c99201c500070760454404074015901d42035074009a60f50401e4902c95403104030000b4904d8a030006d0007030008000e4844c45411035807100941868081040702410700441035440b04c2c80c82a100060a1780d400c200b440082d0320000140100241c0380c00c2c0540b0aa9a4000554001100c0321201c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 585233192 1250 585231942 585231947
    0x380c1e01020c120c121b06040b060a0503030c03030a0e0c0d081e0711010f050d11040312020d02030313031823030726070819110307050d03030b01120f0905010f0c 71
    0x178400001981a40307407042100c00a0f0680e210b0310b4050b100e8001d44045c8001e0003442c01089105400c181d810000c02591881850b58901c02c004810020b602300f0f2010424605441d0490b00322900c0d0307202202c1d40c1c40c91100018200004044003141d2400e00002c620001d4185548501342000c8000400d9050041c2d603224035040d04190600c1300d0400c00c1c101104d5204038007030310035552510703c04032040111080c1e100d80040c80c3e80c0540020744200007240c00902d41d251000960840c0300f09980d018600b5516800801c13003850360b4040048003400a014140d03054032941c0021000202000c0355008407102180c1c0107911f0003200410898003c1c2c0081c40107120141900b044440d00181c205c00c10741d111030024541c0d90078490701c0d0700650900c2c0598201041003928498010000a02407241c0080903099402016501d515601c60702d608001419450400b284c0203511406030254181007500203148090b01c035004940100c14810b02c0ca41c0c2e1044010180802403098080b4041914420401104552000b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 585234442 1250 585233192 585233203
    0x30d0909111606180516050102010506030703020f010c06021c020307120b010e1210090308100f030c1802090901090e010c1b170c06040507380c1e01020c120c 69
    0xe05050389a100c4d00c0d078403a019550142d981900142074411170100200040c010110310710a003130056003080301007080d0745008110f08045a5006101a8000c0c601400546140340c91010596680f07600b0302501e4407008a4030718500810039030100050303a038600740c440a05841000b46070f02c0c0d8641d250800780d10540c0d8020031a01e00c404022103001107490b00392a0309519241c540b0034800c070102d0508290404051700030004601031044690649000c940300c00000d000c0c03001da8400078201103035401c010011a26140c584501904605601510344050203012804240d000c4e8070241400741e0350954a00b01410a101d40c55850490740f0301500c0310800c110504507040e5003518007400060680c050340c084a843c0604441c0c40a0b0344030150f81003407410307041981c0c03545014030680104240c44c10001d02034591104c403005808540c441d90701c81200807030040340e206400082040701e0b54404c0d00304c10502c00618403c00c101d0700642c2400503999051002c1350a04020307100210b008012010301129010800c01b182 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 585235692 1250 585234442 585234487
    0x1804050718180c0e01170303010905060402070506130606090c021c020a0506010e090c0103050402010c030c11120616020303040210050d090209151e01050720030d090911 74
    0x54050070311000090100185400001d603071801103002071000401c55480c0c0404215005454808020780e40e800e50000210035001144105802c200010b012003a01ea03400a500300b03101600040c02e20306140c0c2c80d01c0c034103041a60b400c0c9031400c0c4a44103808000300c600600c0090816a43c1c14010810340100c00382d91400d88034506401d41d4140b2041d110180c4c8200304500505c2d81205c01c46001d5607480d012541d54050907034440c1a90700a40c0700125040d402030003841d004550603510600d40c2c072070340e45080703c002c43c81d10412282e03d0444440142143e440000101aa01c0501301400c042d0800c0503180d841a0000c81ca9401503400920801015942d4221810200000c81c28441e0317440003c4020311000b8031034000c009500200d46024040715000d0b468040e01e0703e070415107101031851081c03002e401203200004055400590200010700000f07500b400301c0131111201912a280c0c1411441c00a81000c1000c400e220010b00c3c00c0108001d00c00076401001054040041c5591814695449060f090a0f1141 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 585236942 1250 585235692 585235709
    0xb060312040f0612201c090b06132009120a03050405190521010c0320090103270218190e0f07152a060c11030c01060518040507 56
    0xd803243d42c10708103600300350188800c0015405d000041444000f469400008410017540c00c0c0d4400c01144156a100e8000455005103070746929039031f01400c01041150700552112072580f07600d661a14001c040042c01010285203c101d40ca452698080c03110001000c1559000c0382e00030810b8002083d0008121001c0e50000d86566030040344140d450071000d0b001d41e0129801c820361321074058512040c00c4020792401c2c8081e00032300030341103003003c100d00b6180c0400b4400c0e5000c081c2210a0040c5c8030400080485803018180418205003d40070b0215075031170070b40c080801c1c43e60b0207801011407806003102c0560917026050b50084e420503806118101c003c1400011281d5038441407a2000360081001d00e549040b1013045078003c586034010310300241110741d40400829171a454070129140242d80302103a8003645043d51044a9098880c08081c08003c8813030400e000700c800c2141c4203590103000030001c510762540081242c030300d843c041c041d00d40703061030003c555502400c060100040011440d00b04884042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 585238192 1250 585236942 585236957
    0x3021f05010506030a09230a0c090e060a1a090f01170f03030402060d091b0305010c020318090703090f0b1e040f030f120204090501080d050708070f0309090204030b060312040f06 78
    0x518003d03001c451003000c80303000c840032121141f40300d08000a050400794403940c82004026a100000802c1c1c49401c544034a00c1d4000b0000540203447e0b6501c5400b151050b1744914a03400840c3c0c02003084110199100a180c10651005100305071401003c2d5288203e004010240e005038420803a03107900000e4402440340c00300140300e000226244e0400b41c07126030000d10316010003606c1800c102c41c0084501c01140c0039401d29050700c810354000b100ba20107048800780882c2034611039508015040c0c0c002001e550074182e8404c801004285403a10700a00b080c8aa030145480b13040c10982146021804c11000d88803a40e0f400810001030703100031103504425410304103991444070b002416035140d41001c00340b60340395202040c00100513010743c002038101d8200343d0903144556244036040720144100e0301d010f0241c03801046210001054140c1c43c4070210701a1504486284c0c5600d0800b050383d00036030056902501410a11110345010310110340908801400203150030326002d564900d0302000e12451084c4200e2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 585239442 1250 585238192 585238211
    0x60906320d02060c0a1119050103050405150414060c0f0d0905010b030d0c2a0308030a020f0a12050612100903020309040615141c020703020a020d03021f05010506030a 73
    0x1404400c0c00007079030003801142c0761074501c1d804a5881c08160070030754081c0b0101240c4c2c0f08505090300201300c400000c1030407225450a0400540107850083c004030b40f0362042c03501004d0b01e06004200745001d03074410201034240844980d0704625000000c2c05e90030402c4410018401c56010340300843d2246040d125010a070b000780307418050300504140d1a2990140200300c01c103030040d41c1c82016100310350b106501ca01d8110900316046504c4c4203c0b06d1441d030b079903018075909001083c4120040d59104d01c8400016207041c03a5401c02e0b218681201c0740708d0012079000110380303640b08514001c0743d0f4420320585812070500c918400ca01e54500c48180d51001050352007080d4130a152082c01142e903226400740080c40386581e160390240c50001006500b000040301d9001071200791460340c0844244600d07e900c1801c5040d20015150f000b50702c0684124150704c04d9141020040c2c0314584503595a078043e4004c0c0813460021342560068000000e6030462407481c000060000e0740e40c5001b941d820003040040001c040c4034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 585240692 1250 585239442 585239449
    0xc0918020d060e01080f030304201c0602030f01050609010c0206180a0b07021011060a18050a05070e014106040905070f0518010e040219020106090632 66
    0x1801c6141403050704254010926140c81c94456040315408012641525056205107880740010307100142002c242c1040999040b0524803011081303a4002d040300c1d00d0085102c044022400550710031191690007100704500b007944100600d00600d015102c0924190308840000c1000a000034005d104540c08986070001d243c95a4600c044940c002e840441d44c25251143d12a45400c02402284161034092500c42220320a800e4002d0907006a40240f80a46a003c40c038009000310345403410240030901100d0000c076008215000c201c1c1e0084010303007801814040001c401ea213058000e040d400540c001c026809040d4004003013000740303006143e03840050100c184204900000e0102c66403040000c100401c5e0910241d0009010310681e49a01388900450003007039946001c0d014124411401050b2034000ca54098440b0780080b1700014070061918550f00c1010203056000c4580130b0050f9580c6c170040c010044030344144c001403d801d041542030f040d0b0314207018044c0035050001041401c09540400d00d50f80703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 585241942 1250 585240692 585240697
    0x150f09030f06070e3a15020c07050405010801090308010312030b27070206072307050d08070e0d080406032d09140a08041e0b0f180a2102010e040e0a0b0a0c091802 71
    0x19081d030001c7d55940c1c40b505065544130000d00440c2d20681c9048000100c05605204031101d00b80e0603220300300f007030786161514604c4814002c24081810307203644a402e000d40c0d5910b4001000451030300840000d14041e541402d01010060101c0c040d548034509015106800240ca09105888544002c0d543e00704100906181d0050031030003021032017040d0140d0802074100d800c151280c8002d071f4420b04100d107107208000074050011401740010f10100010700c107561080d040f1041010640194110862008075000c000312003100070f0403c0b5a5544954000700001c024240a01c5000a00200001c0c580340d25038403260300c9540300d2074180f50107410b00442513884001101009010800d42280c6914900d2100f2080c1e07400391a1900507540300100158042c90b0001054058542103190b203151034500d100c081015840d030881c1a4140311503070300c3d08506550b490003182c401c940c0102c00303010f0741211480d00030110400544909045403c03c4204d40c849070b0702c00844002c03655054440b129190703221803010001e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 585243192 1250 585241942 585241973
    0x909080418110306120f0d030c020609010c0509131d010b1309050606010e030f070b12010506120103030305070c080d0b041d0a1e080d050106020c150f09030f06070e3a 73
    0xc0c05031f0016803a0b955007541c41130b9161050354003580d260b503072503600d003600700c4444805607030125105100b00340480c03c210400c1200c459088400180d40030024040407030700018100500503da44440320039640d4204145038822300302030b1020900020540360780312038030f4a2004003900e041260403c0e103040310703079020048807100c041c101e0207451801d602c6900c0004176038049400c20300710580e00e0000191501b411001c03500710302d21003900b64403036900f181c0d004c502900d000340080c000c0001e80120781c2c010482c480020f222401240c06c1c0042c600320406d0901c02a15030310706030340c606d200c061070100c19891804240c0141540d072240d2081e01395500c0c07143c250c0c600b005c040c130043e0079424049158000c030700881d84140d06947d003503001c491115500d0400c00481101d103800b01c13000010706200510b12550000301405113081d0040689e000c08403440341551403c0c108465200000e5003240c85040b082c148080308580c424145522000082c4105000380740c3e400c00e03100d006041c2450074400c1400c0c0701c2e0407141d07103401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 585244442 1250 585243192 585243223
    0x30102070f030305090705010503040201021b010315090b030618070e190204080105100e09030f07111504030c050d0b1f0e1f0e0105030604020607050304090908041811030612 76
    0xc030340082c02c0040041100322411a418031480301c02081c0c940c010402c0d02c1c4195030581c001c203081200290000360011685e16054103040d1202d49083c0803e00c0c00105101078200c050300005c130b00b85181e0405250040180c10306a04411403c030241c0074407804503070701050700c01401c00855580ca0b10041250468803030210521070602c08100880c8501064124a009004901007069a6900c501c030300c0307140c0101541d514429500c00c11010060360310240c09000c0d030350b005072504a004054040860100601c481b00d1000403140024240701700442c0302d000e5400713080191580d40403246942d0b00c1030103880000d44900314144d002c0f030380d40b030801038440d03451400b03418902101e6556041c00f400c240400401c2e102070202846985a01080d84100f14100301c0c102e0740010003c180c0c1d80c5554003030012503800900250b440740020400030501489600808211a202e4110f10390f65914003080004010b122032815024107040c864182818607045040c0c0c1d0300100116001024032030b482a00d01e280101c17941a4521 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 585245692 1250 585244442 585244463
    0xc0b070212480114100320130203060906030f0c040c050c0d0f110a02062703010903021e031306050c072111030f07060302160212010203090c220c140c0c01090f05010e0d0203010207 79
    0x240c0ba0954000d5402100d0a40e0801150744985081544543c18809403463f550700400010f64240381c15044412b2118060906c246402c1d810007003181408200340501c0c011400d04000a18030b036038407218040c0e41d001d13190041c0c4141c490300ea0010b5a88c0c45101c6008030043c1190420814503400c00c40114030002008008110003a00783c50040e445500402550b2403610f00304002402c549400320031180041504e034180d400460800d6000e03121904001d2610020b413140190216030000600780c402221400340b2500031308210640b42c003c0c6030640a404c81c5000e034210703800584a0400c0001e1503015207000d0704001d40c45000590340210342d043d41250280d0300c040d5144020601040660007580140e03440070030741d10400c00c14006e003c0681840700d5066101c81c518880b003003929a072035014040c041014a4120740d1a16502c40b03038041c3c0e4000c034071410741c99005007026a11941e0450030010040112200c0c00d1840ba103031100107850802c0e07084150307000c2d924240da400308545e800c0d41241d00d207a50128a041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 585246942 1250 585245692 585245719
    0xf0f0c030315050301290a030b01170c03030c010603050d090303050d0b0303090312070c0f05030a06050702031e0c1b0d110409050d0c0b070212480114100320 69
    0x41c0303411500d5089518140800250046074180700d01f5000940ba00207180084691030080501c1100301c0c101000201d034014030300401c0d0240d40c10b000611081016500204042c0c0c00d6040403414a401c0400240c1401403400c0704000207504502521250403c03508002080107110303011034110312400b030003e03a2500810710300c0030070440010081d142c168011a40d0365811505d0344011100102f860107140e80c9640890b41039000502107401240e4806454410799080c64190011040032031a0080000c1621401003803000d02c0090421904a1300c00710b006150300244c40d940086000c800341c0c4032010700403210381c009928258485400c022400741d03000b400ca415921000038010203c40304044103c51411103400030a046900c000785c400c12001c6000c101a240008828004810559074210283d030390074549000c0c1420541c04068411490002c0c88000b85074400c58039160031100406980101108040184525082c92200503000e699110250074506501c0b03009140d000c070b803030703110640d40f0000302100308 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 585248192 1250 585246942 585246971
    0x602011a090a0c02072402061303051e090d0303060e060901270608100c1103090603151305041b0602010608030904020307110601180605060a081b0412120f0f0c030315050301 76
    0x1030b48006c050b031b42a148162221400e410320303101d03101e0001d030002c1c1060150030101c50200e0f980075000c41400315168030304620344011603030030040c00301c003540131036501d440402201d06420342040e40300c131040311020302d42d6040040d2458510003102141603400b4429025151200665108001405204044072081c11000d11154090481c0c800c4650000f0b58240440e144902c0000980b680041d00a058504540c0c0c2c0b8020b000480b01c0310307800240e000c041100221105c1c030292103001d0141f0b02890b03003025604107c50002d107501410345e0012045a02d8128208020480841981d1039480d085401580d02e03280c0500455021078482d803900c0d070900440300005105560102c1100c145580c5103000d0010a0381c440410016014000c10200031585020004101d454080104003014003140451400e040d15801d4075080076825110441d404440000e4041556400c2030071000f14040c18940781d141d844240c0d00091103080e51030f000800741611100d8140381440c42070848000b0f003902030002c011034118050322 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 585249442 1250 585248192 585248249
    0xe030a0f110f0603010b0405100e060c01051b07020a0b07020409020306010b1e0f030601030f0e01020a110c040216060b0339010306120f02040609020c06010602011a090a0c0207 77
    0x345225602c9544034071203d0801c0f1094030b0486090722203850410f454141403001100c00f004007141008610122000c50759114000703440d4941d2100c000040038500040c4d042c0c0d2004112520f41c8801e00300f03104520040c2c0d114038100c0d040d6450282c5c0c2c0b6403145401c0c4041405044ca07888e0080d071501134a00082141c05929001d0440d40304595050340040202e018002c60a1281031300c2c815185c4030410004100f540a0781003104510402c08000500e07505240c1514220f8005010b40d2000800d9a062030445070700400c07815400f40c8044804500c0c0003ca108004800910100d00400b45500c83c1110310156605000d460307501040004590301d03000ba001e034441a2101408046034000b46403000440055100784104010346032072081e07402d116581e50b12050911011110102da01986414010aa004a5001070500c088113540144040d504205004e0709440c0401d0580504a190b4500340b00d1603a00e00610341d0304509468400aa54100c844c0200c0c208426900305681503c0811a10304204400001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 585250692 1250 585249442 585249473
    0xb060304030512070e0d1410060b040303111915150902030f1b041e080f070f210f060f05040302071e0b0403112b060f05090d0e030a0f 59
    0x5000c0d41c0d907400c2001c0d02e121712020802a000b1130f42e1880a00003402500d00903654520800071125017141c004500020740f065038000b032044980229080003019040010000c5820240700680401030840801165032444c1080113018070340c06e60300e03100b1043c2055000020f011100041c9407410354858a404001e5481603901d103c402840d880001c3c28030414030104140c0b144414001440d1601e4201036a20320005626500c9070030030352880000f0710002c00c0001e901c030914180e0241000d10301e49440728130725a40d142c1c031100b000f90081070090b140d52200d141c02d08500d944030380421000c031003a00701071004080001d46e100e0f40178509400e020901d40c001030352100b142e02010310064201c006102c018010301507442030041d101030512040c400101d4200c4844607a02c00540700001c80f41e2700825000d444502250040d6641c58681c600c407040c8107642c003d6403d402e170030020074040350810079079071696070480030401e40c100304011858000607901842034002d0039812041800d0500d10b035041104007900e4441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 585251798 1106 585250692 585250717
    0xb1f0201020408060411100206090706051309140a061406121308040306060f0614121017100507082e050402032403010b060901050d0b0603040305 64
    0x45940e03c035501071b0440940c2d100c005130600080783c3d00c0c080044219000b060030820100c10000e0a0f0301140c1e05840c0007030390354a440b400102c41503400c0e042500340c01d0a00b20181025454100801c3c000d081e140003c02859070340f44180030682542d004135540190003071143c800892000264194070482c0f50400806c06200d65540344595485504100c81c0a552008241305081c44842d40c500500342e40e085c208010842d90714402c84d9409000e12000031745400c00c001400400013050b01c0d4000341004071031400b0300f140d50003059882d0150300d481c00080c0c924040029108500c40c032003141c040c10040d0650040440081201c804011041c00c83c042088052400002c5076107c61000310700c20413201040c2c6520340006060203541c81e85040c43c40f403081c0e061540340b810507a101400c42d144001c1c00d0074a665516942100400600500c241055004002100300010b168014004006910190 = true := by decide +kernel

theorem cover : BRFrame.Cov 585071942 585251798 := by
  have h0 := BRFrame.cov_init 585071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 585071942 ≤ n) (h2 : n < 585251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
