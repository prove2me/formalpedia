-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5146
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:54:05.274583+00:00
-- url     : https://prove2.me/submissions/919d6ae5-b623-4e92-b42c-da5e121a4d6a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 925359712 ≤ n < 925539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 925360962 1250 925359712 925359737
    0x617010e07050d0e070e01030b090a020306130609051203040309081504020d0f02030105100f0906050d2d05030d050106021f0b2d040b1c030f0c050a03080702010b01 72
    0x4414076000a071901d0640c0d999040b1580310710042042d00ca1150a40c040d0401c000740e181c0d290300c02c20f4184c83c0a16415406611007031209a40c980d10190000c1d05038108a0000341c1d1404500300248046005100204444000d956100c1c2031000010851686c00d82c04030500091503404071f8054044c105200c0244644e140c081d0030b0b08222240203200a00c40c800c6220300c401042031015010110036400340c02401241040a94210011114000c005e0042188180018215040c0c000c80701100c201030001405240c0c9a190b40b801c0c0c02060003180808947c0504440303640000c08511095240104040c1d43c131080c810130002c05448040e40a401154800e00d8400030580742008103002525010030b0000710134140f000400c01c042000e804040c201403601d4419803803034130f04041c1c06021050880d41000004011410005270600e40210050400900781e21000020b01039148000714020b50306200903041002d0b0780703e52030100100c1085000031203040a101c0b01540901440c004040e090070b0400c1031000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 925362212 1250 925360962 925360979
    0xf03030f170103020913050318130903050d020c0a020603090114070c021008090c0402180a0801140c0a0207050d060c092903060a0b2b0218060a021c09061701 69
    0x1070601001e48907090690100b00d212100201c1c1000c10359100c800e40c0e0302d03010b420684070180c038423001080c0e0040548520b8080004c00900c0b41e81c0f60a40c1c15103e207814001a004500025084110403440d5071007a5480400940d85a0307000d14030601c10301002061004280034098403002000d402001401589408940140da0300258051300b806103282038455a0b40b5800401d03e051080d40e442ca4029200041c00a221107100940641c0c00d10261880450203564150141c201c44034100c022402e84416800301e8001c42001004220301009032044411107a00c4400142202c0040c0008441040d03881c0540c02080d0780040491005200a2110141815001105d649030304542c00071290300030760000001d5107641c0d8100149010381039282559490307100d05c02105080200301c603141190500c982d5000d80803c91117008456455580c44000c09a8258480900c8406d801c40c100d402c3c1540074403c000000c009031840340c480c0b1154540e0314100d100e4904135016018454082a40051540c40340040c0001d51 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 925363462 1250 925362212 925362257
    0x306060301050f0103060e07050703090b0903031903150603051f1503091a0a020a02160b0f030a1d100630030207120605060f190315150f03030f 63
    0x400950341100d00443d1840101e00800031030b045094a00c0c094001d00c09003507030181c06071400301d22076140e00084c10344070364000499010340302c0d0381030f85644200800c06a4045258a012651001d4200030802c40748014000c000310000c5d800c001c000aa0750380400c9101405124010f1109090320b080b240c1440c101044042d908140003c05030515440d10a40400c0001d800d83e100c401200d081e0324803800781007005d02c0d04065401124541d0040c410f0380e152003054002e0030f45000442d20301d003a0003498401c1202d424001e03904000c1406800c9561007a0b10038907006103a116518494600c0d02070320741e07250402c07002401ca07152a004406188141c007280c11f0203c8031403100403004a000200042e80140301d2600b01e00e0304d1101c1e003024a0402050b80780104000c400c1e0030544c060181169100c05042284007840110805500c0c2901042b19820080001c5210251035441204040401040340055000031480c00d00c42d5500404200100b450108103259001656502c102542d145c12422120300124000022 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 925364712 1250 925363462 925363469
    0xa030f050306151803010212040309080f0d260a0b0103110708040b070f05030f0705071703030a050727140126060303091e010207090e120c24041401020306060301 71
    0x1400244181c074540503900d0130f04041c1402002550b88034150507041c034000b68191022004150002e4000c21070b23036000320b0341e13400c40820400100702c0703001040c600b00d0307100241c1c510180c0d13410030100d070039030020140c9011144144003820307000c607440e007501c8001001c80e02c68203545400004248600c000013120b600c02c5504489003a00101d41715243c50800302c01c08944514001c0081c40001030032100352035035002403c8042e00807000e9840c440e68581c000c2c3d40e00700511040d001c054208000042c50005203510482c1c210096150454100561b00c440700e03900e02d4400c000c4a005100d03e402040065101031444048440a00e072a9a961042155504035480200306131072804c441c100000300152400c10903180301c941c00a007800c50f0030009403440190b00c80c0001405006028031040819112158000d01200c1c8100f00001c00340b0310b02e1b25411460681004218076010b00515180a1140024000c1c4030884a160401c80155081034607141010840c2c40c244c0c50b100764014801c1086030b070717101010b49045 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 925365962 1250 925364712 925364749
    0x240d021203090a1206060b040302090402060c1501060903050c120d140d060e0405010513030806010f200303060a060201060501020c011209060c030c030b01030506030a080906040312020a030f050306 86
    0xc41000e406a4190b0103458030050300100d61080000700c803120400e6285039503010360310422a00380c5580c032170003240c4a00e0202a4015030000d0201d001801c1c924001d11440000d101170f07820100550a9019071500300380d0003103000560102c010f20a2002c1444034040f890340454014021481d1401810345400114241e50240104000480660324699044803400c050006c0104100c43e102e840301d0220440540d000d480c150718110000b01d26072100c1d02100344039900358640244503502e030001150b0040ba0007040c8400c00c400602c4412030006183c50001c1c3c0c528800c0301460326490300800307220428000340c0c014011a8140401000f01e643c020804130a94002880c000c0d042418200d100ca02030000c8602c010102840c040c49000215450307405442c140c42240e03410f000100c0044011006d8800950702103505420103c8614000f42d5082e001b012010341c040d140c182000e54a0301c1d4840328825590907800541c10010000d010103500450301c1e00c90040c00d080a5082d41490004602c2041c03806220307020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 925367212 1250 925365962 925365979
    0x190f051603090828031a0906040c02030405090406050a050709060f1404050d21090f09091406010801060503100c0f031505030109080d05090a1e080d0e06240d02 70
    0x5114442c012a40d40c0240d0b1070389944c50000c2c0340c80585100503000203d60019140002141d5900301710048081115001411700c42d146e101c4001b000b00a2100604071400c1d48000c100000d416102d03200e16034421030046030001001d140c84149041540c030014468400c00000745824480290031100b5061440010300e0180d051043d41e0140b1000c40c0b055801c05540100c000380701e681000106200c0d528040d00c071100d502c0c61404107000c250344000c031b9401010081c107030f900c1062007141c190350701414625005200810f030401d58034513942e01f0600e00382c20081199440e500184640e060030440850020b1036104208210f24000b84010040e03002d52142c1001c0640b640c0104101c40010104d420140030000c0003000710354034034549030701c1541c8942c2300d0750101401d0400003549203d001c120041ca03280c10900c0030300c200444440d4205408011032044848007004d01600c021141c003442001140c1c0039500040101c2d04011646496644907182403a0404550035540611603c50b80c010001180e4140c54102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 925368462 1250 925367212 925367231
    0x70809010c081b07090608031c020708030907060e01021f0b030a02031c030608030909010b16080a0302030f31030507080f04050a0801020405150c03090306190f051603 73
    0x200c0c074200da4400908005404240403111141c810188104040080c08486030941e8907070008003507910501c140c5800307400510229002011081914101c410b41d01c20061a0014540c0e681c034242d0001e4580e0340d599407094100740085d58001c01e0400c1c458000f40000e0000100b14117244104030080388203c0f40164681000c10010703201002501c1744c0542c0107040c4c400c800c0d2148a000212900003046500081c1442400562224040300f15011081d020341002c940b60308002156007203612210b0f03076040d14a4040301140100f2014030140c1031f003010a030740150f43ca04112822450f20000501550b0401803c02c0e100c80010520175000c2c501e4120144054900c8412802c00fa2002d010b0440050800c2d440002c900c036883e0213690007081940d40440d1859002070700c0e0080f40d4200e00a50080941010a41d84401c4040341c424020740b44081d4003400716454660f030b860219081c0001940e59a000c0b0051014414082119004044402038510420019803505141d04480301194003403c2007415036030042c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 925369712 1250 925368462 925368467
    0xa050d3e04262a030c010804080a030e0a0f0305030609010518010509130501021206030f0f1b0a150819110d0c021606020d02060f0105060304020f010315180b1507080901 74
    0x1c100c00d940414000f04800d0b0096881002c0d41c030040c1c00c1ca03110f0300640d49107051940c0070b410a2401160080c8044d428031113041000d500a1903560b800b56464450021540b0004650401d0214181e20130b60799592241000024084c254106030005403086d0080d81284003103014034008181199022100c2618903110b4502e040d0352a20311140c068201d5000080c2104150402514980254070603021a42100c3c071440c0e100303407103040708100700074940c1210b4100c0100190030742207802864002021030225541d2100a49560813070b580d100230210b10341c0010814040d82904e2560301c8003d4034001071013045000c28000703006224800410410a544041c0b003d5440e108102d011182d03e845102005071944581000e13642d0b07409d40440c0303401845842c000404e01c00480c0c40950417a08007820701421525035500304a000f2850204480c1010b03a80c000800d090000520842c2c01040100102164800154015000c0d900c0e1364414901404000b80a10a5515000c044807515a004214a612420010b004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 925370962 1250 925369712 925369723
    0x8160804080d0603052109010801062708010b03072c130602040f0e0a0b31020a0c02040b060a0e090405011b031e0504080a050d3e0426 59
    0xd2590b0510b8850044108140020000710403900d078014028807041c0300e40300311443e214600740039000807040401040014001e911810325a2009031400011440440c03c0b000f0040b05a844502146e444400c940c405084c10311642000d41450190250103666401c441d22805020440390700713185110304005102843c0c480c3c2e098035020f5012409641c0c039030740c5210f009080c0c0e03014021015002c040501080c1e106801d4841e042c049000034082954240b141050b240c105040d00c0c41038084002e8440701e410000d42e040c40105420803d80d203490b0040d40107401840b04545500125500a100801812038866000381c02074446080440b102c0540341d659281c8140540080e02c100300c0c00503144c0000318102134040d00200e03502d070104c1092600010300c80f00010701b550300075900505009410819468000e00c00c80c000c0140b80648800844c02a958025280b07030002600300391140792014404070f20703581014000070324061680c0a1402e080c00d05107640a640801210074000d03244407088654028000306214 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 925372212 1250 925370962 925370977
    0x61924030e03040608070206012102060a110d03150503070f05060a1403010e0f09031c1d060408030103020a080f0309040b0a15080405010605060f1206011b050109060c0816080408 78
    0x1030b40d4840356a141c0180001406580310b00240c055a400881c92050410105942558010011222401c0e54003480225400f40521804000030100004070b0980c0c00c10140348450043c1c0d40000303041030401115a90f00807a0b8000e036100b600300f404208a010b26180c3c40209603202107807041d9450300030503425100603c24160b407402002d0007100003e020b41341c440381d1921483c282601e226942d0707a410303a125243d2003000c1c82e9118551081c1882145500c440d448841050306940e14442102c8100740751518100040720216113a0000000600c2141441d441010041104000030001207a00c0f1118503203038010440d0a41c002c40d0742d62522003c076980d0003400e200400240544401c070042ca41c5c4003d00145080ba01969103608140000441d400c2070000c0700e4500010181071070411800544a02840002422440c10000f90300c8113842010036900000d1a403a03ca0400020300c0d415038030340082035039005c18050080c030184504011800c207035216100002400b0307207002081e40d61356142280090040c5038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 925373462 1250 925372212 925372241
    0x1109220302030d05010b07030219020a0f0b03190c14030a090b090c0f03191e0618030f020c06041e1a13051905100903021806192403 58
    0x15060080c190084020040840e070303500107021981e29aa4108018410a600100140d11a4015442100e00300d800440c070148010403001ea5150f890500b103a10160a403c520003205000050100001072958580035032030498009000079100b100004d4114800d4400080c154000000020144000b036071114842551080304400107003007940c0004d60361654034801500480c208440400706180000b2408a0f6031000c804810b00411180d8071a044003038240403040c400850440e0380340000d804c0780684440700c03458030b42c1c140c49079803d0301f4020b10305020300c2d01110542d04021046013880d02c0ba0811541a5061001200c2081c41c00645070902c1c6050b5a2010881e010300502d00018400399070024280c8014002071060312585030b0040049002000c214440460301010701080b40e4104400c0744002218113007460314180d540c0760085216098072a1040780c40900d12001c008062a241c00c14004841d000ca00290110341061903821841d50003000000c90b804003c204031011074425085180d0441016 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 925374712 1250 925373462 925373521
    0x60305100b0415031e090203150103200a0f060c0c090506010807050f130315060614070f080d020406050d0c050715020c07080708010e0105240123160c080a1109 70
    0x100340322001001b00c450120302c43e009041c01c131a2040c3c1454041c17070599802200c181d00c01066488889120403c5281c072a40213a80450005520704125083c0c80c0204415211044103030b58070324242000101c071780c0200681c1c43c9000103000160f68015004c650080490801d03d5031148204c0d04203141d030042418a074000c1070039503804010030498a0070104441d00450040c080e075612344400b0389032090000c4c1c00c480300342c00034414040454860309210203800e00810800b03141001e458814426030744103401500c0420341c009040c031114400c61013090401c0c0c07124602203044c56030541e581c491718500141015040d94000c03501c40c01100e0301344041070080c442036084900e484c1da00c1d10b02d28081d003031940d43c0b44407130b503e4040010300603000c11b034183c2e4004100071001c0a0707120106006461076442c9100095031410070000d086214290741000341000d9100a8201111030703c50701e000101104180c021241079006402418001203400c110b8103d2450304036032070291940e41544001c12412003070002d40340550302 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 925375962 1250 925374712 925374761
    0x11040912030608012712090e01171e030304200303180a090606120c050d0603030c0203010b0103021c0506120a151a0a090209040e100204060305100b041503 68
    0x2591182c811100204000c0c0443d20f030803084e88400444480c4007140c9030007106605000035180c81c1008a8041641c00d0081c12a916410003850500003604240d000c03c84030024203034030740410894030025204e121020700b080b24040100360340364080070b0001810441a4840810b60a00700d01c0d0040544101030110703a02c9112900a182c00d0440c4840400d0188032907c401041c40c42603406903c0c15a2107503120703941404509000b100041072a0072111040000c20700c80e90b007410710315000d52002940079a1b24010804143d00400d42103030821100d05061620400c07a01c2e500d14010001c0006000406000184541d55540815142030b080b4180c035071540103806c200e00402c200c00200700345c900c0326003e003000003428170500d40036001054002c5035481014080c08121002075030300200b020710303409400402d80e0340050300400d00d440311401c507402200b074000c202803200c0b5500d03120312031703210804c04445c000c8241f50500f0181640700d039000781c0b0001c0500c9588100351500a0f00302c0c4056803c2c00000c400c003080e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 925377212 1250 925375962 925375967
    0xe06090c0a140a03080310150e130c020601140f03120301170a0201050706050402030118054909031e150e0606040e1009050c0a060f02030711040912 65
    0x52000c22032089106940200390018040e280b02c00c001c1d00900101ca40d28210f0f160321020760001007035420f55540d4942c010a00e48070840408036021110744804035408150010014403800d50600e82e111203140414450740036500140742d6046480d09520801c01d1000f00300415542000d001045406214141c4030851048042d00214100c1d01a0320780d034094804592699900ea0401c0e64002e40040c506000d45804245558440c581051004000007802d004803185006203e0000c1e40035102078000c0c1105e01849407488022132030300890b815504d510040f28004505441518074401c4412490f281c4292818500920100300070b103410400c3d00e501201c03082a4a091641100000c4428080206c941002550a80181e5101d030080d200640244d41e42c107802e2000030304540043d0368903441032302103041000515108010489014030041c3c1030900310202400700e83c4483d82d2007072082190803001010036542c00f1003558281c990040904410404840020300036009141b4007820024403ca03110300b5064 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 925378462 1250 925377212 925377223
    0x3030907080f06010602061b040510020c09091501030b0411060412170a1e27030605010e04080d0b0310110c01060e0c0904020d110423060a0f0f030e0609 67
    0x80d94942218810490103082c151114020300c680c01c05688070b8408540e10f03244880c6101c40b071200c003410b040d0920b81d54200240f00000c01b00404c0700942c000031a03212050078100c0038191b208580f04020010307141c1c44921811075100511028211005400104003045401c0980c106c1480008001075101c40d110301c50f504581c1441482102c8045100701c482003202c01074030075a0b600310100c0d1103002400c0c00740c141d10fa0301440b07401c00c8041081103228250a01031000e59141c14500c08030b2006500442c29490f0110896506821018911005034100800a03400e60122515418001008540c000303600011070300d032005a020766914117080a101102e9202d07032402070007100d608240244144d40e41e030040000c1c840015201e0390340100e810012070764581400e40050070b80001c2a600021601d8108000f056190800e03081840031200c0d400018101500b05600c0c1182e401088464501c0c2c00e90000c009072034280e40341035510901000c6001c00c09494041d51002d920f2540900030340b45240b1f4070019454541 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 925379712 1250 925378462 925378469
    0x10e0d020d241503030f090801050c0408120403080f0c0c1c120c020f150f0d0c020f0606091b070605010f0f06030603020609010c0213060b03070e01020114060f0a030503030907 77
    0x103190910b603003002a111800780043d0400030003520050641103440485d0a660510300e01010302c0402034001070b60703079000d10606100d44001d200341c0c0e89450503c0030351800c2400018038180034500038482480850620022503140b03031540014180d440c0c1200405500380120721058640c840042d00790304404002d10104d12030014800c1c10180000224000f080c0c41031480c0e41400f9421540f0701e140d821150074843c0381001035200c410b200d2402d249080c51813800581c0030261700c07000c440d1201d80c005d1a00341c0401a52590302d074840040c21052400b480450307040f0b13800610340b8640c025030004211f0408009422508060b41101c420300c0030f0342e128500c0340c0c00c40300c640c881c0e401c0e8140b03141000560301e0310034803401c4160307503005105c0744c640500a001155030641111007070340e02c07110180c200c1c040105644103100042002240c09030b2a1710700843d000d0004480d03910194196414000030720300300c507003040181c1d070720003000c6030100303c078203c0c2c10003240604800d41c10081813440000144200240b000071240200c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 925380962 1250 925379712 925379753
    0x2131212080f07090e09030c0a0c03050c062706070813030c150503010b09030c0315011401030b060a030509010213030b040b0702070806190207062d0b030c010e0d020d 73
    0x54032102c1c8064030b0044111002000600c102c03c007406540040c0101c6500000c220341121b043c0900d8607917460500001030011542e20600c0b08040080000c10b1000d030341d050030304030390003410b020700081c21103400c8a484074038849501130300318400810394600054820003038021301444d407100440e90443c0304103515400241e403494800c180c0002e2132411aa1507039034540b000c0e42c810b17046910341000110160003041e20103a0600490082604585081001c0d4481a0070042040c0e4a075241a16500f07a00343c21007000d82c105400c00032030084680350042164494140b91600080325600e420704540203010346101c80120303a04204000061069212441e03000f2070207400011443d8550840a070f968004911402c0c0f5a5088080016030b981c0e502d00180b189108107510241c60603174542d440c002143d602c0100d105200c06003012481023588002e0b108a50011130580400041c1d02502c00243c0c0d85c001c84140784d040011080c00ca0b8425280c0c45020004568007508102d60128989002d111034070014200c080f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 925382212 1250 925380962 925380977
    0xf1c02070f021527040b300c0d0b040f0219081203040507030b070504030203030d1b0306050915061b1e1c050a2309030d0306050303040902131212 64
    0x43c1c4071a000201c0380a03166103644038000d0040141418400c580e601c8070b0a070720036078681c3d844d03180b0b88983c2c0c040760380c040490644084511414039041d0390101c0d018501d9a0f00d61024100d5405600e0310160300c4441604003030010595034541c0343c946030301090301700006d400c070f00380c03d00301c000030070250340024180c48100040c0d4101e0b08845001344980e0108a50280c11503214403010801303d41d030940c01a81110715894060f01e45916600801d00c0d580c030982503540314640c0c483e02d540f0300d02c003118070b000f500507894a401d100d080d140900040081c44050042c0751500100c804c502456940c400443d181403080d001c1e00031079996101382c50b98651218883c15603002e80803090415140c4004213107021000e8101c03400e4031088940001c211020f401401e6208180036001088a80c45541250032aa95070500d0342040d6a0710714200c20300d402c19142046080505040c604240025034020080e0303804e44030714240058844846002c940780080c40e0340d108030504113050301500d082c4603e01140280c201d44540340c691 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 925383462 1250 925382212 925382239
    0x807060207090b06090609150c032a060403030507180b210f010b0313140a0302160f0909060624090e04240f0c020303090d03060b0f1c02070f02 63
    0x80036600003290055000e00100444449031600d44060b07c40800080c21506149074a0904103c0d12303845440420541d52020801c40c4901223800350038180704410240c27042d241f10b002001140d96210141005051649a0780064a045d1040f8803000c0c9403202445202c3da26547c48420000941c006030f83c0c0c0c0c010341c40010a0640300e45440a4080c0a103582648100c0660300e0007040e0707492500042d09810001c1c41415103000800c2100240c10702079101c08025005600091501901c0e0443c0c0892000b0010f8800400b00705540005030107500b03e544c5504040350007045480c1080041040390810a0481d0100501640300607543d4108444c442094540665a544540488601c2142264001d1000c0d400a0244441d030000032142c01041046d8000801c05005890304000bc0d00c2900d140000103a01c08010024440c50030000c0c00000700d0a0305040114506113070050499204031845a4158a070015030b0784428207440004c6200c24507a1042152104050300c0e00e039600702c5500310140d00c0344106c8008070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 925384712 1250 925383462 925383479
    0x215070c17060c0a05070501110403060b0a140a033f14040f0302060a0306080d0c17040303142d2106011b0503070602031305060108071511160807060207 67
    0x101c1c014038080e00b00a04000ca45030b4215451b50080100303d401d9503d980c101e02103440084054001b0398440d0328089603400080c13043c041c8803e5940d0010b001104600d82d402c03226125858508152904004040410304d018010b004080d4170042d9207086543d45003150103000b0703800600c1c40e40c45100a94820280810510300d502c00390243e400b0303d01c1c2d40050040b042005150074002000c07107443c1c90401007851a0b9500540d401c01401c1d484841c04200504000c800700001c0e0124000200d0302003030031600701421600c006186003000141c0038400b400c002298001e1105074640d054035600204112421010004031008141c1c00244041c80194070790190b256000c002100a1441440180e41d0014003642d9003072280c600c840e00c0041551a070100300890350110300b07175000640c490303074074803840f2184403119141852801070141e1202d01c6903049004140100790105180c0040300c07201c3d1a00c400d80c20354442902d8208a1080b9400341e40940700c1c680094060000b2419004940003602900d201d5a51603d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 925385962 1250 925384712 925384723
    0x16111212090a051f0b1302030105190e0a020c0f0f0a0c060f0f030b04090b2a030c091011011812021906020c010902030703030309050c040e0c04090215070c17 69
    0x10040d420240d200300c00c2642c80443d0016080d9034007000314902c105c031008070b00342860206102e00c00540000c0140401e0503c0440c4528113215100c4002015250200e15110502d002d4004490207030001842002002c00f002a0540d501c900b40a403000d1500564909540710000313203049174801003400c0d0000b20140151055002101a030b1260000d100e25030600b20000c1600740c4503540c1c0940c1c0c80607008042034001d600c0c41c1c855205000925450282e824605c00701d5012003132030b00d01050040080001c2d82c0a0f070415160351107025525004158a000001c0e540c03401c0c942000c21080d80392005001120183e80d114600c140d01031007501050040800b03003262541c0d50198102154140d00181000040442c0d00809040030200000200b460746603000034105000c1e903205500082e19007078a0000c1c40b50900014410441c01c41d42002000c03002d143d01034031244806601c5205030341c2d0350701180954841d000700d034440808003c04556107000c0d41c9817420416015004030b0320402010b181a44503000009030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 925387212 1250 925385962 925385983
    0x10909050106090c0c060c090f03141b0105221703030f0c130b0f210a06120b04080d1b03090c150804021e090c0702130507081611121209 60
    0x81c1c8002011750354885202801c00707050705104004070141e001506078015070342503020318032070740403901e002c5030b011591031500d06045408400d07201400801e582603a0803030110f03031740d07440003600c15661494490346881c40510981c0c00000b02044d25980040501b00c00702c0218400d0b21a028000b009850320034101c00c15000740349100b07542800c0c48a0910034041c81d0b41c05414600e000c404100d1515049910242595500e1428504081d10b0348c020b103e98521980510320241c801e0441080082c51203441d1420307007100242c0050300d0f42c1c0c000030350303000c203002c0a411840240c02259030110b0100714004004004040c08601510244122034021810428020050b2014030300c683e036060f6661110340801030140309001180140c01200b0300d0121442e11808a8103110b44114041203031202c0842c01480030030810000b110401528000400c2045608079510f01d412280084840c00c40032500101a190f60324840303e000800c0c0301d83d0300310309500e100e014028020510800e1800b0915181d08100c0c99071084a81c1c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 925388462 1250 925387212 925387217
    0x130302040f1406120a20100809190302010f0e0705040b030601050d081b0111030a23010303031104030c03060209040605060a08070815090405070602010b1e0607110603010909050106090c 81
    0x4141d01346000b00004000701070740e1064420b050429604c41514074514032440002c41202607003c826868141c03084140e4441c0d60a0900c1c41d454010002c1d519601642074107013034005042040ca080c980300754040c03012400d81d080b04102c81458840184d965400a100c0c0318440c0d07040c503001400740c0c01d002c166181211006081c8034030303034480c48da104c203660307040000e0304027100320799071048280f26100340140c2c16002c00a8018542da8109007818500f50f0747d4500312550302d520107141d844c3c1501c40d009900d40c11650981380000d0940d0000301843d0b150302c51540701804003600100c010003071058550003880c80b504d08403030400c5050f81c1c031402d0206034018441c1c5003020401c000d000560f5540220b02d45684914040381c07103150f15043c4000034410f018241e9040d290b5074080c0c1400e2121a409100308040c804d4222085e064801049900070a01480f10460501440020402104000c10f46900d6081c0c42d80041401d6204d603120008000100400d40d8155125800d042d800a8180c019200e02e0038803150a9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 925389712 1250 925388462 925388501
    0x221e051b06040b04092013141804030f140c0313060c03090303141c0e0606010311040303030f0b0603390d0b010e040c021006080609061902040308130302040f 69
    0x151004000703060080c03035400241b1110005000c051103240c01800c0318102001100300c440c1c18132207028140c0400c55103050080d900c420030f504015109031109907000c2d41c186000c0c14805580b20301152035002c0004201c04160020030b100c1000c0d0b1012028220642c80030b541c4a940c06d0340d41e03038110781001044901074041003100405201081c414080c51040e048091106490005c6900c01e80c000d510b114074544d182c1d6991202405568601400542e4214809180501411090345c1040c0300e0340c401c910004041c559249440445140503820440c4c10710740040c1603548902d04003642c09a080d000603961704200b5980d00b50a11850440da45200082148220550800c501340b071141e0014805040d1107810300c00c00611a40700e03584d950084134103416280d07025010030300d00c2d50000000d44000360031900c002d4000c0d07800c001c80d4150028506621402c034808414424040b074550a00a1280d50800f80c4448800200401d41e0510114000e0840b8400d0f40c003005801ea2488404040360080305020844200f007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 925390962 1250 925389712 925389719
    0x10b01261b04030218041115030c0a12090b040209010e070e0607060e1006210f030e240a140304110126090c04060806221e051b06040b04 60
    0x1c00c089020101510500349241688a40000c0c510000703001488020404074000c100c1000030107503070314400320825546488046a204070b002d0a50000070319039610720784081003080805100c0d081c10b041c0c07106030660802c00c000703950624642d05a0122800e9014920300c000000d22030180d0740303419200305401da0300e1001d8510000100051903001140542d421030b103540c01840021000c4c000e41200c1c900100303000842d5403900c0c450301c1d0451541c0d58060034a29255a2034004034081e18134a0700300c950b05142001c090008000003591046200b07444010300143e4526060380b1900e1040142180101030b00c44d981c1e028541c0b116007480d03200c04ca0f0000c151850b003001c00c65595005181110310011070300300c00100040008503000b4400d1044038031501c1e80c0d000c0008240c80d800c080c0300e0203010303000340780291000d440c0114402944242c0e1000030800352a02c058807909000a0890120000c0d182210001d542d00c8107040c45980c0766141c4400080b018060b0400b00c24a160413401c40e0300b10b0b41d010010905007840c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 925392212 1250 925390962 925390981
    0xe01061406040e0f07050f03090a02030d020d0926070303030e070f0302030c041d01180b0c0909130302190b04170406090303050c100e060403120911100c0203010c02010b0126 76
    0x4015005c1c10500c5024410b281204503600007442c402c180303040c0145074480250042501d40000c2c0c5200390290f4201c0d41d0120744a80d07001000c070059440d135000811443d00150304010300d4404012a07941c9030302450344c010003019815004005030312004004c070340c5044e85409a6004031044c0c4c0c40025415408800841d2640c240f540001e8501c0c0c078030140708260044400c1d282e500f5503408400c0c0d00700d40040c0008841c1004005035807140c12200d0411401d0601200b0b00200d8081107004d052410043d42c038800c150b0400d4070801050340e40107100881e901080d0071928003050300a40648048a20340040c1c402461400301103803e5400b00c40c1d007982c640c004140f660f1800c4d66154003508021865000c0caa205c2484280d00340600110001010020465442e107420000d080b10554642d4041450424522002290b0084880007040d241100d6000c807030761202d9003d03902004400d00088d015400c00f078003821040d4040d401024010003c3e207440744107170201c0d48903c2030004641940103131188035a007c00c01154 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 925393462 1250 925392212 925392241
    0x21c050f0618070c1b0603060e0c0318030f070c140f1315050306041a0a020c070605160204050901050a0e060402130b1206162a0b190e01061406040e 65
    0x280c00d081c5030301246985d44804002c100307140740c10601040c65480800c030066141c41200002c065450603640f450420300c558440c40c0c8400b23000580c4c0c9450780984052070000074011a4001d80c014000590758003807034900074841e00524451014100c1c6840c60318059810807060710804a030004000f4028800740602c800002c1501c8000761109102d03d80c1c2c0440c0e5070f1820007806010b0740c01950100c0350410f5044c5040b54041e13006080521450040c40302c40780610002031102d00f641c003035080a0b62950fa03000d08075980300c040300070040d620900344000d204038503806521007401100240320031f00213640c00c10541c0303a403400141d40007504100a000e07000da0a880035413200f449840c0040484240c542d402c42d8241c5021819125130014121442100024039000350644628000b1101c0d40100c80310134140544c00386400e844043d29040900300016544580c500081d2114a02210204014046078074414028441e900950400400c0410034102ca0700d00041600d0495840c601c1b84899940c1e10a280f00100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 925394712 1250 925393462 925393471
    0xc1106060405091e0a060c02070303050720060d060608010f290403170a09050d08030a0f0b03030408060f0703090c09020a170103060506030706110705061309021c050f0618 75
    0x6020340704840511308840c942d242c040000100c002d055100f420304104084030081380c880c0d0250b50000e602000000c1d00881035400c1240c01c221882c081c1150b00d803040090b50203000c00282d001000158000c00004542d00100c1928407035501c410241e0b80303c9095440b012041e00071034201403040c080d445907012070034640700d90202e20100c807582069a2640c8000d010140001c1c80f031817038000868204402648000a54000e0804440100f104c001c5519005010301c03020f000d049100344c881040c654001d01130341001c40c800002904807550350f40c2d01c105068581ca029101031103078820b4840070500e118428080e41e640680c0000b0003803122032a082d0207a000790700496500040c05195072402c1100080d40080074001e42c01010007040328500001094100100390700042c0c14810105034584104400050101c140c0f402524001d50311080710f2842140c0340815405580500d00000c2e00c24503140d0032040c1b11200c840507007020310064448180002c1d203080d040b5880781d041251120940f03990030261100a810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 925395962 1250 925394712 925394731
    0x80a080d06090c0914030d1b0204060f1d060f060a0c031812030219051c17010303020c0306070e09060d0206070b070207061b17030c041d06040c1106060405 68
    0x990b81e500c0300541942c2400c00c1d0350003c01c1680f0010400389401108001110108901802006450080207419107642926401c00c8030171548040003103440c6c2d035000001800824007064001d40e9211644040794232401a08040e800c42100440e0180c01c00c030445050404005101d10300b800800740e070072039900b003070401f080c0c0402c01664151500701500300c0e11800508601138444802d141c0703900300a4513140c100c00d60550304684402c00140454800308010741111491003051003180c180100131214001615a54034000a21070b0001042540011b424640040140d081c2c1d9000da860120640c6c0e96446203105642204514000030300c2c510b0142c0440c2516480101241d040607140d40300c485400304112280d00150b44400c1c8180300c1290021844070703c01ca118942e0600d0100a65503d044540070301024503d0004044041220400642c4c01d135000b8040314540004000c50001a600700c2c0041602e10034000c51500032020071540c482c001c1c1d84000781103940182107580b558002d0000a00b00100781840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 925397212 1250 925395962 925395971
    0x80a090902030a02190219150603021e2e1b050a0b3c0a0b0306150a0905090d0f140c01061a0301060206040f06140702061006020304080a080d 62
    0x289400d107403014500420001800588a0031141c0d2412481400030080900703651058031003004007080c4083c4c9492243e8001e07402000f010440c42e010000d8142904004c0d4001203041001e40804502140e44c0300c0701904480b4140c0d0391540100c48032281d4003901d02c0d480c18075124028159818002c80b100f07800c1844038903134980d140d052503c980d42440701301e01080700d1041c1200c060118200d80c0d2503001c04116200360100301449170002e000c840c0c0400700f5010704241089040050204c1949510122606001a06850103445c094911201a0154400c0e042c8150542400442d81904910601e48166050350043c270615034140c20035207600030003140e04402c00a0094801d008900183d0240400744850760001c03d041c0d081c0044a5401826401501c11040703081c00104105940045c10300c2c0c0054100e582c600f800f02b01c500f40b0304040c05161b05011050034281007881142036002922030b00c602e1110700080320160b11380c47c04030b89030311440c410706200364400c1e00e2010109100d0030041041c4c684c00000040d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 925398462 1250 925397212 925397219
    0x307050a06050c0d02010501080c090613090f031218020f0d021e01030f0e0d1b0b04030903020102060708060901060e0103150609360e0c04110316030e0a080a09 70
    0x6811000e41d4001c0d100080001c54058001a010059068030400c580006e025035810084820794800400b030780e2074441c10b00000413402c0c0d0b480f002c02d10a0341d0080c040c01409141e25a050030100601c07810822400500700c0f020046807243d0a21522594291250203450000d60a408201e807041c0074040c201d0340464503803074a00040c1d03200c0170a001c1d03907a0803820919615191800240440c1c011032814121103040182c00c2c0284c50010410300703040030690512810300000d28101900006000b07000801420030700003403006264004100341c0c11a4801d0703084908580d034081c000c5518010960300c65800c0807000c001400254000d10079258074070810715001516681846020313200e400e0131f9111402244040e03200b8003840d21b500b1401002c6070307518156410b001b8040c2d103030501888407540d51007104d82e540d04403040c0d6480b0240074080302054000c10900c20160641641c0c0590b80c01603d100992050701d60300c0307255845c040e004081c1c103680358801030118201c043c0c03642a05540b04d29005810000304a1010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 925399712 1250 925398462 925398469
    0x50a020c1c09080a020d03050a051606060e0109021e0c011104120221072105060a05010e100305070e0703020c06160f090509062e080a15120b06030705 66
    0x215400011034021201801c580102038507051681c3c1203250180c0000e86604007603114030702c80000c0c45515242072640c6080100d01190345004940c6642c031101c01c0e03411000c082c4002c64100c58107030744e81d030720b02625980d0369002071004a01c00d500000000b802d401c251010100b00120280c017814051078004200080903030b2203a40719034016040001e840f59003010f2041503040014540030600c604451340c114080c2140c4526580e003010703205002b0f501e446e003240b165400003001007510510303500c03070110b030f02c1824184003131800340c1002d000b454649030400c2c0002d151b5485900710502100d402c2006000d40900700320400c1c601a00c01085213007416002c1040076400201084207502c58000b0030b001103080c0c3c411460041066814412a2080121036541400159564a82c5907004082143d00c040402c0e20b51103101200f010501300c0a603a001d810003c50100c0c0d803c0f0341840d20500c02078a0030030500d0072801480c454202e05004840242004003403000004041031540c1e500604020b0846051681c5c50000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 925400962 1250 925399712 925399723
    0x40903021519090c0825270509030c010b0604050105040504050c0405120706170f010b13090c320a050705010908071a06040528020d020f27090604050a020c 68
    0x4031102107001404104100f011b0051080c2d00c25801c0075880895140408040c1c03800301401a030702400200c0005100644c0748101c2c40720b400d43e003c1070a00243c90041da5042e240c5d0080f00750700b0215402c0078690341640c03801d07a0441d42520300503100e00b0b00705410a03003484000e00c00280a412818010003000c2501e03604d21400c0b00010400c80000c3c6100d0303081100040880615a6062410b4803415040c44506541ca01e10141524080107015481e010b02820300000303a10164460300126181c075200c50040c952010604c804040b4000e0340341c3c2070380040c100104070894000326100000341c05003d4040130a126000501405001e4000032404000940316588164800c0004440300f03100d0010040315107030640d6011380c1c042ca044804110310b103001720000b9009608910440b607a80b030702d05e03d10b080030a2981c1c142c56140d0744a0310215141d101028180500358020107c4d81c0144020f0038411440c0003002c0d003002a200381c0605280e401e0384601d01480003070040034103040340311a020b00c5000c40a0408000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 925402212 1250 925400962 925400981
    0xf0117010905480f0f0d0308150a0815092b030f020705060406050603011d030a030e0f0a030e0402041d16030c080f060a030827040903021519 62
    0x10000c1d0f400300345440082209a41d03802c681c2d24050354583c040588070b54030f0701c240c81c04803e60704500340810003400070344c5031046030410a80c01503800404405055006203031500c501031400701140c404015004002d034051032440750403d65030004080c2d003031524481c2003142d08141c43c441281c0d0fa0400303000c030480a0948030a04140d03104207580b908009260f060107402c031080b11442007145070464540b256511100020006044d07562100040f50481d1000d500c400c0c82100003411446041e120542081c0d201e501c0b40d501709000074204003041e40c90180129011a8420700c0381c00070800e81520303030f405a40301a05680c41070762250f400c1c0400650040520340040400c20300860030210342c90001d00c1981c00c0e203544040341040600d851840e48985030041061500803c0c504070240640d500d09002480b0380040380c00c000e10092000c0b030f80c1c01c4401c0c144010000d00010f04503d00b04c00c1c540b0602400212444a500034006034480250211800d036424001500100c020300d110544c42c8081c41200c05842d85c0c42c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 925403462 1250 925402212 925402243
    0x2c0309030d050307200606010f050904090c0305010b010e030714041b020a03110316110402040807150207120c05060d060806010605090f040603020f1306091107050f060f0117010905 79
    0x10800600941c810301d00c28070b540c0017000d1000b4954515081c183d8840300280114140155110540c4516008000341e400c0c0500003401440895480d00c0c0000701c04145100440304c0e503003080d802c4a80da40c0507011001c04008082e008000c01c3c1c0c90041048040c82c00c0c591100d420035a10998650048230302038401d0400c4690b038000741158203451400905100c10040b4a145540043c0024410314100d80002c142541e00f120801080340c0700725002500170300c41d0390b00154444c4030380b01c0e00040c685061200b90403905403030340950700095aa60b00d94511103d255000400380c0b000d41000340a14580321000e440b088940d0040000d005440d6040a0f29014003a0018408142d01242e00365840c03400e8020f0454101d819502484142d01d940e002c00c5450b880c0c58107152040020000322001026158020f40c0203000500052226214506903491035900000c0103480c40e00681c20400348264000980d42c0c050004000e1040700e503840c00501704884280b20300740c00059500c403e41417000c1007042000500500c0800d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 925404712 1250 925403462 925403467
    0xb13020604121a0c0a031109040c02071703031509070c2a27020a0c050a080403120f21110c030d05070c11060901171e010503012c0309030d05 62
    0x30304001d85001e19240140108000c07080400540c94803031020785421600c2411b0105120068141c805141d01070040034642052500001103405030f4002810b004071041da4660306401d50107100500c0d100d101c102d481c041800c3c140c0480d1543c42c01d1a814a0b64462010729044405960b15a42c01202d44407100400c0340e4201e0004d40244d441d1001101a00200764045000c1480384090b1811070b00e0034010000d119000b0350104901c0c101c2405160352003140c6030b0142c03c0c2c0380100510300d0201c085070054007040e10300180c112075401c000c900490000000200c50703254601900f0b61440713030281d140300002022a240ea141d1207111240c1d40310101400c8440f607010040d42e1103e2030026404c04a0781c0c000c244c1004c0010590818011910907407404580364002c2d512580e55410a2005845d03502408549c8004030702208100400713600d54121046402c9007120074003400c4d980e18020107003030b241c214095401c1c900c2c84803180030541400e030110181e90030030401501d003007004040000341007502c1140e001b17003c00c070300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 925405962 1250 925404712 925404749
    0x20105060f010e0d02090702010207050607020f0c1804020f060c1b030c0a3b07030f05060303031b07150504050a06150b0a030b0a090606030b1306030f0b13020604 71
    0x281c140050020401c0c42c000c10550704400c006000d490384e141c8064000c0442c1c90110302240d00c01c1d0121110700da040800c4074441c1c1007810300296a8807518030a4245805080e1007801c051030300d540e800851341c08440e03214120b038449808101c3e0100311030840ea84e00c95800c02c964001c05c0b07424402010420100008214003441e070006240c203103c803000c0e03a1403080e1203045090292500c40c07807040500c140e4000100c0c08001800e131140c0003010343d40700341c00e4a88404000b0444c1d8141d05401070640550342101c10320031a1144020715550b4001030ba644000c1c60021082e04d448445a000546046400f410441400142003a8284103d4805881c1511560171214000d02848414001d06007a00003142a4488aa1409151880c41c0c010084140109074460f8014a000c0c0d41d40403035034001d000002c0e010001103948a102030000c12601d81000d0042c0140c0b45001081165885820101c940003000022a00001e54400703040e40c47c024620090202080c00301c0c0301585803603010f04064540d041c1c01c240c08010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 925407212 1250 925405962 925405969
    0x3030f09240518120a02010905150304080a0509220c03060609060315030b0a0603141507111e1609060b0a0f05040e04050106030312021606151e06110d02190201120c02010506 76
    0x180c3c5e0083d074000c00c0814840340c86080c03071742b04495000da000f210b95921000d0100b1b04035464858200700a600c134070010001084980d242d01c1016148030203003800c21001e40138000543c02c0d0b842030320401020a145500c200031947c040c1d00451a00c40c40043d11440d8640c80360b039407a4000d042580c1800c1c1440c3c0d180300c28010440701000c800c1c01d603918400206075115402e40c0d00c070780c4080c1c010080c02c00c100202810842e070040400800b950540d801d8060040c2c012040303100381e5100a0340c0b41c2101e4140305d052000a40010034401c03602907489841da0b151901e001c1079400c0c0c814080a03500b80c01048010403000806120842441d8001c606c500000303e060351030b5080051200301c964052021061040041c0e01e440c00e1440c00310718040343d00100c0450b001d51f071180c541414060590012624035641541c0010305421040410306960300d985a002c8042d100311000b0744d4a400140510700568840006818074203490000c070740805205240c528040708200c9100e03003e84002a03a2800981e4440301802800d16 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 925408462 1250 925407212 925407227
    0x2030412021501210204020c100501120209040f0c080604054219141e0609010b0906070c061e0e15180a03030f09240518120a0201 57
    0xc445200804030101500e00c1406118418400d02c800d002400f070030410240d1349000c10400e0207800500444d21501800040ba84416900d0400c607202c0b40b4150002c590040c001000190054000d0710141c1c2e15134a50ba00c100105100c004240c558480d00000050068000c0040612a51007800640508105000d0280c6d811564420780640e04e2503012010080c0400000719081c030500e80c0b40c10b0748540e162145141d402d0140840807021850500b1590084084814210f40c003c001c1000301d122401081d03000344090300740c1600c007980d01500003c01001640b82000207040f8001005080c1440e2054643c0e903c518280107034401c2011035614410b5400562035541c1825400d56181420fa03128600c040000c0c007c210001c2c1d0490800801240011801500701881262044013a0400703486544a04014004580e100403802c00100140c8001c6142c50141c0050b210a9030710310384400002001070360540c5e01d074002c40940681d0b4003012090300d04d00c1e0b0b583e06986801d5074050020b800c1900c5540001407092 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 925409712 1250 925408462 925408493
    0x515040618050f011d03061003051e150703231509220303061206020309071a041505090306010e0a1503020306040611040923060d0c05100210020d020304 67
    0x544680e00100000e44484150340003c072024646500c14005540004940d2111102070035018494042040350504010142505481c06401110076402c02410095501c0b10b0300608034030780f0340000c040c80b09034014586415400c40100d007030103c0c006413803c0070090b0075420a0320080003000c0410038440e4036085000c45040350a029200003010746040c64420050051a43c440203031300c0c44240d10541450321a0340000c015007000106d6405403110b03800d100000c1c0d04251200c0100e0300407200005840918401c0c407089001204024034100f0346003002260b04503407003440301e03c14081c0030840202595000d02c201d50184c0303000100d4860605001d034010301120000398103440c0c80010702e45c00b4000359038000f0300d0650040d8000340104180c050482d8071405400355500c00480c0038203245000208041010050480d45140000c2180540e180410010341c000542c0b0051309508003410113000504100d15504150007050044070340d5000c0144045003240e0100a519500c5540441800100620072039907132404e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 925410962 1250 925409712 925409747
    0xa0c0b0a0b0d0210030b120a020f062704090203010c1107050312030a0e010e0a0506070e0105091011010b0604240f1b020409020604080d0909020a091a0405150406 71
    0x24038041c10100300800304603640a803142e2601e040d01d1003c03512a410504050102805540c60143d140030215611042203500b07e00c01c1884440c4030303912b41070420960340ca10300f00001c14083c3d1907a549084c18402c0c0000030b5140c2103074403010701101688007400b07403d0140070990703a046e074030180030b084560034001c681d04050300c01d81190404504c00a500d5040d82c0d00b08480303000000d02c0651008400d4010004c84101c08140d000d8840c0260500c28003085080c03085c0309a840340c01da4807505000450309445907a031030990003003d11000d5114940300ea00302d40b469680c442c2c00010035080b51000581c19800540c081d0149607041c102c40c1c60341242080c1d85105012490400c16842109840e014000800c1e07140b5102201c4000130144040d5965500708403161900035141e1903a0350740394a00395868908024406000c281c070310f00005241440c80c4201c41c0469542e58501e400c55040841007642c03410031041c001d014610500c00401c2e00d613542c01c4008800a43c1d170071201d139554a842d5014128840300401d4440e07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 925412212 1250 925410962 925410971
    0x507090501020c0f0409230607090303090e0a0b190f051008040b07020a080307030e01150b370206090f0105090a08090112060f320d080d020a0c0b0a 65
    0x21641c00242c452a01c80c404c43d0700e00f00141040c0301141c018003004034042c002052100d601300c0700c00441d9080070b911001d00015035009590700f04040c0c5200c0c08c1480000e00040c1d0070942000107907225501c0c039401c40d080c0103022034503585205c001240b4910454201c4007980305060100107c107040e012150040c0703000d89070707803010074282c401c00391003160011310140191294400041443d442444000485070744000c04603140c2c200004018014518030304c04242540c80c10b80c040d0a50844e2003626811239082c802c40610f0811807280c082020720300b8422030b241d82c01c04c400d820b03504115111800d200d9448150300030280340ca0500c0c586850401c0403100108182d00d40814010350b15000702d40e07008000d4120003440e030f0300e84404004881e0f80d130001c040c5a64a42c6003a101090030380d210250681100c00b284082904200429000d070307203040c08801c00306490300c0c100038008102d00b4035011200c445800340c100c19060015400e00003040ea40701c501031900062514001d01c0810811201480d04810750100402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 925413462 1250 925412212 925412219
    0x220906080c180c070c1805180a120f0e0a0315061e0e1e09010603050c18180c030307121b0818190e090f01020f1c060909110301050709 59
    0x42d1200000b40c001c0014080004c1c1080034403941282a0b4010403141780c400070a4598408514001e002c141e603480428aa400c040962910000a00488090700f18881c440c0b2440c403400180c580041035003100041c0011000e20420590700e05a03504025030040004a00000030482d00030100c03040c60700711034440550041001c0c040e40a03501d0500c1600c0302c0e00d840160030703158600b01002409400c15040b1005006000f0029101011b410800469100c0e83c122680201c2403010400341141c0540301e0200b00b10540006032600e4106140103900d141c1c0036068070a0642044017103411580a01e006490b1140c100540c668100d620040c0e9602d0a10043c44810b0402d4603591035814500c982585201d01d004020800005680c41d90f03074a1184190703515424111654484460543c0042181c500300a401441c3d8a140b41001c18001c40c0d98505000d03442c4c030f1401549d0b0b003812076190081008109056a61000852601850311031480d182d401900603c607442c02090030542900d500426190801402e080c080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 925414712 1250 925413462 925413499
    0x180f0e160312030213171e1c140a1809060e15060406050702040902150a020106090b311407120c11071703091c0506090f03030408220906080c 62
    0xc1d1486c18554a030b801e00d1020700c891074440018001c0e01402400e541860208030009411420b8089072001e00c02c0843c07000d03100790b904002489004100b00e104200086000f0f02c40d50700c0709900500d0b60428448944c46180031001c48416410101038400d050703050000002150415105051084441600d01414148024418011450001e0203107440360240000c40d51009209680d030410030710b40644400580d40028043c01003407103100d200034900118a0310b40e007070200303005401814042040f082d103203802c40d618a949030880380c0c54800d650782e904032800f810181c0441e0381c082c1d001542c40007c800d2003907203140100c40c0c0c11024001801469590603181c2c0001088100442d1000001045103289a40c105820f504c40c1c120720983c01525900042c4c181d4540b040d185101b180114202e628036662440b0440d038442d650240d0083c4ca40c01070000400003400c2000816500d08100d051240c801c4002100302101c80d4180c00508095484030014420340300d003000005000b29017120303810164901e980c0d01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 925415962 1250 925414712 925414747
    0x5120c090303040e1302040c0807030c030603020306060105090d1506050a060c12080c070812041a091c0908160e1f1809051b030610180f0e1603120302 66
    0x1055060001072000a416620503840172a40507001f0b8030034004804c0b41d2000803c1e00c003040703c0a501184c6440d04c00c1901d28401d1180d00150781c1d01400a250549401d401074907540c111484196001014401550005203c9440b140010804000c04184e039130910040190f4404180c03c18001c20543c1c0022a01082e02080241c10040b558184840c090711000c08001407031140d44000342640f50005285c00241c40f042c018a440b980c001c07480c0341c11510b8491400c1000c5070043c0c0d0310000552000328211510003503550310900342e865606102200710b50360001c2c64200b540009070310b080402c850b1010443c00c2c1c6901d103116071040c8051a440d400210900c40c01c00700c01c58501a0542c85021604001c0c2d00c1e484035404100455001812070f80881d2144546c407040403081c003d114040e014050101e201101e5505541c0300f6142041d03100f50a03143d4810780709000700300300540e100032580c4454803a850f51800b44240f489149200c2c06141c0d0103402e60404c01c00700341d4213001c00c0003010300c100450700c1c500a64092 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 925417212 1250 925415962 925415969
    0x90c070308041110080f0114130209040204210b0f07230c06010803070309062a02030a120e1e090402060a030b0301020f0712080106200f01050705120c09030304 70
    0x10078844549403801c0c0600260ba03012003140c3c0050400c101c819546802180c094400c1e07000404010003aa20703003d00c06030420a000740c094001304100c00201030390005801410740c0801c098401030405a07511364070b10700b203d20340d6040c001043c07010f4040d40a20600f002c4550b8072600d0076610034040d00700444014130704600f0311801d45000c840700303000309aa00e045200f02e54188008104032003c0796101c1603680e40b241e10126080340415601c100028450f030140c8491418020030031464181030341c1c80102d02a50f078035451402c0341d150040700204070004001504c010281c003103c0e92181d441c120f041c002c2c02000c1c8440103502c0c80d00003010000c0030142c2d55880903507034031540c1510380356210302c0400c2041e1f028004403070440b50700d94000f145483c100d28205010301401c60040400360850800c1100544580e46c00b8020074002510750003c1c0c500c1d0080310b800320305078680002d04071950715494202450071074400f659410000b41002803205940944106080e81000b41502c0b024640340785100000d03030b2813140f4071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 925418462 1250 925417212 925417217
    0xe032e0c030b030303010608070f08040b0703111603120e07050603060f010513180f2c030f0409020d063c030b1e0117030706090606050a23090c0703 65
    0xc158140c0c0c18481c1d0412081da0b10083e0031a03440e540c503000080c0000d42d0407070701e800014a0380d000529a95100c1d041c0d0350f0155800001c80080d58840100c1100a0411300c0c1044c484a2002c22003030113600094043d50144a019a56100740704010074070f05010784080d0000008944d00075039040c0180d030350f148100c98000300129a454084581040141e48034050303000340884c589081b240000d20300030850345c10000b0303c5030390800304000640f1401c2c803400c990350703031218100794211451502101042400740c07041c090b9031602100d040120855492034030380d2241e007010741c0351030700071408000c0d07000d141c000e1501400c0f10195024100750b1198041c99080007010203078450582200c01d000201000382d540c000a1508080716003014500090143d00803485811554402442200006244140501c0707540d1141032440146d460401c4946a00014207410042a42c445588000000d4035070365256000004080c461260380c0c0d1105c0010804059843c0030014070b000f107200000304a0342035001000c6030003640c3d250 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 925419712 1250 925418462 925418471
    0x7030e09060d120e090a020a0206070c021f020109150615140d110a0818070501140c0604051606090605040905130203060a0b091e070f020c040c0e032e 66
    0x18006080c19502c400058110790040f00544090742d0f118480c0c000c2480e090f900c2c1a040c0e140e4030020801c80c86888928401038004d61b010543c07440c4503400310032415000424000368078400c46182c403000f410100310036003d40e64030b0307900c0410404040c681c034031200e0701c000c0108070300e40c0703001400c40d110300c480040c040800a04492080304051041c043e40c2610514602c20056500c0459012400758030480826010543c200001464040d00c103010300f42100c0c1150140c521146030000550b02403120454059030300c1414000410703444420041c7c184602d004500074001c5020901c6c1d804000900740e040001007004600c03052143d00c0d0810100c03000ca9541e0000084c003a6a0217200000011003510004d52501480c010f00c601c03c0a240c102d1001c0d800c0c00c80b03640140d91515030550b42c0503a4a40c84102900c0c2580700000c2401d402030200318068080c0340141c900c02092680080c3c120340c103803079216003c203008182106050904000001c035034080c3c8078080a848000c03218056481c42001c030311a00141d02c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 925420962 1250 925419712 925419721
    0x20303030a061d01140126240a0b0f0c0106120302240601080103080a02010906110d11281403090709060e13060b061308030d0b03152412010e010506040207030e09 71
    0x56841103504600712940c50009810230f0303d00310711b2000082103076480e10602c03548507036120300d420913541e070450b603032590307000c1c40c01d84030b007004814036000441000140d5507521400030300f8482140c900003800748039901410101903c4101c901400720a1001c002d1048000020414141d8220401c83d0561b6002580e003a181c1c28582400c134003410385002c008007000d051401c01c0c00070845240c05040010003103141440a020308000e2200a400385104001820a80882c1807181c48a645d100c002280303010315183c180c40540700c1481105500c02d41e44600e1690201d14100000d01d0b480c403502d00030f402e20f040c0e1940d01e8144001c1e2070740e80c0101754102905150382d400342c080702d581e105000c881e180c3c15002185944141e035211100d4903500f100320801c19042c1800035085d00c624020411903806a00c4c082c0408843c0c4a010210072082c905004011448040c9107400e89103a443c040f5448240d4094800807a0b41c01d0140703000360030341d9030250619004074018000790300000e0b0051a04410190141e0340e40806555 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 925422212 1250 925420962 925420997
    0xf070207030f0c15181406031b09060a08190903081b13080a020a0e010506070b060d20040b030c130b03010f020a0203030108060c040e0f040f020303030a061d011401 72
    0x120342d8400d1300241441e08280c45255006051503482c51520038844408990740c450f0001c132030031031021071079203c6000c00003d40a01c2c4811801c91005031032000751401e058401010400307e0340202203480104a0134000c0241503e041e5003001050041e0701418011211181c1d4013510a010180600c070704e242e41454604880e14802051764214071151640b40103060351042215100c2c00c107200d050380035005c005000300d440030085e00207504941000c0c050328506203a50301d4440307071848054141c56001541600e040049040422080e070017440360075503803105c11070010400003103810040c901c0c0d00980061a424015540d4105018640301848802203048a02000040d00409c940544213410074030202e10002090341c000301450580e0800b008035019512000c0e4a003005015034401d00c00f80e40d2078100003c3d0400e00720301d0001e4000e84140c1c80c1d14010116903000070b0440c0c10441d02807400c582c1d250020840c080300070308072010782d031440c071350a40d069410494800c003070340142448181400080500d0501401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 925423462 1250 925422212 925422233
    0x15060801120311010c0c152705030d0c110609010e190606152307020307031e060905010225050304090b01181e050612071206050303030a060e0f070207030f 68
    0x24101d0020013a000e4250009003030111b459109441e52206081c06000807041807159131511034540b865000d01000768101881e20380d43d50b203005c9819020030300044d05000300364090f441c1d25050301d4039641c0310724031004122860a100100014180e07818048594504240414648040034240c280010a100c01e030a00c00b000d0001e030f41c0004106824610b031140407135805883c00c00005010071045840e4044003005032410f0142420180d49a003003d0002c000080c1320f103400a058511030b94003c503a9240302d0301c43c541151030b03241c27040c0d80b140d4000450001e2158804144000c0141c0c6040c286882c0000e5184e25a41380200d009100450341c2d9a8080503071a0300640350b011555550141c0c004107540c90359040508800d1544c408010001c00c104040ae9030b28001c1b080c0c0d0400d03950000c0c03c11807560f6404c400c94010710308000001c20613954900214282c0c80501c02181f05102e05c5e84045006840c1c40750503024600010310000d2100002000e2050180d80071400e513040380d40182c2c540000c02c4c0c0780c5c00c000b80c144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 925424712 1250 925423462 925423487
    0xe030703090509060609120114090a15020d0e0a0f0501151a030702151503010b010509130b011101023c04152c030c060307121e060612150608011203 65
    0x40d0301e54640b5006540150030100c9110180d0112500680b200000cac190707100400d9100a05882885403440307446c9200b603010f4540e40b03100d08004107009490310229402c201201f441560307030403440c0540109128003405858900400341c101e5121051600c8500652842c00c040d600802681c0003011a010303d100300580c1449038041c1a0b408070500703200c040503080340b40441c1254025420403260940729800740d02901d070308640151094200641c9a441613000b090a5400c0f103040c0b04204402c02e0122000b4406400040641220701d9442e01d0b1010300b02c1c2c03180c0c445081d202c4c004180c0d240b440c2d20402c0000b0507a400c0f140e4824400004c001b6180d010b03115000c0c0f85001c020a100001c0103249617418904444242d204194103803a401c903565414007002d031008842503400f00759064540c590007401c55202f10341c040300c4501115418540a420035068404562040c00014042001c107121005240704412944a0b0782541440f2030f46402009012401c0c14801c0c1096404c415010006041c003a9210082c0b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 925425962 1250 925424712 925424719
    0x10e01050717070c0b0f040615061812050a0b1018020306011e020d0c03090b03011502072903040224030a0b09091209011e02100e030703090509060609 66
    0x6514201c5002014100303581800040c845141e008214020b00a401c1510010b800c110302c50300c1395540084040c0d8610b00900112840744d941e0078151400c2094220050262513542d440010402e40703280c9030084480180c100a120400e804080ea00154001580000c01079206a04483d81d50302c9100003158203189601070707400c0d800a0354440ca00d000840d80118442c40003601d4100032040003401c1c0c0c14464400035941c0016030301c01d12031307860b0b481c0c0600e21500340709109240c944010b50b00c5e00c4800c4101e4000780e01040c042c0c1c01c0141c2c0c14a525405021038009040700782c0414a0743d003c080c1ca40c1c410803044460104840c040000864255200c96180e01030f0001d60003202001d81445e01d903200070303079132003110010601c41c603085803031100f0b251181e1050f010341070040040848811540110441d54072038410f550510142414a032155414030300401e02205040d00946039a00c103040440080e12000240c01901c1c2c2c004114240c00a5000000704050b144107550310551960b51801060403032190581c107a92 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 925427212 1250 925425962 925425971
    0x7150309080d15050103052404050a0e010f060602010e0d0207060315091802031b0a14180406140105180f0619080c0a0512060c03091509030c0607090f050f03010e01 72
    0x5450410070701c0c010413200c00307980800c1240e940d64088042d113032040305840161415034441c0d03180c525098100350b03001000c0d4240090311750780c4120030300c0c03c45103081459103404d9100d0400b081441e80a00c2904e03140715500015103d860300f010002525200c1c2e500440051640da00d01d81c1d203900c2128005c000c09460412010000039406188480b600302081d04124807910400010070400c030001c980100126001411050465081c0494610000c00021030036412040f040c03402d1865200401041e030042d4058400050310b240ea001c4101045103050b0401d5006940140780c1c21603080e1201d80c00c0780d1006d2515440c0642c1d1b2510380024405101c100300b81401840341c50004030341c030705000c59254502102100da562019030344005000c0c4100c801e509069440c0c02c09000640040d68030402154483d58103c1940d000c641d10310a0f8121424041d507070340a461b44081126240203400300701064100d0440d01b03220036018641704070220080018010070740140d20401d800302c51a20309421890051038460000d20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 925428462 1250 925427212 925427231
    0x20070e01031707030203070f1a090a052517010f090c031a10090b180c0406091a0f0f0c07030c06120506030619020403051209011b0f2d05160807150309080d 68
    0x2a920301c64031100760cd55006c0c60203008017009540200442c4241c002c68140525450258a5807440e50100e40010080d500c410318429424001c0c41010005807080c003066140b135056081002a400d454044442e44044d01014070600b0200001d200c811a42d0403074021806d1480c00e004901c01841500342e42074419444000e01900012120180050390301541d01c41c014103513540303005580054001c000b4482514100109400d0b100e40f01c0013407040030200954070b03140c900f48030004c502e070199584c015107809209034003e100542d0320450b14083d5102842081c4054201403000030f031902c3c4040d058103c40402c0c4041241e501c903242e01a00d000710740010a8800c900b2a41201044030b5004040040c001074042e0170620220309042d0f1810840b03070f040000700d0300840c0c90b50b640c4a07a4417014621845407448031a41c4000d840158141d041c00b188c8550050312203221000741103840c0250641124442d030300aa40140b00081503142403207441041e80c07401040c00f4805082407102c1c0d01c144643c0c012924105000348 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 925429712 1250 925428462 925428481
    0x11d0304050f0a0b040e060d080a0509040f05090c0111011d01090210090602070b03060103060b03070320090f040216050604030c020915010f20070e01031707030203070f1a 75
    0x1401101d800369551240310070b50300100700300c1000c54059880f01c0c4d130052100340030020a0580040c2d008002601100100540d40c840d0744958015510707480010f800045c82d0946400c084c0205003205010940511080c18a074041946801e032140c4464100440030600c941680e2003504400c288000c4525440844184501c0d890701901040030264000e04030b110100f40d01a208030102412507081e0b901601c441c9052403440109a0700c0505410704050b182c200200e0740d00d01110085000c3d8600c0d460008119040c40f5910f00d5410851109c2500b49409000c1c4031040d0310741401925146500701c0b8010307a9011150700c4444461f68a000151040c030a402c108030416400c00c01d01c07018513008803859102551000852842013442e091018002180c1d01000360040d0700826090142103c402c481306c4100003144116131a064055000755040381000e40108248aa6004400c0c00145458400b0b0700d81900d50b10040d60f01d1294010080024000c2d002000c140b1500900d01d418181041c1041710301401c1500c0c04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 925430962 1250 925429712 925429717
    0x1e0609090203010c0203070209040b04030e060c01150503070f06080c0712111203100308031e09011a060c030301050111010f060b0711010306050a171510061205071b05011d03 76
    0x4a002c1d603c0d101d40c0b607000303074000025034094690040c001d03211981c9540e6441822640640b00300d050081c0d070000344034599115805025401070f0100009212502c40e82524105401d07030b800076000e07400012041c17044e010681c220303905842e8903007041003c0f5160080280c6a6100d80400034040c498080c545c505100d61081e050341340480344104071002d50325081c10b540c0703e40c032054860520a5180341c00400000b4040c0c0c02440d03018600e50118424040c1041b0503a10007031040340d500c003460755101005011555501c480d050219070648031142400c00e009107140e620310060080d103061000380142c20722040c400350015420340140d44800c1c889942d40359030403004c0d90480c00c0200c81e0049500c41080265200740314401c2201c40003000070042e580340c02c7e8810b03440d200e0b241c1c200415004000080450940d00d40b0a1030007504400700c103650440c64004001c20016403004840c00c510305041c18040c0c0c062f03200c0e01003d42c01e0200c02c0c2c41d085140c1e492500c00d0043c88070b114105044910148130108001e0301002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 925432212 1250 925430962 925430981
    0x1f0b1303020108010b03090303040210030e011506110703050714031011090f04021602100c1b081c081f0806150913031e2609150402131e0609 62
    0x30f60702d4699880c0d03182114170380001c80b01d1b203040e5070007400001c0c00343c40c1c90b0070140180030460800040707840c4008030b080d02351941020100e0101407100d20400260380c1c01180d54a2281c10716008e801904d00316a40c40e5102c01c10b611079610f410070000645030713a40d64240708003aa0702212403000c000743d002060707039424190445450284104107490110744070b404c150080b60303105410308011030901074440d403c10140e41c0c10190600d04100701103001c0300007c0d4007101100030b01c9051111459456203495469450501c900e00c51095030b000310040c112615811242d6070350011110348846618038101c0d00c0134024492140c0c8006028400c20341840140316240c4c0300e100f149602519020340d00d90300c0d503a400038596145903004001030074050750480c00f46401124008640f0b52031801ea03030325403210003940514441241102800340160024403030200c400700070380c02c0030030800101c01c1d0301450a6000035591401c0c0550208031581c9400303003d0000f80d03074020501d80001844404100c11521340e0b64202c000c1545a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 925433462 1250 925432212 925432217
    0xc0f0a020c0f0409020d02150d06120b070c0f03050304080f030a02030a06090c0f110f03070515090d051207030b150a031a090c0d02090904030503150a0e1f0b13030201 73
    0x2d840ea110b0b042c2030054001c02034014010052905003075082c80420381a036012401c40c00b0050180d51400052400740000614101d0311051070f1f00c40c2420411007c24025114000740100440c10b2000a80844038400c1a2909418107648070384d01c0c0d0910700014840d048002000a00001c2005814242c40e400381d8091b0001039000c0107076646540d0710b40100c810304400070300803640030038518052501c103081d0070307006130400d809840d010300101043e949140c121500031501d0350091012607241c40010060654842a250010014441c03103040c0903140b40b198110703680c00c2880007000941824080c3d08a003566044c00340003158100500002c010440d00603146d00c0000074200101c0b815200300401c5d007402d401d14001c24505550312072522980c4940c0c050108041003540a0091082640d03c86118034132071400390300c5031940c81c64503164030030160340ca036407042e4416101325200780103141000c0c555640c04030b41c8408801c480001040300d50140e002903804030303024600024007014404003a0100318102c80c0700780c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 925434712 1250 925433462 925433479
    0x51215010e090d030905070b07080d060e07080c0304020108040201050903340e060f040b13020a120c020a0b07030e0c09040c031407031502030a090219060f0302210c0f0a020c 76
    0x64210103170344000c0c2d0301410a610030003060280201510081101500c1040d18a01e030110204800c004d0703030300f0ba50200c018081c0c0c0d4410070095942016110358031035038500303559155150990000e00080300191010f81045030114100a40392400c120300700080311a129000c100ba115502d062820040703c6072440c1480d80c600200007041030391600014010000100b0003030040580c4000d01000305044011303d40e00c44845180c4075054400b034030060035030840caaa1650104216600c0082c00e40d1400144071085500c0581e200c008140151090303a084104e80c90089403045501056900d8001c810a01d243d100c00028140703c2008800d203103d0007100d1242c43d41a0501c14440c0509448400521010342059809558020a06800e600941d03001c2c0781c02d040002c03224000e03004240488144260000d180c44403080a104094011400440f1840c10340390942c900040910822124000503000c0303404003c1c00300100300c80716614030680380190356640ca01d988407110700d0802540c40303a0741d901180c0505841c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 925435962 1250 925434712 925434733
    0x80c04081c030c05070b0412050f0d0515092a0405030316060e0a031707051b0a020108010503060c070f060e06090304030c0509060109031104090c1508011e051215010e09 74
    0xc205039a9002e8000340711b41103a03503a41c5ca941c00400f10880c000000c00900304001074103000090081e16130b8031004040020186070078001813104205610245104003404030812980d400c4a0184941007040d00102400403044411400c2081c003a64005035418040402d0504045008091840196028071828002140c80c80140d80d01e90840d4200500099180b94510320032032441c07e5038a03080300341c7d45002c501e0b0900e02c40740e40f16200b0081a005205402110780350040d0f607849030691307000d001d044014007610708010700501460300c10082c4c010300c8010415040002c0c401c02ea400360740781000780ea099500c1860062801a140c0d801804201c6031580400740c04545400d0405505104600685500b08658116100c4000e0703803002d8040b41d548991112005800541092100802011b08000f100c000000032000640003d605800030190312a03404a1045500c07100c0b007800d41140c40542c1c180705010241030f422400c2c44c1001c0c0c00d4500707600910300005112082e2482c207a2040b80c585050b100510320 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 925437212 1250 925435962 925435967
    0x1380a180906060207061b0515010302190b0a12181103060c070803070c050f0a060516020303160e1c0516060203160b18100b01030c0906050406080c04081c030c 70
    0xa4003d46005900505050003100c0c01030000301d0090503805258903000c001560390910300105c0c1c50000390041d140304010030842c00c240c04814400002c070341c00c40b007500e401d0071a4800e007802460fa40307008100704402c036403d600249611910204000c0704803450b4100e40b82c14035402008168500c64028031800000415404201c1c041d9601580d10040144c650344550808079203400d580b00c000d40341c6000300c140c42c0c002f0711800c00c15178809522410000c51203107001320001007440d001400d007200f59001003041007483d2200503900f0a09050900b03000d043c4003d00030205d451325040c10001e80d07031014a802108213024002491080c10018071180c4c142550302d90310201c0c0c8901070f0300c00d000400041c0803070903c00200c0d51911181d100185003414844081085101464606d4003d9490940382e030310321050203030356403500400441000b03034289104950f03e4070600414910841c803681007000205030100d500c61784d4170b070308440003818090115004140304410b10035140b00340382e0503034000c05c0c58003074918401070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 925438462 1250 925437212 925437221
    0x110712050f19030315051f08070e0f09150a06020f0d09180b06190504050a05030304050105071b0308040303021014190908190206150901380a1809 64
    0xb00030400340e0719540240c0d07041d40500426400c051310080b0b00d010120f4240c84142110301108818044400ca204001202522a00300a4841c1c000c002c4400841e050340d4440d01050115010252044155039858544141031070608c8403006502800c0703080005443c6900141500014909500350380d4a0101c850059a20140c113100b409210445400741d01c0100300c4d00e5001404c03c2c10041c2032213290034044242115800412904000800c00214081c4040e00709540200080c0c10190300130741c0f034603003800b00103043c0d80900c5500400801f00c0c54550703803035000d8103c0050b0045500c4009591902d8482c40c020351504a0240c40c9011107207060044020502c01030070a60242130700c0d0103030701420b101900200c8050034070344a05850b0f159040041c12984007002400d400d5244640d4003030489410101c0c844040032020306a401d00c03560b404001070043c3c0800743c03440004101001e155124660505404885c0804082c190b04e403055800308220034215004001f0042400c01d143e003601003207840300d045008a4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 925439712 1250 925438462 925438483
    0x115060f17010501390510090b310605041e02010e04020a0201060b030108010501180b0a05010c031115090f030c03070201031503060615031d150601110712050f 70
    0x301c000200400c929401410350701d408205070114200050255405130003128510b843d100c030b03016001541e00041c01070070b01c050030065021900070f00c40e107002030f1514200710b0005000000100550607601c0500d000901b00521201d044c1c9540e2003014805081400041800300c03000da81e000c201c0119252241d8030700d0303110b40500d64144c40c4e0300c180d14220307020b00c002900010440c405565a0f000c011540190040165008142040003c1400c2d03041c242c09984440d541640f4000f45c0b400e042e000d40b019034030341441e102910400c4c40c08a500c031550342011281071341c5001c410003440c0100f401400105a244084034800c00a400880311a8035100d00c1d50742d80c030700c02d1a0300e400f02900140858070040d0300c20b8101c000b11481d90b01c04c8480240e265128013007201c0c469031040000804003251042c40e20742501440380c0d002100c9880c0c40d41e4050054001d07403103150744500322072a499510005030700b0b41c0c02081420701455060f000c48900c0f540f40c46080b201d1044c04082941e0a110b075583c001121600000d90a485 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 925440962 1250 925439712 925439747
    0x130902071109090d11070e01030609021c150b040212040303051f06020a080c0c030304060c020307050405060d02210d02070e0c0703050418140708060a05031908070807050115060f 78
    0x20800c480c0300c00c03250303c0156114245c050081d1100001c01d00200c0491034084c0d4003602001441000620420546a091501d0258860b80400c050700c089222400c1801d41400d41c21004249041c04a00042c001e125801044000d01416020311003896490f0b84054807640301d0055013921004e941501c2c40b40200746100f2000140c2c02041580c00144044c006081408040c2d012a004009030100090079600300740c10031000a0340e400102001d40c82c08002940080c4030a903810000d80c00d05d130012400002c540d120103070080c40c2981e2414807440d800300340e01d11a1450107042e5885ca1071070280c003d443e002c41c0c0c8603061824602801254948509204170b651080d40b640707030103107070070710708140031115898000c3c0024600e6514503070180940800d80000748282c1807582c94030054640748040044800301500030901039400610f240342c24a040c00c1d55036040680004a094407144c80b86410343d06c07441040001007180d420b00c1c0c0b010f080c0022080701c90042c2c807095141e481c0c40a146000c1102c100f021000442c05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 925442212 1250 925440962 925440973
    0x708070506070f020a08250501030b06040e0712050c04030303050603190f051c032c07050f0607020a080c011e17062718070b04060e0613090207110909 66
    0x161400d920960f840f8409800071400d107076185141c0d4102480c1b9888141050402103401c02c580d020002a04007030182403c0400c91001e100005c41d84ca8015801030701c0500b40c910000c208590700504614042d240e0580c000d2059161040c000042e035042403104802190800c0042901172074045048070505100e040d203034024104036196204200038514040d079060180d08421001003220031000a910152a200803070000c4202c1074076842541040e01002404010004041c0707081000700d0144100c520840e13808410079090070000d4818401c441c1d000350700c030070b0084000a20f4030000c14144c100e0700c401d88500d80c00b800a41c1400510f1405003103400005144c04030b8200d50301c05814003040d00010041c1c0500642e502a60304145000400c0241400da103540b94208900084403d1a03010038080d0a0060302d03840346000f030031118030702a50103040c0900c40103504160140d1034031410b0365540d000d506040381c400c59440e1406802980143c100342d0f01844d540264608504110f070748540122040f00081c030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 925443462 1250 925442212 925442227
    0xc030307020d120c0819110a0309181805060a471e0a0902040806130602120a090611040312140c010e060901200a110a02060412050708070506 62
    0xb110007840c0d003c060f080c06a180c1882000c581604081c0092040b0b4103411410b0030035000d406800c0400c0401c441045510505144000a61106000084603010140301561b00d18100d02000504070b110700d41c1103180d204520940502030005490760140014070701c100240e00e0180c0b103240c3c2c40075950500480030803040c01c0700d4030001c05064050340031800c0041001c0d40c41400c0800100e01c1c02e4121030120402410a1902c4118582001d400c030080105607811442d05240904030354450100a040ca2a4403101400c00402e02c81250100d403c1107003010b140752180c2c907100424a00030326407542c080e0385e00781c90010703103000e0b140b0100122025290031040c1e80745455a41d00044806c901d00e0000c1103010207050041e41d0004409000d80218a802c15014100c02d28050302e146007101c40c0c15601d0032484c091003458a104109000c201c030040300301840c0144012203020303803c0345854241c0d030000750000307800500000c81d4900b030341c0040c0c900c1c1c2c0b1070000c1c3c8120540d0b07036441541d5005903016980e4003144c10084031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 925444712 1250 925443462 925443473
    0x70204200d1b181e030c080303041a071218082205060f032d2e2601021210080d0801050303030c090a03020301060b0a180608010e072309030c030307020d 67
    0x60b103144c1e06602c100400a0744aa803101c1c254000340d4844030855002009000c03c00203444000040c840079500160800d2500c1900280b5601d40c030141050655960404410014140701100d0344143d042000e503540c580030b00880c0c550030340c1070307048004d0303082c03021035000ca11494584110741025041000044c1503494040d100b040c7c03004151030902d04030040100100e0240e4a07114500d00c01e9003482901c401610b13035040d1064448060400b520210200c1c0c0d20140b104550040c1c824104202000804088403c2c40d103c05009111b070300050f1402840d030308200300c10101900d00c100d00391803040054914014480100b070300e5940081c021385a041d00305000003004049000050554044010b00150010b40c0d240c02090841c1d11580004410b500c00041c07100a05400000079140d03401ea42d641d6261040c6024001031070100c06005094440071420003050100b4070803c50560b10244904040c1420510300400e50340550043d0113481c040d000b0700c0ea05162900d0048152800d050700905805042003003603960 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 925445962 1250 925444712 925444739
    0x19080603010e0106240311070b04140a0516081c0e03070902030c0a0801170c01030203060f0415060306082b02011506050309010f0203010b070204200d1b18 68
    0x200d4040d0740c2c54091541402e001d0040d00010281c8464800c24800750080c00007141d402c182e980401c0c982054109501946107000729154030341c104501400946603807800400034142d07000082c14500c01e02c20700c90700f0302c103001c541d0108014684a600080b9a9038200941d120400c80f904141190b0b5070317090f40e0700d085001c0c003107862240c0070040940b2840d9441e010010100d800598915a6000c404030380c0c800e4194214290a025000300c901c1e034a00000c29000040e40e403111081401c1c101900440480c269031151451101c00307000c024003d0195510034401e49190801500c03420002905103880012401c03070204503080301110ba09014803003038041c0700d0380d04c403012044a40340d411036507a01112134052420007041c2010b40500e0340c031680d40e800d000f001c0e54256110464004a4140f040004002181c502d400701d40c003181c0c1c1960302040019038400315070a0880100503000c3c030326800143c601d021604a90003501030300c41390501c0484d440540f003401c4407207602010100c0c01012100d80d041c4403c0c0c1c000ca09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 925447212 1250 925445962 925445971
    0x507091a2209141504020c03030109090f021f200c010c3011010605090a05040609060e030904150302010801031722173405060703110607051908 63
    0x4004103071550b1042e41d03104840052640c03014425000303040c090700c0c201020284c1c5030705204075003d605000c01154150707124801841080b851940d100c11120802540e078403003800c866001403402101105c2010380b8064583c20f201140d00044080c841d0411080c90058a0050700344000014541c0704030b803600540341241d00d81002d6520180103c40940d490300c03592804000b089002075070f2165040c170414050110b64002511401d03590506c1014002511003080c0c1c55480b20802e076000c035040d221400e02d10010b00d40c039a009413800f820909100c040d00030000003030000300c0083c0c40400040450905245200845000090004104000400108403030380400c6010848081c1c003e07140910078960000e00003d1000c2892044044101c10000260103911104141e8400c401a00800351041c540b42200442859620340394483c01006800a0040700940c4001d0403001d030100f40e8608140c20083c0002c1c1400329aa4020b1241d00006090700344a04140c2e101c1452194000417004256102661980001403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 925448462 1250 925447212 925447267
    0x306020c19170f0c1b1915031e0504030320251e0f140c030a15232203020c06030721090606060e130b0609130507091a 52
    0x94100340310007880f002d41305170310410305c0c030f01c00c91240418401e80114180c0022040d0001d4081081510781016038500c07407440c18038002456060f030b0030814010b120005842ca0070149003804000405405910440d50551268599000324207881c05082c580e200d83c4480d02101950000604201071103c2100320101d0321038500e503d80b0301d9881c00103218082603960184c444200c0a0303612030500601d600040040c83d403a0000d0a5402111400320303545040d40c0360000c150b0400e0b0103402400e40940d510158040543c006d501410388420069100109002e030303500c1ea03c000301000d8502c0700b030a41384841c101c05a490b4001c0c101d80399490041103040c1d00000c0c29202401010300103a0041921040e50180111134420300050140003410a04211641c540148051054100c01144265500e5600d0019201c00b0100490703001c0009012801c0382c0035000f052034000c2c0341c103000d071204031003a500038920554107540c4040c0c525985130074421001034036403414210f06004200301c611000038000013070071031162070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 925449712 1250 925448462 925448467
    0x715030b0904050309040b041802010c05100c020307110109051311210f07020d091205010b190810060b12280f0b060a080f07020a0c0306020c19170f 65
    0x5008659141000c0b6021100740e00300143d64000c614051162075440380c1d050700c08104815000100c040c1e41c40c200035000c1c1c1030001c511200c2080003020481d4165030075100400340440c50410344060741e60380100724101c441109104001005522800b5000101c58000b403a440010f202c45000034002c00140345c03140c110780c20070002c1d11900643c0032040611108031102c0100f20340f030581ca0701c0e0f002c020050b203c01c0c01c64001c0303900c060b401c40e441b184500c1070341c104d400101c110b0f04852420500400080f038280d40c0141d4503410200b40c0d1004041a9400c44030380109607440d03414000700c00d00c100d0703440e03000382c1070124000d114110904801010300c59100c0800c035403032424014440c62001e6140302a404154001d5244c286030000744806001e031000d1020140da10600f451110a40030b0b003a1344c0000c04403140d940001002800f0702d4400c101e00e83c04d95420800d440e10080d100e04044c8040d40c0f1000e8041143d1050240480c400d4440343d13100580240c0080c444190b440c009103144426510045000c10b07554000e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 925450962 1250 925449712 925449731
    0x81009020406050306040509120405190512150a11160807150203061002030304110603220f0c080d0e040e0102090a09021201081603030e0135011403071503 68
    0x5100901c0501180d841c0ca0f901c81c54024204815a03200412003e8660071034201c110b400d120303290586d0f0550308d0485070129210034440368020132011590210303510a100121403140c405020456420301c2944000c2a6041d503144039500c425907103248051100320300101b00c880c03d0b800d01d818500e44200d22030107425107001c0040d2184020342c0401120349245650000901885241030380994425a94900155007589040c3d1030300380802c00725109a50042c40000001400c00c004403500c1030b44110110050754280d405030408a100c032004034812288604107140c0454035031000203070030180c2e480325030341c04580c44c5e645c0e01440041c1c04520a1912150340038003000300642d41e0303055910080c0043e5a030058482424060000c212441a8001c0106422038041d81d4400000100b4080a907505400c102e20950311510040302c90300c0c0e1809040549104030100a901c4103803525120803450480071184115907240d60346401064a81d0000035410303408841c0400460002001325000323041c40303040004d0308409 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 925452212 1250 925450962 925450979
    0xf061204064508030a050921030609060628020601050d0525120305090907050a12020310092415230c1e070f050d03030207060f18150207050d0810 64
    0x13050b1403010b40162035004204000d00d040201700c021a401144402c545004904141e600d8440030305014000c601400000d1500d455600440d140c010300f056160b21070007282e030848000e0390582010b0b9001401541c00001d40340c60107024003854180c209000d061500100590004001002d100380c50f0f0640c480c0500184c10102500b0b0303403030494003079228039a0f16a1144100000b182006121409000d814005003400d0340c0d01000b41c4114580c1c621005a59445000400c0c42400a0794005c102040c117100c41140c03108142807501c02500309002c0050034294441440302008101d14096030b001803440008484980e4051000410a499284405107048000c01e40682040012078209941c120a25012140c0e4802000084001e044c04248180e030113061a0006120f09034412000c1c08058011a8000900c4001c0d8003c2c4002c8566034802c10580f04072003401105501c81c250700303540030311090b14000ea41d201c450080f1450503512001515000740c0c41c0300c0c140e490040141029854208843d000f088120 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 925453462 1250 925452212 925452217
    0x80106050a1e243906020403020d0f061508030306010507032001021309152d03050d020d020102190807050c0304030c0f1e060503060f061204064508 65
    0x326640800103280da0b000b00641001342c9141080f81c40d552004641d4200c5211084200380c0d8003c011000c2d40001c007030700305040680502d403c00b9600102d0710b00c41000300041703000c2504080e441054203001d000c81c2115001c080961a20442034650401c20003d4490340c4a500142800b9110303041080038010b04010441d0080080c00b000c080e160340c0010500000ba02c0e102c0c0500040c040b180040c05000381241040c0b0401d44180b0032200e40315600301c11014001920000883c01100020300d04d00071a0381c9051041e91000d54412100c0580035410720f0f00b50091040c000c4401c406040702d09100a02601f80c0211280d100090403402000000c0c045040c1c18107090000300000c40c01740b0141c0701c0e418102079088440010550201240361200340500d80e016030500d203035004490890921540720f41e039040208860344894001d00f42c2c00030b4001a094014118103801b9030049000b01c1c01000180613850311300c04889400910b41409401c2001c1d40c00d58490046c0200c069601c101d2040c0194503196030b909038854 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 925454712 1250 925453462 925453499
    0x30e0c040f060b220f060f0507030e030604051e030a05120717041a060f031005061c060e1e07090c020c060c0d110105070e0d080c0312040b01080106050a1e 68
    0x101c100c12240c0343c10640383d813810020f800301241d1204442c3c5005806452040495451018848040f441d101858022501f034400e44001400f80d400d54902881d0a5031030380d052206210701641740d00034441414400109480c0c200d5031f83d458191034041c15006000c1ca28030000d02d10300c1000f60408800e5060012101c01a006074455052071200718511032001c66011070050a0501414148410211356540094120307840840f079580043c49407583d9012810701e0107110b1111030000c04070300c11982000502d40c001218105400f080d40d24a41030710300105908160000450032990140700c040c4249017080d8081d207c80c04250044070807001140300450f10b15003045e504409507810182010400c545c1104a101c6000c0c20f20000f0045841c0200000c0c0014440d024501d001c1e070341d15000721301007100000403520005d504500702c0e600d4044010713500030549400c81e4101c0c0c480900f0800015204014021082a0b52005203000f49107810885854500058803001030200c9e050f11b000020400020208425070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 925455962 1250 925454712 925454737
    0xc01090f05010509031204061a06040623130303050c033f0907060f110610050111010606020d0e040209040f1b0c0b0127020c010219030e0c040f060b 65
    0x800d180303051590850304020f081081c142c00411846034400706070025194020750241c1c00203690a244140c9080d800e91281c070316904100d0005000c00c1040d00628000c2d04c8100c2c1c503084010350701d00342e000040c050180d01c014807c080720001c0107000007406103025251103411030302100d0070109070445015440071811071142d64203801e51004403510400d01800100140a00345401c081e003060842d040d80c07201903215150800020240301e007003103803180b00e0346020710306060219034090a10120881c6016202e10501f030200c0d0075065032090709401030182600300c4006401801c00c101400e041501c4030600c44040c1035109508002510655495100d800b5404052a1700080c800300c20034290700840350f200c4904000e1180707440204001407004010311341559070303c0b80f203140c1f842c0c020342c240080301503003542e210b01c524004103a180c85e102055001e4050702c0820003040c214000103800942c119403400c0b0841d44640c01244824019007001e4100e40c8501d0803840000411a5540c5009140c0c0e8101c011450702 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 925457212 1250 925455962 925455983
    0x3180d110907360608040309031103010605130e0f0a03210209040903031a012d051903090302120c0d0c020303090604080c12010c0801031118070f03060f21080c0109 72
    0x4010002c403100026113207a09003114982403944000d05640c075584001850040e01c906d0020250310290094401020301a00c0c0c41c1c50140c038640c124014040942841d4801d10a07980848260305001071202c1c6100e8040d01c030120520002554071105045a07602181c0254003041859803c1c0c03141d12a4800c114000d540007d0032102542150841c0da440d001e100c0d0410102034400c2c5403030824180c0390b9100c8005840b54004080641d501500d0a00550200301c81801080140c7e89803150107804c41d0000714800d601761203402124400c420580e0051010a1a695002c80c020484460080400300d9015000400320b074207141404000411503401074103c001c1540003141c960302c3c24108200a400b01d0010f0000030f0040500400006003101c0e030501c40038190700c00020001003140c0381c0039040860200d48160a896600d84250041e03c4116003204040019181220018807880c054149006481c0d4070284d0700d000c2e1420f405445051149400d05940c1c00c4010411580380000034800c0c40d001c0b502c45c1c1140c09 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 925458462 1250 925457212 925457297
    0xc03060e0606041a06090a0f0f0e0105011e0c020a0f09020d0e030403050c0d03170a14060307291c0507021b030303010603090602091203180d110907 65
    0x20700703010015041c58002d600300f410214494031114100000b0f0b09041d10050380700e90982001850031080340e07004920700780000801044205407115008241e844c075840c1080b8690741d841c011500c4240315141002d402e001d01139164145442003a0325040702d03000a1510081c2612000a1901030046a004803210f650003e21b40010304402d0054800001141c0d000e107003090f06e15140c2c55154804000c00030b115015904d100d90405016103100c10910558161241d21032400c13220074001081c81d03500c5020903034106000035005160029460050b10701c11016843e02040880d00c5074038030380540d880b440f074a610500c00d0903205140104080e03403030392003054085194101500c0182c01c00300003200c5a640c3e5484500b00b0003594400008880c11900305290002c0d00701828240341e802401906c01313407a80161124140b081c11b41000014120b6078450110100c0240b040c40e0170048081003506000341403444c40070b000c00243c5480005942d00401d28202151035050b589490b200301c1c201411000c01c034074218951075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 925459712 1250 925458462 925458491
    0x127061b020d0b09030c0706080105010e060c120309030c01090605100b04061d120f070f120b0114010512040506010342060902270a061403060d0c0306 66
    0x82250110003650030280c8051030700807030709040a409002c0c0075140b110000c910401c1041007124000b240140a84d0361041d103c0200501010083c03148500040712102500c02c4d40c41c040c41200c2c1c40f01904401410306440c1200607400396000244122403d0000b40403c0c104164207000d40c050581c13107024009100d2800a001c1c450a41403504a0405075805000901201c0d03042510003260180c605c1910f10014060000602070120301c594698007800744020a0204650004042d000c1e0744101c003140c1c2580b6103908804019645a01d00a803142030200010098107028190b0b543e9804018940300e440d04101a05940c2005019230b002c40b411340c0700c1d000400501a50014014580420040305140104020726007400d500403040740326800c40c507180d40081100e40c140d004000502c100b076019911080000071808080c001000360014038950300c03220326664070b0700d88146801d4603d16124006d0218070400c03140021341000b4245130b0081d44454584011510000b071800c015427190314081207414004202 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 925460962 1250 925459712 925459727
    0xb12030a180f030b01051c05031b07050402070b060112020c0c040b0f030f030403060510120210090317040602070905010b0f0d0e03070807060b010e0a06111204030c150e0a0b09012706 80
    0x401f00400c0540781c001000803004002c941b215000300311080048030001c5032007802d00e1455404aa80588005542001c1085220005128140c00d0701c07400900509101e81c00141e1240d1006800160071100d9104074902c0d0560000003000b00151220151000c1703580403030314002180c0341541e1503501c08103040081003018018540d003e1000c0d0045424103182c111240c00e9100000c0c0c0003441640d130308607800c00760781c41109036200543e00a03408400c0c05401c8500c180081d4818002c000050040b250007051000c0c0900516040324484038695150890800b0303030801507000074114180281d114034104202d510100b02074032140c0d01440d809584e4200398603000040381c503c0c00ca2a41842108010b01c110b50740c0b000090003c0701c1150a000f9482410b01c01c126040021444103e440c01c0b2020801005010b91404a04107442186030f80c80202c00075807406480d5106030f1200c00740d01c40091041801942c44080180c0903069043c10114270a803111013605c0c03001110b9032017540640301002d40401c13005921060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 925462212 1250 925460962 925460989
    0x344090a12080f0904022a101b0c020607080a0315090902030705010503071b080a02070608160507110915040c090b071214040303120b12030a180f030b0105 68
    0x441005071001e5a4407004280590801c05040f45004940711525464540480700000588050280c01000407404210405060090100c0f94410400c803100666864490f0a4103143d10782000005420f460108981000c0f8004040303030080000d210380c200007019200941080b00b065200481d440c840c00a83d004110316031380c49080e030303141000d030304a001da107000c2034401c150344080c03811658030340d05e400c02a111000c030781c1c076140044803001c4489004e000c8600e02030b11415116600b65405640d45101c103c3d0441001c1d1481c0080034500951031405a00a10060101c18031540b4102c034030003403100000305e0084c0e003140d013500480148885440d6a2400e4070505140d02800d00f400e103145400d000080000303000e007000051548100c640d41c0000d65000c3c220500702d020500141c3c03079965440345402030507105d01d1681c13030303100714284500210645000386408a0000c03020004509142c2d091400b15103214900001c02d5445421242c0810903110b40d140007400f441c014110201154909011b0003084503034ad94 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 925463462 1250 925462212 925462229
    0x9070e04060b01020c010c0f060c111605031006050102190203010f0513020a080f1011070f1a0a182301020c07141005090d05100c030e0105100344090a 66
    0x220038600240034002316207846504100006629001070303a050b2050349000c1040d90300c0d403190080d01d00417007040381c03008030503941e0607415074603603030b00e10b940e420281c404038040d107805030f0000e11402c00d0000b00d04005101540c0001c2c004544485406894002c89600742c8091030882c24403400d580941c20003100100081c424000203010071b54101c000305881d11200c0740c0e60764000780c995040c1d500d0100b08500f5620556000f44910b0003c03003c41c50465115001040040c0010800d603001404040e040d01c100040444c0801c2c0380111000241c0d6070540b0f04040003a000760800810580d40d018400920192161810520040000c541040c51003404142c0e0309040ca4400c00c00c0d240d130140c0250b800002e4440650301035030161544400da16003942040b00005001220742c0c03501c0c10b444066541a0058070390009071000800a40d100c0b4040301a14661a0102802c460032841c2141100114100341c00c044180b0760f42d1240150001111180740c101000100b80100100410300307045501e00311314035200400d00700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 925464712 1250 925463462 925463477
    0x1303020c0a080c040c050c15040311030702010e0f0105070c14010909020f0a0516150203010905061206070822050604031119020904080403140d020f010c1709070e04060b01020c01 78
    0x6240d9039510f502e200340c403900071500ca9250100003801081910326800310103064500a001814907068012800c40b0700b5400180496201c82c8022030110485111640603520150002000340c03d1012040d0400003140c10810200012030115101c0013060000c1c004401c020540f940108000405200c80c94009040b001c1c4104501e02e025058507040b9000302246040642c0c59030500340380000e002401140c013800d281c180c400101c410701944d60013503041c1c88048004011544810042c00f500310013240d20107107594413500104200078080d002c21076001506030042911044401001141c0c1d8108890884207075001d0801d01082513000000c40c4201140c2000030800a50100549c08030184014000381c002e888100108090141c5102150302941c0c0149494002d80ea201845540d1400c1807000c00780180905041d921740c845041c0180044040709035144c00c0810300a1541100203403001d048405180f080c14800035200400c02e03a4a4899030040c440061001040c0f0300180c1425042e10b101810420304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 925465962 1250 925464712 925464719
    0x712170c13030b09032b0f0c0e1306080a08121302030601090e030906030c18040b1e0f0d0302030a0f050721030b0616110a080a2006031303020c0a 64
    0x2601407a030112a00701d89407400a80310302d60700609510464920107901550680300d50380151a088504101c2c1c00069030800c42c0c0168210764108a90304102e45000103400c0d55500c02e00c91910180c0320040600b241400a07819a07110b14051520804902c100c0b0300711804100c80c40450002102e40e07a00102a000c81120301810382c1c0000c0d15450140101d000b40780d80d982030304000c40d01c10006d5441c0b4510240015075a401c0c840e000075090b4001780f0000d07034215907104540401d410030340140150104090000703003000780c56065001904080d100051f400c00d1142c09030050650300c0b940c070420742e1070180d00610b07504c801c0707060003c00b0307125801c02550611004218406c005001008401d10101114000d404000309500c000c5024010b0856420792100000c2038900d030340901078901040003441528103424006191040c40030034040d034845c3c1e10300b81d0000b00d2041c0c04180c14007640c0160070f51669075200b095922030009007441d002a03c0d0340c102c44a0007480c8004140d010000301c00202c40849404245618 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 925467212 1250 925465962 925465987
    0xf1101050c190e09010e0f15010807030b01210203040b070201020c0a11180f07030e070f0515160b060901120c0302120a0f08090907091401140712170c 66
    0x80c10b948180d070308295807aa40c0c00d0034864024032481c81c0b4014000c02ea41c1d6511082d03d00b407014103850703540d0318040780c42c08290907844007a41a5078581040e110136415540b00d0b0400d800506846a0305810b00c426003800c40d5080340d480911010350132810100588a0519040c10301620b07400801c04019a0320400c80c0009245000801036515980300d00120000b00f040e02c04680e40310781818540c179402003000c09000509641c514410b00c900d016907820048046c19414a13542da00140c03144e0f0084050460341404141400c4100c40030040070300141030314285c0d00204804450a40400540d9251010000d102030303071900180300c50040c80361408508818810751900d01e8039511621000303101d61841c02213aa01504140100346a05404c5036201e00404c1d460f00704000c07194003e01c40144900b02400020b08810301800600c07043c2caa0b034a0101c4040c0c5940c1d00151000030031280405076004007841403200040c0650b000c40070205096131215003540d0400c1c507080d5241000b405001c2c000b0420b10140c202030350b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 925468462 1250 925467212 925467217
    0x905011d030f0702061c1b090b040b0a0e0d03050909011202330c1608210a120c030f0c0302090d110402161202060a151509050a060f1101050c 62
    0x11403000a50f07240700341e00c000b52042c4143d01c00b054082d61030980d0b0303401c0550307036038412101c0e24450103202ca01440b031a007044a8804040c0034820004000384070900c4405200c0c0b0150a010115082003d4240e003c030b8009032841030316149c101c0000700700151080341401c1042c01d1034010101c8000803080c004d0294000f46c1210f818100d110111003080760b260046078008640e44280c0041c80729403540d0344100110090f02e50700c010300030000c4070110b6107000844100c00500804140071481c1c291314001c02d000b503848680d9004290b2942003140280c0e660030343c08058400c06981ca4025100080d007443e80e800c4100548401039408010316205021861107511240044c5006a500c0102c4607031801c00d100008000307004500308451800540c501e40c1c2c00700b06440882c5240084c2c1502290300d55a80c08520100f640c50108030300c000c0003a001d004000302070050702c080e4000742036403c1084495440e40301151984601d58440400540a8027880014507044006001003035003170002440315280603c901d400f1403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 925469712 1250 925468462 925468477
    0x10608060613050a0f090509030432150712030917250c1d070f0e030a060507020616030221100803030f160c17091201020301090905011d03 61
    0x841000039000e1100c038a1500400c0540703401000c07201e2480c0ca64600030450881c5d402040011440c020200d0810310000007594111242d42c0542400d010f01c4099801001d10506000d1081052a06a02c01c071551030510320804501c0d80a00140c5545050401c1c201100c09210124140351800000e800442c143c0c200048025111040065484103512908050768500140301c000020845507403008018010308003c04441a48107915011050509a404100c00035281ea00100d240c42c1c0680d104180204001e6541000007025101c40e41c00c030f46c80701426100304803401c40042c1c00140412040e4038503207540c2080b614803494110b042c04401d8843c42103031081c3c0a42d45d815500340c1000221126a250f1100000e40016000c4e00d0300d90074884409840b8880a84050b82e40414525005191502c03e6086544c840d07009001d0003d00342d01c400b4800500c0e8049440a03030490309441c01440039400c240002c0d80280342d110030005880d00103007441e81c210390201c0c0390300201d2001c900070040380b0b08001082c1c8020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 925470962 1250 925469712 925469719
    0x609030d05070816051309090807170a0903060f0608030c0105010303020706020f100203090a05120c070e0c090409051c0e09060306010e07080618040f031e1d04090c0f0303031401060806 81
    0x4406e40c0000d408511103d503881141824149074192040102010146c016a48070740701e84681d0406940840303000307006164106000422180c2c08101084841e0095031820304042c01c009040b40e11224164107550084181c9034003603455000410815504000840041c4881d1014150384a040c60125840b4038000c0380a100a6030080301003500c02e44180700800000f5030200440300000e010083d00042600000e0201c0c80764001d0b0400000c0070400801d01d03611910a04c2034140c90094031000b00401031800300c90036503c0307208603140e80010083c4108002c0741e801d0186c451210524110041280000c0300810b014001c0d04100c00400c06e5090644a8a40010301800e010032669940c03004581990f0b841062008441e010105100511000e8900700100d10b00075641c088404981414008481440c644800005991620403400100503203803541e01c01303072000b40302080d2060582c07603840c41e01c107030341c2c008007043d600400081042580501c80d20316000450003104041c0d62400c44042c18150008010600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 925472212 1250 925470962 925470967
    0x405030a0308150d150f0902010c020603040c0905010b181509150c07180c170c0f070501092301050907060c290108070b1602120f0609030d0507081605 66
    0xf03074039a0703402c1c12903100030000d0305020071100103080410b00c500001c0200f1512525080610705008210300950710140d030180c440e40003d81a50b0b0074040d060b80000d20580780742141001c0854503401c2805560300030181c0980351074844031100a90040803800c89007a5200f003051103094500901070303100741c1d481080304544c04e844041d032a180711541440b4501da5040e80380141500030841c512014002e00e036a41c000715040011858050007981c0c140404034010541d500500300040311301c070501c8002c1000e900311114040c2440c11710b0b0786450079640444002c03260201a00c008614071429140550043d4041c4002805281802c850b041d85900c0c550081300100006040b5940c1401524040702c0c0520020002c1c0c00c0580f6010800c17a5032021f000c0c050b803516030182c14070000b20713045004152044e5945001400c1e0310380000b5420400c0060340804d07610388501400c69122800c10003070060500c1200c200c006166103202250031a4115070004040000f070251020620170070080d00340f201c01101d00641002503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 925473462 1250 925472212 925472221
    0x10b030703022107091119450f0501230403150b0d03110c2205060103091b0608060d151d070303050c070b0a02061f0909060b12030405030a0308 63
    0x14182009178000c01103240c1407600300f0742010100d44c002c28203035407240d501180c00d03061884205d462501d21280404d089500603500300408450612030004088034002d4110400183d0341ca40810022a50101c4460780310749070100b01c01d580041d20780e0104586005c4880c00c000316120202a540228040a420a040a0805045c0210343d90248200c140c3c018440d00080c101c1f072900134056141c3d410f18800fa4081c0408109642c10020b10b550900c17040300020340075400000386a48000e1000600c024100f41d156035001d004600121100e2814010341e00d141ca20160030803a01070403012000c1c054030301401c6010350312008115690000c5040c0d40d4149004614840f2071350041603250703c0c0401001103800785901c0001091780090040903800c55410555040c03540c2d4032a000300da809801c0b456005038100c030b0700240503016074608945024a1994019800c0e41d1140b0780c580855502c880300300c1d1071070307641c0362402070920b003100c1028181c440d00030003980349c00d0502011a884148034074004081c41103420106c1e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 925474712 1250 925473462 925473529
    0xb03010b04180c05060f040909020315070203191818110a2a0209010b0d0f05010b0c010b030a0309060c1a04080304140d020703080d1503030e03010b03070302 69
    0x324035000c010700c14000c50701a80c0070a907040c05480002c88400f010781c040021581410303002c0c1d0f403000da0009000f506042c5000017440160480c06412a414001d00610401d0b10705404c7d03a4501440341076009503118a556082a600c0c8507541040500f40402d07002c3c12640010742c221001c1c1900d40e041c1c9002c8000b0780c0180001701429004009041d50800824608951940316440912400b4403c2e04071410341e81803600001a42a406400794008008400520020045100070049100300240010341001510050000c40308203801c02c0203c0040011501140b110902800f0380740b0350110060041d1080507a4054000c4c851031103420103005a6504a1080c44900030854026a1811050990a182c14a03140d109503008030303022108a1002c10030819031440000f460741410540e0380081c04503a0031505c5030b45240d00440c808035034650329602070000d007108005507032008510907150482c2c00313070420301014251a20752284078000e82c000142040581e440e040000300c1c002c0c818111220000000412 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 925475962 1250 925474712 925474721
    0x90e0f15010e070530060a0e04110f0316061706042a090503101d06011802071509051501170c120309090c040e0c162a0801141005010c03030b0301 64
    0x2d140a424250708450040144042a107108517400c947d044840354544600291502c4290740242c111143c148200b0443c3c2014203da000300600102103c000c050360030700a07813818440f40c102d60300162814030700e40c2c401d4002044158001c08206e83c2444580314501c002c80c0c4211742e114200b0030030103646680d1903810b4001d9548801408018056501d4009040c1e100c2d000f41505a01a85402c00446404c1e00c0e10040814018180c0b00d4006880c03036080301502c1c1d0388011f07400494040e1524900c4601062070a54180300e8013030782c1e5100340301410b0382e4012003c804001c140c0507400f010005840071641c070007006001c00d410205001c11105c00005120201b5164030318064481e030650030200c02004d01c100c0703c1c41980904100d820502c1c0c01c40c2c45640344680801c9034011a038840c0301071b02a4003031000010311060741d50329402211010804042c050a41c400e50303120b81d6603225240310395440d500345100c00f1504d58030f140e000d1400e00d414440140341200080942d10340080280c04c156441c5144000340c0c1e020f412 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 925477212 1250 925475962 925476007
    0x140d15380f0a02010b0a0f0e010b0d02130e06130204261014041e0317152812020d0308090f0703060204150207051e010306090e0f15010e0705 62
    0x78992103041d4200040d008018001e03203248140a0100009080254032582000381c0e682900b030006164a00418448140c0000908001c415004d00080001d541c2c1012000c00910108400c04010f003403050521011050740c3c000c40784418010081413200300341039900600d60040d0b8a035581482411900401c0c2030100e0526101120340c02c0c294003100c2d000509045072700441c0134040c8160314844010800e80000800030000380800c54102511561800d059445070b444041041200107006ca80750010706035070014000d1401042c1050710805119903152a1a400340c02c10156036a20b8203000d8001440c20020240700804002801e8001f801d0004148070384c0c2400d1a0190460f81c030316490b841e000b0060741060007800d9107116056030356505541b0000e541021608060540383c42025807411a00f20320403821f005505054444000164000e03051003852440350300c5401508040b105c00a28904110300501c4844800e00c030180103102d000006031a1941007080d6007440c59a6609207403a5007162940b440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 925478462 1250 925477212 925477237
    0xa1515051f0c0606090905070b0a09181b0201020301180b03120702131104090f050f160e09041a010b0304030e09041a040c15030207081603140d1538 65
    0x200d0014070048507401040005100c0c00a0752105600c5403200082402b0f200d40500001d44811801c210407170310000c5a822003440780a0200b81102c952000361031011301d5484403c0180c2d0b001004000c1403400c10018800300c500711406010035014000002d6540c1700d040d191041c0100d0010781e4400310f50390040c030058100d41c201001d005040c90022002201c0c0c003d4440d1140140c1010401000241b5910440c0c2c469610b02603045050f803180400c001c2c2801d4410514000d00083d5803c009003652001c01e464402c40c8200c24020b400d9032031f401c0e10922000181d05c00c44100500f403081c403002907001426410301501c1902c0c0d000450b6a1400d002c5405c0080c00f2403408020b00081c18801806601e2005a098408000c0000000076042004a040b441044005001c03048144141e072021250314494124283c002d1802c51400544001d0300c00540d80840d40451140f95145c543c04d5010f940c3c214a00c0041c104060014942c0b511401c2041d02440b0100c51207a500380e1146003400e200004030207030f407004c0c070380c90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 925479712 1250 925478462 925478471
    0x10b13030f0c14010504030b0f040501020409151a0309070618030609030507020f0306060310020706060e071e0216051908030316140a0f080709080a1515051f0c06 71
    0x504040d00080214050035801204440f100040c2d5405003084504495005006030b500e83d441c908080482d58014000311030707035502040006114140e5001d1074141d04040341d407400e4441d2034039030f000e2a4030721441c1c40c43c02058410b00411100c8000031481408032085810700f504400c00c444220b02c44000260030040c8590314018452040c158010050001544291100000b00305403108050361050704a030642c0d030585c4100000c42c8000c4940d0080c200c940c0c0300380d00c0403841030344400da001c03144402190a20700080c0d51400394440c80d10900c492208280417400940580d03c80c1041044100c022030140d113002d01100107850741c0300380352001000000e2600e1015a0f46909201e40300000c20500390300740c03c000645c03e00907410001e022100315078512540f500e403460340422200c1c042d144000d0042003041031184110300050030b000c062260781c00c0c9510400300440440d00481c40c03101155641c0c440c00072204105d000a02081e200d2843d105641c404180c10200107030301d012012a0b40d07119145000713005c4e60070f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 925480962 1250 925479712 925479743
    0x903010c080f060919241215060f0501030902010c020a0b03181f0506010c050f1024060e030a060e060106020105070c0503091005070807210309020108010b1303 70
    0x108007035014502041210700c8548409003082400d210680d2110048400500c03030041c801142c0d440403d01c0c0002442070721014912100c4480c04646540c803041e030503454410003800b0071022508003a28003849030010000c26081103904000400d4900503a41810740e68403094055a00031002282c3c007950050481442d0b6031140410105500269400240c07203640760340f0303c00d00003000b042c2041c404c0002d0280e52000300b89910a07101420001d00795a042c4903a034588a80850000c1c840500714001800003009a02220340e0480e04480d8801d10b141c034244003c0321420784890a5004000c00c5407080c0c83c0041c00445100002420046504d800800062504000350002c41d00810124102e030703c6070300200010307518000180c8289840240050154004000340c080038a40440d02461000403440c14071304028003550340030090744c0b003c403096030402d8880340741d9012190074105075400303100645403c1c0704a07070f203a030b0010340402c9045c0182009210301140c00c80041c145a1804002140c000a070342001861 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 925482212 1250 925480962 925480967
    0x3040b1306090b28020403020d02060d02040e131a0702060a0f3803010207152a0203120114151602100909060e160309060b04060f082b050c030903010c 66
    0x20304d8100e103241349040c00030340300c002d6103520170380d8100e036000780c038032140007900390b00b00912070b4442c2c0305480c030340c1750309200c040744640340010a40d2103101c0090f4442e5510089091400300b90100c0640d000c9464411810484901d602285554020350598000700e00564120000d4001d86020548103034031000c04e4183d0500030441c402c80e140380301350020484032419032a800749401e070310400d00050030240504e041054968505e0f805006076513007102d50041c86500103040c610b00440c3d444034100040e8030201d101e40d9070907803030741c2818018240c080000300c48240c247d0200300740d03030b285440c641c3d051500401c5206a12203458120030310144d0040450700141c40a8001034505a218014400428540b240204c0c14150f2a102075010303030428640d410400b41542c3c400c4010307080541080b038181e030312030384540b0700344e291402018090181d1440300500c00d420044103518000c40d03c107000b540400001107114012030746841d51407040c165440c105a0380e090090b901c518610820704100d0b007540c038080c10b42610a5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 925483462 1250 925482212 925482241
    0x1a210c0403021201050c070f0317010906080105100e060402071b2705041109060f090c0c33280501140d021008070909111206010503040b1306090b 64
    0xe1003219029070401001d504142200c004070341070000d240c0200b02841c00b060b401d0300400c014610900c0c1c0001c0401c4220089441c05800307030f01c60325010360dd49200740400082802000d900c0712230703200c101803414505106100c410002404241c015503001070680d091000b01001080c10b4800b80e805482015503070100020104104c140e41e051409a04085414820060141e5800703550040ea42d81491419a42089601040680016070000320766408200984400508600c20300c0d12503038060300c1e2008514203505140c00d5110703050000004c0700050300700351240d501d1240c0340c80c03201561408903510346c0b6002c0361741d8a08252440043c041303003400b5002030340b258000505070703259a000c060514060701b0500c9401c40600c0c0000354400c1480240c40015131185180d0b641c04445807506d41e4807155162188070407110b21100300410101c0002d840e600e4100051401a041642844c110b4a50301d010f0700c0b44540c0d06006000c0111800c01c810004044c0a00c0350444400e01c0e0f007011b141800c0d03044c1220311400c6030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 925484712 1250 925483462 925483469
    0x206090a080105160215090c2b0516050f13020703030902191a091f09120609410312011d090d0203040e060607080a09060306050301061a210c04 63
    0x506c0340d001c00c01950914480ba0134050070310b180050181814070002c21490501080e5061843c00e010089a0040102140d4100324036000e040a007842018466002c0c49074881508a240541034900c400307081030711201892541c4a044090040e140d00f12890101c0c06000e2821340a54080b081000b42e2401c2e0743e20b55411800c0341d5102c484940055a41d982d000c603d070151045540c0e00c0032a80c019400c0c06000340d04409145e81451900c000141e07282e20b04092041790780311068039156a107912150400c13000482d030303211301071101ca40c0c04586148083e52a280700742a03000300c01c4d800c0060b502c903815404208240d50028007041c090360803c0d071f124109403000d1003c003502c003100240f030b94000c5509044041610505602940c9c09585032900744010390107003210150400380c0110040009501184205002e00316401132a910041120700d000c80040651b0030710f8008900c02e0349464010090443c0862000c11100446174085466160440003000074200c2009203128100c034200412a001d061600100b054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 925485962 1250 925484712 925484717
    0x3c120501024e0402010804050c120d12090807080a021f1e050402060d0c050d02030c0306011805060a0804060209150c0f03040e070c0c08190c050103090f0206090a08010516 75
    0x4501d0103180b0381c0303210412092461000312890340850050b51040700c245900c00e0254040790714091421000c02d4a50303040c81e880c115142c00c0060440304881c1d000011a0481c0b44503d418010680a5203416255104603040100300c43c00004004d01e00078002d000004031203412880d090601410b03007a011300038014002500a10b140d0500b0000e40d0a0000e11506000d50b4014040701e0900f503000032140b0082105410788400d2280500941d002100c8900003944500340400d550b07078407030604100140146106140e0000006c054010a001c2c0362141d00c10f45140406501d03060303105407594141a0300900c100000c10340c00401005400503c00d80c01001043e50244400840e49098109144c0603140c2c0158003030800c460801d1008030359201c6c030038810744805d640103201d40e1005130394034642c40d440d0001d41409800340c42070703091011003031040c11501070000384000e007018480b00c900c075514040d2880c01100b000b413182c8004031303c003801c030b4a03071240d003201809040b0020032a0342008200398080d034160b0b4010200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 925487212 1250 925485962 925486057
    0x71b12061803080402040b01200d020f0607020a23030705010b090c130b030a02091e010f0c030f0f09181401090209010c0807020117013c12050102 64
    0x340745203401500c40e10140c0540d104050b41d1501d50811018090341c10f0101d04118030403a004502d45901c1c2015049400c13400001d040c0403044c0f1402a0500c0d0040000308a01d40080c41000070464000c103041c62050361003d500b50ac802c028100b941960b0701c4141494000b4071000c221785082010551020038034840803902d04099070340349800e20741640316400008d845440c0002c1d04026414a00c800b03140c02040c0d250003d400d2001c51070104625030300c034510290380001400320100803542c20400038980e1050341d203001c01c220401500c1c080c000300a150340460821138040640d00040b8480c2d031051001c0d08864400600d07072480460b20402600580041d26913400001000095414403442190f050003c1a1a0941d43c100c45440350489a08130380c40a034184a070000a0110010b64610054060700041c0542074056038a132641c030039000d00f200d40c4454101c0d074001c2d2111031452694003080403156442540d642d0381c034007880c041d40079008030202a4030185851644101c45c0c04412001001005400c84880313 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 925488462 1250 925487212 925487231
    0x90b0a0e0f0c0319050709090c17060709050111101a0405101a031b070305030405061303090512071a0903120a17090a0b04080309010e1203010b071b1206 67
    0x292160701e00000954940d00484e05280f0042126400c0c1c10b0301030183c02070b0b4684641e10402e020036603222440441e000000c0c0081444100d00598030311105002040040001c0c3c0b0301182c000d01411541d01810f414040c0110b03203841d0309041000000d80d002ca01003402d00070b01d40700e0710301c1d90002c2140440052143c0e04140005080c0812245aa000c0b5015607050401e0417a07014441d000030b80c40909850303000180204400ca1111800b402003a2441c444e549041da60b00e40360802600f003400c040e0030844281100c00240000c00d80c861000340c140c1c1c0b01100c03103030f091302d901c0281e05250495070340c0400c000f24051400e4503407684c3c0200c0038140c5204103405850815100c4481c0500707138441e03000da03032010440e954001c01840350069400d6502200d0303c403c8038640d101a886225510104540c1140c0501e4000300b08004040d0038001c1d0607450071020300500400045d4180c4144034001401880310584000c6541c100b80700301108a00018060f00c2c01151809440c0c20100e80c04110a4600340c96940c02d011120 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 925489712 1250 925488462 925488493
    0xf02120d020102030a0c1e0f0203070507030503130506070210050903010f06080a0b070207080d1202120f0a0b120303150102010603020d03020f2a040b0a0f090b040e0f0a08070303090b0a0e 82
    0x4141e84295124070740001c0c12081081d02c4030623103041514114403060205030001403080180102450042d001542c9403031000e900e455103401c258002070f01405042c0840300043c0c8904407408030500560403d5600c80c3c681c135000c00e0040640208414500e810481c000407601004170301c50690780d0140c1c036200056516940d090303036034010510480d0100c0c0d004061100c00d491081d002e0b500110b07501c20000d45005450300e8540c00300f040c20740b51501414118014490040362500c1082d12868090f101c0360310204041001c5502c0f80001044110250000589480c40740e2013980102c01a590042c04504907008a0400a541e104003040300041e034490f10003a0500110301426024120140700725120000d402d0009003c0030704009a80541c00400e05080444d100956144d40c07406400c03d2100042c6107041c80e81000140e50703041c04501e0268000d4030100c14809004100d2040d4581c02c1b62100ea45c1d406245801c5000300041c40c005440e2002031028004068969004602d4100d0300c04111450122840d140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 925490962 1250 925489712 925489727
    0x2808010b1807030908210702010516020703060203060a0807170d020106050a140316080307110a06050a0810030b0c0307111513060b090403210501050901030f02120d020102030a0c 78
    0xc1d011661006800114418802c0d013124500c0d61007460034a003170610500d82041c0782103900c84c08811410714401000615542446801c3d44500074180e1340f5860000d60801030344503a200e010241650f80c0010002c3c11036145d410390400102050011201c10b0755848664170f10803500c0c0b810b2001980074510601c412544140900e9080e140c004202d40c07602842c0ca450082d55243c0c50081540500410340d010b0452031034280c20000070720040d07014607030791204e40c5000c0c42440341c020710061045030300400500010703a0010954102d6549400d02c1074090312030b00c034031802e8101103500091100780d2160400050000c1c680185006903800d48540711460301e4441101d4446100000c07000345070f50100b00258220500154089026003e0840010040b09840200710005001c88050b00031074143c600e050b452080c9141680d500241001003002194100000140cce681818407010b4880c0c074031041210309554801d22400661030b0810b080303c80c84402c81902a010350012910400307480c0c90304060009442c09400d2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 925492212 1250 925490962 925490989
    0x1c06180e03042c070e010f1403160203040306020310031e0f080d060f03080408060915190b06070c0302040501050a0b0d020c1603051b1e010e2808010b 66
    0x80d500305810808080c01c0b02e500000010b032900c040e810310082d0754401d5110b45018144070707030303450a501c1720510000d07040710340c43e01c0380d501004050541c1009440e852010b41e60001e030188402880e040d15400101e10318040c54101610040c80003050144140344424041e044911500d0b030701500c464a80d0064090340b01241c0301130700c4100a0640840001c03515001418103d404800002d551070319031030070201c14805030b00100c80c2000c0005080c402a0b0702008410783c0047c518004215000010034070042403180541149070503008200d50036070520040d00301100e441c4000e00310640f140940d0030b021303004260501c4140d005030715101c000315042c02d2140884d001d0b10900c000039441c010380e07012418001e40c00030805203140c1c00780d072000407048109444084021802070780140b490100c009240c10700c03114240c03100e51040b01080f00c02e0306000000da2280e2491b9509080c841d20003d4030308040340d180760400e0407000421506150941c5444800700070382065a07203540003007091a10b140b050041d203500444 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 925493462 1250 925492212 925492241
    0x40501121509080c030f0913090512210f070e1c0206030a020d023402150a0915030c030b060703081b0f030403080406230c0c031c0618 59
    0x401840301c1000c9800c00c280c0c040c810b0220f18505070307a507402c4ea0700f1504000e848a40e84140003d144480d4540070003180000c0707103045010440b0b00203aa0f035643e6640c080c280442c0c900c0c90042070849014060304501d0010a0384201014603c0c07034200a100c0034407900f2500c40000c112011b80c102d0190030114569196600c1c103002c81c1c2c1c45428581c0070882542c0000704a1150300760200b00c0c90301000900c0c005031070f41d043c40031141c0818460a024200d10844d000205101000d42c100034500940d5031425242e25060b00d506001d550740d44c0c0b014048480ca91617410030080c0d00c1400c00f51825569140c3c0c04115000141e0b80c04220a00441d41041034070702c61f2110180008a001d004500c0d00801440e0000c0218207042003540340c50000002e409807a00b0484003940811540010801030011500922100c5641069412004050503000308144440640a0389202c1004074200c00380c02d00800c1201c400c003001c078401091015007450b21307201804441c040d54040e1010034052581c1031109004105e802c28944 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 925494712 1250 925493462 925493483
    0x102060a0e10090804050a0905062d0906180108030c070b1306031d010f021308010e060403030b0a050a030c030507050613050108070c0812010509010605090d0b040c0812030604050112 80
    0x101140080c2c1040745095861060801c00010382da47e030105580d0003000080e60118803490002c0801024060301c0450503000340c02030404500d900b61050340700450440403580300034280c441401047c00c60402a60300454010560004520802d0000180000304081012a907500792107492070728040c000c02e051160901da041d101030040901940100c40800201003000d000d540307200341524252161269140e5545900180b5010702d070244206490183c01c991000b488200c6e00040d49030b42d2582c0c010405010541c1d1003852008661354a5616401410000e0066034581e0322402d140b010900079104c00ca4940c414a203000600342400310980e0051031010380d00004540c5800019601d22900801900411032107646040000d50390001030010000ca140500c00158101424011485c0040e0012000d004003400b00b81e440355509041180307500c3d4000c0c5215403544452030003c00001c80b41c0c000c0e06042c054200d90714030220041b000795104d071404450a024990341c0e03034811000c0c600218800340402050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 925495962 1250 925494712 925494733
    0x3090601182d091e060c0e011706061c0e0105011d070c24020c06060a121b050d050a06050c12401106030c03040b0705090a0906050102060a0e 62
    0xa03000400c070b040040000114400c1c240769540b00380d02080c0703100c0388074880440038000c050041d1441405d000c24540d00300718000780c1000e40082c01403c1c40c8003469605401c64400a411520380d01305035400c144101d90401103018020809001800101d0308985443d8a801c0000030354440f10140100d41040300b1903010721544921a04540782d402c0604151038000701003032541c12200c5210341480941520b03040042c2c86602c04800036050120140400d40700f1100c1120921042080205c140ea281d6880106503a1283d030429181550440c2d5a12180c4d00c0140074104106001e0045152a0b245214040c1041555038a4042c007000d400341c0030010000010b005c0010715102c507144845180d82c1c44c2039000d14014507881c6100000f04981e070704500345500122280340d04000d22400890401d0343c2c1100d000d0705510b0140300308d4005000081006d0710100e0040003051007540590204c80840070007400403440f15484410440107000e00b44134050040c800e01000901d094210b100c0c07040507400881c05008003405 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 925497212 1250 925495962 925496021
    0x9100b0913060e040f0201120e0601051e100509030f01090837020f0c06030c07060209060409050f07110a02010e041d07090615110a20060309060118 65
    0x244001d00d2905680c076040410100700701c2c0c542e07078800d511800d03044012000c10f10004200c10741d11498100800e0604059001c0458089900c41c1920800d0b680820340e40c44080c840c0300034880c0402103a812450555010300e103160f00034020101d181003507080701d0603901503110f41c9003240c14914002d002102d00744a540700702101200800d04a2403030400200850710006440301c182d10f0031010190240c0c1c42003864000745807090014000b407480c01c0315a68103515110148e500c1030301c61880c1c000e009650024200342c0941e0350134103640117450f40d01801c00092400032482a030080c8159040310100e41382d4010420010000502420303003030390694500000305022400c4c0405402c1c83c80c2100d103100540103403141c0000007080a04020010303a640030484615011001c250069800ca0030003c003c00c3d504c40404022001940084559004c102c1e00c1c8000e0820780c01c090482542a4810b40c40800082072021040300041c6040c180c0740c039110b2240c280b0454505800171100b2210ba00031414024000385144030b80c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 925498462 1250 925497212 925497229
    0xa11340c09020f0408150a0b0d150213171b040b2103041502010f061220030a08040305030a0810050f060d15030f0516031a040201030b0a0b0909100b09 66
    0x14601c3c83d030380d8249501d518402d42454102c400e04045450802d08008444030306000724401c0c000d00756507000510f01c2070f0300c904001c034100c481002e00150b00081d025080c00040c0f1002401041c10680100003044080d1119072601c0103038901040548218202e01c001d80303454030460864050080640e2615044511920a204840c1400c0105030005010000b841d0403086418040210660300008000d05090b042108581c3c1a03000201c0c000300e0131140000040d840c0320b00100c10f01d0700d4052141b0345410200080d01d041075001004205100c0800d000042100001c0540030303075000c5440d03003c0c030340d901d03e003013100c0c2141c040c41480c0d804080c4103008080c909050000300402000b40e8404640c0428119524138100300c142e10807181a14012114401c2c00400d00c00340494001000041c00b02c1455a201d40b543c20b2501125041d800250f00c000c1011680254000f803c03601020b030801c01c409954071902481508020b000b58043d206081c000b0f00e0500307480980c00c081d207021526841c18082d11500b80960300c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 925499712 1250 925498462 925498477
    0x102c07060e0409170d060503190f0221030403060921050d0e120c0610080607080601030c05160606051014040306020a051c0c0f0206100e0a11340c0902 66
    0x500283c03489041040d814008120176004a100442c0071403a0000785854040810301800f600350824a80c8400a00040c0d02400695011649410f10b0802a008c540e400c40001d183c1d1401c2c0c1c440010004200141d941255103510f00511507004400801240e030140c0d4003c00315400001601044121000d00d44c9520040c00302d4110801c84003114043c07101c2e045260300504a4580079403043c010046400c501000c03c2025013403903005050f85081294000d01008000b802d160305040d00d6588d00311480c4d11580a0700ea1030140344010642004582c10b08000034107803409180e000b211804900309820303001c1c000f05601c000003280f4203031415103140c80b010000d400c2034410100300710b41000111180031995020100840c680000002e0130300100d074000c0d003058400c3e8000c1040d90000e5040114202c81e81114204850780100001d143e07a0f54140340c88001c00c1c0c4803900150501000c0340c2c1c008620540a1011350002c6104445000302e01d8024100d40494a0b106004140000c9807906004840e140d0f000303400749 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 925500962 1250 925499712 925499723
    0xa0201080714040b040503060c040605071203091e06050c09030304090b0406030819020c1e040905010213030506041506080d030f0b04020c2b0c060905102c07060e0409 73
    0x512240c894440320700d03440b99004031084c00300840d090155103018803080f504007890705da419160624004001e803840c0101c1102130121501c9540380d429050203900300401d00c540c4448840c2080c0c0340300304840c0b41d9015980b020b595140c40d00000a410b5a40b041c101c03041e90741300400660070940340c517058030040e10a480c03d503038102d52101d0000001031007000207000c80101c0440400520f0b03502600c006c1c60481c210030405e102d000e07190248555480c240c3c2c0104444078040da408520100d490510b07a01904c607a0700e0981000c21888030010a00802080d0140038500c80c1140f07400c081d98440c14102030714694000c00b00d45400030303d10108030324060350021400850004010981d96940400541243c1044440d54416005860584030300d2514001440d92013040d043c0b841c84210882100900b4054850030081803542c0c3c0d01202400d0040801240c25032400314030051004881a42c0300d0f06500890032950990720541f0001c4105c08040030031001c007035038003550390790315403030b00c42c40401005d4403042d0000e845 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 925502212 1250 925500962 925500977
    0x121020d2303030f0907030f03050c0a0206130e090609191401110d0c0f050901030f0b06160b090c0904020f121c0207170a0209060613060c0c0905090a02010807 70
    0x4030a906480303424288076846016545034500760840301440400102021502c0d001550148001503440c00102405601450280c0d06d87c1c4414101a24061418001960200000c01e103020f40f0f42010a0100079070b80100340f41211506c0f03002d49203070354010644440d0190b0b000710101502c82c803100140c01e00141c3c021944030041002480d0200d0840f1040302c0986007900740040c44c1c01c00b1a4040c0104107620500b46043c8444d048900c2004205004494425042644400f4060780d800d6480d00280d003078020081603903580d8000c2ca144c0f6500041c4560048a00d145800c00045406c14042964408072070090303c0c0001ea55215402c10924010301c00c2010f41c4034055154100c0100c50030400140b0300c120040c0b0444e01090402006480e14500d64425089c42d400c02d10111540103001c2200101d042c0d058803a03551603162400080c0103402002c10307140c907448ac90400020304982c0312004405007400341c015011400c3d294140c00301542c804640200c0c1d1948005071303d02c015441502159400780c030602d4101c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 925503462 1250 925502212 925502243
    0x190903050f0d0212130210140403060e0309030111040e04230a0c0501080c0a050d020906040b160218220c0515040302031c1b03090905040f05060121020d 67
    0xc80781c0040514403042a404a04038131010704092545400504401c050a9242401e0740081d01c1c0005603407809042203899182c004003550340b00262000b450f40107100744032411480c0031069482e04211340c02e03840303982803030008150001aa000c4030b003603c4801000c40029612621801d1041b8000300c0000280040011034040821080c440e04101500c00c580b450796903481c00000602040000e401e10486810801201c2d41175a0400219000400b03200c501588585800d00040c0142c01a54048074110310001005c400041e00e011840e08500d208840c0d5040c507444201c00d103c20b00c1d03001c030343c1007003070300e03200301801080710085000c0511162107004440d01d200e403140d02003100c4030200a0403a41c5100c003c98280114a000c1c0904864850110303122920120200801012101012107100f401546204507105040c13081100f480580110700781400181080e14281c60340110b5a13405417014000e00700042155194a0311510640401c1c240d5038440b19486d408005040840d00c604440319030354103a142 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 925504712 1250 925503462 925503487
    0x90503040303080c09120c03100c1205100b070305030106080709050603060d060905030a0e01120509070e130618030e0d110613030b0403050318060105061204150905100e010519090305 80
    0x161b0341044107001d411588015402c1c1807a080c84182d48282e1981441b095240c40355100c42d105008180e00040800d841d12081d100303042000454000c24004080041d00c5024550024003e41c121613661b9641c44042e03175004403c6a02485900806038442070800c0450494036001000c402c20f58003c98001490311740d9a03440a14541c440464440442e520141d1400035603080f8003e8480300041c103209210030329040c9007003902c421050041002d0982c0d0f42011980035404180210031560b4440010031522201a40e007192503564602c0c03c80001d4a0403100d62082d0030440d812020659025603605034140c051420031a458009041440c02c900351050f0010206180c41a564001c5010b074442036945d040240da0480301000e143e002c4001580024010801516500111041109402d10061668070349150502c0e0040c1e00540599040f030404c18100240180442c2c203120306040c08030208031810000044a0a0b40c4007102c0d01407100e18000f4080b001c0396255040503072882e11030f140062a090100000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 925505962 1250 925504712 925504729
    0x3051f0b030d090815040f1e0c0603060e060618040c1803150605060705060106050a0c050d021c110604020607061e020c0601091406100201061802070b0a090503040303080c09 76
    0xb540004600003410441ca5038103002d1101d03c3c14401d04040c9072031601d92500651407000d0080140b03001c0035807600c4028004e00040045000398050001c11000717640703030301c01000f80405d80101e5514150500105c0c19502d0f25904494591040c14203181222000c00c0802004142285141003402031008284000c0182081820060b44c41a004d03141040d5404011030201c038000d41002d40640420800c0b80d010440c0080c0d0b03e07045407050710700196100b50100c0201e07040c0041140003003d07403141001c804482c82d000b00345200102070402e07a051800e10b0500046400000d01041d0341c41c2038100b480441c0c00f50911030000c00e0201c0c0118408601c01903d0a1049000144a1403080c01c0a5020840c09080c58082c40301900515101c00240300384205012074180d1040060101403048a6042c0102171960013034214000501480304100c110980000340346001c0c2d0702c01001144c410180d0000294085850701c10201c142d038003c0c000314149411541c080d80c1c181405001c10014620034008130341107079a41c030304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 925507212 1250 925505962 925505983
    0x2a030e0a09020d050109142e06030f0e240604090b0f0901110301030218061302180a1a030118020c0714010f0206221a0403090f06050403051f0b03 64
    0x40180c0d10750340703c6522011900706800601102d030a05005400b18002034001c46c1c1c004001d0314000011403900848000d050300b421103a88016000384e0000a401a015480503a04008001e41401040d000c00001902c6030b84c40d07500003801c00c0c110f4211442c4403841250b5945e001c1340103440040c100c040b030b44900385021030445a100d6402c030594104402c0c0c00080c018400e07071071254072101c4d0655043d903002400500309150b412181e4200030700098002c4e51807414541d45190400002c560f118012910851076042c3d01010ba4003c1c105200300013680100452080880c0c4403c5282a0843c0d080080c3c000e05581e180c10351000403074080c451340080140a101c0c2100a1403030f24065190351000c40005403021185900040542d000380080040400c1000d240d5292944101070102044940d807a04c192001d0701c1101ca803070f0b0a5100001c0001301504000c002c01903480410b5910f0803980c0c0e48008442c244903134000100700d0381040c40c1c00c080f60b854408251911406c040f8000c1080310b1910046480e2003060721 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 925508462 1250 925507212 925507229
    0x12251209080708060a052a1e030105030a020d02030a0b09060708070807080606090102011104230904050a020d11130c0306050f0319080403021503070f2a030e0a 70
    0x440206800303401800020003405a40301034500540743c4040b240d1101801071601d40d88645aa0028002610030070743e46a20010342417011510808001c00c0c3c0c1040e40110700b03148003034880740f49922185420001907a049a00c000d004001c00c05850b800e0150001240c030082b60507114280008002a00a04660b8801c409810042001c1d1802c0301d40204850009030071300e401e0042d40e005020143d51f00c188403503400342040d02e5407551680359000403401040d420400c440b105101007800300b00d04145000041e62100e1406078642c2d0149188100202e02030140c40080255000000080c01401e0004107402c82c81e0146003014004804100480c080810a0450112856980035050f030825018454040a42030965801c01d89280038800300765200c8603850b00c403d03e200317a801040c040002140450f805181c0c043d00080d002140e07150610855081540c3d00c00104068040e900072441c4588c0c0a1001b0001d10201b0a500850414002d1340303000026000b03030100441e00c02a0503690701c6802c9010000e04012 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 925509712 1250 925508462 925508483
    0x70c09200a0806040f0c0c0320100e0c0102162904060201090308010e070f08093406020d0c0b040213050907030b06060c0706110a0c0303090e1005031225 67
    0x10f40c01c110403030716000c03c0845802c0c600308003405000e0303104000c103034440d074581814010032090000d105041c03503600f10242c00501ca013942a410002c3c88d42c101a8070309840000300e841021207080160703121905a01e03680c2a460f0b40040406c02c15100404200f003021040d011101c84001c917580901e400d0748290050001b50791124030100406501140040c0101403150f141c0041d1700300b89400414070280b43d04a0002c0001c1480400d594402c02d10400902801d42c110702885a0719070f100c002c0290404c80024100c503c0450000101c107400491201c1c441e4040750358079004a4180d40d86c0c50421013015000f40d130802110b04400c000d50710140f00e01806000540024550603240d03181c00750107440004c02860007500c041c0861030680328000b601400781c5030b641c1050054009051a1180b42029045000d0001d120b9400004107042e004082032050301c11170344049042d0341e1000e0360540500c10320300c909034050340513880e0160421400006000008980c428640850102190041580c0d001c41c1058410007000d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 925510962 1250 925509712 925509721
    0x60509040305040509130305031603060503011a091803030703110c060f150a0b12090f06040803070905010503040c0603050628080715051e070b090d02010f02070c09200a08 75
    0x20800d03501140006e41403180010071b0350000c0603800f0140c0304400020f881c1d205c000e1028001c0e000540600000350003000102d040260040f60010140103c0d80203660311004510301030b5141030b814040880e080011840d54032034032011402403280c0012070901d000c05200b0219801c2050040c54003d8120307110030905410f1440c0500b000c600c41c21255441422668001c00c0086007400c241c5400d01e0105103054207036510a40064280017440440d0160f40c000c660400040040751405540105042e0380e40c0b001460b00c906c0103540031320003610003500010b03007100c007008a00d1007504619401040a442c81e10411044540c501450381036107040301c0384a00351001130200e09030402001d0001c0c956421000f480449081c0c0103442c40c07055003030058140111241c084148202d42d030032540345c1948400130407041d107002c0d40c0c015210b021090181e4015420403071502c0c0740e0a540c0c000c1e100d49981021011004620b465070300300c01024082d03181039207440d041d011025210301c4540900403030b0f0f03800c0d02c0e041002c2c40c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 925512212 1250 925510962 925510969
    0x20d0507030c17040212010608031b07050907080402101803030c0210080609150303090d0305130e010609061b06060b13052d120706020717061b0d0605090403050405 72
    0xe480b40703004200100901c07003800c80e04454070820b40050701030f00c070328095202c03c0304840d014021031b400500d410303c00003406040c01c14959201c0c2e00f59040d030206541c00c550302c0f2410814100300c2601d510703000814200114016250695202e00020142e090000800c81081c16136040c0510340c0e030058000c41d981c02c4a1400b54106607666501c0c003d2a464208100e250a40c00150340c0040644200e218040c132410f581941c0d00c00300100d4041c1e1074005d10f858481c50380c034900241a43d01000480c07070b003000b40590003d04141083c0c2c3c0d0b02e0680f00c043e00d94605050415a0440700100403228102c20041c0304000000803d140344580ca000e804c01d8001c2a46c1d60084c56148801c2c94a194801400340d80f001d400f81c00f1008058042850b45005451050001b440000000b0b078280404400c4825a002c1c0707400c0002e035190001200320482c1d4031201e080d401d90040d0040386845681c1250741c0030360b40240da4049100d00c000355000380030303401c0280c3c0001842a00c0301c0209907012002c640840110b10300280030b001c1481c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 925513462 1250 925512212 925512221
    0x3071413020c030a0f0203070804180b0102010b1e0a15021e030301060c1203020909011806090203240d050106091d0d0c08090d1406070f0c0b1b0409020d050703 70
    0x1110410203602d0140c44501642da01d00c1861108000c0086030782c280e149035842031044910700d44d0407840080d225501e800e2411f02d0303da000c402310740c540c43c0381030301e500c0b9154018001d40100000c0140000032480e00b170a021004544000203240c3d008000383d0003c03c540100d00c0f64840e40b000d080c3c1c0207181c82424260a09410104000c0c1852680e006000400420340d12a50909400e0760054840404420300a016000788c00390300d84141d88031140400200f40601d4106192881c503191400c14452a96500000e00807840b06035110704c41d9010851144041c0010b54000d0254402e014120618a01c0282c94460858502d50007290406458003160758000c4500d001940032001c403800a40031003020840e0207004e6540401000b8600113021400050742d60b82c55052440301c44c0c22441c1ca103404c064030700c010b07602c4040c01c582c4140403800c0781c19003110380c501c145121800075600c18800c100c00e40701e518100540c40c0c0307a0a4260460700c01008041004810360014004d0b20f090400b000c5000c0c104100e024003500c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 925514712 1250 925513462 925513489
    0x9031b050406170d020f1c0905091609060e011b02010e09040b0402240304061d0115030b010e04050318040b040e0a02010e0402131404110705030d0e03031e07020c030714 74
    0x19880216241c00d10380c0c0c049041c1c2da10300c865100c7c040101420038010f8078800d40e56404940d02400200810912807480002001e880c0800d40e2090752280c2c941809030791806c40d0917100c034006138510780c2c05da42e4641ea8a1a0b0b00311a801410044905850700e80040d80d085011203084400100c04414001141403c40400100c03103d11000700c1420f00015081402601008102034006c0ba100c0c942c00103401440b021004050801200074480c4050103004102415030314802100c0010758140000307002d100c4441e40b180141e501c10055440c003c0014a01d9500b00c80c3c2241c206c0e801981c3e010f0900055031244502080030081c080900580840c138000500a0b521a400d070b40c4c0564010090880200c00c1c11020409840000c4c1880c1a1100343d00045401130605a51030300c2c0580000403501701307102e03000000c3d10411707001c16400c0c00b0243c2d040e518192a030009598100c084000202c20000002c2c4d020201ea911103407034411107038038031600d400007031904030168400701d14850001d103a414281020107018504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 925515962 1250 925514712 925514717
    0x50c10090819080708031b130e010504060501090b2514100b031e0304090c030209190b030a1107061e0e0c090c071a0106051b0c0109031b050406170d 65
    0x400c0032503e0324601d41c030915000804079035002000602c13010724035403142544010003141544512603100c1589029147e80944014120b2a400001d000c0ca010300514041c2c03241a5144205a4a090428078080d0040b00d12040810024140000021140325101940c0e0b401078544458203003088146e40d00700214651504060f81c10315010b00b032a51800070b05101080d651842e412040202c030043c441c210f0146402401e8082c1c10310404200040c0e0607006060f09036012200043c1d007409104003101345e4400e0744600d2a00100500001d1031202c000d6220003126500c01c41c0962500d1140c1d0361719000c85402d810f009601c5010007000d0040c020043c4103480040e05660024000c1c00601c0f400a81200c0000348070b03030b042000000b000000c00c44031600e40c1c00b0f050341101404e180b5584801018000c0d030443d40b4105011040a0f00203400034400141344480118180c484518503800c54031043c3c10001c4520664004920450700059136480324880d00c80103080710105c0505031000451507504001740c41c441e1a04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 925517212 1250 925515962 925516003
    0x1e010902010306080c15030c091f030e031306121e050108060c0f0711040b12010c170106121a130222150507111c060f020c030412050c100908 62
    0x8107a01c0e5500905a1b80700d0050149440795281d810094051103034a07842c6d138001c0b881194005c6109100c8030716042904098405101003020304922581e40d001d214100890b002d4000000c00c0094099800020340040031100452048120444a5401203090751901000fa90b41c00040002c01c006104094000041c00396840ca003030000701c4404018081c2c01c4c1e000d000f009860803c2801c903a1554084004034401800717044074243d40441190003404008480e20103c3e08078510425032104060702141611100e031200392440d6024030940c0000c103900310000c100f500c0f221080d9419581ca41140a444001d441c01c007690b0b074202c005840b503540d03503200942400d800c07000c50b00307006105841d0080001c11b0194a0a542c4030022410030044001d24808810b820551040c030300030146205801070298180900010720401113180d0070041248503030901030f0700319082444107102e0041d0781400b00a8040c003500490701d413072000c0c4000440c41040c480c01e03200400c94480f0b0070080c8050a02030070803490a44501d500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 925518462 1250 925517212 925517233
    0x9120f050d0504080309150d060305061617011205210a0905060903151b030a140609061e031f1b180302011b050f0609011a030d03020c1e01090201030608 67
    0x31780d179005200d400d0b8850311000750209101c8400f102610001d03000084280212540c0781050b80e11071109a0305644000074406210390182d00840340d03481040340024000c05d284e8a000c10a24121680100440349806603084a10b480501090b02c0d44900803880041d40e91400d0b034a801422121040e40100d004400505c040007940d500851501e840e0b14100810b48200d5944a105096116014501a007860b102206202440545920100d01c81500100ca001151259000c01844074400c89141d64400011078038240f04440500c507001c49100b02804480e054180c0c1c5543c00d00600c0342401a28410341e80301d1a040103e611081d060760306c0394050802c10321038640704502150940490001034103202d40c21401d100745030b070b98168036000250000140e41c030407a0000d0025488030802c3d030704c4803030719800c1c180000d41a40084800b0640000010700411308500341000035406500f15403914500c40c05220f003030f800b195181e00120350703028880400000e0754002920014048420701c0d08000f650340d101030b4004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 925519712 1250 925518462 925518479
    0x180a0b0c09010c1415070806030717030702060d1a0a03080d0b012a0308090d0530010308030a0507030c1b08040b0a08060a0b0304020603040b040309120f050d0504 71
    0x5600584104140340d52010711100695030540c810034002d046407000314001201500100e0400f5183e0009840c689050300e400c101110040403d6810740c3d4075030440c1d10104040c1c21442e4810340c0b280c2980702900d00b040803540006025410a04102c0050f81d00c40e41d0340c200040183c042086005001c45503510300605584034030041d4018000c400701190b64a510f130b00c9040c1c3c0118080e045680f0240400c000e60030903038a00c1300d81ea2120703000450101c6c03952000b250380e0300c5010482c0344000722141e8030746003041010f2440600440c0030403514602c01d805904082545625043e40078081c40c05407802d581d4a08001c5440012184020642420180b03000e0b0b0f45c1081036488140085288c141030034149851203e424000443d1055600801d0b55400005490951a030428052803203401c04070784c860200781d84c2e0348030880f01c1d11003120003d45c01301c0c2c2000010001038045043d142c0260181c41c2c882c601e203440e03003480c0205080c03102094500810780140c120400608001c1d12452041c54a41f40e414503107441401d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 925520962 1250 925519712 925519733
    0x430f050102030f0a0e150307030219020f10151d0115030504030905010f1809150b070f080309070807090b030d0e0a050d050f060703021e0304020f04020c010906090803180a 75
    0x1d00b4104295884050046d5072103800c0b140d14603c01940240d503a042c4244040c00070f45c400140c400740d0761010f9402d441ea10b40007050300300c4516070440203440b5058508244038003c2c9001500c481517a800168049401c5058811201d07027140385a049150a504000c5000401c1003a02c0c112020142060300304000a0307440340740d60080303c000b0308110741d901411320402d4030390201710440c1229401c1d80c0d40300000e09040c5a08202d41d40d0b0035103601c88074425207401d091001880317004009070000210a090400064050340196480031014040d9914035071603a410074144046507101c41400707919004d186416140c2030004c00108011400d0a01182e05003a01003081c00d0802d2142c0b51043d00281c86000c04e100c0c3c207001042c00000d52406882c030a28080304050001d4000c0d000d80c211262152028500c400e81103002c8a020319002801141c1e4071030024100806940710007001c41d81035407201e954400003180f038020588050700c40c0d8804c5132240342009180010540a421524441e405204080040b4030f19600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 925522212 1250 925520962 925520977
    0x503070e190339030f110909061801201e040609051305160f0516050a0311120d0c0c1a04140c090a0b030a050303070f0801120203430f050102030f 64
    0x96901d03119401c3c1c1441180d601d1b0200c00581c10000300e038200043d0750f4003c1041d500c60744004266a1a070515140003608a41d0003d1404404455800301415a01001406001540182c2d415250f07070300c20783c0302c2c0013005030401d50124000c61400001030000d0320340308020a00803100590708005030b00e06070204403141080d800580c01403180c40c50715241d40d00d00c075404a40c4a641c83c6150b0a4400f82c00f440d09550f9402e085405500181c003010000c01c0c51900480d540c010030300071102003800d021481c3c610400414040034010305000d4405103500024090310602001c22940c9040d1105a18160400c501c5030201080c2042e210307005102c1e02ca0b0166540310000d40c0014690b42c00041c45100030011a141011500d00601107210201c10002182d0307000400700e0a40c595036641e1001c0b83d90381c48542d0010100040c008ad4140c014090600140b80d02010781d214a200400604d488944960100d2180b03900820248482c00c1d06d02c40309100c118481840d55000301402c0c8000c62500c0f841400307150480c000e003035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 925523462 1250 925522212 925522223
    0x7080d03110930070308040302090c03010e0c090d0b010602030d0b03010b0d1b0f0e0403020c0d0206041e0902040603020a091203081602010b03031305031c0503070e19033903 76
    0x343d00d00022200c070318064200c110030011221110b46038281103616400c503102c1244251006800200c0900805060302d0499064048001c05911100d203880441d0300130800d00b98000581e000803c0200304000c02d018001c00030368010315500c50202074030b441a56070012066009071b0401091403003507141d00000004143e08820755000b81404501c4500144a20341d210505211208001084101c1d8568045001c0d500c83e400311086242c924061004402d0400b0307020350300607402e00c0100604007400480701300c100300c201001840503842d514540100d8015402110020354080b0b24031161075000300c50040030348100c60f401000c2a010355002840d0000040440b01c1075000043d448507103d000750010f80b9070310001070541ea02c801c500c892400240301a4401c140c801e1007603100404103021500042c1c002e4405684e6040c3c40c0d980c5554003900c3e961140f0306015000005030342c5040c42e5881e915400005540318081c281006111901001d4132602800c40582c260000c00030b0623411004654082011242d00030f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 925524712 1250 925523462 925523509
    0xb090105071e0e0301090507170625270611030f0a0e010516291915080a0813170304090c03060b2101060c0c0504090f0507080d031109 59
    0x103030300c103d4620301d84aa040344c1640c00c104040007004804980e24081c0e070f030150300c0403000000c1d0250140d550107042d92450b02c2c40864101d01070035051f418500341c0b2110f1003410000003080060b20000f413900c1040310070320503400001d00240311480d03004800184261000c0f000b0b605203003c1c544441940d110b0310321898240501112103506903402803098616407083c4d50003409152840d402c10003109110002c060a5450042030364240b2181440e4055004001c07d0941c04c02400c0401e5542d0020200307100d401410b8520010009038281c010031040d5505c03485180480c0c0c50710703020316001da030b81c5055800c039180708022840e2801c941030f170000c1604e08070f4180c0c24010540580801c0c00740e004003600d0300016140c6c0b2000440c0d03130a540031051101e0b140c0d5070f6041c00301b00582e640c1c041200c510b00750350710080c94039148007000c008600d0243c002819440c0a44520142260142c1e0b50a1070101254412030641d04000c1403034440a80610951030b03603103820b4903a18030b0701c076a020004565a0450b8070040c0c0b1420319 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 925525962 1250 925524712 925524767
    0x10c0c052701060905150403052d190204050601031806020f120103081905030c1b010e16030606060c210e1c0228180209060d090b09010507 61
    0x204407036207800850240c0580c00b541c640100810045007802114068040d84050608010303210040b00c0c1120303040301c05024503201342014030a201c0d40c004042080c0b9a4a00c0d5514040c0c401889500c50070102c0508a0a00200b00d206003c00d031800104803030b0616143c0420980ca804841e480c405503560b0000c00188c0e9003407003800340b444030300950300d921800303e5038480044100801c0034005d0903000407992022100354500309040341d262004070b50300504144280710359400750713500c134000429000340300300003040000702000000c1c0b400c03240c4d24078200105180e0004006000716440350801418180c039119600c645580c41d1210f0050441d01e44e0400101c50b003030400c100e07a10544c100705105500500c0041500000700e0b410443c0d00d90040140d229890b003004a400359020010700d01c3d0081026028408158034003a2000795402054006000346070f02004401025960301008050914015500095240c0c00e8140b011400310b0042c0a4011170f89480c0502a54a4020031a03006445001200c8100c0510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 925527212 1250 925525962 925525999
    0x1e070b040f052409011407050a050703020f300304080a0f0e0a0906080f01091e050a08190e040b01090504050c1209060919031209110306180c010c0c05 66
    0x203107516a045040c100e41d00b41c902c3c1035860303014a40904540c00091103450000514040e11178819140c050101d04100030b141007044c05407018008041c040d0064941d250003003200300b07041941912299052403001c1d46c40c0340202c05400d0050100541c240d03a4142107142903540c00074a80308141e59502400141c07259025054400da840040b881c00140078801401e945a188601130641400b9454950082d0180d200300410144241c900c466085400c040080e16448000e0300c0d4400764080170f940f540660500c0d5000f0410043c01428807840c0842c000c035001514010080082c201c0c107100b18401c0341016822401a030f403200c0100250354080300c0000d055243c0c80108200c9104032000380740708420b81810805807100100307545109560b41d1068502500301245186005940820b0040110346990b00154580031141c1c09441403500c140842116000c2d0000001d2074510f003140c90142e5a103075002c13a0700540005000d1303580c00304401c3c2825007040210341c0e16409940c040d03005040c06074202e400305150605 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 925528462 1250 925527212 925527223
    0x23060a0b0a051002060a0606020f0601122a0609050a051807020c0d0804030b0610050d0506011b050d03240b0d1119350415060b1e070b040f05 62
    0x34180c0c3ea007071031850b6000e5200e4200703d6126140030f1509500040b120700114407044000791f100058603e5038240000e01d606d00441034010394091498003181c8040d80c075a550b04034010341c034480c1e01e001154031700400101a9402604440c0c0904101902000181c5401d14410800c0564034002c0b01c0ca646d400380c0486c9003190040040d40d00c08001d242190034003880c00020011b8a00a43c8001007a0395410103121510903240c0004c0001001001001c2c843c00540c0d0002e60410750501d00307240e035950401003400141c148120207031410f4100315036800300650507100b80c0d080d41c100401e90092a00d25840d84d82030142d094400c03400749040008900982800f030354400400c03043c20348206a29030401c1c1074101d03002228558918046400c089115401c0701160240401d00701e1000500038900d0054055800ea190003d0004c4400d0021400d02c0700100c0038501507107000c7e0140c440016119516503071584040c080d4104800300080c8200300311804141c002c002540d015400005180d40141c0d5441d2413850300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 925529712 1250 925528462 925528469
    0xf12030e0301050a02070c1208090d050c0d060222051e04090b0a05060901061b1e060e010e01060f0e070c15020c0601050f040b01020d0e0d08030a050423060a0b0a 71
    0x551a00081244c85080d503400703080d03030f640100c919403081c98880005108021700e080026003694024480e0080500e01000e40c1c8001340d1050041e205101440310118810030b54100040310140d40219140c0342d0300f420700301711400c07415a841610610524110100e04210552200f10f00c20711840820510140c1392904455116507110480f900035141c02c80c2c7c240d00030201520398dd48102c104a000080280c444c2c8044584404038040e84407040519580c0e114120350003c070030f03528042d01403030580046010b5104060100001c2d10012a89011180032103085a402e50402142e59512641c1400300358148084650700402e6405c24150208207800d1209050102d05550344500e0b00005807403860391404244141220001c0e03620a00001c409420081038032982c2d07403158016070250a181c00918410708003442500409012014410000c0d00d03541d0307072580b00b2a03503001650303120820f200070000100aa021a049060011603074803038080015929a07401500d079503011911081a43c4140c0d4644078488002c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 925530962 1250 925529712 925529719
    0x7090519120501061403030715050406090807050d02010608070608010e070509060d06061202040e130326090c0108010e01060305061504060c0323041a04080717160f12030e 75
    0x39070240b030038502911450141c1448490301c1803082040c1d007030000c2076400342c6500c940c2040f050000c20706040e00404c00180203a50803034550155801061020005140d0700d400340c005040944040d51010342560219071080a0960140a0420030150301c03102440c1940c140102101040d1942d00048032140070704040c0c250b0140c0000360400c00203115a016000311622a254002e5a10011300c4600c01c030300840c0304420310300203200700140944101a65030100e06100303040c692f4140d80d909108a1400f242000c06400100e070708024070003001010054071104080900e86a1503542c14002c1419801c01c040c81608207058403500402c84070360742d02064503035406c002e04115407900d644080c0204640c40c003940c03c0d4003040030740a410100704400100794803440d00300d800c420b180918003007007044000ca580c403030308120388024000803e0540d42407045000915061414074850100c0c0007120781070090025507a200145c440030200881c1001c260b1602c11a44e03500c03a940d580c3d41141c1401e0303480810043e01d40380e1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 925532212 1250 925530962 925530989
    0x609080f03070e030309060d0e07090203090d03110723030c150718320301090302010c020d030c020d05161a01090b040506060f090607060207080901031407090519 71
    0x1a1200c040051441269555510000144003a040c540c0b41d00c5404aa280c20000030011b801c0c01b001a501300b45d006191079011a0201c43e612a4a50203d810030341d00d886040c1c000d801c0d40480c0c1a8140158602c04a811442c4c03850801c0030740da044000c1c19039000c04100090030211901c545030080c81900c40d565111400d07140c03803103d1000d000c04007541c2103982402140d0f0085507484650840c000758401d5440421072007103070320307400c9aa02820341012000c83e483c5c2254072015507031588003030281c105001d2082e0004107100300c980c500030741046510015401054540071051050705c0d40000d503805900c25074101141d07544041d00c950041c42d07028510140c44c0310701a0a081d6503510500c003001b4100e90030040104100f0601800b0003040d42c03801d81d9202d5004200f400040c0c1360404010003480740a034014082c6d841c0042c0c1d55202810381e0404041a02c480502140d1400996014010301440040c51440d1201d20700d881007000e040800c070390094034003858850514122800b2070601003005010160300016 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 925533462 1250 925532212 925532227
    0x2c1203040803040b07080f01090209030109080d140622050a1b020d02192111100906140103030c170c0708060118023408031801050c0408030a030504060908 68
    0x5105034410b5404885000c00400005d508a2040d10094040c0e8003240c04014a80d180a540401940142c9200c0780d25540e105880d900060b403c1f0000e1642400361a8041401741c061809038801350384c002c050901036a01c400c80b510240c6c00601c00441d510f5030080300050581c0b1800c10f03920041c42e0460000342c03911004c1c4041e0312000d40001e10203040100340d13400c0b2021042e5a045000e01c410038060020a248035004000c4418408044402c9012800307180400480c50741071030b25480e2040303544400550070f5131070b0705201c18001c030750080110b41e003d0440355007107551459400400031544c40740040c1142138518206144a44150304848100003800100c038070864913441c42c96143c0700c4c20312400034100e05070074010042c030025000b038540d40d0300d8004a5241000305014181603400e010414004050704801c0c41c440020906800b031402403c0c01c032003103082c4844880070a821030b1400342c0302c044100000e0100f040340000c000100c0d041038403e854082820b458500c1c152000e003942c0423004144440100d490b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 925534712 1250 925533462 925533473
    0x80f03041b08030a020d0e061201230d021807030902040507170a0b0906010f02071d060f030a0b010501030e031902010e21030604111308030415032c120304 68
    0x710030035009915841a941c0d52200c0c400d03600c1c0301e6189a01e000d85c100f80e1301119003034000c0f01e02424504014091504c0d0440c954580b04200328260040381e1046601501000103d4038914185100181950265429183e5400245441d0b15075504084181c000700001075469100381c008100d0306501410520103400c200c20701825031005510b000d180c1d14698000129010001d00a0011005024148203d9900d0b24030044030403014201e80b400942c481c0b200d002070100b080300e5810000443d00a003104103030400c2020400c0c0081c80a80c1c40e44664440071152001c5115120341b1030441d5000d007800074145d020314042d58214024240a070b910540481c03800e69603140c0642094088001260a4602c8140c4160005600815114024000250600018925091590245490305039810484c0d04000e05030380000f6150780150048040b6806c04241041400454805800011010b0402388941c010300415240c81d40400c804030114120074003540021001c06101300c00c0b194000c0c095603a41c1c0d242c00e0401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 925535962 1250 925534712 925534733
    0x3320705011e030f1d010f0603120302070201020f060f061c150209010c06111803030a0813110409150e0f03072306042004021204121e0201050a050105010f1704080f0304 74
    0x4948179508280d18480301c5400c40c4600001e50b070f8442924005c66040c0c80045009410900040707065102c0d20048206014081113020721813080c129400c551894408140001d001190a010010700e4900700d00c0d0380055140f180d0140800280c040058541551000495034030314182070240c40d04d0303d40041d07000b03000d850400800400318901000504407400c4c105040d81d9200b047c0507040054159404030704514808941c40b0121401082859103110f124400a801c860148104031160401854401c100b44503c1c002c094481c0242d00103880301e81da03c000c04a0b200d00c10400018a08161035a154003000039240c540c041c404141022500780340741501d4040340182508080170180300803204020194a4140200d170100d22548201071a01d07200c1c0da803034400915048040070180640c04040c000200d450f8001215000c20b20341c00411207040c168490000c84406030000350412100809640845400170725400300c00441c000f0040d0f20f0750313550800550901500d400260152400014042444240c1c000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 925537212 1250 925535962 925536011
    0x17090309130246023304030305060d0803070507050c030106061d04060834051005030901060b032d1b1305030d0c060b0d020f04020702040603320705011e030f 69
    0x50314143d041e16441c5c0d03018036a4004841700b035400c80c2c0900003800a84a5000340703070443d801400c841414200e5544800068104030b51160020b2130104102c01400000c0101000008094000304080e605040d0010004460220358512a42030748180d4034003a2240d80c003000c01014079005039008000841e094640b1041c14100314600d91004800601d0300c03143e00460070023111002820f0140c540400b00096070346404c0181440540d542e00c1d00e001a0f8250050b00a600c42c4504032841c1510b000b100d480d002003496034a9118407003181500411001c40004443c5601d84c80326078040c0d544038141001002c61190340c03604415054013a0081a04c100b5030400441000340f4811001801500003039000e00c07001c05030040020b944116459a20240d5040990081951038000340020501039125161b002000e0001008410b04600c2d50360300041844a48844200c0000c61002401c425484d003c0002d04403041c0c48000c0d5030509519500103040b134001c0e4410709a540c842207042c440170080011072000c3c15031860 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 925538462 1250 925537212 925537243
    0x4109060106110f070e040201030b0a0324091511281115041113090804030b0c1602010e0d240e01020a140a1709030913024602 55
    0x500c0ca00c0d500205007010103e1034100200b10103031520700705525108024109a052607940c1c014001e807a1540c1c1c0c40440907501928541d0f5a185c0e1103052243c02515030819946068a00a8071000195001e5900054488010303804a2180090340220942d84110303c0d41083e034000707028119501c08070b000c031300810740c000548452080d21390354803c060700d41449901206001198000080003c0c40d01031801c41020b001410403040995822850011524812000d0707a5a0b44085010820080c03806001540203000007005818400d00c0f40050780c00100300c0c40024188805104140100d4450202e51482941c024800401201c62412441c0520310980d0002d4006c5003080e5050344002814000c645280401d9540c3d2000d01007210706d2810703035802800e410360400601c4901d000c00603648800007405890004080c50fa10740801040041400e013210818030341d14010f1100003100399240410030113106101855001c00c0240d81400e242c4299540341c8075140c0c840c0c00101c0c01c070483d400110b00442d0301d22030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 925539568 1106 925538462 925538477
    0x9061810020f040f05030102090114090301110418060603050c0a0c11030106150206150105040311040609050c07030e030a02030307030f0302190c020907034109060106 73
    0x1020142d2501022500f841038004140444005120450085240080340d00001e0407003280c02100f450344610114200c1e6950300c082d007181d003020100303080340340c0d486440c2c1102402e810565043d00414034600800400d80d14020301c5080e0003141a4402035003802c802c00021603100300e0b0303408200c84014803c05100e02c181c8007402484040c00c0e4402d804100220110700003860000028608440300c54088940940c40c1d80100803203003900d8110000400c10145240030402814460b070000c001c1915080c100071003806034a02401c1d840c0d210b0b9540f40c5030f140306401050b503078450b0090040d40c0b5400070880c00000901414410b645e01186060247c202980e14000401403002502510080340840e031840085240c940d111907408100340c1002c008010444040d02c031190324240c1408121002d0302c00010304070414506100b2607134030031003203a00685001038032603466138020b1040c000896502c = true := by decide +kernel

theorem cover : BRFrame.Cov 925359712 925539568 := by
  have h0 := BRFrame.cov_init 925359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 925359712 ≤ n) (h2 : n < 925539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
