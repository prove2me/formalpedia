-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5011
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:27:08.333196+00:00
-- url     : https://prove2.me/submissions/6bb9aa03-c4b3-4b32-ae04-47570791d27f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 901079136 ≤ n < 901258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 901080386 1250 901079136 901079141
    0x151409071b021c150c120b130f020a201506010302091002070f0f05030a02010c020102030d060b0d1a1012061208030907050d030504091a09160f0e0105030103170405060301031104 78
    0xc0c210b0701e4000b084140061702e030140091031180715400800d0380c1c4041c0417540d42c5400c00c00c4d148100300054204070b9008860401e100075080221315200040c010315152040c00307180d8210583e1a4003000007020002d60071040d0783d0030050020042410103400f03100c400c00549331680341d8404080ca68000e0024242802049846401940d0100819804505040145440120b04050720940a117820b101c1c00e1043e000603441c511542103120401440e00d800010041c00050280c00b103e03c40c40c60a002c0900d080ca4503501c02c0403801c8035227920203100841500264018080c5241d5441d1403100404c0107640d51000342e41c000082003098922800010400c03510780d00c10310003540941412030f600b0301b40d12401d440042c02c5001d14042d024405640700950701c803521480c0c40c2c05a0750400202001c42c02c0c41d0505000f001a401d21081c503012401c80d540c8640c002c0d014030034608488406030b41c0c083c11030b031035a00c9103418011200301071001d41004010208103a11268010341c0690b00842c40344100030180e9040c00b08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 901081636 1250 901080386 901080413
    0x30c121014030318100302040b1207120501080606010309060621060b090c0d021e0c1507030b06090415080d0203030106020606010e0d03120b03010609151409071b021c 73
    0x32a0b04200000410034040c65010380301031074141c032a4174200160700c109a0080c031840c1c00c058002200410300501707616051031a284201015591aa4a941881d949400340c0748280914011504604001001e0354400d0f80700520340c50003110041102552142d000d0782049200380b5581c0c2ca03003c0d0800000620150740a82d0040c0d6078282e400e622301c2c4ca40040315090354003070b90103c0e400c401d40004d00c0074140e14055004c4100e03cdd0045090650301d2100100340c640c1d079048400f031002010680c0c40010381d1503000c1d11078880c0740803001d04940d01d084601010000203100e440c00d049a0b0141c0309001080360b5104200548c0e07040440d030010b541d2941041c0010f840c01d84010324513410050607903020030706510340c652100f02586d858141150507000a480c2c2e10064005008142c1d010742c07800400140d80c43d103d802c000c0c49481401d501041d40d070344030898491a407054082c5560049503d0f008240e91912421480c1c2960015110380350041243d5400103648521584d24031681030329000780c1c4001d21550032110107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 901082886 1250 901081636 901081639
    0x61c0c26060c04030807260a12060b0418060801050705130807180209011b21081b0c070306090602091509030a021909020403060e010b03070f0308030c121014 69
    0x2440c81c01c659955030900c40c901001702201c80100d4170350100809180400926500d2400d440051400040e04000c0d5401c501074200005440e15010800030b03882d480790382c045e103280030782c080d2070b02c2d080202e0240c601c00e107079913100c040694901c000500740c0c10a1240078042d00e255980c02e40d940c03100340348000088001c0d03005040c99400001041140f800720002c2e5002e0001e12400141c0c442c03c8000044c0c50045000da0b2554400825202c503804115188035080d415070880f0300841d00801d10a0002c8a00100c1296018129040b021440b0203444802014001c01c290700c0c0b0407030300400d03182e540d200151921050115090340d008070b00440b0300d190054100b4595100220a1402c0250140000e80c0e154403940c0041d0140f4074403c44141407071903649059019200000c019507135103a81c4c1c0b03001c000400985800e24201e51a25079808624600031035041e0842e207001c02c2d00308000c1c0c01d40e180c6801d00e60004c1c11a4a01039400c01c0324084040d2401d8400c0c5c031440b0701c40ca240c10854505648012680000345c1c4c1907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 901084136 1250 901082886 901082893
    0x30c07020f100903030e04091e0203060a0b01080604090c080a0809010305060f061909080a03180803040e04060506031e03071a01150806040207061b0212030708061c0c26 74
    0x35042c1c55110042c02c1c1101d40500d80750780c0c00c9400d2408607000342148440541040c070442940c2c8504401c81e003031001305030700c260100d80380c61b031b07030031043d84111040444190300203400480840d2492509030811400c59000d00c40d02c10303410303654901680c540f600c5500c0480e480800800d0070105e80da0148281e80c0d02003815550070280d1022800041c0480c440c4805052030300000c4810003005500c20326104c005080b66404a441c6440c0c541805030290382401c0031070341206191500402c110790040192030840e503844049000b20b8984d55900700280030001c281035054850342e00d1042c0d10901c80d0480e07944601d84040590384c0c031780b541d0a00100d100440000750300c980341010010000300940500070810109070340b070320550944070900007031302900c11100081d02c11410440d401c00300442004582e41100a270b41c08486c5a0020100502e659000c110b0f41c800116000900103800b40c00d0022540f90f54503c1603602100030010b0341d6170740c82c1005080e000700300e025064801c0d26030004140001007000c0e001a0004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 901085386 1250 901084136 901084159
    0x1727191b1406042303060a151202030c0d140d0809010506010309080d090309090f020306100e1e1201060603020310060504030b04170d02031501080606091f14030c07020f 74
    0x300b40c20b842244120b0000024907400c40e403250400b1441035a55a00090036100c450030070b880200003a11100c01c10341020703030410000240303c0d048940340508040d0f014001d007140b04402d00802481340e0203a00f054400c007a900c80058240401031002d26000c3d0728548683d1a1030070715684450842e000205a24149454800c1720740c08900641c00361804a80e00c1c0e1004188460b26140844000400350300c22008281841556a0001c8041e00510321500f400c2c0c4606e104100a0720044131400303484d51000d42c0103010020400c40000104010a030811005880198009900300c64642111030a92103c80040c0e40801840007048503101a54020215440d0040c00c2600b103403a507118410300507100820740c1141c04036007003a011282c0c1c03d80d2142890441c0454036450b00400700550801031552850010310401c001880501d010703010394256040c00780503d11994850584c5c5090111031603d80e50900485004200821031001d0085114001c0e5203902d64a80b60785106225107031803100c0703038284a01404142c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 901086636 1250 901085386 901085389
    0xf181f021b011a06030702030c191101080c030417040518040620030c0307030e0709050108100608100e0115031109072606060702060f0a1727191b14 65
    0x2451800050f00300c40555603070f2182c06040e4614802e12150403820300480f40c0e10700c021803000500d807440c0d9010380d15070034001e8240001103c503108101c400030040002400458081081320342104005180300305914503058581c8001503d040060011500c00b48203602040104a9240030b80301c4c1948145015813103403100702040d84c0c0640002000c0c4901d00c0c1021001540c40c601c282c00c804070308000354040d9143d140c0ca031040c0c031300603020074064003000384120090031a0340d0969100d01c004861100d0301038010301d01c1841080001d002c2844410740959280c1c00021003190300d22591070003c6104842490001c440300050028030100184440107000c04040d030708032a078180308500c1281e108114404c0805586203400601c240c05200e00280d00b069001c2030300c55003022841c00605800303040340c40d184025a200c12410103a101c0c1181c0d0702191200040d80030340260f07400900c010f50a4010804c0c1da041d02131001c2c8100301c0b18015a01030301e140e10900c2c04494138507101c40440f0064901d052200f0500d101610 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 901087886 1250 901086636 901086671
    0x902130203360309043605120a0516020d20040e01091101080403021f060e130302120f1b030403120c0c0e071e02010c11060f181f021b01 60
    0x540d2a806aa29491039890b0642660307038a9446400b00801b00d91040c1c014080b18030800862113080f0303114031810b519244030511140513101c00f05801e61356a8034241499248080c000741080040380c00c101091690b000090707603100f60313003000c069009038090a1a500b008210556055200d04486a40b4142c69100810b45c248c40044a138002801c0c0480d0780c1e111854101d01e40350301c0222128036480190440c051108480d00040e04482184501c02206d44440c3c00c0201c034000660300040140c0d103c00d40b0001002500c00151103905a0740e14450b051541020380340c10008981034851403250000a802c0c020400c02c07119104e00d410701c502e4905c0124130b542d070300c1e841c85807180d00550741140948400102c101d8441c42c0540340003250384002e41a03d480d85080039019042241e007910208484100840003a00d00068807481641c1c6a05420442d4580c0f01e0456014901c03400c0d01740311030103214654000e1000c040400e160404144000503a0340703d810703085c20300c1c4114000001240781d0410340903030b03c40d00040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 901089136 1250 901087886 901087897
    0x120504020a030f0312020304031706030c030604060c0917010209010207170c01080c07020d0f031407081605030c030423090108030d0c0e0415080f1f09021302033603 72
    0x100703c84075000c0305040594601345011940350758030b800003040000305079200340c444100c41c1d10f0240030202c548a440030181c0301d0b02c000d45000d4040e40320100007004100355402c600d100f40002d0a0680c103a075158107030724081044008580000380e4000864a00d20350b4100102c5004140124034031110800d43c441c501d4554001d990000c0c1000b013480b02050303020101d1022102265401403882d000340e090340c64107035003410b40d40d03000764003207442d20050010b1250088100d6047c85d0b804640b0030b15000030300096680800c80ca41c0c041e03596110622050a001300200001c1002d850503141000f0104c4000c2585204d03c40c08030700c22400740c2d10385001000082c000105990544441d0303075002c00d1200100404031070340c10100d6929988682441e0310080700810400900741035560070026690b60010208030581d441b404403031948403118898180041307003000c03540071007411480100920782c2e0a5180b1401c00a9030010359145a07601044100a9458000020500d40140c010504441c604082c3d500150f183d0045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 901090386 1250 901089136 901089143
    0xa11041b0c03050d1a010806100e0d0c0806092b0509013608010f02130b0307021002030f01060e180c07020d0803040501020c072108181f120504020a03 66
    0x45010700d07080600400c151032440c0c4006900304100c81c007000d50890a0116111854042822200414414100700d8000c8207034400d15142d58001c12a1a010b010034191310880c280c840e8519a4400b1581c054140400c5010780812030080c100d103501c0d902c43c09103440b01030006403000e034040c60140e1001034000d0166080000242002032650749000e038103500d46190300f54000ea01d100384018144008807080881c00a517803904000b0050800b862500804a1051045400014005103010800b41080130300030342d400f14140c8140c8505182c09844402a82c1044d242c5076110b810260061001a91282500c00d070940c00310399168505ca50080303600448007010b0145038000c2d02c00580502591500700c10350031100d912408040d6685020304009001b0741081080d00e50500808000003000c000f04090f0304035404610314150140310141d40d8400703080e403001210010002a160145210b5a0780350400254203101c21a680d03c15072102000034001c506611001c14120710f42006d100168444901401c286d951 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 901091636 1250 901090386 901090397
    0x1803040e01090e0a1a070210060b03041212090c06260c0f04030203190309230423071e051806071b0605070203060f090a230706020a11041b 61
    0x80b1043d41400c0500c1e90a028081d900246090b10100c0042070000c1d1203003c2c180c1c02c0e0342641c0f490030700400981e0b5192007030350382c500e038144080303008100e4100b066100039103036040c80c0c980c042c07600328a0015510000015114038840100400c01f0035007160074046000070181e44010180c000c00360320580141c0c05006010b550b4804503445d0040c85590040781d01540d001400c994044071252100741c00c10080365003c900142c9059070000f402054105d84c4661542e0b10550b41c0000d01002d014080146a40407100e0301203c4460721440301810a101c3d098081c015036a2102005c0c03a444036645000b400403940c2408201c0108101c501e8600c0005000d144d01208541b515610469801c1002c410000703c03000b8281c00d00040000611203410400400035036100f40c094854aa5920740b0040041100300d41600d02c1d60003450b42c100010301e03003a40402c82c208441c062590084041d0600d5031410040d500140301603030100740300406008003500c03002078040b000ca038244140d41c48600034018044060307810701c00303005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 901092886 1250 901091636 901091651
    0x91902010905031f0e030412030c030c081b1c1b080408070807171b270903070605130f150b0303160210090b090d08040e0c031803040e0109 61
    0x20310035140a001400028100c813070510720000300034600292140784030903480c03400d400300e0f10443c40441650212404101280e0251b80581c40079203200000500031130401480a4202c400101402c014018454484580e1150000d100c61014035000c03011040ca280c22050106071041c240c0d10001111007840d41d140003824001079464802c0540c040d641104400c2d0088950100c0d007000300259243c03c40310640d020201042c16441d8580d10385004041d40d2290708842140c03100c2605102501c20741e014030b405990702142d14101482002004242c07400318181c0c00c001100000d001c0140641030300320010291024600300c0356940d0107900104510000d00813403113034080722036501d2503502014003d440a01580c0e56401c89891940701d81c0f040380400c80c850185902e2034442c2c1880749000c00e043ea04c004400c039180c5490b40c02005044030040a013280d05503020040170441445141a00b1b000301740c11b620460f12400c1c090a020200b004498421403140e100b0b00c0304102040a0b220030904541c803208000030300c032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 901094136 1250 901092886 901092889
    0x9080c06090d0503160510020a1e0c0609030f2a120216030c0e090606090606130f03150c391202072d05090a02071b05030105060405091902 61
    0x8240d1140058080d004c0407888a02e14011021241c040c68401c00649400c4108043d40034101e0203011070000002e2105440840c1034003e002000325840e9990500000c03034403943d542c0c2c1d0b082c1c5405c1c220480c006404201c01e90078003030700081da074070b9401c0a1060500301d968a070034100c0406c3c41345810180010502910a001e414002d000d180880070324111151003458903030404034000011480380e420038041000c0040c4000f00c021604900480c0014654582a102c3c0d008005090704000d1001d0400d611001c4009801070f1190400d0005602ca00644005c811182050f54220390f00900688107100d00400404418006100700d00d2500107100700c071011b6924580c900e41412120102c0c0140000003516070404413540008241085650000117100b0460125582c010741400c08455640b104500c0e04042c0824507002e8411640641c0b011001810700c00c40e500e844840c07122002098080b403469410034005030070300303006d4507030b00050940d0148030504080034804e03036030840703070340b06000343c2407900e04a82c00c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 901095386 1250 901094136 901094149
    0xc1309170301080703050606040204031e05031c0f0b0f060a080c0f030106050d05060a05033003130506091506090a06030204050c090a080a03172d04110109080c0609 72
    0x100e440c5800c8864a80da121428266180c1c40d80c00140c0d1980300c1c1400141c441e192500071241a80d0b44841e0520100c00b00c81d096040c2150708040072165070105000c12008030505d5201c40c52000c0c1800d0010a6400c515003d14040701c01203558a40102d5284030006120345400044032828a110300d800960380e501e140084420713010f40320012565400010000076200ea01001500303030050400410003840c0ca60310f04200141001c0d100b01c9805801070854520040c2c00300e104000307404150301d0a030002c204c240906030010703030088580ca889010010350170428480d0070884140d0211942e07006020400d80c5e40200880d9200082ca22489044001c00084803c80180c00030802564040e2051109090070040305680750030040c0741d18081c0808610019401d02c00083c0170441c0c9805407a5a000050716031602c042c119801804569840f85c443e038042c095110000c404411080c65540c0c01d00241058608501010300ca065014100325820305e00703000c24800460354900003a41141e0056a405500380450701 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 901096636 1250 901095386 901095413
    0x915031b080402190608070c150504030906021b0105030610030f110d1a091614040608180d140d09060e030901020c1002190f050a21020c1309 62
    0xe15000c61458190656004414540918400c0f03c110100b031440a0074a04080118442d440005000c40c000c01c2125000c0c1010081150180d9854000510b01b860348206a9505135022000258024020032030315a050020642d51021020a106900105030000345a40006400f1038400c0703111381100700c8118080d5220750300106500d9414404043c1440b00510039402000008007030504100100e560113115940c9400a0700008005041e15100c1c1c1b00600b0440303070031040240621030440c007d850000b0780030001e8001040170b95500341c0145405826103081c1c6d2004200d0940355401035030074101d00381d0050400091290200c0a003900c842c003204140d00070307103400d070b4000e0075062416140303200700135020008001c0c03198203030200d41c4102e01501c248161031100540210040e0080b4100d40088101c8403a11104940544006c8140b06e94031340380c00c0c4c104a551041190021500c075004002d80356010910320324010180064145e01c070940011406e440341030402c5500050b42d91a02c6810011803d55110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 901097886 1250 901096636 901096661
    0x1606121407080403021204030c23030f0303040516060f030911101806050a050301231302070203010c051c05100902040602060a180f080c0f030a170610091503 69
    0x2000c604201c00007a11000066a09070014024002070780c4a01d01c52604a40889621100710301e801d501d0540100c2c0c4c581c403074203440041e501036002888082d0741c081014110483c1030f203000c0c595a04081c908940f4081e01c203c54207000700182d15042104c00d42100c03041d0405641410046444d41c0ca41c030b0600407504518034110b6101c145440302c9201980c2c48000360041e5468481ca1480c0302d6100c400617103090080b110100300041d0208018414000c5032a101005414014140c001180c020400038044c2400c1091509515030f0119440d42946001d0084850291060811034030307240060400350749007141011140240340e100c80104152000f80b5801000070700203804119220341e190200203480310415150462400e08200c41030351001901e00c046188a40d00484145951a865503032001603004602146881d01911210140300e01c0c01744004c0104c032240e03a80f40041034682541981d0900341c060301c068003c141300d0007024225a048450745054400744400b211500380083d4044002d0401540141d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 901099136 1250 901097886 901097921
    0x30c070515090312090c0306010501120b06040e150a03021c050f0d110d050306030c040f0b042a0311030403080c040b040f140303180f0105040902040f080c0102160612 73
    0x1007420240072014041098422070803c80b00d8540010341542e0f400c0e51b410b0a07500d5000300c001040250f0081c0d1054249643c090004035884a03960002040780d0840c0c0c0c0b1000d4042e4003a007c00119940c89466210042d40c00c40305a82c1e02030031500402c030241c455131103a510a85c404001c075424810200603841c1071124900c21035040c194040c00007410081c03084001d210604ca856518049180100e00396841179601074020f20748902d0510802028220701d401486185594600030742458482d030041c2c141d203402c11000c41c00c1211504664001c1c1c0130003a5007000c10103140400c0034000c041302000700d075001501440d0800164a43c40f0448000b44100c3c0c1c4002651640001c0c0000d2001c00c1e44d000004581c0c20214480c035081e03540c0d0a06440b40b19088018498507803403070010764203190000d01511080c0d8185440e0381483c0c0c5a0071220100c1e40103030886001a50180020422008200041464a1400c1c40580106041110740a1201f000e5000d00401e004841210720b04113480d81c0d000389074203030220040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 901100386 1250 901099136 901099141
    0x1305100209180c070210050f0a09030c1d04060b15030403020705010f05030403212904050a150b0a031e09020a061d041503050d0203030f0906040305030c070515 70
    0x2454000d41c020390310980515415048000d9000002d5003061143c0d000b03141c2c052070404a40c1c00c00c840b286084000e4428800144006407e1140407800703800001c42c10b0319030f42e41c0a420f40c101001c5419a41d446107035030f4610018503002402d41c1c1101c0503009580054045900c55100d00010f8042140c0301400300a00804030070417050580c0000e11400300d6900b038031410305010076100d040700c043c0310450b0094081071010030090f4500e00045004180e031015a000091410444042000890343d05d200c92440c0030b000c0c112032030f480c1c50b1a110315900306c071070f8000810030591545104100c0d8520f078403414003861000700750722034144d011340c000d580c5c05801540b41154401805800e04c004106040c820303402000d144d003001c1100390154111090b00c07140c069251081e0780c112402c01000e845107280d215002081c41c0000000100104041d03415101ca5030080c40c3c40c2c8c9400070450b01030a0000303240c0c9246500000510000c25084801c07650404898203600e540c2e021142808c3e4a130200f59081e24981c100440304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 901101636 1250 901100386 901100413
    0xc070807171606061a090d05070e10170c0d031b020603181009021c080712020309011101020a090b090123031803040f0e0421090f0603020703080106081305 68
    0x2001c2a603c03c10b8100a0a920345981800083e000240c0142c50841004944424030f0121040c400706845903048031110390700d446081070700b40b000703481d8a80c40e845003e00600107030901215407098181c00300001c0684000000000f40302510400340901400a1003241c186265a004004060290040c0c18540e50b8184443c04c40c82c1c004907200040828003e14121021690f00c90140c2400d0640003006000d8100151300b143d01d11000d00b00080740c082e101000750702c000030700b80151400001c505030090742c2c40c0e00c9102c00240c500150008000c00c00c4e407040080d220f00a0300425400305a601e80e85240e1b03110f0360007500588003a040f03059050f5111802c2030301e070504010314900a5100d07220f84c0c52601d8a07688400320741d41e0790b40183e00400202580b104020700001041a21155000e070140d410a070406501c441684001c0c0c6502594000081c0a100103011010244104000411452804516016242e18000d0a030715040c0900010448088046070710300d03442000c0444516040070035140701c07050191 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 901102886 1250 901101636 901101667
    0x708091023010503060712020313151a0d050d140d0f09290609250305010303020c010c24020910030b09090f0a120215040b090f060c07080717 62
    0x141c08560480d90320000701c0c140c1030204109004400f00c0d111201662034020380320300a500000c04044440e9084106103021544003100e0b0001e040c504035001440d289040100020800303901c003002d000d404c0d92001000011000a440030644c0464600103480f60105c00400020f0b224903604048468105441e220200901e6030000034054030800d1a40c002503408030402c1d1106400c1800c15012044100c001002814800c5901d42d200301080c0e85140f400c07820950504240c26481031200000703075104018400c25404021880e01d152090070311410519040e60303130340341d02034501c040f080140d0034150507800d0f20700c0f40c0e40550f020000020074591401c410558020010001c404000f445402100003044110301c0108107044100040b90282070101103a4480030007030b0407010101411841000b051121100c0c1000314603000e2840b41d25034080d94204445158502018001e0030400c5412240500c18070f00b51980444280c280d1000780b43d80c4400c40d60070640e0000306000310000d40350a0006010244000d00d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 901104136 1250 901102886 901102931
    0x615030e07080d210603080408030a080108010b0604050423191109061207120606080708150f0d05070801020408061602010c0e040b0409020d03031d1507080910 70
    0x180c0032558107603501d02005984800525000000c50076000c8003004024090810740c5030410455030101703204d0b40d43c1c0c0c0c0d2a02d056116038000c00c0d0b10380000c01e01d540b010b503200c1c05d820300602201c1c00a0168502e0703080001c803940314a2190358440c03580c0e01496001d2068500702a484051140d8400300d2a00c0c110490000410300380c03004c0c803103003032610b40c02c58440c2c111941602d01001000c2c1101d0f060481d41c01d075000c05928003411880070b020030515800200b6000b03001c0d1101400190b51201c010707062000002e002ca5401510028040d104c442154189854005141003041c404030340d403640e0380c0b0003400d0040c02d113191074026030415400003034007064540d0005581d0380140144140100d1559404604074222034050201c0d40000c0c14103103403c0410302e000d8214000300d407402400080e004065900180040043c07150803070100707403110070440110071680e00e880c0d48500503c0291401c02d4000c03100005c20300c0c00420030b506201c0c0ca0320202e5032420303040001030404000a8020007082c01e44ea01116500d0f40007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 901105386 1250 901104136 901104161
    0xf080106080f0405250807050108090304300305091005091e060d0207050a050f0a0b0a09030318051b0d150c1b080c01051b07170910030203061c020303160501061503 72
    0x10004001341d15440790459510bd10306020165080a0a1105501c5600d41d0400402040d4100b0b0071440a82484001c80000301c03886034583d1540d0300084000d01c0800050292407205010003441002d00b19200c0c4030024035180010300c0c1c03103040400041d0006a0314010000048159440841c04204001c00020b2940c3e4841c0298101c80c0704210b41d82d11a6601c0c01c90b807800800d1074800170081014142540c118a00d103c2c8242808203020005058900c0e451303040e84019522584140c419214003a01d07032242000c403101c10303210101100d820340c070352481041220310007440c02680d032000075841a00c1605030f410700000c14070903c18054114104483c0da90404c519004580d4640804500103800341360440310601c8002015500380306441c1c0744d040818a403c82e8002420004000c009407655403102500c1c42c1c1308440d2030040c2c59017040720502c0380b01da890f900d110101030542c00d118400369900209603505492014450301680d101490910b001d001c8562003a8034031021044022611740e01500301440403d01c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 901106636 1250 901105386 901105393
    0x5091513081b0603091509102a0e0f06070c030f2301062102030f0105070918090521070503070f060b0a14010507060b0909030a0f080106080f04052508 66
    0x10500b0401955200130b494000311640700c0c090007031124240f81c108175403152408080d2031340b010401e185201076905681910409201500500b02c1e00c440801404420000615040081e10110750228850100280c0c00b41e20956002c200c803010030841c07050302009140c4c4910040302d8147ca42c54402c9500341d2070074425000c0c0701528483c4411080500c16002250600300119100c040b0396907148588542c2903070207903018050070a003041883c200340a0f0301d0080c02c0741d81d1a8024289409074408148001101da04903640c200509940415000110740381e82503028200030716a040c1c1341030707146590310414400400340e01010901c0009e00c00c0881c0441101c5004d0403090104c1c4207440c040081c4180e16010783e4200c6002060000813951144001e041e04038440e010028800d20744200145070840101d449000c9940005603070391000741e10500d599880d6006081c0451f0650500e180a410040000c003e41c8590041600082c00e010341044a03041928400c10a10b11302919040500c242c80c2e600e000740d0000d0b10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 901107886 1250 901106636 901106683
    0x20010614030d0c021008041104090c083013210b01090c080705030603030d05010f08160b0913060902030709080d09030f120e0306090102031f060509151308 68
    0xd0080350426443c55000b030407490080300c1400281e50815024105440712040070500d4071113510b40d0312444c0c442d580101e2440104910b0030700d40e245000d442c00d01010780003c9400310806d442d070140c62040001115909400d49904190300c20594280041d80050801e40382c9600c601101044010f0148016004840d041d009a0320b44034020180c130038149003080000d09a000040381c152241c4007440d00314800078103032031401700e04c20000426113000fa003140c498055424001c101d030302c10030410308080103008012141440e2521940c544203010303114100d4000d1100d0300c1c49140000341036200c0c901800c480d1070700315103908100344d0040c503858040c000e00e00c0342d1060b4041c50f00200e00507080d000850341e0028010101d13103a950344855004070a84581420702501d011482c2c284e075000d00145108000031400141c81e403410b042805103030710381010400512a079600d403d2140603401003c44000d010141d400ba0700c540c0c10343c00e001e0120711494100c0c00c0000240a030200d8401c0e40481d04040c0814203d06040244 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 901109136 1250 901107886 901107913
    0x131506051e03030d050601050f04030b0105181027020d05090c01030204051021091203140417071b0602070501030e2806060503010c0302071a09030a2001061403 70
    0x7580c0c107a03801e81c1c16030050104458840407a0400c076070220061402c0d41c14801002d9480c1c0c000d40240d0012150516100e00511580c102504410101112000390250300d040801c0002954401d40c014003010070b10018980c5403019158225459020340c0000855440f0140c402c510002d240a031610302d0343e4000c1d6220b01003158424003c1c2c60942c4c0c0d008200042c40c00b4070682c1034511721011071807903512100c1100b0510003250507100e07840245026034040c03007100d40c207801d006007124507100b444a9604120414440031030031580f014213290000c2c04405586502d076041001f4590403100001d120b10002510108600d50302080d42822174400383c17428070ac2100c0203941da680741c00b41140d000c0d80c0903020a000800a41c8041484070200c0e0190500044194694000c6170035503403445e001002107500069580b0800c103149988910040310714000d1710a6040c00e107902c540320301c90300c0707400703020801e55150040050880000359040e403007032500200609a0707603007624403040d0381c08400d2500c41d0066a0903072451 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 901110386 1250 901109136 901109179
    0x103080333030c10020c130b10181719060b0a0816080303010b0702010509060d05310b04080901020f030c01060609061b0f0c03080d090c080c090a0513150605 69
    0x3c4440c0c015050350032040050000034003900300c0c2c2c1010148c07680081e41454a51a500c0e03200c1d0f210303d41d1030301c400300ca4070b9540c940c03240d40d140d10030019541007030468404001c1c0071404440300344450900c4030034000541031000c041d0000e09a00c5034003455610300094900400280301e000c1c0f000c500c0340854150340c0c480045442e0302003407281100403a020802c1200541c460001482001802450b03142081c400d020780f5011a001111052242215148042c080300102c14240c0300f600c13424070894098216655070740c62443c5e4080d100414140c0d000c650209607030700030302079103010700486c400f16a1202e01154030a8060540303481030401003201e0201c0820081d100740348580c1a1007480801801015056540c403802900c0d000082c0d170500740810010001070700301001032941441085020030f40900318101038820059640c0502850713481040080d80350745812200c83d46c17180000b400010369542c0c655524104140034800200100c114243d03000442e002a4841c0042c0e0b41c2c284c851070003071515000403042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 901111636 1250 901110386 901110409
    0x3110406021905030714010c14040605093001270c180216080c07080115030b0c0d020a050403110603060d140a0c06022a090103080333030c 61
    0x16008052103a030401c4144810500c41881801205c0c904201c075151410113400140c40004141d440b6401080c00a074000d20359000c0340420030000c4d00d000d18148010305140300c3c05c158580114200c540a1003214440641340403001d02d0f140c40d4014441802103c00d00900841c000500201809640b81c240342c4001100c90603025441080c10b503030b603820081c001540c000342d01188521683c08000007075600c002854020320030b81c4204c030b043d80c0b80c610280d42e403030a007401130b0081d2050341e00d01030940d203240f070f41007181c50105d03608040190115181c00c8902511445050f00713203612107000080022180c1c0c0c0c004001c00403139009054401c039030401e50b4200041484143c038041c0d4403202c1080d650001c141d908040c0302d0307150803407011111075011503611081020305c039601000150b0003103030054108684411040350300750351480c618059105007400144d0448010700018003000760120004c0c1060a5007500b40301301d0740308407410303243c07500426400305461903480810ba0f000f03008080c00e901007428042c01048 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 901112886 1250 901111636 901111649
    0x3050a11120c16030e01031d19031403010f031202010c0c082803020a0e040e0a060c0522090b01050a0905011d040911041518020a0903140607031104 65
    0x91900c107070840c41c442000c0010300a0001000c040104289400ba440c64402c0f0103480b94a07403e60324074894001500315002d1100140347d02c0540309803003441c0000460884d43ca68000c820942102601d410b00300c45201c003c0c51a036500c010b0010020552a00951079181203034429501e4400c0c0e1207900e10202c1c00e90b078802010101043c0c0c00380100c40051021009002282040030214021034090301b204419142100074140c040b81d8000307110801240e226501c081d017000145c8042c400140c4111600d551341c15600c001030207075665140381d00b880a205030102ea80e04001c00c61101d0181143d0481020508814860141418900040480c0550080060b10030382c0f820b50b152229198078050055031901400c1105044204056031003a5140c1c2d518401c03c84081d0241c80c940303040d5100c0b001070004440c0313644c40d80d10302c001091108200c0c80b80d103d82d105241e40b1101e4000740c1c4800c42244240c881d0041a08010f080d840710b80d0085141380d1000807028403e044a80d010312012641c3c82e114407003031040c0c2c061070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 901114136 1250 901112886 901112921
    0x20301092f1836240402030c0c030c07081b060910030e0313030b180303070f0e0604090c03060501080c0f1c0c0801030c05060307080118091202030a03050a 68
    0x20020795010180011060102800340b5980f1500c8400b1400f048140b20049000c201290241030041a0b000054591040346002889803e1420780520444c655002c0e00701c0b071056400200107a030b04802041581d407100700c101c00f12a01c40b0602c0b41280d440f40541c1c01074001c10321803441801003550300011000540700d806420185898014028001d00c0e510186d12001410741381c5401d40014441040180103000d695200b40c000641980341810095801504400d0703070078040d103411144840080110ba0308440360341000720a9064013181611110000152203074444008540064641616080f001842c5001d07501001019104c8005445a41c1d0649080c480100c0a10140c10800340c024000c1078281c410328142e1381e1005440400e901035908500313101c800036504d440104104403800402c8405400c0440c0c540c2d00b1480c01840080c00e119051240349038403201810050018052540118441504400c501224003800c200c049d549038061050040000d213002c00003914158140705030070700c61110300c002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 901115386 1250 901114136 901114147
    0xa0606090b09010e100309020901120506130c08060703021206090c2b05091c050a020a1e0b180c0109030803040206090a09060603090209070c050606010f03020d020301092f 75
    0x1e26401044100341070018805030720720650f03240141044401500d603004107040c00d441c414041000d6040c1e00900c1c014266140400000f40d000c5180c50b40201d000c044184c00762814104409070b41c129503c0800e00703024a00621641c071307500d60002d110084060700c202c0c0082d00d0704401d000741d803002203820741da03c910140b25140d01100500040744401c4c004840c8110400003141000c411190281c0b8505510b0780701c031030840000c9055021160101c8030500304030742400342c0c0c001c001c3d44070018003100401d80050250305403001d98000540035441a081150403605203805400c44400141084200c80e451007041c200201c20340c40b883c0b02c54156580904610b0031074a070b0346d0070700113150048400d01e64052100040422614030074420007000b070402d075a01056104060050125100c0e000c0c0840040145035003885004c65400129150000710a285c543c40340c501c0ba54048000340105c0e8500000c0070700002c000100750645401c446091900208501300c030200204c20300001c4c00a401c940b180c0000144076 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 901116636 1250 901115386 901115399
    0x60a0c020f060117030906130303030c020a080f07080d050a060603150501020a12020c100201090c0504050408070b061203041e08010615140f0f0304060b1912060f11030f0a060609 78
    0x265413400040c800c481c2406c25240c0042c40640140a180d03100302402c6000f001490752500071883c3c404100d0015011100380c9403100412031203918034804440800045482c10030422801b11107958001e0b100420550400302c5550010346402c0c0f244c82d001909010703000c1c00c508000c0302c0ca54129401600100300c03800e22a40c850743c0310b204581e410400e601501003886400c6d1196078500c856606a64000580240f2525202428403c180c000328080c40c81c083c00c0000003000c450498440e181c000384952069030741c0f40300088007a040b514640c44540000314002650310200e07030382407894817078810003640201d469018080c200e410912030350401344030420701c17030f802076000b501c010440700e41d00081349152281c2242801007a03800f40990740c00703403000002084103000f2180b05042c1c0503801124401c145800700350040c062248107000b0317a8402d843e61030030803080028a070f019070b082450103041406004000d144550072a04101c071918034569862000502444552142074113494058503130116a038107059 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 901117886 1250 901116636 901116659
    0x1c0509040513050a03120c03091211070918030e03030304081917240f130c0e040c050301150908060c0c160e0a0b010c0c03060209061308060a0c020f0601 67
    0x100b61a14252200c03007aa400b00740705011180e141030203911a4003d0b10f4841c5403000c00c4401190803e8101846c1000c6100091190748405564202624181c4420844524070604041d2554002d288030761502c041200c160000340f1000401c98001d0316401242a45101419100e210445004141c00c1c001c000180d1501c6207902d031303500040d01e82c0c54010b256043d02260928165026600a10704a0300c42c1d4000e030f02d07041d5180d0070742c1c000324080e02d41c0c0c540d0280c031b900490307001441d10550008254480b000d10b040300e40700780011992642c005200780500030b500d02020300550310a0082c25440b61070541070b03030a040e00a5445504440141000300500da86005a0720581d42140d800d41d1130901070040c40101c16200250840c0c0500310703103c401c00703c2c7d0603c2034106d4101ca043d540c040341072010b1034200002081a02e06103800701d942085000d41c2ea840c000d00041c1013841042e01c7c20850500700c91011500c0751000807014410b071080c2804204c284140102a6500c5a01d034540c0c00c0e1030340c040e03070042c40b4200d030b0302 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 901119136 1250 901117886 901117891
    0xf060705100903171f06080603100212010608061801030b2d060909010e0309191a1804111b0313080309032812120c0e031c05090405 58
    0x3041920350441e01090140c080d2446007030154005000b040700c00c0c4100d2070540e400c982041040c000f40d252032070040b41c1110346452521655040c4010342001800c00d4900f030100c50143e0880309011965658410011443c880080c000c28000920800029080e070814250390307001d00c03038005455010b603884c583c1c50010750f030f070000e000410000b148804260454560a000185a01d060800c00414902203003480030701e62000b061414568141702c0400031140d8013104654187e202980d041e01c1c0507801d1112048100441d40c8408a05940c3d203503001c8809004002a0255001040001c0034500120007080151070003140350502c000380400100030350480302c4012543c0c0b5040c0505982c00d10817509819009024141c3c020512600005810591840c0034007660710200200e4020080c0d00d2070444910002120020000b0001400b04481c0340010b80a9560a14005c1c0125001c2c0030b55943c2e054018452030004000a0080c411203407aa810060074003c0c402c0b44121503500c3c00e060410540420000d413802 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 901120386 1250 901119136 901119143
    0x50c040b13090501170105090105070c061a18072d0f0c020303160611032701142809030f12020403060f0b10030501030f061d01150f0e01050f0607 64
    0x1c00c40001409159401014000c2c40300071304158503215401001c83c25210000d0014120741d241001304101541c000c4e030391441e22900040005450600c41d900c0b2881c90380c02d078445a5221242542c010f08102e8034180c0c007480740c000395441c101e107405110b040d281e1901c001c0b8041d03005041007a20201805126480b41b06810b01d45207812011104180c0103c0d0441e030104110280e01c0e07030550113000070b2055600071900040342500400e880c6140003030030a00308408000014080d05c07074911030300301079150940102200300000030015406007000c03928040c400742e295280e018820405c915000741c04041d03205642d94240c264407032010984110b0011590b2074110711014010907403d000100204200b4841c0e0b600c2c0d0001072078005056669041017018041201e4600420181044e005200103040313550803001c8c4039070111001c944035a200040e103e0460000318881d060358602400d80040c17040040c3d07892300700c0340c69140f4400a030751a001802c02d680824050203412401c0c5482c0d020450500030001c29a8070700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 901121636 1250 901120386 901120417
    0x10603020c0109140102031e0405030301030b060114030a1d060f070e0429090610050f0f0706050702060610030209062703160f050f0d03120b0a121104050c040b 70
    0x9155a403420303a8550703060840c080da9404070401501301c4041806040807001c1c04a0b000449c0b50030340d603660340c1c2d110501004140d5007c0601040c81d59019034081c0d412044622482c0ba00d0385050101100106000c2602e070124078242406100c070389201180903401a00254419011a91600e00a55a52051440f41e0b130f0081c0d5945855601c008141c045403a0b4500d4100c0000940d000341c004020107541d014204510a0b0880400416129005030480d11925810390040c0d450340d18038600010707107020300280074141c14105804c001c4030701d60125034a03220b0902142c0c00700c02441d42d010102d0807402201e0381c0c40e030018400c01c090300d8041090f046442000300c020030001249041080030a090200c2044030b0005070542e400280124160081818090300d819194800003070583e030b001030515411800054244051000b031208881c3c40d5400c020302c0000041c00c1c0d110302682c3c400c1130184002c400c0f881600c0403503611110782d000f45014015280904411455681020b06004040361150f110070301011a542 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 901122886 1250 901121636 901121651
    0x19090b091c2102030d0606020d02060712020f1204141c1803060e0604060608060f04060e0a0204060b07020315070e01120b040f0912141803011e0b030f060f010603020c01 74
    0x980d199030490780b14401c0e80c069500d84e0106038001059410b507400001c25900404601c481c4680c0c0003840551007080c62070035005940e01c1d02d00e40300080c0728481314000a260f001900e59188480d022015000310721070620b5802c11b001d000d1907182c0310006000444440e00d4292076984402c0c0c450191600701380200f88200c4805981c80d42d640c822600c03c2121100c40742c00030010041406801d202d0340004001306400b414581c0380545180058120041000308001c3c1e07584694210078008100c444c003110750250040001c103483e0781d0003800940012804a00c81d110349000008161041410240981a1030300c80050504030a001980c141c6003425294a1880d42c0f00d6842425548a019441c0c0303200d040d20740000c4003107090030100b80c4072540e80a66004c2c400d0aa07001490010100b0407581211000d0050490454034080000d01402c2c0b0001a04082c0d1320300100007440c45441e40c0111f11070b582c2101140e60540e01c40c203100b6140c82040347e02c2d005d204c02c1a00100002030090f001003000707640c208000140328 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 901124136 1250 901122886 901122923
    0x9040c02030c070e180a0804121a2a0c070303080402060705060c070b0a020c071e0f0b09101b060213080f06040b0a200904060b19090b091c 61
    0x48450380107802c24501c4e20706014080e0041240d46610300c1818018040c2501035865031226480f6500ca120241006602600b042c003510940759003651100011001e0103080071100c250030307403a10b8490501c0e2000707515030707120a14605204440002204c14090b0812074551340b0144c422142c024001d0b60450720400a010000d201070002c14450f000c4c070803903162240705900342105043c5004003601c42a902c104113800b034408000800f030781120328916100d10060310a2a6036900103c4603404181c40308101c4c0c4001c2100c4005001400000b1400c0d161142450a035441c115034000514074100001110882e08001050042d001460303014400703426800c0d01c6580d003548500d08006a9090040364000e0f006100403c43c0041d1072503000b13985201d040c412078a0464034400e017010341c1382c041000d5420014400741c0d1902c07241c00150007080540305042d110101e180040f60180b501004110018821000124045924005680c042440500890030740000d03d1140c4001e400d149078152103007030388030814a124 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 901125386 1250 901124136 901124143
    0xa0e0a0e1207050c2808011b08070c020d03030e030c0105061e011202070503040f15020d080907052407031106010e0106120203070c0b15011806050a08100b0a0e18040809040c02030c 79
    0x408109000050369210210001a010600d86512007040009c1c000e120b200da84c00b111111900760125038050791200b0f81d2900358018130a100c000010343c000411130444c40a819405a8400da005940a0100040812500341100007020450f40442c0d00305cbc01c0d290f1810055030140900da40f141048a141c01c1e21344140300c44c1c0505903840f0010a0140c2503186000076418004210400c8403401c14134110b050110301d042c1c0750030740c4e8000c9038050584030035030744065407503104017803080d8401c404070b26511005800d0040c0000c9201d0404101c2c1e120340000000d01d420040d2002d4100d4195540d520b031488610f0050740c01035031020b0195020408035180a00c0030480010f0120f008581ea90384140c020350320708001400300c0040d104420441c111105040191582000460b984900e40345001342866642007620500d011040c2c0040050200c00f01d101c08d01d9076088010418200c00890b08104030000f0310101e40c1c640740c0201ca0040c2148401d0164104078105500301c1105070300c0c2c9005403030500d1a0080254035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 901126636 1250 901125386 901125389
    0x30f08180a080a0e0301050c09010f0e190303021b030a03030b010201021309020c0f03042303190303091e1104270507030611160f020a0e0a0e1207050c28 67
    0x703180c00000b0f0f90003106034220040c4100b100041d0700a21180c034200e41d0062140c003c0c07000542c1401751509440040601c0381000702117030302c0000c0c011914065800103481488455000450241c802d07983c40003560f1901000c144004a4014020f0620b90f041d56000c03805416100703121419076400b8086d05a01d0710303d0100700c0c8040c1c08003030001a03e801c00305c4800c81c9000d05012000050340c00400041c0312140c2e0407031842125507400c00d401c64111943ca00400c0c07810794540d40381e20000540ca542170040650580106484600400305254944203510b28025441ca416100400980b40342c04410003070f0800340c01c810325400140c5124409181c020300756030701213030071401c0456440c0c0004105008114952169409170117103014401c3c14885070307094000300c0a044403001f50038200340c003c0600441d45c8056003000602031103d0b800280b81419615040680b024402408650080c020b5105080800f90300395079901360400018580e4208040c00d00441c0240340507081c3d0500c0d00b40c00c0510140300700084440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 901127886 1250 901126636 901126643
    0xd020c01021b01151d04020d21090f0b19090810020c070e0601120b0301020d0f150501112805030a090801050601080c180102010e0d031a0904030f08180a 67
    0x55a002540799201d0859900c0e00491214014103001071150700c3d407054038041a017420302e41003140c5468074000640c02122800e0000c114103408200c5c3c0b0210a001c030381d01023500740c81e40c0300c40705110344902000c5a9400c0d00d00601030064000d01c40d8080000200c2d03040100d80300d0300d0618040b16900d560041d0b0518005a40401c0c4407a000030f40d10388403d804001d030100600e103056410101e4200540028044070318202c981d0500e5441e1000104160760070341c1296000401c1d4402005072171152101c0c0c0b000b400e00128000c6a1a070001e80015655008150752090807207070070094803c0300c03c0850f003c10710240c40c80b018081c1e580f6221500001031070400003000b103204651590401c031881c202a00b400c0d600d00134000383c100007140c410711100400c4001a00c1208440380113440881401900407401004142030711034413031040c038400c640500e8055200c40764408042d444406c00b0303403401050090201080c0e0b001800901540c1100c0e8000344559895500845410b070810140b00c00500210710300f208040003517 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 901129136 1250 901127886 901127917
    0x3030207210c1b0b1c150e04050d111c111002030f0c0a0c0201030c02010b09041b060507120c0f05011a090a09151a04110910020318060d020c0102 64
    0xc0d0180640200400011240340c043c801c6000d0805440c4281c90040c8516424100b800d00c1140815841507003100b80c1c078072810000811135994881d44000481401d0750161410300038a0300100c0c0486c844c070300c040c0c06030910f41c00420110203c400240600c200307803d0711604200030040500c002481c28401503800070344041c009600c900304800904881d41000e030001714282810000300400c203410603004040b264090a00103900407046c0e40c1a0301400c902c03100164004400740401003000410b000c0c0317000000000c442801e4007030f11841c0990f104c0c81901d5002c0c00075243e42c600c10754040d208201d0b07012694440e0000c51801ca481d03544079070a4941120328550f907080100c50140c424104443c0302a0300c50202001804100c090ba1100301c0d84107910640091102e450b00b001c50322040046103450300e90303040904104241c4400110050b000d4000d099058480c0005132904442ca51002040c0d0350311000e0000c3c14250000c00404100b6103601a5400e1100980c0034440c004e64020b0a101616407500000d404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 901130386 1250 901129136 901129157
    0x60114031219030c0c0f0305070602091c05010e0d0c080d020f0d050a0c1b0b0c0f1204060f14071d0d060c08062b020d0b070c03030b030c0d0303020721 66
    0x90103a03034168000704204a602205d8201081c00202d446006542605005036076498a0034000080d1041c80c1000e9044031901c2d08200422200920301d20016000d41c00800140b45140b60481d207950540d800c1d00001502a503080d40400c90440040040041140c1d006140684414000085030800000b03080000e42d03032801c10071018014010106000c0031440d04558a00c000d100d20b0310103695008000c1c2010440300002041c43c0c0c203920484045800070701401c0e448010b1404458801202102d049960300d0401c5d010402c030132510300502c04003d06c1207010b14250381e1000340031502c0d8019005a6804800c85004c003211540b218244c420743c10740071f44400304414101080c081c08014000d02414010900d80880b11605880724081050f00d1034041074031030300032282d40001440c0110b09040a0300c1260300c0c2052241c0e094102282c4d85405209071001d0000141c82010140c0301c40350203170201c0e0080184586240007074420717401441454450421400102c100c4004400030100150300500032070640c840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 901131636 1250 901130386 901130437
    0x2150d06170d0c0b0708040c170307030306050406060c0b040303091e030f020f061302190b040608011a041202060c0a0b1803180603090718021e0c0601140312 69
    0x7141c080403081c2001c0030b500f107096541c0e09103114020400d00030482203801003001c2040c1c404141d801404040300d0600c540e02c0c45a106600d0340e1020b6400c401191410900003100d06160096004030780250f11281e441d020700d611401810280200110101952001e040c8000f80102c00b1b40700d50501a042c005003d003c180c40c000e030420a0080c1000c0a5605c20381035000d40b04030018005920400c01c29011106444520103d6045286005021410030400001040070b81449014004651580d551030342c4507603880c10500802c0741d103d0708020b01d07418104003e200503121820181200c0d407010301481d00d0050000c400c541042600e040032614081c4900c180500800120551161580304c000694500712961403c40030390340304040c010380680008400240110010b20007000144004281c2400c0086803140080080d8003130710808803800a012202500761740520103a42c2d07550095002004940d09084000400b03800141c031b125854428402958040790040d07000d00141c400490f080e454a034002d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 901132886 1250 901131636 901131643
    0x207060f080402311103100b07030c0602030606040b07120801091e200406020105011a04060e0d0c0b0a02010b04110304030c08070f0218040b07050c0a02150d0617 71
    0x10398510401209605000250366201a54001c2c0c204034601212002c880b07400f0100a4042c03400c6101030645072420f03000b05440c079070006610410240c103d001c10941c540800e01440d00450b000640010350315109040022019402503810880042c06142441c3d030310f501560f85640941e004440300f0820b0f554144800d038004115a02600b0707607410502c81403004400c881803c2d0032031820180c03060340b0380c02c1c030322444003040c00c60b0a080b03a000c01d2a560791340d0b1542e002a020f00000e100e01d500d101d800800001d007809000c0140d805580740d60390b50300011703c10f08c010011400001131041d40c2a0100075070020742900000020084010300341c0021070010290010001203880081d034140c8200750800801000035800b0381600c1440f0f90180c0340303540300c0c40903003000d0940e4940458001d402c412200d02d0050680c03105284c80d8402e91103604d00070040c1d0303284041150a030042ca02d40d00100da001100003001890300f61a0080907903514000345040030280328a401c15906075900c1903060480c14001c64000240a2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 901134136 1250 901132886 901132907
    0x206030a0f0c110307112808100504020105040519051909051b0a050307110d0c0506060a0503070b0a140d0204030c0902030c0a031a030f060a0b0103090b04020925020706 74
    0x10300300650412002c0f0910364582c8500711004282c0c90030f05014008654500b030110b14200c0440589644071040e04420010440d81405045000e10a00d5001140c9030900c2c020148a103070b060391482d04251a10003403010b441091000d903140310700741c1c07440410141c9408400d4440580740c50300d030442541c40c200c1c0755012640d0160440c868103184107c8482210710701c0040724002d1240e860300030740c4d136a070342007048904c50100e103940001c50054100c0035040c16400007901c80c1460107a0142c8005803503810800c10715503160321a4a425401c0701d0700400c42400e145002d8503c50000f410090501d000b4803501f8843ca40c13151034030303005441c0d0200e003d0090041012224015205980045142d402d06001d0041d040c0200400d04041584840c840c0261059500e840000d0602c09001c584035040c02240442e1501001c66100900301d2600d45101c1c035562290152054154004103813512a44842c1c00b17110302000c00402d00d6014030b00388039504980301001c507034059100e6041d038060880e0303505010000304580800d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 901135386 1250 901134136 901134161
    0x7030e03090a15090305030c03040f09050613020c0307020901030507060207050a300b04051e122502090c030106030f02030f070c11130506030d03140a0b04090206030a0f 74
    0x384501c080c6030700c4844075181600d021941a60700a0044a0120740080d440d0300b006207540000308402002e44030000c00360094600701135950500c04c8c2c81e80c203e1002c868048480360360000445c0079000b025a0654001c2c0615140081580d180600070b07008110144002c0e44100e030b43d544801400c00010b681480300c20080c0004850846000b45012a510702da170035001e10b1000c1d80016201c1503107800c10118040c3c3c05072940400c080010b4641820300300c1c0c48002548270080c1680c2181d055405800c004100400203c00008025040240071010100550680440d0030607a481c4c2008400140c3d450010440c0305a103c1e206480c0c1c2d81d818840f008007a5154044022403150040c414089d00d8120441c285922901600c9c00d518080428241080240804c00388c240d088062140060311054031f90b0091482024103408441c1302d1001510120219a001c3c3e02c1c103415200780070041903043c62541c000c450401401440482c07804415000a9100d6005840d075862107650342c441d40c2e60303114840c0540910080f1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 901136636 1250 901135386 901135393
    0xf0919060b040e0f0906150609040603030f0f0e0d031b020402130611011404080903011409011d060c070305031005030625080906070f050409050c091f1d031c0807030e 73
    0x217024062a5031658050a40c0d030010070710300d203080050f1700d0380002d0702d16441000f8010b101c981e699090140041c1e800c0b86e01c1c5c100080d5402100404140100c1c00c8442e80b44c40604800d07120f0105032021902048401c2c40e5800341c0d4604a01003000d03a449001400300c0080165040524924259000e0300920003c420645ca99051a06a204170440d00140a5000b50400c941035958050503001900510408504000c10007035007050050841e41580100340040750403410056041801034100d94450003164003400c44070080011500003403241e405190044001c0104549041d12400000e007403502c100c075229034100900780420061181c2410079a8410507908140c0c6041c100544900d480b100000d01075014881d41c603041d4650342c0c2c411401c480040200c0b45040015083c6021941761641c010040c03e849680c4460a004040c40c9100c0d46202041c070710f46403007851070000007420940c1c0b00741c1980c1d00ea05005904040061416041d1010402d01203a40c3c0c62030035240c80c6802600715034049560320140e0740b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 901137886 1250 901136636 901136641
    0x90607090b0702060a031401090e0c060c071505040e1f050607050a110d020d14070f080c01031a04090c0305010c050c15041712070e0f0f0919060b040e0f 67
    0x200301c441100e10583e01514816680c404010080c1d000d040e00d207881a0302d0089a03000023441d0182a4850700400341a036003a01c6105030b24808000190046030305000c000d42015104200014801d000c20390036103485c0c245282025994402c01d80b481d0700c00c0f113030900000035882110140b61344d010001c00140a04645090800080781c039026518012840b00910303140c1855081415561a689107580381a4004d050400b481c9162070060746000c1c4168030071a09115410300490010603814081c801d5452007001400c02c2c00c2200f004501070800003c2c9642510581d20560803140c840340680b05425014851082c0e0661031403902c0d9086515076820242080b40038002c03824017903404281e00c0030041c2d808442080790740340e5003450092071000c0a9498490040085c44004c10080903641c54807441c02500e8464100800038207010b459840d0f48151544022440c07074068141ca07050780232503085000720110002d194402c002c0e4404840140e002750000301c0b40801d01f00040c1c01802c8485e131b0b02038141883c1c03900341e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 901139136 1250 901137886 901137899
    0x7050a0e1e03030a20030408060f04020409061a10050c0d05031b03070f080a0504020607080a020c130b1f05190201092102010e1617010b04090b09060709 67
    0xc210050a051103080405040c4400090031400152004070040980780c1c0e41c076401070050000c0c1c4507130300ca2000c011104c2c1144032004101000399011201d18a01801a035961a0300b0a0503d450042040768043d40d50341c0c106e00480c07072601c0341580c0c541040c001d140c81c103440e10003008145122031480100f0800100001c1c3c8504078041440c00400146050413526901d030342404031011002d11030f510103101008010481c031184d001011141d000855201d110217501c4252076403043d10707001c442c003030340100042164100240180d030003000c0c20708551050b07900c91001c0e200055a03007009118442c5c400c40d22004c00215502c0c1113503004100000c4000c002d0040d00d54403a018040d8001d024034101c90f007004401d0b20074001d00030340050b10b200782d00034004107016028031182c942d1a86900d01f050019864110f0b005021000040c0e581c0044041c034401c3d2024a141560801026904000000d00365488626650094595008140140d442840310000901e4800340a40c6400030050140040081442c001c0084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 901140386 1250 901139136 901139147
    0x203190c06030b010203041707260a1202030c060c0306030f011401060c0c1d0f131a0a11070507080c030703030e04180213050a0605040c09090506030f030c070e07050a 73
    0x7250194103020411000c2c03000140c1c00c6000d1944990441c81c00340180b21509180802c130941a100e0080520303808481d0505032120040e001e8004c10000d900c000e055501082c1d95805010010900d441200d181040780d88015041c040305854003d2403100c04424410249401d1094104243e44d0800030810340d4100000294007000611840043c0503041c40e0400c1400a240c10307c1002d4446c52450041c02c071001e500342d4220910440c1c0d000102c00700390020420030b003241c00010b41103a822204800d4076107021601450600b1001c0d00400b4003d40c6e6510341d0345c403046020042d00140b030050000e080c1403890b02403030030f003040f412511081c42038200000505c0001e03000313080c1840098060714001030391031180d100c81000184402010358000c000c00d0031f44440e441640c0019106d80e00180060001e03d0351a030034001590202801440425500403042c40f1001ca07641c40554014001000c448080b0304a071011030070359020904032012504114000e112a0f800c4090080d008100c1e450701620305000740000030039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 901141636 1250 901140386 901140389
    0xb1806100302190c050c0d050a030e030c0418121e051e2d090604030602090a091e06050603070c06200a050901090e01030506060d030c0c120203190c 65
    0x2080490210420005200b68142c0740d0300076600001000700b0b814910702804606420000700c0700b40c850358000d0711090070840182408680c0c080e00070000400c00341d80503103c03030300c0107012a50140300e440c0c0c090043c0d40d101d0142d106414406200d00f2408261402d0a50040030000082c00a201c29000360548086078280c4160b842c03402c41c94440d40300c810700c0c0c00e001c5010301341000c0d0350f0700030001203803000c00701e00e0100c4404541c0c040c407000b052406d0043c0d01c19807094020494055404031060104201090054000303051303461009100750719041c1c5441d03c0c00201c0725040c03140c07a802000444180840d0005210f10340c003401046440c01d085180c805801001d00c820b4280061003e502c4a882c001c0c068540c2c00c1d24031581102d6902c19031039202d0100b00600c15045003164a000450026001880014050781c0c0350507039800002600701c654406092201b040c18481c812010031020002c034a010928400d1520040c00514584c4914126240101803501d4980d803480000c07084803207200380000f01810300703510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 901142886 1250 901141636 901141639
    0x5010918150e2415280302060d091502090d0f02211006050906030c01050a090e16120c0e09060a0f260723040b0613090b1806 55
    0x6000112501c46409800005100341c4548250001610203030761800079203441a001100744890b683d0750f2040303001c0901d01d0010366508038540f07011403403038200007102c0802800303954804035213900d5480e400308119900400054600e140d40d5881c02c42044100441024009010b2005508007200f01e00022a03901d0803000040c044a40045441c0440d281c914020124110b0319040141c1e442003041600c0c2c545445446c4116454940140800e5615080740c00c60302540e4050010040c403049880103407a55401341600400340141c0e01000a10079101a5202c1d2043c03154141884ca1603114940142101c80c001301c90094181c240400f8820140e8000d4000007000e00c1290001c41c1911401c001c140768124603000400742c01c5612402040d4a44c0107003442c14801401c01042c030701110030342501902c81c0c0b4280103892038203880e006034040d0b4200c1110798519503240107000207500d48806c00005c14591054240603c201070420003046005101e01c1029505002503d2200c2c0c1741c030071000c0c1039224882c002c1113079 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 901144136 1250 901142886 901142903
    0x2070506090f0612150d0f0b2208070507090911040504080c01110304140705241908040605070e0d17070b0717160f05070f06020a0c0605010918 63
    0x124450342d03041c07030020110601401c1e007a5111103038505007040a8044401015020044107242114200304d542c440455821180710900c007800d0340c0c1e80c1e91101c4000307803143c03c1040d20004403802700100c2200050110348500421396a480503407500c00e04084144c0d0002000c145055002c00104049a0310110904001c43c0e00007029604d904e0140c0c1c0d24068800016055860080c2d80a134000700c1b1001540110301425000500000340d40c50f2980c1c3e1429405426001449084810322007252101c00380c0798103019825241c201050100e1020b05c0340c10000e00000020800d074180801d01415104082d003262181c945089000103500120320703508041a00140448000c6800441c0400001c060f900d000d540020f170402641001680204040c0c0609007080c2007003542e40106203030459204500c0034102280d01c0707510030064000f600740c0b01500f201c0b03001d40300a2008500c21001440600c0280000c01d1540c8a554080d902c0d03003482d000300d030016003250000794603203101105061585540c0034603566000120 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 901145386 1250 901144136 901144147
    0x181d0f010e010612021c11041404020307050a120905160e06040b06191209050d110d0903230f06090106050612012601140106030b0102030a230f300702070506 69
    0x10b02e062490401b070b2141280c80c00414801c0802c4410041c022600760403e019210404030301040100d00c403c0d902d6001060080004407001402030064408110707002c2c0700001c0034901a20340d03a040140728044440030515100c400d201442500d00f443d90845015241000b002c4144c20100e40140300b1822800c8a90a0340032443e001035210f50321140c8d0b400d180920030b12001d001882c03c40c0d0b5035a4803404d6036022464104080013040780000e9909a4041c10b030361401a0346107191a8480c10045105110a03c200c1c19405004e0904041052502c0c249103280240080e1509044003421520300340c02c560b2107440b040002c03030040c112a0b034402e030546141c15540804042220a0102e0a24410a00709003950804080c40400d008420b030383c0b412124152002e001500811004980b240b044039001e002155100030000343c1c5c131601c00c8c03031125540010001103242050030811613040750080d4024034503c403001e08048406c4000241c00d880c80340764005140d012030a0480340a500c031a06809002c0c007a13180131a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 901146636 1250 901145386 901145407
    0x1804050a03182c0c1201050402031b1b16050312130f0803030a0b06040e1b0c0109051c05130e0a180f0209060603070c0201181d0f010e01061202 63
    0x805004000e809501403010000d100c0c0f008030801000c0b0020007129025000800d100f4120040302e90010722a0b40b00c8039160300b001c00b00300003500083c20720354003818480d400e44c1e00310b0041e02c01072103a0942010200b060740141004140b070202c3d0400c880381d10540c80c0500304459280015515040c4080d107110381e4031040340e030800e65580461648007404100340c521001408010110095004040d01181840917808507024488584154404c3c001ea922040000800100000d044441c2400700600c8440c80c0481c0b8140c41425600c00d100207031026001500910108401040002c0e407071071060820350704081003582e040882e1040b40c41040498062040050b26460b025844204bc189050100e0000d207809402c104080214003001280994800404241180380c0b400540c0d200d01c80542d210b0380401c406600444003001e0b1605c82200e0135a00e00c2001c180e010404080c501c58101214001741e007450107003140c401e03000043e0300c003520384003a000040c401039501018a082d034a40b04000075030390780c1d0300c1c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 901147886 1250 901146636 901146677
    0x813054204030c03060513020a061d121024120821061315060c140a0f120305040320030d0e0304050f06040506030402010e0d0803010605091804050a03 66
    0xe5050401440c005000700c104920b501e0350b00b003928011482003101d6501c03880700040c24001c010010794048418402040300f41e202c0c1415400351140450305c80c000f400c2500208005910506d00c41419410100074140712041078031500e113800710b810b603002c0061030a03035880b03011840c0d090003202c0540302c1c6c4440e40c000f0320441600f200c040d64111503e0010030100d21090409540b810396226100300300090090841200305d000b151520100b201e41000741900c0c0c8a81511500003400b4129101500225100316042c420f004075030b0b003103005580044080403603117070242c00c14903084403d03024945010240400b19510005c013441c6594aa20040721550140e081c044c42c50040755400a00c103802c1009081d21000048098011a07009546c4d0b4402d11b1140350410500f070240b801180d42080040c80020701641c42060b290424650181900c07007030701a2503c4413101360340260846404140e0000d1a1501400c00d00c0d40408015030309841c4841030b081ca40c5c0e82a44a050900000c2c1c100213590850908040004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 901149136 1250 901147886 901147999
    0xd0605130f0f0201140307120e070902130e06120304050d080d0c030b010f03060315151a13050a06081803040f0e0609220314040504050103081305 64
    0x14616040c400038500d001c004024000c2c20807070029000300361070b604204040c800c0c0c900551450b21060245502031444100500081c075140b4424403880ca130024032041248000c11842e41a0f50494a0b501d0030521640e103c0c5c5000780c6a50b000e80940785003c00f1a038804000e41d8103880b800c8441500103c0d00d42003a1182e40030300c0d14404026494407148000391a05a401480b91180c280c9032440c803222850342c00e400f2900355100c003402c1c1001c561310031140803080b68404000004e03070395940503440b91940c2c21003010390b480f0706681c00c5100700010600c840b81482c4003440700800d4212803500392641405001807640e5009005004034441c924000c4010b1701082c0284c80290080944c0428030f10307035540c01000d042c0d000795402ca000b0040c003030104591059500d40e41ea0208110300201084001680e01101d01711000745e400e000d907007010b1102082079542c2e805828003c50007030342015140d8103000b0300c0f0515540140e200900c0b841c41528400d4480b600243d00c40910369200300300b150031003e44402803ca41c10380 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 901150386 1250 901149136 901149143
    0x80c060d0213031a070905090601050d0b030709090b01080c04232e17030304050a0b070201090b010608090d02010e070b180303070609050708241e190f05060d060513 72
    0xa1503040c0d29104034491500c5100e084e519046d4540d036450034003151031010368440740003800070840c0509000458000900c01300025040320720b140c1da2404030341d04032140440112440320420b40100006242000042e008402c110303402c101e804006d4010000a40840100702210400c4600040154180c0c2014a52480d0701c2142c1e03100c0c0c100368100c41c0c42245460700652401800324410018046000420742c1d120b19481030041c52041303450f03283d080002100508200440d9200d52850002903103803480c1d107008000c0d03900c030448181401c070f8615081c000409400c000b160b15000798404401d80008000c0120f50000d03c00c00e54504d104010700c446060f80700d031429018400050402c00700701080d40600b2265003c1d43c00c1d0362040d5143c01541d603d4076801c103800071058840c0c11307090003103044030584144c12228007000c003c51520113088244602500f1284204e0780312400910b030700500c00c00e02901505050080c010455490036900049c69088510710107085180c0d40c4000514601d0084601c2d842c4540 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 901151636 1250 901150386 901150403
    0x603010b03100b040c0504080705010509060c010c020a1e0b0f071b0503180607030e13020c19030201061502073b340c0611040e010906080c060d021303 66
    0x1402a508006001d41c030f08814090b920b80905a44001d11601c00d541c16200000083d1506914010044980d07400030070300c29510074010030425104031402d00c5182080751107074014085001007401c201404060000d800540200302481110005a00c64450341e489003040c1560380094503004412661205000d191003d0800707011000403d0000000117494142500c240c80640503965100b030054a02441d540280403454946100865141c00480d40e80b01d4900e0240c0141000c00601c1f015180500c110702154180e1008001d11050581c2070041c000680801001e02070101351140d0002e5070b0301000d1280e25540c0300c0e00059000280c0f28070400740c5201e0942c40341010003450f240e10603003c1500a850701c6002410f940c1d05400c1c03928144401c5d1401c0c0030a4214800c0706c10305120191480681c070041125041c1c1d8031070203621803a6051029102500703211000482941c1030105081c212200c0750840c88455000710010350380c6a840008440b000d055601004d0307100d000b414520754009170b95400003018982c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 901152886 1250 901151636 901151653
    0x16020f03070804051311031603020f0403120e01031b0c02040e030f0a110a02130e15130201030608010b0f012001061206051b040b3103030f0e0105040e0603010b03 71
    0xa80043d000ba100219078074039031500700e21100001c039410405620003c0100780002000d401c0150b40b2403001080300d040162603d4952000c801c890360294008940030401060f4090303105074866200582c8201c2801e00b0024941410358140000400c1103000302004100b00081d0700315181c5d81c00041c140c0c4c071001d0459031140070103210700c003040d045404007070000f0782d040ac0d85500008001600b845c6e2160040c000d440c1424501014002911005192400511400c3d039804070044040740c0461290b900c420110b00746e030300c06100040c2903031003d5114030b450342e040000050050340c40300b15080c0c01c0d101c00d080c41b5507920780c07094101d1040e800041c4240c0740365192240015400030028819809503100704001c00c4140d585c025841c24084045030580c002c0141408144581f0035620020610301401d04000e581c103405d4840071045041d8030000a41c02080a070a04204141d00000315001400c030300c0c104400c0c55142e00340001c1660003544140200703003a4400115815407000e50041a9140001e42951200c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 901154136 1250 901152886 901152893
    0x60f070204020909090a0506090d0e090702030c0604050705131b0513090501060c0204051806011703130b041d0112030c0c0509040302011b0e01140904140f0403090506070203030316020f0307 83
    0x90200c54030a542500030354002270038083c408100c8102c0700c42140c07070b25404c0715021802d200c80c43d1002462981076210800c81006242801c018007441603200c0d030f00924147e070426090254005d01e003d2001c000d641031454064100c01c3c0d02800d24101c00141c03401079210f02184150511418040d40812900d500d0b000001c21a181e001a10080f07950082d501130195031603180d01041ca42c0804e184914160b0080340060007480d901d020381a00e40c41a20044030300b003d03d038881502000205071302c0500306001c006010420010440b030350341c1040146003034944442d80341502000340e581300f440c4000c0402070450302c0101080400103400000c0d02020f048540645014500640240040500d0004000da100000344203c4d1040c240c0c000e0358032069680d005900c4c8806441c11481d000708100b01d90041e200d040e0806680302c80c401440c85422112019855400e00c0e0401034030034070705030b044640a0f0004000540141e18004216034024040510025983c01004c00403170a1602d4948120800e0000240720307020b2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 901155386 1250 901154136 901154143
    0x20705030c060d2705010905010c170f0402120115051e0310020d060902030c0c070e13140c03030a0504061101050402010903300c03110609060f070903050d0c11010c02060f07020402090909 82
    0xc1c28403c5002b00f04041c0c009401f6203492000b41005500241c5140004400700c0e0244040c0b900544054101c902c0d000b014110182035a2101c60700101000c401032003000a85040007070003a1020210021214440c1d442002c45c2d16010881003d400d415000035600c004031045500803401040a008215228100400c154000e544051400e0f0b03010300c102880840c0c003860390003429000d80007081c100403103000155640c566421300c08000f103105001e540703c000c616490500040072244102e030b0705c0654070b071f003800006801001010f628001e02d80c501000c000042c0d07003041d0f020082e0798009010407003043c07a44407510202140901d84a10450041d544400c0c900d4005920b0442c95100341c40e803c200241c420301c116070340d0104850b80d001720b82c05000850a02030300c0c2003500383c1051052410640c4240c07203841d020724100048403000001083c0e060341000b44807044415602a003403d00c1c1c0f1840180d400d400160490085203543e0191680001d625402c5640e5581100e0b89068041c003030301c10740c0c504060321649 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 901156636 1250 901155386 901155401
    0x30305012c180c030a0c0f0803030f070e030a0213060518090a350a0f0e0a06260a06030201031d07033e01020705030c060d270501 57
    0x400c856888800301c080c1c0303150164695025140d0500041d901c03048502c5440d00b903080800d069004082820340b4a880034015080c465008084003001d00b450b20302c0210303007e403843e40415940c0d0030038810300940030381d5090169008405440d1034001c000b0f032000040d0905490180003584100555844034641c0c0c25034001c02c04541d009c0754078848545160b25000e104d980308840800c2250012400100050b4141042c140b119460482202c600301c4007008000440707640d0308608115034408134408506940c0030707899042a010300e2805c402d0700c00b0101d02240c18000c05019103001d1080c080c08660019980c0445d122410030107004c09041c070704080c505080204140e0100303a002906003144141c8003100c040f03a103058000c98000411455103103440c0e050003494807925030b030a1841381f5800b02c05c0312110b070900c0d8520346070000c00740080005800006450150160b00c6035000f0b03008151000748035500c2a041e50f0a10389503c90210301140c2e00d070b2611141348654803080308444408880780042c404150302046 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 901157886 1250 901156636 901156649
    0x1b010c09090b01091d1e0708090c0d05060a0c2a110306040201080a020705011b02030d0b090106121e110a02010c0903080910111b01080f07020715050906040303030501 73
    0x84a01010401120600228041c183c0300002d0285e045001d9413100342443d03440804580020010500d5101041c04039038107541107070010f82d40e80d05106034107006004540aa041c112252031a90403255030b2180c594a0040c104105d00742e0302e40803015103d0060882c00001e0150001503a09200b141000b41d250310b0300c04034280c07a501404038901186040008600b4003498050319100d17801c2c0c0d0390b09038283c042c1d07100000c12a002c1d52545590b00e07040c0780400700440110000d03000b0310b450303180c1003420300b0442d00d4051040d482004420010005143c02034a40d034008500c0c40c20108800c1c0c2c03551103009110101c5111b650f070f0b00b89000c0c01008141015030251546245c1a40240051061441c0c12104858240000740070b0f2907080100d2282407409035070308140e00c8064200b002c0c13100001d14140e42068030210b41001c1034042c0300068540e03036901c10070039940421040015100b0f4100300a0080d60b50750381e401507001d00046035490410003400f9070151502c000c1d000304003540d00d039100c0c074006000d40700070f200c2c04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 901159136 1250 901157886 901157891
    0x30c080303090a1704230306061f2303040b011503060501090533041518090e1002040b0a0927200c0a050c06030403020d051b010c0909 59
    0x41044840031086078002c04141004250031200c40d26000044a001c04260844a90400c00081c48010030008181081041030b0754441100700e0200381030500e0001002e442c4030781c600d08410540f002e00c1d0140b04206020394070f0301d5415a0000d02d00d4a0300800c05005c0c0c1c1e032038258044200402c124004441d1410380f030240c8100e521640c0a030a054043e24101c0c041c180c0414400c400c10300460811140c10300200302c02a01a1002040301906004580606055404807090004062001c800341c42510b404030116450800d07506c03850845a07140d07403010b030b001d0214080c2d124442e00342075880800c501d140c0e0f00500302c0c0465072503a4540128a030355006005510101e42d072000006080e016040e07404058828401040039006040540080240300200b8214040e80d4038010001e210605180134014012240006060841072030410f82c1c80c0105441c1403510505080081200096001c80c1600f5109120b060441d1144401c0c40c0060f400810403600c2031140d0f01c3c104110342c800f81d0103c0950101d98894004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 901160386 1250 901159136 901159139
    0x10306020d0e070e0a0504150c02010b0102190309051009150503090106050609010804030e01050c0304080a1505040c06120b04020c06070e01050c0309210a0308040b0a1b1b020a0807030c 81
    0x10b00d40c5400f4948038558800140000285440440360051548030b4030611740c0c0d80d030b210b88460b801001c0302c03c1c03032582d83c1c0140e565112440007540c04001100d410400303111000701c203a1981d40c00070702c502d00d503000b014020041c00228a0f0410b0084154034064032942d0b040b4040147d403803400070450f400440344414950700b001d80000302d50618500312904500c041c0e68000761541c07203890a0710301840344111141040410031140b07118001c02e001030000340007008044c1a585035076082c00300c00c410040c50289450b81c03808043c072000075059103150040701c005050010010480300c58180c01000611aa070b0340090000600001d10708011400c00e02c1008140c4032044649200070044070507006024200c5140d50080201240070b2a02469184440580403040794000358114207103400e201d0400320072008104e02c1c5091004020b041c90f00c1d5a40b16420800400104606412004030b081c014045802800703a8040740c070a4401500032503401603034025200050480d91004407980d1501a80b00030785504030754810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 901161636 1250 901160386 901160411
    0x40216110a030312150e070c03022109121504060b01031a03073302060105031b06030a020318060c0301180902030714030307060f0f060602010902090f0a14010306020d 73
    0x14050b650169102d040c0200f01c0454040106a10f02011032150001040010024003041a4a00c540526995003484014610300030740382510901586e2181c0d6000b00024100486003829285114000c54410b8410084030462034104200e0006040050315654200018020950003064032070b50288d808014498842150081201d070002440741d05811101c1c08001c1c16940341a07641041c00b80d80c0d80400069021071090000184405811015802c004010006468103100d0704044110881c00c80001500700384c00034410303205c014403841d4180ea0110200b0854521100c02695032042101243d00505140513556025002403180c104100c02c02c41a00641030002d0091007000340d8003070700420f9058140360082900c01068018190148001d00014000c01d0722402114140861140006000da00204020341511481e402c00029a07040c141c40d0b000686800b40420340c480781c0c0488403452515458a01d60260298103d88961605044008810b00c07e071580144181c14403e081000550704030034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 901162886 1250 901161636 901161649
    0xa27060c14031018020d0e10050c120f25030911010512010918080a0309261803070f0320030a0f121704240506060703110c04021611 58
    0x2c030b000449105459042105070701c00305080c5131200f90a000075007412264078010b400c840c000c4000b844076600c00d000041c2c1c91012031060b180c20100d038045403850160700384040c060006011b049000200c4600000034540654031038880c1190b01c4022601c0d04403828041e0040c003500404000f900d11110740c050b4603034150b001e84d084911003900c2c00c0014429031701c0d080303003440100f5040b00c0019816244015950006a01000801c5e0b1585152800550b50b4075a09005c1400850745c84098012041412002c1011140405584480300d05c0e80b42203824001a002003801c03ca507551082ca011031010101000b042004c5890012245030003900d62405c2c018030041513510120000080e00b9469600b0041e40403034001e812061070a0145e041194500620143c030340c03030001084605940c841e001c581c1c0c49170041160310402c3c1c165003003030300c050016050800000700306124400000341803000704004500c448100b404511103245005100710b4032061400c40380d0040c411104004c803a2010000c1e81d1881c9860000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 901164136 1250 901162886 901162891
    0xa0e07090b18060705210a0f080708160c05060117101b080403030204031e02010e040605031b1201180c09020717090d051c0f09030b0a27060c1403 64
    0x80d41d190700c00c2d490001070042c264495102558a40150100c103568009000d036000c044640d403200055607420302540c0100600c10380740280c0d003008411401d00428940c40220780c0d401c0030311811200d0081d0310819080d00c03080b6040c00018494001c410002400c0c0181e40ca0070314070845040280c0b4210a05c1a61100456030708000c04000581c0104812000c28442c0000c20380c03081c401d0600602d041e44a40758003100070b20401000c00000e140d03400c0c0c4000c5507806484d5003406801627030700307010312410040000e4444c0c00009140ca00724501d400881c3e9203603203040110501100780e00080008040c03180b80e0000c1748508a20507100302061031030000302e6200920859141e1500300d46a000c2691020002d001030f070b80107507540c640c8032140024180100b00c05000d80000c03000c40a11100b03207074400080151500301d82c0c020721028404030820070000700e041d1444007540880340d0100021841c1c0c014450707480c4a00141c0008940042c01c550240400074154050005160360751a0184610030034004d080030fa1008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 901165386 1250 901164136 901164157
    0x1506031015180305070303031116020f0f122404051f09060c08010608010b090603010302090c070f110108181b0a051905040f05010602030f03150a0e07090b 68
    0x9003400c2051040e1008011801566803420894210554070080d10312001c1d608207541c0c64101d05420404c141d00762194052a02c4588122030400e0b5007a40303400d0f070980751100c1c0070f806016101c240b415a83e60302180040d412000400d00140f8000b00074045035280b04540d0b500cac81d080c1041c24250a88604900164460340c3d1020050841001001d4250034800c6802e0f41c0d00e0000b82c42e900408001a8140140101318040d544c80070358a40c5045402007c40710103a000c24044003040120b4a49501d541040381d043d01c0d01991014241c1d11048029a00d9200b05030004d40403185030600641003003400702e810029800c1c242d03030341041c0b6101c0401104940012001038801680455030400c00a11100c0110200100003030403202c0565030b8101003100403620b075460350207801300300e8014885842d040c401c4080d21a050101080550304002c0046e5803849030480c0c0368080c010110000c0e8184803070f404140a10500038110020b241d81e070311020280b2034410754448010800002010440c0541c20040d543d41490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 901166636 1250 901165386 901165411
    0xf060a0f05070807030f030506040e0c010c020a080f03070642030c0f08150405030306011101180308091005060a06180906030525030312110d05040308150603 69
    0x9822505440c030414846545051081c2440540041070104020f0b003809802034480442c60085101c00400311900206510f114900c0c01803200208e00c4001107480c4810320a0804d402c00904500001d900da03000707544910320305e114902125030000c102001500600380308900030301401601030b0b010320705445802501d9404031155440c03202c49070514503840e80944400050820115240d40742e00c904014035412207400141000c00402000c00108544400b20440300304900c114106541c0c0c01d82c41e440083e0080d4104070180d031624080c0003080d4401e0000c0f4000340d41403521b00740b0b54540505910000c64605505024411807404d00d104a0301800344903803802410341d65032504141040d0b84e030a030341ca19065424600c40d5400704850303050384039910240d401800140b482428401011584400d00c0c5003411101210380f8080002a8120f120311000000c61080030401c0c883c2d0340900701342401003140020300c95040034140014103401c969194020010b68603120401000c0c8014024203100946a0255021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 901167886 1250 901166636 901166647
    0x303090507090b030d0e01050706140702071a090105030603330604090b01091d06010e0a0608120d020706021204111003060608040602070203070531090f0f05010b04060b0304060501050f06 82
    0x280303d0100c1b83c00c40c1105060050402905031200170465040c0000345941590362404e01401c0e940401502004002000c890000354800c5104a05203000e01c00d09641480300c044041071040d03405005d06803580034420306101c00425aa6801090081c82c06500d041078014800465054102400350b101d031f42d80c201d240444140d04e0f1058100003414102003090130785400030300c40c0ba503440c418404540280409254120b140c140018030340102e614650003560560700550100c845030140000750b8001c0e9142500042e128006400c0c0a00a849000c25013250702803910201310400c4144074071089006030948548401c038003118803d9003116200e008020100340340400080020340d043d002821070610250985410b10ba58001041801c5415120381c218074101404420f50030510002462100d80900001d0013023501e55280c0b4000509285000b03050961101564818828250802e001d201000342c010404199100f18510b03d54109940c1200c51605000000075070346072241a000080c2c0c0000c00962805 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 901169136 1250 901167886 901167913
    0x5120a0203270a031d181b03011a090409140f0c010908121305100f0e01030b010c03030207210c060e210a0207030807080304140609060a1d010204030303090507090b03 73
    0x4004103042c21044284000170316a6540b5460111002c0301e500f4401d1164a041c43c004141c200d1718480c0c003803040404140010000401c4405842032200c0c0a0705640350780e50007880108001d40035021020303121000c407002e80149100d00003841c6003c90010720559800e9405880111900c10705403003042681c0c2c0c0020f0058103140d00d18030040014424034500c0710101966640841c0750414040708400100740d82c03142f0040031a8108042548201c42480c003081680c495900181408280b8600a801c05074007091200800048811494143c1030100f400320b112542c1c0da0008201008800d0200e46090a085441d8a03154002616082d9103245401c444140c880071a880052500441c5180045103d03005001020582c0c040080407680c0c042c0d02d080707070b076443c00d8100f00c0881080d8075401c000d190b0240d002c1221a82d00483d034160400d002150100d107907050320045840c80c00300d050321707183d0390351002400104061305a40300c0303034000c1c4c8100705030b070b010903918131180084511107a009034250308820000341c2c0782e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 901170386 1250 901169136 901169147
    0x10603020a0e03161d0601020604030c051e03091219030e0a0306050c040905070206071d010e031903080f0411040902061c1a0609031c05120a0203270a03 67
    0x10307801185448860110b5900c0060716103520400010307011040c10740203000c2d009458645039a0708840082c00165814a100000d5441c1e00c004d00207400c10801540820410000744010302007614044a402c100f003a545102549950000e54100d102d51000c121039000c40d6000f041d015004402c181045058040f241c406860240990541c1680f00800020100009a07031344038070390150402e80c0b105515a41001210001c442e0040c000c48103640c0f04100b0002500d0344220240841d4412a00b6100a1050480144d454842c1580c1140d85409096002035000710350004139074915000340d441c407030305440c4c8201c81030809100b039801a0501401e0f146500660810741c1042c0520b03032000d00311510301940c0261204006044680d0716001c15110054860118000e40c81c0498183e01280d50f03030700d02151000007a54548003800181000800000038100890003001a51200f50cd480c066403258940740c40448000d6004403074010306c410a9002c0380001151450200400e07030f02d80c01c003c100494480d10152034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 901171636 1250 901170386 901170397
    0xd0e0d1803170c160b1306090b1b07050307062703030f0503070216030302010c0806013608030a020706110a0b010e13020411040501030f0b0d0b222001020a080301060302 74
    0x341845213100503410f14015000c0c0100400c10011040d8842e00180410a0400c2040d4007480c108580320340c0038845080c15404458140550480c040448818003014908005c0705500040d410700074000001030381c40c3c00554201e400e844a5010b003903602e4100b00c5503074811049020180001d0310b00c220b003c1e84113003c2c40c01190030011a00442d0b5006804208015051034650411801031f5155101000b440b40c02170502c1d80c02c440d09080003014043c4005003d0f094840c6926200100080e1401c580c0c0f81c1c00e05c403c250405406424142c036921031040c1e6000e90f0390540b42c45800300242000b40350204511000c032b01c4480e8a54001800a8a42d10b0541081e0a070f482c081c0c00c4031100c400042c0c000006036241c1c4201c07503100020581158a0700d103048000340031a900e80b4042155541000101c101554800c555008076590040c04c00449480d918400c1000340c408264110140c24050284000e0110406c0f0142d40200495150110307011441c00498075200030140090038514144014420796000c0d030050103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 901172886 1250 901171636 901171657
    0x1e03030c150608161d0708060607261b03091c0615090e070501080c040b07030c0b0f0411041a0f150d020414100c030f050d0e0d180317 59
    0x7685030726081440e040150391203074801e00319640c007010031400964800000f0110302144201709103152040c130240800703000803d820711a860000382d0700200806580a01c2c842000c00e003031f403045182500b001090603880b5201300c241d43d4a607410030489504001045882001000d4104903000b000c420481880300c85603001100c0c2c0540f20303070382c1c0154403a500100d200103200389203001c20400503040280b814006035810840c104120041007020059909003100c0403151410345990791000c840c10200c4d80c00c082da08000741070f640191305000f0104035020030f16001d607000b00300001c01c048506040000b262514400300048409028084036145082034490413004406411034503921048013001171564404444d02c1c0d4a43da010600b440200400c6e01900420f42059402c5001030522400107800c0c44070207070b8010108085500b0410200d40b00310241c600018407040c040c8507400806000ca40c6a050300350810b000030348460302120858001d64400400c0f81d800c5112180200b00340c03552269541d000900c40d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 901174136 1250 901172886 901172891
    0x9150c040509130308090a03080c130b040909060b1c02040e010605030f0109060507020303010308190e060703050a08070503011206180503070c0f05060a050a0807140d061e03030c15 79
    0x101d03074403090040ca2040369440c01d0302c4031002da54034000d00319075030181119042e54880740d41d441c000394009100d0f6030050a0790f03900513100d400504550704041c105422402804034081000221999503070040010f60f8801c110900c00d4010460501c5a000c5901c0741c40015440103140043c09420701ea880002c5030390100c40086038498684020903d8446440380010320780e9545c0c00d1405c00e2041c9482001d801c91454400386140d945580c6400c80940210156503000100e0162a203091500034001c1003080702c0302510307090b1030b40c0003400c0160030381d00648d81c0702e8080f4a81c0070001d000d0500c503104032030580782c00d10043c40216165840f0b402c010320b840c0c00c8009d103545a100007007010070020405070210138800c1e41003001090400340c0128100c503141c0d00032402140180070360354032580c20200b0380ea0360b580d080c505011550380d241c1048540c00340c00e00c6d840100c03240004c0c1d21840c940c2c640d000401a1800111107107030303541e2141c4070115146000d100107800203100003061400100c107940100b84801009001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 901175386 1250 901174136 901174139
    0x9020a09150201150b370f030902030a060204180c051e0d06260f0d0807022a01031805150403110609010c170622111c0b0909150c04 58
    0x8608404140c01c0807285940100d9001b18080340030680b000b205510b90012071541c013205c03208000210180014400b4041c030408400c002030300c0b0350700c40d8009640082c01c035030f9403518038101400294418000d603000400e0b0303201c0015000c03a03180a505a890550381d600342c60040c00568107283e11460f055541a10b000401035103000219a00030400a810040602d00d22685100c802b094600c1283c020790345160000400c1100301400492140e8a00300e050030300003019a0784002c101d040c151100c502d1541c03180810041400340303c04c1c02d00d10440300c500ba02d0402c070314607202c81000d20044107100c005180d50710940d104a9026481904160445c2c07003820300301d84200f241c0c1c2009003446800c0301d0030f0107a603556004110141d9400f004841d0f20362090a0a03402500f0610041030b0000001e07106030342d011410300780185c01203c1c0366003d00550550280d0040d1540c00d4100ca0f0116402080d03194040785041100600d05490701c4074055004000c0f01c0c2c020400c41d80280380e00212541c00401408520409000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 901176636 1250 901175386 901175411
    0x913020d231e0c010c0c090504080d0c0f030605030a020a09020a020c0604080a052a040b0f0d21020f0d0e010507200111030f04050127120c09020a09150201 68
    0x10301810707850708001c5005900c40d40b0b802450071403150841810000d0a06111000c15211a0414180c07840f0b4400802c050361241040b40c1184500c44036207117518138014000150075440700c003120600c0384650f0300740403103030b610010550754500440f8007960021122104200020781940185a8203f580c019548010580400500c04d40c01540c0640b02c0c40e040a01c1400420000b4400c99050140034140400b010f44e1240383c41f1380080f4502c04641c003999980034014050358446a100ca00803030001c0012240500b41d1402003203405040801d03500b20001032201c0002540017044083e40128414018500e101c60b08008444440c0c1c070016041c1401000c10640c0089204002120080458101181101014000010310b02e0308440d84a00300da0700144003805840050400b02c50456800346821094040300445007070075840410540150301c1424000001d0005581c84d1040300c550080b66078803036903640c80040c1c10503442161400e400003030010809102c0454044480c054850140c030000403803080a08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 901177886 1250 901176636 901176643
    0x803010605130905040f0818040516032324102d02030315010e06360a0323060a020c0d0e10030203060d050a110913020d23 54
    0x30054400524001940d8240c0314602c10202d004098201c002c00c02c83c0303881d07280c0904212000200800429001843d94144814116440d80301040140108021b0400001008071a6058215070000c24280000d0403000400d40f02c150380d5003e591b80d8110103596031644070812000000100000961324465801e07180d17141d0419a000001c00e6840302d09441070051304160b01c801d51103200e0400b9803e8081006196607010007a09c4e0000e40100c22000c4007110100144c0f02090100070607500b080b0045500301c00c0344200112410030201590040441c03010302c8074005120211b42d0002ea8200c03012400800020f135141300e1041038111401c4c0701c1d85004d5058044c26040100640e00c20501580100381c0300107902092158004014a9050002da10052100031a07080b18440c0b1400007491740c0800000d007c2e07100c0c00c9103411600d5000d401c1c0c1d40400200d18040072142e84141d11680217400f28000a00c00e201203003040f070304c15a001420444400c0c080da80e270840e8204c900328200c0c0130104071180d00c0e40e180c4081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 901179136 1250 901177886 901177889
    0x60d0507020309011b02030d0806031207050312010609032607021903020a05010309030e0405041b09050f0f0915090f0706051b011806020906070c090e1e190f080301 72
    0x307901442d502d11208000510080d620790221011111081c600b20046c0c0e00050b04040416a6061035003080d91110300082c101140709031280c1a0f401c0c0014030fa820000b0100003040304c100c1070904544143d807580c03803c0314903c4050000034a5000580d585142c001083c40c8507038130320143e88000c185050304070b6012462442c1446010400c540c3d64540a1045141006550b00605003c0c64200416801c1c0c1d1402003030441c9180c4250f02032559200464284074880c040c1804030740c400700d4000d035203c0d90b510f0b8a00003054111802451348484002060030003020149a50103490184020603400c3c1d03940c0c1d4071422110002d440d407a01b510420001c180400380501c8504020007003512060b465081a2215103ca002d03222014040c9924000c095030315481006041e501960700311500503150649400401c1d01c1d4401d042e00a4030210001c840021014210342009000340091002c0d030301c40014a0340c1828208405400d800491381040384100e81150846e6903141e031842c0101115605d0040350b80b40c5401e030b41c0c420b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 901180386 1250 901179136 901179151
    0xb070b040c0b1c11070f03080907050402090f040c030e06010b121f18091e031803020f06090307050402161b08070e1e0a0b240f09060d05 60
    0x44804000c107200d5003040c844020400110741e203150040c80740000d10644000f54109210f103955015200c0402051010b94803915480080820203011a0501034103e541c12034500b4410700c00c03000086518205030080c1d0348054400703810046c0c1200c00c041004080e00e183d07041c003020542e0ba54a20f2100e802c0800040d0b00900b0003d54440c3c2d03c803a0801c4012035100300515441d5151038200744500c6c1400f444c1c0c0d421044a0a0100c201c454506034a050360186c180d500010f4001800340c2c901444e86002c00410500c070b00d129440300040e0040421801247d1520b500c00a91311a0078503400700c4c01401d0560052150200c01016120400e84a8000600f00c2c0c2042412645a1070010401c2c800c0081c41482c0c1c50036100c1d8103104000441c6040101d1350303500414010f5102820a00c40402c00e500c0c008a0140700010110b690020580780000014008094600019200c0c45060103400c413081262110b085016002070101ca01d81304030920603110940c00405040e030822001c100d80c0320b28802c41e12500d4040c502c07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 901181636 1250 901180386 901180403
    0xf0a03020304152f0d03021305010c0807120f0e012607030e0102120117061303030b0109050306070206161b26070f11041811030c0d030201060e01080601081e070b07 72
    0x4e40c1002d0624202c1c1410716101850304c10400000356031203208880e002c0350800d103400441c5a40b2450302d2041801411002066903940b48011350702039400240c0c011551400b80d5031821800400e000442c2c11000d0307290314101c100d00100702c19569202208103c0e41c00303181c0d0b081c045180107066643e6400c991005440030441200c4000500000740c90403582c001c225501002010390f420700f5606a50f01000e201e60040074580e6815629401e6406281c010b0022b1100070259007071450244400f03501d8101c2211481c01500380c003149001c81502a0940d880704000c6000b0301600307003042e681d407a045036003c01c1c8410820810f100c0144480001c100040000500c100f5481d2034030480ca14200c2c0c21487c00b05c884921441c00c241c01c9560640d41e1a0101286503005030032140710074020f0303001c01e0600500041040c1c2014100f840c00c0f0a150301500240201c41d84100148443c2c4c0e61844c2142d1604000c1c040c42e0300d150022100d6010748081c2d004030004000050055a1400b0b55074002803400354030405046a0990 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 901182886 1250 901181636 901181717
    0xa08070e0a270c020102070503030a0504110d050a030e190302060c0109120c11090609241e09180606060c010b0d031e170c0d0b060f0306030f0a0302030415 68
    0x30b660b405110a0103003540000c0d810209075a5a0988030f0100030038089109650345c00003002e2098030a000314803000c01800d0124406c0d59400c149490b42c80280c02600410f4011002c581c00b401c0007040c46441c1c8d800102c584040a086074200082980800c0c2050415921908280003040c500c1000140c0403205803140b00c01908a8500401e0b03070450444800e200301d040c10304000158079040c0c6050340c0110b581c0c0d243d031103003011030000c19210300344640c240c0d41101b000c508162031208152002c01001d107017259003455540c1da4050324098401c0c034080c420110b4010202007051810030f100030301042007400c0b0000c103003e407444d400324816450800041c0c0024110722291900d09001c071480601140041c80d081e042500181400380a44902502034220b6040010300340300483c9150748440c0a0784da0042010303a468140c0946010705420540d0b0161090003840000d500b41030700090201e5240d50700d40c026504280c64040f0884088043d08409014014101480c1c0ca8440030310324a1a1120303580c004410b0b868 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 901184136 1250 901182886 901182959
    0x20c0c0a0f06140a021e01180c09110705030a05090105070f0804090e0606150d02041a0c010b180601030f1803030e01060504060609031104090c1d060103020a08070e0a 73
    0x10000f102c2c0407407009010002d0301a01580403d21a100100070340c04143e00c1920340c100307035005120580e041800c40c581500b0701020441f00004880403107804c1c103800d029a40c0340d0610718640e403151240080440d0300812100c44d02c41c2c041c9026101c0c00c0814101039041801a071148000000101d800300c809000000e810f0101c2d1034684501c100404002006103028548440458980e0701c64010081d1030110100c0c40c0f8407021060740488018184d0141c3d2034035aa008151b45805940118a000a282d400c001c03ca50b45400c00407013616203698059200c110a03101d800041d40280b010100e140c1800c3d88071107800fa2540143c8101d652a00d209903000541120b220340b403642115141c0e0020340c4107038200b2300c0400003d54400021429250040d507200c42401141002500070498a80010242500b2160010703415030403c1440801c1c4103a00c00c2c80c440c0c1e907103900044080744520040d080c08510700700007003400706100d5415280c500e20058508250f0f9034980310007030421503e003d0480d559040512021441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 901185386 1250 901184136 901184147
    0x4080a05010c050408150a110f071202030306030312040606031e06060905190203090102161209050a030305040323160603060b0702031c02010605060711090609040213020c0c0a0f06 79
    0x451402c0c0703043d5042900340404d403074a524140f51080031202025000c40c0e00d000c504da101c1b040d4081951b0125a0300c8220321100314981e040340e00d080c0c44607410410030352052030010045a1045400402a620b00480c801881701414000362095410170b95646010002481d5038401e1003208081e40750351030b04090246425030a075402e80d00f020004d2810300060140b40c01070020000d294440c3d2213030140e129a1241c150a0090003050305d07050716409980701a10038001e200000d035442d0301aa94807440142d0301c601c24040c060344284802030008404010820100e82071070b001a4040025069051015240c0c02e070b03161814600c1101c01e01b00706140481002007e80521071a0010700c0320004c0281043c8460b00000c0d200c400230841d1048a034017031f40c0c5001c6200d02c00e50000020704001004a601d407102410204003628620740c60344e0141c04080701142c3d0910703107804d80500c11a4020224078089214400c4400a50440d030003920303641c402c1034046117681c0d0b2804d0a1402030718000c12300c021200c0c41d01600600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 901186636 1250 901185386 901185401
    0x623210f0901060f06050c15040305220f170a02041410090920010c1a040b0105240904060b04090207021c03020c0108100503100e0105090d090312031104080a0501 71
    0x14680c0c0f40c00000c10801c040030414004603001800c044d5210003c6c00045030404425400b9000b105038144108810150403c000d44889000d25006e1250345802040f0303a680c00c0030340c0c0a007410a00c1b51035810860105090001c0d40070440d00130945000000b0396020a0540b00c0c64801600c0d02101d0004101100103070032480c80080c02945000d101540711500d515641811400f8200141402c044904070681d025080702c0d040c881d03000c1c0c80d80f50150444030420243da2800e45d411111280200700000c0c43d4503100c0e6401c02c00241014042d4004140030b00c00c1513941c2d1001c82019001500c0d40000104242e1580281001f006920b8016a484580e07104120fa02460301c2d4505081c9824007c4540c0400d500080e0301039501c1003800c001e03002d61606060241c2c00e40859019552500c1130ba04205403d42c003d400010040040070000d00c840d46682900c3d50301c031440040c041c0009080500104040ac002880c481004012810005070010101d0a81c0c00d480d403060f00b0024055010000000801400340305c3c184 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 901187886 1250 901186636 901186651
    0x19080613031d060403080f16050a120e011b14101d011e27150b090613020d06050a030b10060e0a030f06110307021f05010623210f 57
    0xe1100c0d041c40001000f9000f240006485e541c00800c0082860000c0421920110080c1c0000d81a4600610f0003039540c10341e241c81103d030009800b10600e80640510070300440b000d4141c40c0c20b140083c050302c00c001400103034841500c0100c10403020901008060101840380b000814001c18001e103000a40142d00c50f1074201280a81e1400c3d540740c40c0c81c65124030f041c50740d00c030205002c10f4001d00484880000409190307003500d00e00a42c0411420002c400c40151081c6506e480180800341040003040b5a850007100c590344c0024070241400c0d52100c19078000c061949a40000007113054403500800c03c40f01d0550001c681408200050041300000d140184000307002c01d1405842c481001c0012800382034880c40018100a8140c81100421410343c118018204030302c41050349901e01003a0080d611500c1c9682d0400345005c0103c05290100035001e001e058400c10748030464510b194014148146a12019074201040c041c0319200c5605d0010450341c4004a1660290b1040e04001640c0800018043e1159 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 901189136 1250 901187886 901187927
    0x106031727090601050a020a02041d0613050c0d0212190309090c0207050402180d05100e0c0f0d0201020a0602360102060c0901180803032e051908061303 67
    0x5807541d5075803442503a000d0002c0c0b8100d40c1b101095101a4038020101c44002c0d8081c5c100440b0724918901401007441f03030f82c540c8048a2598a901c204920900808000a4031a400105a160940c208240c5200107244064140600b200e00c0c641c51500f0829039003500c05c400b07940980340809155000640c1c00c050f00c5030f004104150551000702a64810304d43c071071180641d40204902e03124414080f0b058203c40f00242005000042c14034005407a1203046104200452401d03050340d0210f503000a441001c2c0c500501000e40c2564050200400d513030039590201d046111f0f070340d9900000b5000d03002a103c003800201c0d1811981c1407100c41c07601d6046800f44d0b03c1582f003400070350080c1e00341e86c0003d083d41c2001d96440c8407541d0f202004c1c01241c1040c4180d0104031079020b041c00000f80490000011449401c0b605100000c10110351190f82c0c190900c0307401c00304c0038040d142051009240a00304003000e01a510b002b604c6048e0fa070000641070030011208070788488414250281850342108100da075215454022 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 901190386 1250 901189136 901189207
    0x2160c030b07022406040c030b120c04050108011e0207052805210a0e06040b07050a0605060d02031f270b090d0f050702271b0a0806040c0201060317 65
    0x1300700c40300140090700c620340b201500109180280e110284810000e02541e030030604421840780d5581608074081d004614100000038030190611030f10b0342c03c0c8281801005c10150507840040039411070b200c151401e0081e1800c3c141030300c060a0105008c20590300e024520804039042c003a08000400025041c03415500c04c88104440381d0408072402103000d8200320321030b201401c000c00e070f8a0146402010000300006105028803200045110405e07110714400d00481e5951030510940807442d04000b034050303011040c2800c0190030107151802d0381303040301000100e61f0000c42050240015500540c60134803101400001072140c074000d07042d8000410002080e2040b401c90004201c41c005100e004c1c108940420720b28119078810000c61b4104883d20701c4030100200701c1c1818240d001041e9040281c84248000b440034101c0900d065a00c0602c00c1d032107d0100369900d10510000d440760140700070440d503a42c280400000d00d624260700c980340810f6035142d01c424040030150714008030400b048400215070b408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 901191636 1250 901190386 901190443
    0x50a0f1a04031a0406140c0c0c0618060c03071e060e0105061e0109051305071209030c022704120f05090f010e2b0309151202160c030b0702 61
    0x1070520101543e40e00b60282ea55007001c40c02401060b40b1106040c142c071080c0408040410003400142503941c00740c0760058000d0042141e244104892031144441c03440c1681000d11b0200003400200700c2c02d4084ea46800302650310048500100181010f001507550121814080383d88240d0700180240c2d4000c110909081001070791130740c9102c0c08000001241c41552405911502c40d0b50000e04010f82148910340c01d603900c4801030f1504903041d400080c8a0001c2c049080171031b0143d9411582c1644a411410000b60280040203984000c901000c0359541d02d00c0540d14240301c03000c0c1c811409000306c2550383c804400003d08103442c40101e4401c220045c07040340425a20718850248bd603030b003400c020f0803402400000c160f6038054845d09900310206603000e117504146030303210320602c1ea110380d03a001810b039186c9050240076135042c0c10580006100c42d882c001e12041c41e43c001d0801089085000154460319a01c44003c9041c035081200c24080900620030000d40401004006c04000c44245464050210 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 901192886 1250 901191636 901191653
    0x1f060e0f040209090307081321030c080a090b070b0a06120507090203041110090503070905090d1d0a03050c090c04030213020a090e151003021804020f04050a0f1a0403 73
    0x200003902c914501404541a078601700308a90415030f0050806440e8100d000803481c85299600c138101c130300f00400894000c80b100800701e01c00343d960316490361802c2e84490340b0384440c10b8020030707804800d120f81f0480c0891018030302800b41c11147d1180300480d0a520740b80c51080705540300355001050301c90441c3c884100040001c60483c05135110b100c0d005032643c0d1036043c89045e505c0014981500009170030070108240f03900c4103112047d607000b036044880e003c2da41d13040501103550403244003485402244100c15250302c10144144c125200129a000c48a610000a50041125402100c96034844c80c0300501c24181a850307103070702c8140c60802360705062070b5070042148840404c0c400c0c4407035036000440050302c60103030b59510f002d080304000803111807400320f10403034103006156a25441182c000c4038203070220748a8021034890406098040d22030b044d64900784000394000200701c9200c81001e20011451b82c688985260080c880540910016442d01e007001d144003d05503060042c15604210038404102c548 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 901194136 1250 901192886 901192891
    0x16120305130f081c09230325031106030c090d050a060c121503170f160b07120501051e041407020d1404080d052802030a0e0a0806010312111f060e0f 65
    0x1b0069108590010000a041c01031a1500c101c404034405040000d01c0084050340044c0da2042d50140c0703828005200b0450b0a000444415100502c00c002603500d90030305030218010b891043c411100c0c040c600c1d5982806407400c0c148941e000400c44008035501800900422101800f01480001140e040da1030300c42c076503c03102c400403444040004003804040501011154045034083c0010700b10350710f0f4076128030040b81c1a1b400a00040c02c440840340d80034500e2042078104c6034000c04861000760822040032181ca100b0b8840c0303a0090340c992040c5082594011680d1140c030007940075041d1010048405071400511260081c04040c040c4014082000001a604074480300c4e800c000b5103a100e60001c815102c00950140004040e84460300601039800001070100e40c80a62110b000000c610b005000c0034986a1290061941c461001040400c0407415900d2009c00a0f291901040200801d560719041e0100322401c811100a41c0c0c404040b0040c0c40b992010b80b807501243d11150800402400100754003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 901195386 1250 901194136 901194179
    0xd0602090103061a1e042103090b09090f07120203040f020102070602070803220519051e010206040605131b050406090c200f0706030b0316120305130f081c09 69
    0xd14100000171345120700343c1d8001e1005000391403400c1c03610318265200011841048011943e05140450b01484041c01c0d2036200501502103071316a41c0345402400c51440c05402ca00c10321042c0e5048002e9080725000844c071403401403070482040286071000918008043d40000115005400284540d40300441210911800d60000d80841d60b14200741e44002d45190f406280d11003072669105806070300e50782081c0122a01124480300c00d292a8600d404003404601d802030040e00f20303c00240c0060100d074001030b0060614806e003c5840100d030b40329010401003119010070013006030b00070002c0d444d150043e180a070140501c11302c00c656580b0400f400b0380c4000740608042074242541043c80413802c01c0101b2401d56a0022034441950340c0d03402074006c2c01400910b50003800703a007032002080440f41c001d2104440c00041d4101e441091520200c4035078111524000c200310703030000c0004400080808050141010b14040c1141d407803920340c100c020440112111083c070015580401010820303100c01d4420052 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 901196636 1250 901195386 901195417
    0x11070b0f0603120301091e020c010e0d050a020c28030b0f0c07020d110d120e0f040209090118020c060a020c010f09050c010f05121006020f01051306020c03090d0602090103061a 77
    0x91a01f0080182410038400303001c1d06101248644a403541500040081d9481c2c0b01a6140d00508450803200341c03140500344005039002960240c102e00744401e040300611040c00c6214000f540480f42c480400240340d03c04d560120700c400c12b010b0010902070206800201002450780f0740921036010442ca04803c0c00080c104011031540610a40c80f07403111b805066510142001c1c403030004a601419041d070001d02c0c18002c0180581c0a069403c0a108445070305400820410480c0c2c0780040140001499404006540742c0034440d00c0c980713940400005014a69070180581c8800c45130400314211682d031142014444c0c02d0414100110300f000c154900c10000c20b10700700c0099801080280e90601c90320f100b90380300002140810003507803002500c0e041a41c00725400e480190350b04481030303400d032078082d00d501c2c0030450b00009480000345d565009000e986001030039641411078075000100100c011601c00e841050300028908185d6074135114590250a9030f0f040c043d05c00388500051086402030341400407801d00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 901197886 1250 901196636 901196651
    0x308010e0405070b030705090d06051b0414090702030c0a06140c03060901051207030f051524010507030c0f0b040212150a1503080705100f0207030c0201030b0411070b0f060312030109 80
    0x138403031b031f01700c4010b447d0142c048031200c5054980140202411641c40440207180240c490b070a01c07146044408907010880c4006c0b60b01300d000d040002d07000d00640084290b1108104c2d0040c4400140b100c01c1006026042c00107100b15200104203040200038900180004200100704440d1b0300d01c003560b815180165110004101c3c100613180c5003881e250000352006162080002c2044000901d0a02c01001c0c04002c000341e40391a0300200140c207081c2c18180035009800002e031a42d510410203000d040d4080c0c41c01503d0405030740c40d0703054a81141f00c0181c808907041c00401081d414901404c40726140f414000b80414110b00e171500350001d00c09084407112a855400a40340e00c0b0444a4120145400021441e41d5000d58034113150340e0100842c00319041c5090034014200605075200762a0800d03010f071151407880c3c04550044000b4086860f03d0b6601c04c2d510500d9107001001d03040905022403141d41602158280100c5002e000c0c88014002803080e406409000751407141c48065a0441c1c0380000042210b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 901199136 1250 901197886 901197901
    0x10090b150f030a060203190203091f020403121206080f0c0d0501020909070507060c090e160908060c0c061b120a140f0711153106090308010e0405070b03 67
    0x401c007001140e85840341c43d602c4028030605a0003140500e81030041080c000000d280964203a000450b0004007a404c41449581e02a40c2c00c80708100c00d50301c6c0303080107150a03225940e490b05592081c070002c001541140348019241c040b40700d040058005440108201e05800a41682c1d5002d003030302040c040c04c4031110500410500350140c070580300008101010720301d40a403000f402600300100a64000d801e00745000c2c0c059018440e00801c1e240010007881b6550b540d80c0c0c00001c680280c1880d541048a1101c001683c01c0c024030549010728800503160b590348560b0100d01d880c0040c09008148841301028224003154500b0044584a0f1541c0740b076010b1955520740341c0b0b0010007030050110021011001005040036100d440300b8400c04550f2507141ca41c1100c0c3c000d10f07a131103e100c48101e0311090b0035004202855a0b600c030b02c2d08613443d1030505451220031512518044508401c003195120703200d5000400b0560030000d698050104219400501d00d06600e0390380d5180d002d446203044440d8000003040c41c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 901200386 1250 901199136 901199149
    0x26120904060e01060c2904030807170f09150c0406030902011b0809100503151309020d150c020d090902030a0b120a031101150e0c0417060910090b15 65
    0x920705075a5070105981e4441028007070034003208040310010181542e40315800e411b11040d081c2c1001400350080d1994455400361823010028100c070b000d01c0003034035007440c8010465004074403e290800c1c030b0401c5802e01410b45850041095100900c401502c010410030999010a0750100c43c1d02d0303d0041115a02d5000503a4004000e244502a4004540b0344da801d004481c0018407092006aa8078048400080000c50b1366000039510004168820183e00103149041900348540b01c410250003e0607084590010303510100100c82151600580e040716480580a44503000d1600540e002400c50040418401001040746005400c496680807000c200c55528a50104200200140080441c0b02c00c61207415034501071008200c0000e01026400c1c1c1003441e06008901c1c06284282040350f600307090207070010381502c0082028a08140501c40091002c01c0701e88805844070340303580901110309014810300c0c100000140c070101c00e01c1c00c10300520005030810048035130101002c0903820a1020010000381e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 901201636 1250 901200386 901200389
    0x18061207210e0a021003151205211218010c0206100e061c0305090a1403070b0913020318150718120809010924020c1203030f0a0906152612090406 64
    0x29104a08a00401e405612300c0e007900060307015404540605840001641c01c1d61a8040d0103040d28905024203802c038030710151841c0d0007a03940c007940082030403948081800c40c0d04001d0441e005900c10810b10182c442d5014440f400f8240c0108402070929001010581c0e60384964101a104440d100c5004241442201501c048242c000c011406e00e55880e800402442618000c1c540f20340520301001410408080450707907010707406003100c3c0da42004c0700c500030025080103103000c003401c42440c802401841c01b4840a001da40b2050f03581007840c281000020500035401a4141003113000202c24090f400c000880003044581c00b450f078641c4c80848400480701c607985c0758030200f040580c2101d2a040c1401c020140c0b02070001603403c07604401c4180040041501c08014000c00a400070130210b078400200b442d51941c00140c94402050544807a5102c1c1c00322048031038800351b0700c0e0441c1e000340081c90441e50210819400b08035241c01e1818409400742d250400780300100c40501300050b107055641c845410110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 901202886 1250 901201636 901201661
    0x40602040807030807050f0705130f090602030a140c07030c06020a0e03100e010e01060f0915030b0f0a060e060f011b0602190201050105031218061207210e0a021003 72
    0x715a980d0300d00e003840d800d400545c0c045659004401c103070b0303440f0080003404e0000c50385c008100808480c41c5410500c000e210000000381016252048040803810b1400218011080320200141080c07144a88404500d005440841c4060301040300c580401e034414860844641c00090040c1c0e55584e0340c109440c400480c400441e094050503c203004c5e402069032280d000300c0c9041000f03220329486640c0c007608807112401540030754100c4520600000c0102e0f80f0078540007441c03448280d02e6a880fa00d03180ba0646044a40100d00f0303844c80c013000400b10060203000010860340961401c03604110f00000c2c043e4800401e075a042000b05181d841c90321700a4000c903a18182c100400715968004682048500c0243c00380140142d070908000081901b00020001ca0b280c82c1144410305001c441d0403181d020300c450b84403040c0e01c010140002100c2c008800c07107032806000e050b1290f540805842c80d00c404118482d641d091022072509140d2408a40c021410f4084650b0481d03020026000c5000d003540186000501007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 901204136 1250 901202886 901202893
    0x312150904030809010e010e430f0e070e100909090f0b01060503060102060411150d0e0607030e0d0509130e1e06010b0d090c0b030c0a23030f0406020408 67
    0x20505402c40515070183d80311078003c1c001e00c480104540e0a884070311003c08d900740e2003810320384903410b4203107107414240040103280b884400514401820400b403107401d001c007181d2030080411443c000035142400800d43c1c03128080301454112000740a0a0840b45254091800f103600910f0161081c4204406800916010821500c650034842d81c84288020103c0d80402600008a0103900500a40c0e03c1404141d005040c1f9070358640c3e0300c0030700441203900c05030040291280c080305003c944000d0924450030800008505501254003890136401030b081006061808001ca00c01711004036a41401d1605800c02958425241011903044010316030b02610146c500280000c3c8000702090a5a050004000d44480044e9012001d900c41c1028454880018030400c502d21042d0f00039003080c800e45000d940354170012507481500e0112a40211742c803c2000e0b0001a1205007650021450004030300c250728207150750160b101d942d20407440090b00756505402013800140400c4215012034029002e03070020b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 901205386 1250 901204136 901204141
    0x3030605101d0906061b0114040b07120c021e2505031203070c02010807120c020606040f06030b0406150902070501020405040c02010e0d141e09030c1203121509 70
    0x51584403114900308021010a0b2065064900045641e000e400000c01c2c0c0c0e0328008160440401081400c880c403441d5548400184002450b40112644114040d55240c50b90340f404010003420440450401d00c1716a1500120508207940014402c81c0d85a107035209040c01e080c0c0d00ea1a81c034100040c0100c000909201001051b04155000031004544007030b01150220000e11440d00d030540401c0311000b0000b0b240b44201405580b2503c0750641081031410000000c60364104501306407030342403504002590106062002c2c5052030b00c142400c29801410401640e8215900d0710440d140141c006412542c503141240005443c150160b00148601e007030855540c0410301d81603020350054804c6c0d91241d032500400d01015030043c0185d560604c20760000d005000e00e442c40c1680e1049000f0f00e55102038034207020704082c00304000c0e9020801c12007130515076120589201003501c0c00c83c41000082c02110070070340f0b046400c1000400d0b10b0440d48034108240a6a88031440340f012511501e050582c4000140b09 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 901206636 1250 901205386 901205419
    0x60627051909051b0d032c030303150306130b150f180f0a060e0a0f020d060815010b0f0a0e040f0507080a0605040b0a2310021e0c0a1203030605 63
    0x2000e0880501000354560054803070800c02421082510001c6c01003180d10041e000320b07981007410005d680d0b902140302003401c24900003091442c1c2040b600c15040700b035000e15244440c681000b60580c4003481d4100060203950503a140701c2d443c1c1c0081c21181e80045007004020040d07a501404002100c00a028415108500d00400c00307110f00a841d0751101d0718260b00820340d13400d0140106000e5803108100141c2c65212060402d00400da090440f00d0500d0f800d000c001441e8100e402040c004284d030500a144071031700b0558031441c004060b400800c1c141c0741040003542d505100b40c19618581b4680c1008103006001c3c60210b03020700008020001c11605d401e007001700341034104a0250003007041100c104100368894013032104840300002455804500c0c01c0d420451108441102c03405038100e860b6a11804c0c68400110b40f407889065081009a0065065818003d41c1d0b0703008a414503400c400100808403c80d404510833101f0350240c00800480c2d91604d905260194204500409019100307010392145040b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 901207886 1250 901206636 901206643
    0xc0103020903210a120221041a1f0803070b0402120a0b01030605070f1403010b090109080106271a010807170705190207140d0221010906062705190905 66
    0x2113596021074500d031100200d200082c4203840540b005000100101c0c10314070091140d02d1002401210404007401d410040002a002910300a030048440e20b0700928904480100d0046143c2050044e58000d009410100d0140594150041d030151221468050300e900d0171824850030200c003a2070f0410940000042182c2ca41c0003610504290361050041c480440703089440d9420340c20001d900080900042c07000d0410030300240440e8005040200049030303249443c1d030a448159002c1e10f04449500d07004d440c46820150005016500c2e1941042805d4070140646c01c05c00121010390304020802c800214910f00440c1c1c181100711100758018031624000000501a40c0200300c24140d1384520400c000704039000180b010195a4060780030007219000101b4482c0302d9001500580c2c0c061400203030100d07070110b45607007500080d81c21000400c1422550130003005032a400d90104104c0203000004000071164190001884d83c191140802c1c80c0d00d402d00d003000d0b980e69080c0c0c200100c43c40c241402c410060b000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 901209136 1250 901207886 901207897
    0x70807080403170a0c0303051003140105041106030c030a050606070b04121215050609040b0d0602090a0e040302060a050606220503010522030e1f20030406020c010302090321 76
    0x2401091a001c1c00501e0f031060500a00403824045840341d4030210005c6c1c000d4110541c42400703481e0203045c2940ea0307110120b403480004140d10150b5036400074081070103440240e250749480d0076911a403448c14a44c060303420074400109041c00c80c130350750030100d081070ba80e2104654205810800408103402c1c181400100809441480c41c046007100a84241164013402350040310f040b02d04d503210030a440c1101340001a840802d001d540035990300c01035001981c5030500c00c0481c0d0300032a00140c45042c40428441d00d030903203070055502d5961800410000a41c0080c4081d0720040345080822240c55580129140313009145101a00d00182070901011801c0e44c2102800ca8400328006d0005c2d4907410300c540058901b403007900c0303402c410f2640441e011900884000364034503400380001d15566004041109030044100b66600059090441d0840d49168200c00d9620042c1d41c20240d0300d0940b45c50380c0a50b0b60050f01111a05054010449201603603090000516680c1e03c100d400b11704004e071146d615020340c0300303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 901210386 1250 901209136 901209143
    0x1203090c0a090e03121902030906010f050d12180b041401020c300733030c30020408010c0807080403050a08090c10050a0207210b0705070807080403 65
    0x1641c0005003264041c050b442041201001440c0303005030f61144070200c520020010403103110160440102c1151078401584600001e40140085504000c0500c3e420758039640001d116030420508a4003003007041d119100d000429050184490821008411004850340c2c4412003014000c100000e007103006c0c10000b00d081000340d007900d152008100400c0103400010485040a4246c0c81250400c02c011580c84501941444102da099554840c0c10151001c4e0f020f000049449049040100d40310050b8107003107114030f03542424000105c440c040203006012010003c8226400c401c2c0d034403828400035810100b1104941c00a540c2e940d1a5032880b4060001450820002010400040c0f47e071440380004074015507055448602e41824100f0885908030040c0c2900300c14014890303811300660712080c014a00400303988030141c44a81029003e0700307010055005081c2c6c9400c12500d900c000070403641244a46c0c0e4810129000c81e29a00b4080f100790181d0b13100100480000103c00d800d1100301005003049912 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 901211636 1250 901210386 901210399
    0x9050d020303070225060c030203073201091106030a0603141b150327010c020a030f0e0105040506210a0b040c050c060f071b060f06080f1e1203090c 65
    0x108a10174090f1144050f00040100c0204020f100c0d0b28070443c400300c800350191045070309040031500d41c0700302403001950b114440d9800c640840c0440c000b1050100340c2da11040002c010b00c1e8003a84940202c0080301c000c40341300740000030005807541402e40c0081701440d0844041b800300c043c3d8458040c0d0b43c0d200d9225441c100500e401c0c43c00560b140c0701c0442503020002d000c240d4150346030b8038040c0400c55001030900e414801c0c0b035801c43e02c103030100344298442c6500b0f5a005082e000141d06010f400d81094940403410400500c4a1604e0359800c0f40883d401c5600907102581d48205500c8408007405066010300c3e00c154661043c4010031400e50001132003000104c07000c10485020304425189440788a000600d107400c40c900141c529520108129030111f0181040c2036041c412449403901308400d03030003c903800707503030386414141080840c89883d0241004400400210800c00345250350b03941c00c02d0240d20480802400110711841c28407107907100040c904d06a54070703810400342c541d03103070401b4202d050300450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 901212886 1250 901211636 901211653
    0x1c030e13090507091e02160209090d1403040602040f0807090b060a0e270c0a0206060a06020304260d0f0206061e0d030e0904111203030402060a1209050d0203030702 72
    0x1001d20403546026482402810383c5490b01d010a8090075042e0301030550a0200e110445041c2c0060004141800d000600595042c03440c0c410011a01c03405000381c14680e003c615844103481e0443c0507881000c0084d124207407030b540d80c2c1c6000c1c0d010303100716000a0441c08000000180074000000c0203010342c0c1c44d500c41403002800420074800180681754005000a071000e0403190281005801643d03410500c1d04800e95040c00703600d50103c400700035a80611044d00c000b412801c40ca50522441c0d030010011182d46030900e1505400075664021801040703040d0300d0b60f000c0e04010040709401c1c2054251a8015200e412841000280410803108006000342c0200800140b49140082281c101c4841c408002c90000c00c4504c00e01090f281c040c0030480c2403022a0641041c4c03a41c440b041c25210301d100700725002c100e585801c1445068200101c100400f54000d000380401680e0352026035116021314608500303803940e60301c0c8440141c03254107009805401054485007070141e000c0300031803113100b883d021030b176519 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 901214136 1250 901212886 901212919
    0x6030c08010914150d0204060b1c060b071b1505070c062d02010605041503110901150509151909080c06090d0501110f04080c010e01050a0309021c030e 66
    0xf541d4407602d07041c5110407140026408100c94550005045000c1d0501d03250303034110350102d002c80e00702c0d8001814051010484c0c0304ca1102d61802c04420840d0250305000141c174201242c0020f024101e002010403c00f03c2400880c1c0c10030484040081c2640c0c01141d0b200581c1d81e8010700701e03610582c41910082c0030181c01203001c07800350380c2520a4144e010b000710204e884660000c0c00202c08000460300715501d0347c4000a26a653740158850030f4100e0360107548291961030148c5544200c501e03000c1c0142c5111004103c01029041501c8160070b4900b040c5035280000c0700080e0801e20010b109100c454030105e801c8034400c40d0601f82c15a5030075540c503508051600c0311812a56103c01c0010958810000c0240b0842c604005505d550b155100d02c0022034109040d00310348184c0e03040311020440341c0c2000f0400300311101c400c204800300c54500f820050074020b1032100082482c4201900300d42850b4580d0461421900c1d04003854030581110f80110410403030900c1c0040c003154855541d035114041c9140c20a03540e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 901215386 1250 901214136 901214141
    0x6040209030a0f020405061e010f09181d150a050907090507031d070b0901050708040f060f020c01050702060910110303131a091c0309050706050304021309020306010b0d09060606030c080109 83
    0x1230b21407013040280c0c0038490011101d004d10342d0091810004950030005062403036204088001c03c1151011482c2c40000d41c0d040c8215a011002902c10783c08005414000f102421040c0c0d040020200c0214080c0d82d9004401c0c070301003083c0c1c02880118904400c000d4801d0340740d4429038540b0f040c1100b9112a11081c03200e0740d0744401d94000d180061034100040343c40c5601840007080410b1081d000b05091640e01c45403005800190303071003540428484004051142d0341401010502c510900f00942400104e401044403030080c108210301031528440650070f2203000300b0f078a0310b508030742004490350703490443c81c2018080c2c0050303c22a038102d2400c81da0806400b0b5199402d02c0340070700800030a980b0005103569500900390130740540a0503551405613011540a00000026200c01d45a080c1e4038205441800280004042d0201d410703490001e50000582d00447c83c1411520b036240740e9038603850f0210910000340403400000300007a2038a0f500003180c50301078010300070704c0682d030301e4400b40b50303a98400c0c0800703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 901216636 1250 901215386 901215409
    0x31b210503180d051c021e06010b0f0705120d0c0212030c07034103070e04020c190b04020102060106081003031812061b050c07030b06040209030a0f02040506 69
    0x1031604144105a0201400e40c55008003410003803201c51086501e032036041c2409074698100ca284070001840a65103901004400b403588580f0603241d10303026280d40042d4683d0018014003820850025100c102c0d0800c03071080d214142d0700403040d1000c4000f21118540f25a1101c00c103110070318217003040c01310194000b040b2540842a40f56100b8955640c0c25011106a030012100300c05208251b4040c030300c112009091910803003210440201d044100b5a4110100d445e5581c0300700c13020b44108200001958012440c5900d64000e580250300c542048465074101640300140d05e10b18030880021704248412150018005d034000c1e020f0b542a80d0700d0700400c81300444c0171290002c1020150170104000f91081200c2c159200341103440e905160f45501218020101000c4c059a10300e4540c2001e10400c1c00d42d01140d5202ca02e01d04081c0d00d416401d03180140c4504042c40f015004140300300010b1000d403501c0c1c04580c5001e07001029258048144d10342946132469840d0164055441d041c00203640741021202540b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 901217886 1250 901216636 901216643
    0x614161103030c130803030103050c0901090c0215090f0a03020c0f0402091503071205070c03030c051309050c211b091f02330604090804060f09031b21 66
    0x40c070350340c1d40504151030369000504210703003504d03403180004031540180f01860182d445a8041c4c8810101c40080003d00c54040e089841c00c2890280825541600080c0701c40340d00c40e54100e0068240e1b110001241130220044c10007800d4007909410100b0940d0205000b04190801c850b0086800740c4c40c42880102d0243d00400e94000900290038907040c1da2140203140d1080c0702c0d26000b10700484000c83c14050b10003d1310617202084001c0785510070146c0601800d6100403461901d54206100c199107228441c81911816030480e5548000c90070160b58001143c9460a007040440405c8100034448050320800701c900d26240070040c000d6842d0070400d541280d8030b2407002440340180500480c2c0ca010fa4803003000c000c100303501c00c2140c40e0300309019080c0d0050b010310070141080c0d0301d10080e1241144800000708a903110364948a02e100000e031805065074140c030714070716204506482d504030903541a0765603000501029508003900314035000348a582001d4981d1403404410b8034040010300e0101181c0e03050000e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 901219136 1250 901217886 901217893
    0xf1203010e06010c0819090503150712090212030f071211030711060d050405010b150c06040b0903040308030108100b030f0a0809060d020d060519060f0806040906141611 74
    0x39040c0d0304c60081042c0e0540110702440c50524281203142009000141c1c005c003240714907004101c81d2400f8844040d590001541c035007645d1074812030003890000004440718441d03584c0e025081c01d5450f102010011400104112507584280ca0003481d1035400903001200e0b07094101c422840c0e914070404d01c031504030446000450600e1155550b200b20f803001d1204041d0419400c1c040480c18000c980103441c0647d0284000250b0a04182d00b0300440d0b03803400a0b0350400d0380c004c0100d0b218450380051400e42c420b40148140141d5200e40c00c4480c114800c1c1d80c4007911288000c0700100e80103102042d00398400b0400c0100304015081d040a050700e0f1402000c41c1819500715813942c1001c01d40d108003c4c00c0b0464002c16461400c2c4c01440514201c0c0c01846941e01c11581c1c51380107100c02d050000140058841c0b00800d01c080e28603007403009000000e0342e2440c00804c1501c1d00807071920380303a035044400120741c8801d00740031000e1400405105908202c60f4244200c0c0d074000c02c520100d00417a0300641e0120350342c019 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 901220386 1250 901219136 901219141
    0x1608102301180b091008070501030207030c120903170c060f0c0712020c0a141503390408010e2e09020d06060b0304060f060f090b040b030f0f1203010e 66
    0xc0304a4580c2c081d00e0040707200c0c3c440c1c214016540e15800c4452068003a07030302d8100300f81c0c10180c5951a08000d6003082c0d040c1481001080d020a401030b20070341e03440340d20070300e00c0741c0440810a0455188207164801000790803900e0400b0518203005014040800041088904d41e64840300344556006040e0b654840088041041d00d010030000b64682c0411616401100e0454580328080396444181d03a00c40030940903601899105407604071020a0008881d0070b9103800e60a00c1548001c0c00060a120954009450b4a0680e20b0a860840c0d14904a2030441550384030f43e0b88206541c0a00726040a0420700d00543d004c40d5903940201d40c562260f00034180180d1501580008000001c00424005990040141900b00e00080131400340e000502400403074151039080615002c1c0030340d032401c4408804c0700e09110050180c2c4513a01d5040d000c4801c008004510313940d000c40864020443c0008440c0c242c015480200d48140000450340340094054044030b030000e16011030741895001c03e009040c10132002101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 901221636 1250 901220386 901220399
    0xb2b0903091e031a1005060a110606090103050312090a0209040c320f0a080601090b030d03020c122803020a0e010e03120c030c01020a080a0605100e040e1608102301 72
    0x1946074080541400ca8090940350b40000707d058003c1c030010b000007140a406644200000e101c100e0700f100c016103480c06254195600e4030b41b41e0203000d1429a8040c100d800007810b42e03800704240c0b0305181c1c000d4496603290070681061000740f06a030144103034805031152000d1841041c000640c030b086102d400c00a65034a00a4204400c0a20340140c8661003013a1405c00315000c41c0600a49001b0440d10100140c4681030000342350400030240001401d04d481840344501031b10340400c6d1401c1e2040e404030074564506030364807184c0107201208011400500c0c1c20010111681c1c16900800340364100761241b100300701c01c0ca40111180c285d5050080d0305604480d0b10410700e2a0500064025050200c0c29203052092902078182280c0007071041d540003800d2113040c81203030141c2e031051038094034082d10940e43c51f0800160240078080c1015a40f03000d00d9450b844c8268603942400307116440c250027084005d070705644105081d52108450509842030380740c01c00d5010344180860031100151407164815130035a10300701 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 901222886 1250 901221636 901221683
    0x30b1c1113020c120904050112151e0212041e020f1201110d06050f0a030b0609041b0b0301301b09060303080f100b2b0903091e03 57
    0x1100c02400d50b40a1004000d0104103000c108030000b0003862540d01d401d4407800708070980d581a48032000344510b030790880340031800010b9140380c40342d201c020109100043c2109484203007030180550754620310100700348541800480002d0302644c020000d1070f0681c915104032458903546248025031082071115400700f94144030240c034240035600000010682c48070384400306240e10001c00604c90781d075500400c0c0481d01d450300c0d01c00319006040e9071841d03685003140e0b2003049081000c1c0c003961144010301d00207000c000304104a4a0004800040651040d94400402006801c00c0c018008007406107840c064410415903032520500995030b4440d00b02100301e80725241d1051015206482028030f469001c62484000d008850086120b90b03503010301da26040c94598000d800280202c040e811400c038007000030b090001e06a46403000302000c004100b102c0c0d4403180004d0b0901012842d1100e0400c801607007455000f4400740d0440d0a16072004020640000003c4071b07401c4280801881c0e00d034045c203002840c80e03690 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 901224136 1250 901222886 901222909
    0xd06050606090a03080307030609020306010c020d1103010f2c0a26030c03010e0f010812090105070b10030c0602010b01020d03050a02070f0b090d0804020603040210120c030b1c11 78
    0xc0c01da14645a01440490021025a041980c000d100001030102440c0d040c45614000c1030500021400c604040300001d020b0642407002900c507950806044060080c01d5002243e882c00050080024503125420b80015240410224580f5145240c90500c4c00e4a4015207452403c2840c020701092282c41e07030388428551408c4808240345540c0e547c0070401d00b60342001103000311000f95010351290300d040c424001c00c0364014409000034144500400c0050b1002404c02d000d8104448040c2d183d00c5405c00407035081c000c904018164140034024002d01c1c802184809041c0ca0244500c4130a0f19101c080c10b030700740d403000070056006074031920301601d4481c460f50040360400300010015280c560643c54400086600e45025150702220909220403110700300f000f890419014240444a841c0c01d400040890000400c080e001d50540000b1150780c52050150440c0007003075003c10482041042401001050804d54181c0500b080500c05011008404040e031140d40d8400c516a5000054600b80034454010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 901225386 1250 901224136 901224139
    0x70c0b0c0f0102040e040b130b19150f0f06050a050a031a0d111e010c1209030506041103120408300d05100b04050907081e041202060c090d060506 64
    0xa40350101d45150081c00207000801505202540c4c07801c080c201030a2000000d401c40b8003182c581d02c4014001000250b4890780002c07040d00520010a8040d900400340015040c9842c1d44040060003158004801c009102503454140724410145e884901c10b8a00e40708030301c46100480c400f405444c926a00c42e0b00b24507040c2d0f81180400303a00d1940074012449004900070215614182c94121640c3c0e401e22460780d0502d0300d503a5001c851000c65142c000381c803040c040e01001d030400c4081450004400d00666400c002194400116855823921307003000b5071400b588014151081c0924480c200c1c00d02451800d413002d40710010094144c0c4424031070034503400320351080c0e08200316680700e0842d4003610501e805441c000c641840c0200b800d28080e101c11546000e240c00c041c030b07548001e110910564444c0e950359940025982000d04050b101c80344000051900c0d420059241d100f908100702c20001089501032210300c15408031601c60325140d400c01914054401e40a4000d11140b082c040403070f03081c0e000307a07800210 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 901226636 1250 901225386 901225393
    0x71b02010c06050c0a12020405010c020402031e01061d0303041d0a110a0302070521030c03150a1d0702010501030b161101050403030e060709180b063705070c0b0c 71
    0x85664030401524000c8034070501001001c45c01043e0b80f070b08000c0c481031102d0280d0003145010304000000c0c21084105034064002c6034040005045001e100400030104802c0800300217841d03948020013403801c1e54800c0c00407107400441c104007140303050001c00e0700c0544000d200c0591500141c800340201902000f056050026243c200c1c11803e4003181c4000c0c5071448940e54050303036030000c40c00d080c0c1c9011252000c084400c080ba80359039516860401c15203400001c000c00c550b58988440711110103043d035212165601081030240081e0b81c08039440e81022040d07032408030808a0391500020f80c203c1d8400d101c00b90007200d5010008120b5049102100c960080608200000500080c0e00d81e013124011907044000c203035220020701858400300f056a038410071a18000d2400c0f42080c04c0390302c100680d00000540c090300d4007072203009581c0741c0040c0c0300141c0b01720010369004071103135004c40c0e410307800034407903d200340d0300920050f1100703105500301c0c0c05154028203a45041071510106c0c04d86030f03100200c0c010301d901 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 901227886 1250 901226636 901226657
    0xe010b0417010b12070501020d0206090d0c030512011e12050706030b0315010b0a030e0d05040909020f0d061a27060109080708010213060305090d0311090607050f010e0105071b0201 79
    0x58a07071000602c0c4d0045800144a10703400d0100291900554205003003d65100108200b02d1480008542050603024900b81c0c0602c0d07024901a101c9001e00303002d01d440510203400116031100450244000b913541d4483c1c03040c07942c3d80e640c6d40081107800c2a0000d040b58105140912286000703410000074018045c0c105d07031082c0b50000148000a00a0300114031b082c50001c1c0840070030ba03150085a6a007110000500140244407901601c1032042d407142c9584151505408001e55540d040d108803428005446030003074408030b181c61001000c0d801c908442e282180f070444801c6080c0006030100d43c5041030504014540c14820390360345014001e0080741000f40d040c4010400090a0005230f00074490040056103882600503d4110a021504811308040c03900080182c1e80c000010180d044a4840c00c3c000b441d01c0304e003020076200707202d400c0c24140c120500041000c200100080e5079001801c1c1c4600800407094240c045a0070f8031016a03410000860180c08590100b803401c4c5401040c0344141450b20408 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 901229136 1250 901227886 901227889
    0x140105070908300714010b06190f02011d0604030f0e0f060c0123041124030403030b041104080f0c0109051c051c080601080903041a040f030b010303090e010b0417010b 73
    0x10303400804100c500d6103145c14000d403522401d004024861800301c039481d08281400e5001c5075140a09891001005240045061754600030350046500003040070150011915520726140e8a08040d00d00324002142c810600c1807191184081e40302891005003e001c0a00e072002c200203103600000d003030101c82d550f9008a02030500303070450f4407002d00d099040360800b1803905041486071800c1c44089680a081581d84542c01c40400242030340402e103000c8426516626175040880043c80b62101e41c0b5005071400c031081d201062400d010701304803038041c430444281d11109514a03481d107a501110901045050100340f040380f07004612146813908451040d00f0b0b190a6494151400c80c80303404134182e58190303144001090b0380c0310b404542d1254081c03c128680b801c094202d10b0b40c038031aa1040c1092035401544851808117000c044070028845040c0300c0c1d14441e03c1341451402c0f03039000e12044002c1100070324000b580120b00c2c481c80d070495451088060600345404042c20340d11000c3c5162003c155a92103580909 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 901230386 1250 901229136 901229233
    0x120a021906060e010e040b040b0a0f11040f080c0619170c071a040b04030e030a05150f010f12110d080c010902270402120c0a03140105070908 62
    0x914010300000c00c0c501c3c41c1c880106581d0406070407160085090800300000310b00110329035508070f54402d618012075a250312107000107126074880f0180041c01c10700c0d4182c80040070409041038844030022a1070165455500c0345d40c0f540c5050300c05401100034818401484025070301060040c0351810440d40300c00070f0803074180034078108499405100c5400710300c90061010720500d076000c0c120800414662800d164440026800d00100000c0c02c0100c0040a41116181405071822046d4020100c2d20420b4200b03100b0b800440c07049440308070130b4104000004034516031008601c100ca8200e988100c800126448485070340724a42c4030142c12991000f454000195a5801822900707040000054104041c2c41040151310502c6900e051000030302c0788a81051080d14902a003051f0304035591000c201640d404241020000003d003548515183c000005100125064030b540264a00c02040300d580d403420181e52140d807038064000c1c20b90042d10b1010140c0140e102543c0c0140e6220820040410400200c895 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 901231636 1250 901230386 901230433
    0x15020f04080115060f02190507120f060b030a0b070f02030412050102091e0609130e060c0711010206010f21050316150905060f0c190e0108060909120a02 67
    0x20360b80c0d5110311400e034245441554002501040c5411090040c1e07044000b5581c000092010150105942100f02000410030002c0004c1c411840103140225180c1804000e5410620041e1003a90030117800004919001c10b001c01000c2c1e1082c103441d06a00c1d0200e044130100b0f082c1e4801c805500c010000850307800c2c0e0f92410b400172144035000260b5142d010605000d0004180c020500f000340f040d8140201c50b54a500c242c441020003074408240e40c802911080d00a0000100001e00b58064001070066041e14070340100741d01c41c054040d081d01c01c12800c00483ea180e40900c600089120801010700c0102900d0b4508242c8402000300c0b00c04034401c41e2241825907100f81140014950603140000c104104800b402c490030b10600420000c001d1a0b40321680c445170020b064503c007454200001d510060301c20251000f030103000e05403c6040d400510054894011100d035540400c0003840000c0780c07440c00c0c0c0c50680c441d4803020085c05940301d401000c0c0c52290482c41e58031003507010304c210104440104030354806 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 901232886 1250 901231636 901231649
    0x1c05160611030403031a0102071208130303050903061b0f0c01240f060e1f0903080d1512020315180604080310081207150f0c020c01080c090108010315020f04 69
    0x10307560b0500e0b04e0080e0445a42c0e000c0c0c1889410100200e0fa0303035a07004910882100d001140b840c000207038500c0e140c0ea592046255101a59104160120901d03034002c001e404140e105904035082a16029400c2804031002000d03c50f09600030040720000070b0b460005400c8032001c6c4e20000c10b0080c58900100402036111094a202840301c480800c5102c6e21100703440c00a0829003480011105e01c0004034030440f83d121001515029040c1e213040020344a20401070040d5003000666807198a2500349902528980e1170380da0003480361500101d05000d0070241d060940798002c004003407000d03e9003408c00c04840001d151190781b08059142460b102014010b031441180319080c503996071300c3c005101c6240a102030304408a1b95014039198907003055240304989159800540c490804458040d000014121941e41e2000c4541030801d1590500e4000a0300400107509803261120342e52031b001802030502980b0b542d6030008807588010404165100c1d926079001342c2e107407809451324114924012865101d5401403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 901234136 1250 901232886 901232921
    0x108070504031a0403140c0a083f011a0d090c0b0d0c02010f05071b030207050310050406180213020c071d070e091009050915040c0f0f060e060307020705130b121c051606 74
    0x140454515185070350b014010100d4cc0059900c04155061440c0c000d4041a551a1307507150261750500070110700f22401004114222940d80241c0c6103103001921441c11030602560038101250000b00d02409114864100c66513040e480207960b0090b840c44101c6140e0580c158000c54101146645082c000e0b2200041c000388081490300303203494560122040d10480c01640f409504406005a480f92a10103c500c917501000d610f03010a0001c007800c200050380503420a0444495020810071aa038942d4462905031300e0f580c2c207038804e660a0098140d0221400d08806068000610400d40b1130360103a904030031401c08071600300c1e01c20040300701081c03410340f4107840e180f0b400e020400110700700d0368150020340b9401e140306007441d15004002e80241044030030184525800309c0000c0d001442006810010100100b16610b6590809042d00c010102d080f0032078001d11200d0315100c444e22001074440d81d66100c40380135480c002c0c0c0350700003150b140d0003150f0400752844880c1c001001040b80c0c0c0c00344811074641c40000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 901235386 1250 901234136 901234237
    0xc030803011706090d080606030a0618050a0b0f100f050906160b0a110d0b0f1f030c09120f02010c0804060f08071106060108070504031a0403140c0a08 66
    0x403403800c00000c04a44d21503001c1c003000b04400e0fa0160b08140c000b1000c1d21403684a880b20040701c4017619143e0082c01c840d1030308940d00440c081c01034000c00c1c043c2c1540c0d40c1c204007013031088041c0002d4200c01613800e5080401c005068900310b1041c030480c0703410a01441d01605010804000820691010b40c01c02d40c105e410104103014400381c80301b01f40e00040074020421461895661550b1a03015500540c0f071640da46110324241912000c40305403440c07100030b0980042d69005604216041d448038600b500280c9807040c5c101c07102d80208000001e0710003c090b003000008880e9503000e50031020380403c07810401143c2c0e03440d00061490018202034040d0380c403002004d901103100100881001401101004850f420302d459107174022940a4000400f03282060883d540c49200b07481c0d511a42d4002002a802001103d0b240720041c0a000d004920039900c080000913400f103418001c0c081d03100388513011380142d810f403000184580000e088ca180c10741c2255008010a03000e102000410100d0300030b107400560344 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 901236636 1250 901235386 901235429
    0xf1b1809110a02011b0801050405042301290d0803090c0d0606080c010905130b120a050c090609010e010603020a02010f050702060615031003060515040e070602070b04051c0c03080301 80
    0x141c00b420202c00c9080041745c10001000401c40c50043c82807070700540da2a8041000e111846941c01007601004004618620b80551100c2c0202000e5000d12200e02075145c01c035045030002c0c08404d10809006001c402204c90b141c6641e662540041c04641030348c8514404d00c183c0d500c8440001e9205030007810700003000c0c1d20348900e290611840071244d6041044401050046a03a1541e41c14a28801d83c5000140a00340c2404a2440c03a040c400d501003130310480580340c2c108800010110742c0c00d903090b501c1e1a2103440c1d00e001d1044d92042030041404001806005105540c800c0d4050030700e05001d8400440c0c1e044c54602d20744d041314806d60301d000060f00001c040000f00c1c01c0c2401c0e140440490200605c0c5185000240c0e4038a039460f60000501c0302e0344030404607408405007084101e440c1001407041050250100b0400c0d1b80d44000e201c1c200250080e80710015040c410b01c000d0754101d540c0508000d0032440440c3c107041980444513411200c6200d03a00002c40490484400345019102000342803802c00800103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 901237886 1250 901236636 901236641
    0x3110715090e2a030624090a0e060105121f06080109051503060115050408030a09150f0c02010818060f0a11041a070f05100f0f1b1809110a0201 63
    0x70050920f0b4500302d1180158001c0b9032882100d0050680f01068403074603a840054140ca0311010803403512a4168040d600c40e085203030040080d040100c17001d440440c1e65030601c1c5417900c0103c4040340490301c00e000d05001c4403100ca00c0154409083c0385400000094550068841da0081d009540020710303440062115407070034030a4540108036600c40102ca1000d10700001d83c0c4800500070ba0020300c034240c58001300203004200307840140105100745c948401e140300004005403640c0c0305500c1034900703450400d034005028045183d041c2401d41c0d210145001640c0040d5005000604002c240a0440340c0704042800c6c1401128011343c00310516041074145a60b8010558504650306005520104410841031008040a030101409032503825202e403054100038859070740a8901420030b025060b91118049456800781d03090291140040000203804042388084801a4155220015900e0300c00b01e40a405801c08910008000291101c3d00c0c0e29005944161801e600d14480250008181440e4145e02070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 901239136 1250 901237886 901237891
    0x5040b0f090309090106180305100509060f040c051c02060a1d06040821090303031e0f07122c10050f0903070305070507090618060603060b0703110715090e 68
    0x540c0250f080c007404000283e0440e4040c81760302c00f030004800084204c25030310003406004680000688407807034103140b0030102500c0101c039000f046010302c0c2c0000d50080c6080c00440d008035080120200d000c1d080405024035092681035a440701138480080d0001680d80340c0c01003600d80039a82d600000302c13401c40c04003000d6201c2c1842142c8240414401401032000000d1440d41d20f540d214500e8a540c41c4d0342510040782e103d041120b13901808000700b00300548401e075290748071280042c06003203001e60b545003007181e01c40030503200d2200044c0222808000401c0c182c00180c40f10001040340f00001082c0b1500c2110541c5941d6401407039000f204060548800030701c0f62651100410414000300d2038407042840d00c03032013045c0c2c000301440b03004110030090100c09c01034140500301c84101081031545900f40300c00c201c02020000020305041c54008600c8070320a00401040b00c00c108021410080c080e074041e246621000102c1c05148108003002a40e130000c0130b0503909004071a1030700da84c51414180c0d10f503110b1100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 901240386 1250 901239136 901239151
    0x60617060a0507120902060c0703080a0e01020d0f031d010e01060602010e07030c030206071b060809011a060d020d020708041203080108070b09060d0b03010603080405030c0a030804050d031205040b0f 87
    0x40c402085605134005295007248101030300d000400201920019250f4000d121401501d032240711008020400000024041f030001030312446c8854841038012079071010000480743c0004d41c1650414881402608115694400002d41c1d000c37103016084c0d01421200440d00c0c81e411a91030320010084240c081c450184026400c00c050b0604601f10344501492046900c80203018840c000740c420203122054a40a8514040441e02c0b90440d42c3e422000b01080c070140c60038952540f030203460040c4514461031520b0005c40240100d42480440300741c6500075045107109882c500e800b08020000580e00c1801030029104003d40040d00d080541001021918140c10050140e4081901030000d00041c005844403a10b04891256a4001c840400c1c8050b0002c690a20713019170030108040208095080a4025a80b041d4102c840c0314810071704000c0d902069200c0680b41c0e160030041070007142840183d880d03101b8000d061006130219107062400071164200e40c01d640c60458002417141c0c28a0396080183c20140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 901241636 1250 901240386 901240391
    0x509040f1505040b0a050f010c060e0c0112090c1a090909030d060e0112080307090e152403010902071a04080304021f321b120403051902030307060617060a 68
    0x103580c404603441e280e20340501440341f8048000b09803541c0c80307460b100c81d00701d07803090050103030160b115084d81d075501001e1768036030111350182e511a490900c0381c0708018005800842c0e04000c60714041060001d0010581c80c203910840421140440c4c0d00c4204640d405007800d40002c2d946c81002ca04250102c0b103054103c5041440c03404010071581d2002e114904a16403c0640340d41c1c7c075118440140e030701e001c1e1680a0003107a030000341002040c0e104000304040d85070094800b61650b0090180303da400b500340d03100320001080240014000d5800d01d40c003902103d407046040422000040341b9040c000300040764221030460f00001048110300700040c901c015080e18504a0318441c19408000c1c107100000ba15001000d042c003900b50280382200304104600a803d002030940d21070b446480d0403400549941030880b103203c1e15a0203c450341c0d00008483c11250800081c02580010284000b602080746c1003d0b6070600c0305202c00d01c0030401c43d104100081403100300841c250103140184c181851002012070300010b1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 901242886 1250 901241636 901241651
    0x5090639060103060506060702040e0f120901170a0e03161e08040509130210030b0a0f0b030c1c0501140306060406051f090308030a0b090f1b0a0509040f150504 70
    0x200004000b815a50b00c0400411142c1e200004034169002d032800203035001d810045403203980c15000c1030600d402d0b0580300075a40750f441d201741c00310390910071203580c940003903151340c601041c0b01020309805402a4050340c0c04a441c810841d04030f441d5030030100d11201441c425038906c1c8100b2404461142c900d500c001d000d483c440030152581d81c0c82e0700903442201d01074400c120000e16800c50810b25468126801000c4860051003600c00a00402132140c41901501207035601042d402c089144101c2110400c5503d245160303078031b00710101640c00074625a14620711281d1802888981c03400790b2400307000500b10701208000c0c1c2000301440c0ca0405084603004500d0303d00240126103d24560400386007000202e249506c60020341240c2d6411180e102401942020040c00107107510303508480c1540e0011903203640e682c0ca508c545095180c80a580340108010304981b01001c6120300742c09880100c0c42030904506000c6510081001e90302440846c0201981c1c2c0c000000c482c0100320340c58070161006480821000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 901244136 1250 901242886 901242997
    0x5090106020718230405010218041406040207031b291618050310020d05070801063f05011e030201090519120803040b1b0702040507050906 61
    0x5100400aa103511a04c1d40012403084000811061180c05a022442083d103441d04041d4000c1d00600c41c0d803a6845c02c031180004091406000f6492a00317515101c030310440d02c50a040000950115400f1404c1c84040b010002d480060164a054a240900c0201d9070351514068400b0790003e40014890b040340304c580501c01e40f010b140407003111300c00c01414241001c206203100401015042d50105c0c1c0e0611952034070b864441c0c500c2d0060040342e203070744c80c0c01d10040e2202041514851024080d003000101130702004c04040700644c5d001440203a0780114900110020800061420f02c41c0116200b03423070311040104030450b0002c560030303c6400d0300c000813404681140e000819882c140d01c101c0f442500c41c0f500f008802041044c1000007000c910804284080d42c500c0c0910140d081281e05903a001f001d20b000510040c426405000300d6180711301c0c4a481c044450f0700f0800140f20140c903980070403609020074640d54954030010074000e00d5403c48250346089621921041034030385003021619500c10076401001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 901245386 1250 901244136 901244159
    0x50a0f020a0f0e150f07060b0f01052b090f0c0906270e01021308160f0b31080f030903060103120302090402040308210613090303020c070f050901060207 67
    0x42c40306038a090914900b0040004a22101c01ea00c4101002000039101c034211142000610000b48510b2044c09104a000c007000044044541c0043c0031079001c20640095042014140c0c0120210a01c20904070807008008070032100b4428044609006203e410300a01c41e8002c0303030310003c0030641002d000c200c0c14140c1001c0488038000102c50540340c00c2001900c0a4001c0e0054400040e010b8000c42d155030091410646e41d0f2220703c1104480d0007541c103d1180caa40300c103008801c0c0d4105080840321249040d03000c40a80e8003941d01038004460144605c42ea60f102a0030f000c640404120804c5026800c1440c5039040c0424100c0c50758455004010450080e02c01045003411a80c1007032910a60840d0b90901b03901130712074070036816441071001502004000d5030001420046000300d69841d884c000e0700101c540061801c2d2607107540031441101d4100c20040a03001890b03650301c24075001d401c080b100447d040ca8100541c0051002d0b00d40150180541e00700001020300600b954401064854036040f0607514 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 901246636 1250 901245386 901245407
    0x6110a0c05010c1a0c0306102a081e090a09020c0c060a0207083915030a060306110705010e060411011d0d0c1a0a020c3001050a0f020a 59
    0x6100c610f12910060100b4070712203c3e0840146100524145082203150040fa40200c07001841802440404030350288102c03214041c60402820342d9841c1c01c1c001c0c1040741c6000c039602049501c8101004a511000c132030401d404800e203880820252605044170401a031500640c11080c80c444c030610807041c1e050000100b50050050650b00d0541d81c44450704224101030340d50708801404c6c81040c8813140414282900c0c4003400318211190899064120b06c040b03501403c5401407a40100c1c00c40c002550601d0700401150030240000c8006015a40c0b555514103460150030b036200118000308141d02400002e014a022400305d180140c903843c42d00b559044912030305602d01c00d04014803544000600c0449800ba180c544900030400e903158015403802b0001d0075080c0c052031922044c0d94803403404c055000030a40c1d0000c01c42d80c01910710100d909050214001e504540080a1009051031400d40b01100740701c1c6044203030160001c21540b8210042d641980e0f4480b5010b41007510402180001c0d40d8003113100314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 901247886 1250 901246636 901246639
    0x60a1a090d05070b0309030307030606260a0b031603020a0e010605070b0a021b06070905030304080d0302180d050a05210301050103020c011b0c020a1505030c0c071a0406110a0c05 78
    0x74041202c0c180103180030741e2a00003404458002051100d00c02c0000041d5100c9c04150b0f030305200312a100d000440700401142031204000c0c0808140200d000b4000e05520752040c0d204900148503003943c00000d14105400010f4260311484040c244194141010104043c0136021040c52080d490000014294456900090240d010280124401c400300c0e404443c0c0500104a4810b2070141c0440d607180c6074034040da90b840104001060000341303814044203030307800c9803000d1018000b500881d403001d9020b940f1941050a0b041101000017190342d80e0b410304a424540510000d11303003051a41344c02882c0c0101c0490000b5080110f58211810f20070080c21641034880a00e07000d038881c00d031074101c50701500300c0407400380203000c45003481004e5076030112030440c143e40201e03070240c001a564680440d10701c04104160002410800c00280401031000c001c1c8500c00380e810840c0c1809540d00303100d10415032040024030064100240410000740e0010f031070920884010003405030b844481d92101c1c6c00c8602c921555 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 901249136 1250 901247886 901247899
    0x20616030b04110d0b12030a0e0123130b040f06211a03070915140303070507090b040605010203090d060f020909040b090f03070b010614041d060a1a09 66
    0x400188207400c440000440580107001c403a101c003030688a80c0e0401a0344c00c240500e00740d400d9100c2c0c541006401220500440918501404084215a008070030384070ba50600082c29020360620300001d20340082a0380d62010151114501440f801101005900145141c407041c0000d00c0840c070740b01d515100319402d0341403030b21454964001c5075548901c82940c400e409481c5c009154014103200c8014603c1290072425620301a48a15088013190b52240e104002140983d50030300210008807a1720040c50002170840c0d041c860241d5600e450000150803101c42d45844405030f100300d041078001c40000c1d100900145060400d440040703040d003100f8160240c623442e00e030340001c45c07009007650440e004d550001d08242c6051500d030400c400f050303c094410b022248a5250072944241e40401a1403910781e001c46030049a2b40384c4a000c48404016694628440f0400c2000007840d03494540d0b520228a4402200550b0b403134244104100030005500c8420000305a12014009001880844002d0340c001c4820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 901250386 1250 901249136 901249171
    0x20f0705330a15150f0905150913020405060309010902030d0f0c151d060108070608010e0403050c12031e07020303010b0904050c070206130311040207030801050d1406011e0b04060206 80
    0xa011a200040c0d10005110080c014180d2803150320880a130400e0611b82c4034480c03e1a40d0b038090092526942d09aa501c0d04001d0008400d030349011a410408030307810040c0075081035218000070746a0750068910003080e079512110036045060603c04804400da0f1408d00100c40901d000307001d031000e01003600060103040d42d51718214008803e640680d100c1054000c0e141410b2403506002542c03145d00780150040e038840c8074000600d003032040407501c0c142c3d5510400b0241e0368446a4060b80c10750801c03a0541c01c940584200e00d038059440e20083c52151500788000702032142c03060b100003003864005e07105900310b400400060207a01940f104941e0022025a0000380a9540445001c3c2c1401606002075100d94000b0b8410b95038035041c400142507038003e8440c0b0342401941402c200480c40b91403002004030742403070010020b500d850b03041190594003c0c1401d407000c81d10781e1110b5051080903049008800011072000c0102244940c2d100090203145034440d1400341444800780d84c41d80010200001010711165 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 901251636 1250 901250386 901250411
    0x2010c06060b2a1c0518180f15101d3304030309060815040e0f120711190f0f090c0302090f0f04020f0705330a 49
    0x210030010440010042c1c3c9460001c3c2e40140021034980d00002034200b1004108150000850b1141150842c016510342d00071042405482e603130060750b00c4500000070360b101002c0c982c903082c0c14140ba0f151100001c0d00e09141075007080c40041005070801308001c5121001c00119200e10780603100c040b065080c8088180346480b10302d440016004011600856104040100090b0707035181c42005060100c1e03030340b0004403400d000c203610303000781d20010f4006007441c00c040084500681c5800d801c24008002301100f5402140410f041d12540101d418840c1d02c00502c0b0400b5071414808288007000e86450a890480721381c0b1005014415841b005121328607103900001080394a60100d1b0050001c3d0050411140ea0354040000f4441c1034400c607a021403c0000420b40c6138864821074015032002050030f04511020800d106048032280b40b096007080d400c210000803d01c408029040180c0311340010701840c0110035118011203192080c0d007080c1006440700111205d601c04050368003414031036000402c2e010608 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 901252886 1250 901251636 901251641
    0x150c170a0612050a02030106121502162429060d020c0f010509100606080a110904290301020304020a03110a0515071416030807080c150a0c0206070c02010c06 69
    0x240700d0007032a40c140b0341034001c0000101d001c0f884903000300c0c000c110b4590b9504051106900003007000b480e03080340d11050b041146480c0d0261800301010300502c4a210038540e6a507988012101c3e40c400428845581c000b60107915001c1c0f8404450010504281100107042d043c12401111642078440c1101086100a004031941a505203850380000c85410707140b078031000d074020203055030241c0c1e09008981010910900c540a91001c0728056602d030000340d610003a106006211120322001900c40400c0384103070381d90f00c174062001e801b000070701481c10310300c100e52407500d11840c0307000028000d900610400c80960790b106008012a500300d0b41c00c04681005000181e80c42c80140c1200358841c00b07291070741007032041c0304028000341807041019142c201c07644611156141c099400c88200d041e0300c1d40041c000551840701a008c418800c140b0181000d08030b80d48642800502030035030b224022400100680110b50340a07100128920380050001400c0c072903001040c5601550019042c402c100c043c0204002e4242e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 901254136 1250 901252886 901252889
    0x41203080406090803010b0c190b04020405070207030b07020d2304051302040503060a05090c0906031b01020709050f06031014010b0c0a02090103050d02012415050f0412150c170a06 79
    0x204c200c507134030341c0c440400c107600e50450242d48449100710035400141c60700d2490881107103030308000e2541c1c04e6503456080002800c802025102180a0b002c0008002006041d649000e0300c0e0301e402511b00b814487c0b00041c6110b01140c4500c680f01c141d80e0740b00000c110840200d50603118159401409580d0894154020b84503a5010030382601c2410200407071884594042e078011841c0005641c1300c0241c20080200b116010b0b640694507401501d2005400c1101c03c0310a020b159060050390146569a00c80b142155000c4449070381c403101b44810030020b441d0501c4440040e46460108104441815100c0c2400d12014000c54440e8800001c81c40c02c0c3c441c0c01c10140c03a260381d0041c4109031640c0c40e031401d030740c440c0c49961900c0099800c24040582c0710301a00d4a810300811a4099042c0f0286000d58007800340d065490400d0503c90200000005140a54000d202810319000c1003000040140350601010602e065242c04d41464044854841648003107c00003c0325004824201e5440b002145001400107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 901255386 1250 901254136 901254143
    0xa08070c1a0a0501061d06031806150901060c03050a0507020619031d0c01020c04020d02130f0608100501230c01090b0103060617120a09030212060405060c04120308040609 75
    0x40041900000e00950001403281c00042c10512199030384031025544000c000301c00d0851028001200601c50504d1005181e101d01e242040030107003071040c010a030500d035054820050302c94402500388130a0404034a00c5005007220b00d031210790307100c0311740f40104580281421282040340000e4080150b6603044140c0702c0d24590550110304a0f000e400018000344060b044142c02404481d4407a201c2c44c4c40030860b5551000187c0140a140f40c8140c1004001d600041d840f0728103d900f4010100200ca20710209400382c80d150340c41000050a26102400380d20000303084419180d4920010300083e680b00c0c081521f1008000740d03902c00464900342100c014001c07003d40781c40e41c0d803800321040180510544294100e0380034032020000d45454084210b948000e80c140d0400355408540050a101a039030020030807801c2d42e281840205441e40e0000d601d1070b00c0110f00c0c00e4103500410a02c000d0000a1007240d03049611101220314092410b00d0348803010b40c04040140604c1601c400003001c1c4101c540004580603031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 901256636 1250 901255386 901255403
    0x71a070c051b010c080a02030d0c09081002030415020f0a08060307150f1218140105071b0503040b0d050703050a0e07170304050405100315050f010509070e10030b01230a08070c 77
    0x3980c5100955940049d450700101c2801d140c40044410b0013504800c054a004c88080d10014210f507204902940c0060301c2142c60086090300d00415007040d1001c1c150707004040c86041e5407060103840060003014054005446504034020400100c0405600c0182807809402d0075a01c866441d1025248007409112f0f01d0f06141c02d003074140582e40502e1406c8000140319861490440420517056403c803902101c010012500d4090b50300314280b105118514850b228004491a00351101d100341c90750b800084110307000303545540a009030180c140c01000c1d40155559000c010403080001c0070f44c4d86004611502c09024018030941e411040148202c4000d000060418081820030070628503842d18140310580d44c1605030000c040015082d03024541c090310908900c1c4500341d09100404c025110b004c0d00c550280301409d44400500c0d16041d10321921241d081e1000034130640301304005004803c03030303000302d040c400c041d60814101c003260402a00c0040e1000e1400031900e507240303902510340c0c80b400310010b0103601 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 901257886 1250 901256636 901256647
    0x20a02011e050c0702011b0c0e19020408072d0816090e07060503060310090f2f012006070c3309171c0f0204230a050402071a070c051b010c08 62
    0x34042030103409000844c00b08c28203010ac41100c8802c80c0214000c115140e00686010415040c8200704011600041c4001d154408408038482c800805158040b000540120004034020560b030440c1000800c0700303280c2440402c800b44e54403521400f05000e07910170301c1808004120f01c0d0300c08105004940a401c441000310468a040000366142c0810301242c580c050710b540440d115054801c0c40018000b8142e0044d24801400010b49100b0110f07050100d03401a100740c4424481c804201c2c0900500c01512103468250440c10154550034078111000b00b688140d2034042d5056090340071110403140c0c0c2c2240001c600e0303024681408481010211202c00050216001e0560000c00c03401c00a10b41134031204020701107404460700c05a0046115032141d0b02c0500220486843c80400c04040300100109000104e87d180c078005230880c0c10000c000c3d10600b101015100080311901c00c243c2c0c00c6280d07400c112114101c51741d035031941c0e094030807216452801d5481d0394484070b0340682d100347c41d040e40c0195500d8495 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 901258992 1106 901257886 901257899
    0xa0216030507061407030507090503010c050702010e0a0f060519020d050405040c02100203100e0f10030f140a14061308180310020a02011e050c0702011b0c 68
    0x80d9100d8070307990207042481381c446200f031166071800605410a50b500820344004e0313403c050b00130f0b07241405503d07005070401c095032115942481c1140c2c0402d1000e0106248000a034010445003a0015020685a8014018000d01c50084450120102c24050100da9070040300480e031001c5a420407050145080c00d4208100010150045804011000d45100101d0788229804044404c03200c8041c0600c802100c0b200ea080643c42c040d41d02c0c2030401c0780520603d0000c170301c002807400c0c056242c0c40040107405468810011110000c0c0c820780101820aa44c1400da40ca1911015004050018091940403e036500880d0303080030400b41020b142243c0500d4080a040a03140d01d482102d0713400c042c01040e8002050000c00680c0003240303c4c801040101c85100201102504450a107005c01c245102114140c4011a409182011425000e20302c0200b05082c5c400028000340715043d00414131 = true := by decide +kernel

theorem cover : BRFrame.Cov 901079136 901258992 := by
  have h0 := BRFrame.cov_init 901079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 901079136 ≤ n) (h2 : n < 901258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
