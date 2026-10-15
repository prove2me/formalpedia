-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3905
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:00:51.941415+00:00
-- url     : https://prove2.me/submissions/3f9b94d5-198c-4513-baee-b0b570ebce80

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 702158273 ≤ n < 702338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 702159523 1250 702158273 702158321
    0x70303080c0a020c10030623210703150905240106051b2a03210708040b030703050a061d0402090a14040506070f08130305090f040519 59
    0x48000c880c1c1c058110304031169602c1d181c0300100c0c144285555001c1c0d02512580a5100c080c1e4198000c80580c0c03007049131000f400d840c100790002103601402d8055480342ca01c502d903001001c40000001d04030000c1d48221484180c03a50307101c00e4011440c541420083d60350f0740d000410b003d81040103008102c0c0703000130109400d414105d20442201c05015001c140000000d4000c42e440744054074000191385e0400340c0b6103151012000280d0024840d00110b04040c0051080c0301078a0081b44a540350300c0c1c1d00121000e403d05c51b1403007080b0768101c0241500c1c500c0080c040001c860341d58034001c6120b0007095400003402d15004069000303c921a030030030b562001d1042c00009203804260034441c0c21903011190346c4142c0c4d440007000b2028001200c00c1e9604051070000388010801d000903124003494143c0c5819806010107030046400c40c80031a5140040a04010b0110100b40113030020080024080e008251020341c0c4800304e0280c940075101e0502c6209111510b00c0086280e00c549031390444180b100c0b15481403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 702160773 1250 702159523 702159527
    0x121b081c0c051612090e1e07030c090e060114030709080d030b0d02040504020f032d0c09010303180e07210b010c060e0a050109150b0a060f0302030702121b010b03070303 74
    0xa11403500400a500d088020604e240c000c081c8540100103078050300c0b00310f10308107984110076900516002c1c2d5003001200481c50580c001c0c05042803660f1607656102c80c00d07181c40000c90b1109000340c2501c0c10b000071074840cc072031058250000e5118406a44a0050045c40e00c808185810702a401150406107003a86018681d82c40c3d8040e00e0800d901242c010881e901d40740000748480740c88003c1c0f10b50500c900f21803101400c1c038891805001c4a00381b107100004d0180000100c0c1c860700710901040e07010361000c005100107401162550031001156440310700d034946411030031310700c924251b54a602081680304860500c000d007150400890120540501600107500000780000d40350100c000c05041e1550190f80c80d4040402031800c2c0341e1307080f43c02031140d00c481c4d0a101401c0b0040d07a0511510b541040ba0703c0b0194289400c10500f01d44941d0744100b000801ca8030708038000d401c09880c1c601180207400b08040704c040c81401034210300580814007160625441c102ca42120b02c0c0c0416507000750030409040003ca6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 702162023 1250 702160773 702160807
    0x50711071410120608070807051504030c1a0c0304090617010603120c0204181101090806070215070e0d05030c0d08060a090e0a050607050409050f04121b081c0c05 71
    0x14440e091403c20603003219800ba003d4002c0d5002154648102c3c100010303100b40c0000c00008440c0140c41003807220356680d20004052045000107420450140d0080140a100c40b01c1100e06922500096080c00110b1801c40c0c195480b6030700841c03190f92607400500c5134000e071003000040d04204000802001c0d1544e6101c00c0c21401301220310050242d201d45200641d20b65800c003003c103814060540c2d03c100b49a1502900e1552901c3e082400241c49050100d40c04800054003402030515800501e008e0240b42420111f03548003c01200800c2480300840d03c068681d6511480d006200c5c00103182c450b080c0e550550310340025003440104000d07008041c0102031b240c11842e60143e0380b4568001c201d00d00e006c0001c1e480c10303204410040c0184160b03c00c101c5075580c024003038810b0303480307990017401f032504c3d40c052100b030002040e076015022070060b0480c103100f540500c0d1480f10700480720303c014420604070307152072005400100000482c80150b110b00c1a0228480c413500214010b54103090b418074490103070b425040c2c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 702163273 1250 702162023 702162049
    0x102070c060f170103140f0a0519140d0201051803090d080702120d0e0a120b070c020f03010c032703020304030b100b0c0d020615010e06090d060507110714 68
    0x1000640302c08001252192882001035021030550b80310b1940e50f890800f1012004030b503100c45d40d011b445401110980d000c01c14030121034000b001031040102e02d03030041810450701c01e4216020765002c0c050340f840380c4080c00303004451402c5400010b80343c900070a541e070448410b640c1c0b9541540040220081d565141500e29003072903040001c1582f030f40d2803440070586100701900c058880d88985003004400d5a8420710400402c0015204401e225503154015504405d049500a0011540b5000511043c0c0310b0450100060300091400d01003d403c0400b0a00312000004600000398890794074130700c04001c80180c1c0340e0801c200c0231002d00320703200ea8400a45a0283d4000101041420000305a418140501d6100a4402440c0442c1e403030b401010001da0742c00c0600542c0c405400340c80000782014452a00d420956841031b114403030640c00030020408180e200d0519182c0c8802100344c8040428041c2c8941403044000d41c40d030502d00100d502549291a585910a103003004141d1030661442d01d4100405040d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 702164523 1250 702163273 702163277
    0x10080a0c09051e1302030412120207080436090605060f0a0521060c040302030f010e0316050f190221150403110607022a0609060f16080a0f020102070c06 67
    0x440448000207010780001c500441c07004c5002000740b1040c85400082c0c292035013230980701c10050054042c940c41c02e0740190200902040c00902c002c0082c604103001c01010440346801007149001c001c41c000c18100700d00c00a4400c0650740d485003504002c01c40c8510340e002030b81100c1c4010091800000900c921085008813800b4018803400d0103a00a5040401e408064001c416608145130603101494150003d00c81680300b0b224030000d03540d00030418460f2038010901100514a400c1c100b042080e401464103100f1181c038424a10980c260000502c08409400000440d03a00088582e0040103130400d00d00000c100490719410b10381c0030220001401c084039140d41d605005190b03696080070340d5244000309002c06607000d068100314a540c1c1c0800d4103c0c1d1000c07203480c000390b200c60140384c0113198030450001581001040002113943e2a0820282480c1c03050444014a420500c40e03c07480440d0321500f08548908000ca0b004003a87d070007010410304111184021801e0042649030041c00030340c5031180c101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 702165773 1250 702164523 702164569
    0x60705030301031b1a250c1a0d020309010515011103091c150b0901080c06040e0a060f140112050402010804170405060f03090f0f0d110c10080a0c0905 66
    0x700740c1e400343c904030010700c3d6014100010500e000c59050050f40102c2e04200100718410440d44107490300d4003040040e1f40c211820f4080e260034960124400b00b41141c45011100c0240003801958515000440c0b003000d02a0001c076460600c0c0002000b40c038a80804503050000a5800180300c0000000b6200c070f0040844030001c440c0d0b2580c0c0c00710206002d10402620210b081103412940300301c103411041c3c01c44001d0303401c41c0d4580c2c0d80f40c07000c98403120446801544030b0b004000420003800601643c83e0404400300340060074a0740c44c004c1c3c2c10000056170016003140048103580d143d96806c0300c246841543c0e803d00038031040c0380640c0000d01500005100170f01142d52000c407074240300003440549015003000b83c0a04c1d0b0f01d61a24640071900e80003122403004911881e5480c0c0300d44c10000c1010304081e5640e00041c0b1658010300410349060300219400714451064200d04003482e40d60708944101c0114903116194182890328030b031002e607943c000750281403102c074140410003600d50492014500e4449200c4c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 702167023 1250 702165773 702165803
    0x7120207080f070b06090c040612020906090a0612111e1c0f061701091e030c0c0b04180603030f0c020105160b0f0f04030906140706090305041406070503030103 70
    0x440c1c1c1c0e0003040007207802d58402095002c100302c020740c0000e0144204032409405981d86000d600d003540304030302a010005003080011642680d094018082000c40140f9a03410710303124a020500d142030701d038000000510441041804a02140310703a964000d08040720a03c1d140220354181c41e00080308126290202d40020200280903269800520111000505000c08110010301902a10540c0202107006000143d140d002407014451261140d600240114144600403c148154041c5030300a60501c00070b103d546000402c68040130f006410b40800d1142c5507401d0081c0c541481c210441071400c801c1c50310400340007080d0000501051200d40785405104070009200484242c000c50207800c0b0382c01c02010b0030504005540101510034424410314100f41d84e502c0014610100781943d018002c40c1c480d80084c01420b11400721140c4136080c00c29650719104c02640d401c0200c500034113094000440118050040c42101a07601c0c0340400201c0b95076081003500e845041d00d034803042c80010800f540c81220a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 702168273 1250 702167023 702167033
    0x1506030403031b021b03060121020d0b0103080a0f0e090a15170f19030c0b0402060c0a0b010302090603030c070e06010207080703060b100813060b1c1b080607120207 72
    0xf140e030500c5044040c1d00c4440c04800a580e075409002841c0c010079900c40222101d00b400a902030486100b00200301040d1516500c1d80da504500c040c2c26a0001b424403c2e20b00815941c01c4950f00851084600c0340c1c0c3c81d40c4605000b400054000c01060810035040d00d00046039841c81d101c240c0180d010322740001e40490f03072840703018104181d03070186680001c200301c0e54103c0c1300d01180004107041024180e801403002e0307005044c41581041001404201050f094802281c0c500808513030044c80600b0491034030141e085594a04200749100f16007542d01c4600601c1181072220b01a1303000903081d0011800c2c400141591a10b9206c0c40c000c04149482c11000100a0b81c420020400108600e030283c2c2d443c0c58407410b180015140c0070700e040e801a80508001d00e18070b44034101e032501c925448a101c0810000940d181d00151518041c80b6520080002d207e94011b001003090b007000c1c500c038000500f40c0f00c00c0012420b0411526038000c004582000c0b040144250f0425100619000f940c035005a0303c1d1414901b03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 702169523 1250 702168273 702168281
    0xf0402040e01020d0c02060f01060e0102060106030c1407320a1514071e08041106090a0504020f130b030903160c0902030c18040c1e17040f1a150603040303 68
    0xf00610032820328040e400785607004595180909102032a0203103981e01cac0d81d003d60386c6140710352030705005030700020040001e0f80c400d9110050503a0f840c170744030030510542400001c0c02d0308204400ea48524209e00b4075405c0b507000c2d201495403071508551a5031a043e41e481d01c1d0340c4400381c0540c00b41c00da42211180e2102c1c0c2c2d507950b00c541400040107190318598108084001c19400200a0829000e204202010310741c5001d80e903100d200310343c8250001c40307412051040c80001e8002004294210303007507040201d140e03038036400940b2200c02801c108980303811050142a540d6032483d40828215503041042c040b0440e80401119904c41d000310007820b0079502441d10074036104c0954005400e081c0b0101c00d100035170301094010560403080240c1c006100801c8410402121071540124000c910210341440400101d10700b154142483c03800e04038800508a134204141d02d1f81101c04803001c1128a10312020001c28030b81540b06006220750002c15882c0c4a801c440e00101042101d41c407902d00800050101842900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 702170773 1250 702169523 702169537
    0xb0901062006070f02070806040b070c030e0d060f0f0908090906130f0606090b2b0b030f010506090c18130f0207060902120d0509060c1c0c02010806090f0402040e0102 73
    0x7040316003502d000340e0000c01302c0c04008619001400f59600000314440c3c00201c0d9805a40c100c074411400b84c85d075810654440303480100460912004008a880d80e0392156110307030b41103000342d0340490f2040019400c01304450030b2110341c4070300c04d142140c0350011810310815181a40c02c251030340380307194444c0030000b81a140e8030a000d2001505000c1c0307107030340c0001c2c0360802d208803405515018a420740314451408a401104c91120000e0103c00c40c001041130204015400f007880003000142c030265100120381080542a60022140c0d141d03014424607080c0046001d9200380c001144500b01241e140c441c1c01c2c0100141e0301c0e684105034510b51854603840c0c540c0000f200601e0660115075410107450b0207400303852201421303445800340c01b01d61800004080340301e040f2070403a41d44262404d201401001074541051406d420184100741e039100010307a8401c5001c0c0e070907030141c85801801044d4400100000801004a4013584140c002d00813006001e80f001600150b0407200800d108400c400c3c05402400703242 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 702172023 1250 702170773 702170837
    0x3080c0c120a0c050a060f0c030e1c110d0903050d0503061804020102031201080606090601050f2718100605190305040314031501030b040203060a031b0e07051c0b090106 74
    0x5d807410b000c00189521102d011010072106024040248500b5011154104144030b81c540098590320307070484508481d4407084181e800c00444c1c160720001c0c59480e121902c1000c40c04a183c210b02481071060400032201103060924001c0e00d18a0100c0100300e4010582c058800380030704075400b00342168000d00035030703440280b02c0015101030341e075440d00950303240c0b81642d1b5203000300c6074100803070025403103001240c8c0b442c1070f041402c0e0300c0d00680401c2442c102015203600e404065034145110101c6e80c1c0c0130070601c114941410721950a00706014110b600c81c00c1d56100000384a01000b03504500d200c008038080c0100c03542c0c18009071903551805c080d10b40d036451951004480c100001005203040035508600d07003c01c0b003a0703810000d01d0340c01001d0001728842522041d500c075490703100420009103100780031803031220b05c01c10341c2003003a9a403039010101d488252007140c08142c01140b440024420705003c0d05080c40050014851700071080301042200030103014039010403900406501e0b9690220701a400030302c14031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 702173273 1250 702172023 702172033
    0x6050307110d092108040b070218090322080d050f070632090601050d020102030f0a0314340323010512030403050705010804061407020a03080c0c120a0c05 68
    0x728030300910070001070144620840288842d00d54046252180c41c1c00142c0c0803400d545411f0910001c45102d400840c002c0344c0c85120844180054540c030000305008420b100021622541444100e180e5540ca00300d200d24101d20401003006801d00c00140100c0b0307210182000e95a0304901c0030300c140148107070003002e000710b82403200081da089143e0000c21510550680120010f48a080c041c00e498541a80c4004076580305800620041c9007030140110101e105004883c54800e40e0351080189400c00e03010300020039902c4c2c00361000f038800b0750310702a840702c490200c0c1ea40551239524803001e902c144c5410310702281801e01c01814414000d6118950003588103004100c2c0c100701603c0c184030f00d0400d018030360240b44c81c801f0100e800003001041e44c09481c2d020f006803140f14100780044450000041094440703d880d08200d40e400040c605a1a0203030b89103a000c1d01e4400c81ca401e026040c03c1024000ca19820000c0001c0d4201180c042114568100307500101503460f9010341048450780c0c1c83c5540a0098003070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 702174523 1250 702173273 702173293
    0x40303022809030b1008030d0c020c0a0e04020307050f130506130f0e070b09060d0b061605031207080106140c0f060709030c120b0112170a020a02040506190605030711 73
    0x484044000c6a2180f0010142640c686059984030178540c802c002c1c081d48248000f104071401c517000f054081040d0301c111143e03402e82c1c00c00100c800c0c1490307100021220290741440705508040c80b080c0301408040c2d5042010604000c0400d201c0390041c0d502c0029a50b65070041076196482c03201c403080701c1c800c00d8014006030080070703200300041120a5034544184164900007a00383c1001c0152a00400014649828002c8a1000c4800340814a0041750311100801804059840ea000c01090039030043c3c0085071103845c5003000702c0310404c001d070440081c462400e00400000340d0101800104c49961545a901ca901c04030800707150072a100580b01c101d02a4108009041c0d43c400203580403240510780000e010303503940b61610060414010302600c01a00c07030740180102917070002da0508051142011000000010b01c0c640000c1c0c1040d402c2c500144c20400c00c02c0194549801010b401c40002c54500440d40481070310120f501c0c85503c540030a204021001400841c090079420b880800c401080d02c480b220307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 702175773 1250 702174523 702174527
    0x3050a03061505040e092a09010f08283306081903050f07030806090a020a0e0f0d02030a0c062007060309020105070b0907061d01020a0213180804090c080405060403030228 75
    0x3d6051f126000c2c4000b14000241c10f10042103120880d01543c3c0030b010000320041d6210000d035803509078045200850048480040d000e500400000184ca2110380040030000c4a440c4107420308501902e1190b080010070304c105040441c505100d2002c42004034604104c0d842c0c281c0d058080d4840c0c2005884000c2003440c00e01d50821000da1161104a541412517641e021000080f80944102c0b0000202c1140c5c804000303003001d0100200f07041d4010700306044108160700003880c0103043e150031035188c090074074100b01164003c0204035240981070481c0107038488080c03000355515518402c0c202055203c08020b030031359000c2c3c0c00f00d0780010741292220500345882d40c2d18554481c914891940000d0482c0d00507980c0491010f1060001d0340f0503809400782e6081c503020403050710315403103c0d1004980c1e41e68818425001d018002c84096210750b1a0a032102d150184840442e0302c40720032178051144000800001130000f2851070352056041c1801038885d20105490014841d101c514418000b28001c0c0c4ac03081c2c070f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 702177023 1250 702175773 702175843
    0x24040c122001032a1e080403030504030e0d06060e160203031b0933090d1205040b1602130c0203071509060513210c03031e0903050a03061505040e09 65
    0x1100540381d644070208010340300082e2140c034490310170010708418046400684245c114581240c040e1030008004030300c04002540d02c503c1e0b20001c0307171403559840d0100a146051403050b40e02829001036285c0c003510902000c2d45038400180001d26140780381e400114074501c458143c690390803002d0090002d0101c0080746005000c1d481c031500750441806d1144900c103c0001c41292402da00140040592185561b5076052500c043c0446000b0700c1030600c0046410400764001d4205042c10909c9031103031850600620841d03030484084228002e04294400034565000011903605503404170850541c9035030f80301c49200403e0036030002070034242000c2c240220f1308200c080d0308680324003902e07a51000d02c05840d240ca07240b05102818070040f0706a22020408a4002ea2092405098200da4069a0f044a80c601000c483c10200e0440100e140460443d020355458450100035000881c4c158000c54103e039070142c058095032150000c1c2d6004040041c10112041c480741001600640c0703200c07060b030a00c8035600454 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 702178273 1250 702177023 702177101
    0x70615031b050a091805010e150c0a05040b0304060902030316030e1806130b0405130311030f04030f110a0f14030307150c0224040c12200103 62
    0x200000580c54500c003071007006803046803001090421443d2400241c070010381004a6401c03595500d0b0452500811020f0003404115123807140540243c0608000d0242554809480c603415501c0078003204007801e0b040030455003035070210040b60340c807580c0f0351600001600520070000e40602011a5612032100b9403502000c0c120310035101d035060400521305008048480b0500d840781484c92502181050070190001003a582409030301080c050f50107000b0500350754040e502c8a190b040c40c9a03004e418150f120412aa4108525001e146401c030781380c000710403d00403804003620030140d00e614081040b22004900bc03000e0b4001e0305e0b40ea5000e07036a0340d461b2602000c0c1d10441003a030704c8034481400c4510700482261040d40e0300000c4000d210b02c4038061140100604044541507101c3c000f0b036a419504481e21405905291071017055041c0b615160010324070f055640002110f5440380c03071810020350720304003240da00140c81036170003a000c0310000101c02504000e240c0c08851b40302e0741c1201289802c9484440301c1d07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 702179523 1250 702178273 702178283
    0xc0d050a11150103081303050f0c0f10020606060f1c0504060605030f060a0509070320041a01120903020c1504050a080a02090c090d120c0303110f0d1107061503 70
    0x2a100c0004042c0c0c452600c0401210144404401400003441c03074400f030b2058680308480030381003d440c1d580c0d0340d2402d0650110701d02c1561105159030458682902d26488400c02a0b6010413400013210002c7d68804028224501c141c0000c6aa0a00c4060f54010b0b900c001c450400c042400b034490b039202100400c0265002d0780c034036041400200300da04000588152404201000f015156180a4040700514010300601ca80b4042c021002002c03c101c10180242c076154050b80800602d081c40400c000c0b40c0c150500c031a8240c2090140455580c1c005490300e01d4407000f40d0000c2104166444c00701d0a20006015403644a040700c8050701484144601030070903540b042ea5444034480c1c45858459450043c5a0002e602900860000b0200c8122002401030603c02900305d20411102c0d5440c3d40540108440d100001044c2c540580141903141c02015016046440c0701e5141052106094115120f6062902000303a03c0c0c041c2e0242d17011400b03048480b810f0300698204040d66220f9104404480c6900c829a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 702180773 1250 702179523 702179537
    0x70e06072405071409060c161806060e040b010e0a080708010e01020f071e0204061d07090e1f08060906040309080601140103051914160309051506060c0d050a 69
    0x44071286200b490701034420740c0c03900c0300d80d2525244110890351012030700c01e81000c0284030401c80c044081051004115000011126003410000c0160b103074020070301d4203019103040030380c2080b481d5009107000003a9141a60701003031050b2064010784464a11044a507000505001c0c00a0180c0c0c001c14084203980c1504002e11001e5600c118207403d0703015800c0e075488204000c015050000d4500401d40c044420292824082c1d2480c54001504036801580070726109001510a680b0165014840c954000058242101401e00b09407881e085550000c0084e01c8464540101d00e0a0a4402c0e40450040c100903003194510b18100644039212482178030103c0c0418148070000c103a81e00045160740c10b94194091004241a248004402511010b0a01000707560159140070291849018207000c00141c004903a809007040c80b100b9016000f8802400c080500c1e08640e04000f480104002800c240c1840d6107100a0b240e02001440e01d1041d0910400c0c02e214007914901c6a0390014090108031842c1d45584c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 702182023 1250 702180773 702180833
    0x110714031908061e0111370b0106050c0c0604030503070201030606141207030e0f070515180d050708160f120f0b150301021b010c09030f030305070e0607 67
    0x40e41664058600030350144000c00d400d00300008012241c888113505251400d405148101600d0a2002d1010f00c060000310780303100f00000c81034801d0f5112854008002c0720301c0c520000c2c0c584031900396040c0078000070040002255020484100485174421071700401080e560781c2c5d0307841c001d50749900c4040128080b0b07003413000018049014260620761640090207030b52038100c111280fa103d981004000b0800c0c550399030b00c80c580c0c51608220011681c0022002800d440f8280010401000a5441b40c0c0b409940c040104926031059480006841d12007074a0074429030805180c05401d102c0c05d508607540358403c91003001c41003500c03650a0401c0318261201c0c10f2320340e0f4680141d078280a02c0002e0203000001d0f0000000b00048070940c00c0d5a00100703440c40501201c0999000a00f03917030001c517002000c503206a404d0406403101b03100301003200c149800e00c546c1c500d1441c0e840b48a0096840e40160034141d80d4800500d004d40540040c06c1041c2000340b0884d43c0f00c00c2884c001e111644101d5101003240d085494103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 702183273 1250 702182023 702182027
    0x132d0b0f011202070201020109120f1103090303071b150518061608090a1806091a2b08030c07050d0806130c0203090307091d01020406121107140319 65
    0x81200324040e03644440c1d4060400c2e075100a0343c00000c04078110f40d03940c880b40010460040c18864200c0040c1c0d04e004a00000100c010700001c5202c05000b480c2d0404c0090301c8260b9000400c0710607007540b280c550303240c00096561800502560307501ca5106a42036040c80808940d001c0000d010084007000b200b070b10400c1c00c00070310100d0f000d0442013400802001e980c0b0340214a0020240c115000300406a8503020748500a040c040307101020020000e98843750306100c2d4000070301503010483c40c200c0c1c1200900d0080d80015071025051007408070702c01f601c2d03031118880e07006d104d100703250b001d0304646207036601e091803800340b2480d0388943c400f610b035806034003d0950114883c0c00d40a00400c0010081c101d070003000340f2644000c05d002e59500301035100402005c080ca840912100300109024080002c0d40712244891089031b004041c048044c503441004180000f07a040100340002c80c04c989400121040840d02440513803240c8200035080441ca06011711050300c000008010700541d140706901c405c2444802 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 702184523 1250 702183273 702183289
    0x140d03172a04060f05090d1a06130902280f2306070309090203090304030203010906020904150b04140a05040f0b010210060b030412140a0e030d1d132d0b 67
    0x43c1c1c4000820051314030004500c1003000e03000b0080002d002103000c00c0165199101050010800848c41e8030030000c008003403818803025040b80300b000b10f00380724607501a030001d141c41d0a03500700789406203d222003001ca9608204080d401814900c040158007a031030340d1880031000d0700d0050a822448000002c0c040d642041070695100f6a40351b2581c00e0100c0c00e208650300a500018114459407005010010242c0e0f424005e181c000b60081b800140e451a1101c14032054a8000203250009445030340c0800000f04101c045034125900c4820000c0d012074180c001031910b080c40c1c2e00c642c0e80075042030f1600864140781e5100c0141c0e140260200d49100740d51a0314042680d00d948200071040c0c009000040104c2d00900d01d4004269051601300e001e582c10300c0c031103207040c0c11401802c0001003e5011580c1c1d5800c0403c41d5441c000039034203062801d4180c0710041c6070302c8094803007124000d52540c0c0302100e8029076500140341203464005071888452542c0c01400d143c1c50446402d190060410011043c60304141305 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 702185773 1250 702184523 702184529
    0xa14010206040f0203210d0507171302011b080d0c09260a02061b0106050103021c0b030f0303090f06180a03230304060b120601140d03172a04 62
    0x15060995407500c0d01002400f503a141a03030180607465290381c2c070850203002d4000e200c040500e626280d0b05841ca002c8210b800040040c02803210041c1d050304101008000c0c41e07423002d0101c0110f90801424030040f00c62030b100000310150760f43da4560003010841030700c001d44407500000e00308001c0030111204c2158110f40d1445103045442e00c14080645a441d42d10500d0030400300c1c04e044464403405e550101d86035502c142a1880c81c0400d600044070044800e000c0c40c0020082448d0640c14000d40c0b0795500313075801c180600030004075910f0003002000d031014880e0800414182c0b0669860b4688600720300d40b110903e00f2ba4418078090400096100e16078428480309624104000b002825020f40c0c05507140c6510321103900719040c0c03800e4040c4c10b00201c031008503c00c3d032054002082860409061203000b207500c40104015400401c0140300405481903502040c8a00300e58043e40442c0e5404e064510f202c044150024081d0500100070400061314152440d22090301d9542009442443d420700c00d074082e0340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 702187023 1250 702185773 702185777
    0x90506031f08070303090812030403050301151e03051006080912131215060b03191a0a0305010507020c0102030f0901080c0d05190e01060303080c0322050604020a1401 73
    0x200200e480a5107100c100310502501d101e4140c00301e5103954060b440d00c6800c1d0b00c120001902070340c0c1880344030020300001d00d46c041079164582c10360800c0d6401034a54041405400405051107488200340d510400300005481403286000e2104080701c1e90050203005c0c00c844101d40030048050001e02180306009a52260808001400c2a4118451803801d40c0d4062447d01001d01c00006010a40c2030700500030725807646c410341c280760b44d1303001400d42e240078bc0310150b008010030754084c0300300302c001004440080d0041a03034407800122075011203a000c090000010503250800c0d091540403003000015072005020305120780071a84034410312801280c3d2442070b00c080d10140c1c9130a200e0600700d0750003140e403039801a034049400d500309081c25030b0703450803200c04850207007040c808094210100c58042c03050f0341044400134003d10190b030658074003900d10140603140d02c03c1190008002001c92400702c00d4000c41040c0c00d0b80004c201c0744103042c45a0759030b01c00e68050388109080c141c0060822076940002c403501d0f03010707 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 702188273 1250 702187023 702187027
    0x6060302100f051602040b090903070c0608060f090901180b0a1a01091413020a050316050a0e09130506091c0509010801290c010e071e031713030f05060601090506 71
    0x1520711213200000c003207070032545800715201c1a80d560f48031a885522210015900c0b0001414054000c2d400c03544400248200b02c800e01505440b5103000b049803040c10b40e01c041060725201c9006004040d40741c81040100c8400c01c0300e000700040d0002c400c1c06002c0140d4184443c402030f900d04091a100030703030341901185a4980802290b141c4400142c60044d008201c050548442c100510603680300c0512040091800410880600803038510000100d010303180480c00e0040c1c42e030014000140e4802c0417841400d0034000140b81206910490700043d50040999019003004000d80d69188220008114000c4844200019181c41fa030180c802000050755012a9a460802000c00340e2210006210302e20144010001e05080340f0300082003181038000000403010746800b122401c05001e60051440c01e403010380c098910000c50b44010007644e8010202041000802d00300c4501c40c42101488030305108104d000105209100c0340c2c019020313000300d098403102d6035482d00440d1903d646014040e405001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 702189523 1250 702188273 702188287
    0x4030c0803090f090a02070602030a020a11070501020343031b0b07110f0d02070501020c1806061c11070b010509070c0b0903040e10050411032401050d050406060302100f05 75
    0x220081c84ea40010400b20010318002440e00c0352410380c0d2044031103540c495000070300d0f44509a0300020a40140c1c8420002c1c141907410100001d4480c450f21152803c510b01c0c443c3c0003d8110101046039100828101060f00c50280550071100d041004007400d07000b1541910400b060100715640e61040c5950080c0e001916070b54208c002e88402e480c0c145440340c2842264448030715004c0401410948003941c0c0c0091041c54507100009280080c81b09c80c0900032250f030080daa03a180e0110030b0954202104a846a0f124500c1010840c444038810000d41c0b000c0b820102403c80b140c0c07044008143c454082c5140100a130303250300500000000c151414000240d010030001c02040078200c034690403209407400e8910703059555000960841080c0d80680160038016410405c900d424400c0c85080301c030510343c0030706610300650400c40c407042e07480350010030758500441340b907081e07200e2801c541d009580c8100804c19801c0c2820700b00020b12507400304078043c48010003010080d500a00041428045996440b454002c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 702190773 1250 702189523 702189529
    0xc030605060f07150f05132108010306050403052b0f0b01270503030435070e090109200f0405010522090f240501260c06040b04030c0803090f 62
    0x2880819444c1c0703031640c40c000795425148030701405018071000301401d024544142001d4071601c1540ba1000165154212021406038100c2c1601d4110b03038100303000054669175420160354601c030300c0000c0c800500104511041100442c0ba4400780f0441c000c40412031080041e50210403250018a007078007041403c00340e456108141c0d44400101d00300150340e0540c40d5552400f00e89190010340210401c2485403000c80c00f41c204907210008000700d0011800c1c56200e01c0e031440f945070240b601410f1100b83c141000130321252070035002645983e80c800c4a0245800d0051000c0f962520400c1242c0e00c240c0c1c1c84013449480b80b4090003114140d40009103040d005c42c1b4402000f000007901c40d02c100310f903192945180c00c04107428000f1300d62042d020307072914990240314945e0490605c543e202030504040c03a020061241d5451292031400005400e00807400660054510920b4101c680300d5095000000040128210021f50050011203210354200403140e40ca8092030764603030141100050b000081120030004901d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 702192023 1250 702190773 702190793
    0x31a04150b03010e070f0501030b150a0c03020c060d05040516030302100c020a0506090d090b0f030109090201020a050111091912080f1c1a0d030c0b090c0d060c030605060f07 76
    0x44000b800010041c0c071000c0124101046584000d60302500520100640d503014000d048000e40e044503480d205816001e80030850780940740c0d40d0010401800d06000425008201200307480030b00400d6651544a41300340701000e040120780c21101c6020b09080e40084081c0140d0803010350354190003400e4100c0540c04124002c2c2075a1780d40c00214410609082c012070001d011144c02070b20b0f02409000d100d03481ca90b01515040c1d0603400340c0038003e4100301e20a4a0350501007641d0650700c03820f40c0855180000d000403032414812a1000e4059442c1c03918542206440318000e24640d00e00340c40c2d03565003000241040400c45440d02c95140504100310203000065401c000603d0790504006c101424105142d14400e405524146000b51a940c4d480091800300594401c01c500918101c8504076018101d81c4d008000e90914040280400e51034004600d010317105200d4101c2241015003420314440781424510050480240d0102c0401d1401801040505258080f220142500c072012440c0111590301c652000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 702193273 1250 702192023 702192041
    0x100323090304030f051006170a0305030430030e0a032001110d050a0b040204030f0201080c0d09061508060c071202070b071101080702010c0c0602030405150907031a0415 74
    0x380000c00003c800921142105540359010300020318603120b040120000707d50443d0041a03d00350040c00818401d000003c00c0184103607d45001512170b100d519110701d02c0100d03071100142d1000d081680d404401307250400c0030418002581c060108445655290341c40714020000900001d1601c510404c1854440e41002c2450f02c60900004801d203451800580942002403d40302050321070302440035081e0b040c09400605241120f04514161440c1d50395813080648400081c1070040001c006241a0400b03002e0b14101c1290000501c1109150700c0e02e00300030505c421400e40750b448030708004030321808005011031107074925a48440c038103240d0f515072007800c001c0c0c0312584003144100c0202003110f20349000a402c09e030740b00b40b003961451816200090003000c00140b2160442e0324219200044692154940d040d1541105006981c0d440b68101141010f031032009000d6074841d4103041c810113180015509040b203000d6100310300041000c201d810440c0205580280100f80c60150300c2640c08030503403000e424 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 702194523 1250 702193273 702193291
    0x90304030303050c1306111011040623030108010b090a0b03070b0d0e1f1b23070c0f0e01060203041505090315010b0a0e01030506030a170d020408060105100323 70
    0x103001744480031860755000e036005480040c200049640740d00b80704009000c4a081001418008405c1d46c0c01240f0982c0107c0c81005c080211080c00c140103001103848040c0398020340b01020b55290784800394640a8514002404e0050940c40001410b2a0003846038070401b14005001d4480340d4900703520840c0c117800c1031902c8401c096039100d81c0035a00004108014001410000d41c020f043c0611400e20100c0c1e903640c8150800341c0e465201480355070351003944031000011440340018420b903080300154042c01000e1001f0844013040c5d2001c110350401d000da007004c640c156044460684e807074000481c4c0300d01851040416141100010006840c01500946444c0002070102c1c0d00c4e03807a02e44400c4100e041c007a0b1050480280019101e1095544a100390254560a0038140410700385480881d13603030040640c001d801ca20041d2407442c20031072140100d58040302c3c0c4040542d10b86448a0381682ca503942842828418204900013003c294024002d50b010601030100c0349a1003601600160b24810005100507a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 702195773 1250 702194523 702194527
    0x309150304031e08040209060d020f062d181203040e15030a1407150e0d050115090b19050117040c050411040305070f080303012d15030b09090304030303050c 69
    0x2500d002c1c1d05020b0540010f19a0741c440c0c4030b0a142c014881411009400305005120104447c00540c42d0b13884804c992220686049aa44c030554082e9030700104408212003411003880200f914011241c00070742458410711408c0300f4462052410011194803140500e4826002400700300b00a0180082a0b07038004480206454440702c0400000c0c1001e031100401c03150300201c1d2080c0c0114080c00c01085014083c9410b207003104900b060700c081c0024841141c81407165444000f00d508000d0207402c1f820002081100f204030a0340c5481121026080f018100350103070001c0c41e80d1101542c070b0403040b8002c0394010385451342500c404418002c41c0034030040c8150340f804540c0c0c0d40001d6549552180f4006005a030814039240ca0130340c82c120707050424641c4000c80300b100c0c00c0c10500035414007004690440700998141854072500a03401852039203107420042015010740800100826601800801d0303960b55607081008003444000c104510000361403141c8198014041840064069402179400455011000b4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 702197023 1250 702195773 702195797
    0x608041b031a2a07150b0f0603040c1d0405210a0c11060f180301062409050a170d02060c0d0b030c040905010603050f0309130b0105070b070201060611030915030403 72
    0x107607411505000e11001d9400004002d014082041444c0c1107205d6040e000344401d101c1840010000c8018180d00b0340f1881c40000490304105d00303403502d04028403e23511410440100002400b010090407101560035000c0c04000300c068540c41c03080c9540c16101440300390704009500404513042d04030044200d81c0505007801c402881c2c0d1301d10b0050f040c0c142d00d002070656101400c0e00284804809201428040ea04040050191075251020f60f04000c160f081085200380e07000800300c40d001d40660080c2d03000000d495001c10305100c1189500307401d0301349101316401c24070140070403a81e40104031a00c0251420601c4060640d091680004110107801821140454204800101101d29006003240c03240c0d99070f03c0170030400c4400e000807003521001034040c6091030f80b0000404c1481d0074010308540e005a460001445580c011401d44405603003044107401c3d90f04e00054060b00811542c055800443c41c4602e03403800d0301000200700d4600a4020384038501c4100201c4000b80300d42c01c040c10480501c118a4085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 702198273 1250 702197023 702197071
    0x60102150a050106020d090e01050114040e0103120f0c12030509010e0111040f0e0c120a09050607090503070f051e040b1005030a060609030b07120e070608041b031a 72
    0x40307001d120003500000b415450f20710044d1806408144420a00c44600c04c10007140e0040001181125401c0c2041d91010911030b1384004180f249421000030f0032100c81c0003005010070400740c1c0141c09182d40780d0540b500310204055803e41c4404100902648103d100c54065a109810140c0c0115617500003150400d028800e01e82902c030128030750420381001040400616160807280d50003170542e5441e4040e1428403025145462044c0444941101480d05c040b0352241201e6000a00300d80c1c01030142da6442c2029070008003c031496100315480391165100100351074a00703e034850704403040280081c00021088000c039502203d00c1103840e41c856900c803540040c0744c48041030100322130695520305a60b4a08131140c507007283e1941c0c0003101040082c82080c030000b12100c04a9810409a051a002c90341101c6001ea0142406900c04000c600500c800025419000a00300740a1482a14001710b0303039101c00d5803403e00381e04520001e040185c594070700c42151b03a0322050b4203410844820040b150500b0400038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 702199523 1250 702198273 702198313
    0x80c0a0f0204050708130807031404030b0f070e030c011803050706090e0c0301030804091a12010902121506010c030e150904050603151501051603020307020306090102120f060102 78
    0x58414851035480d240c114940303446616444112800c0c50390a07070030001c50300c02c1c8415240d00000c2005400141076014940030f0700807444028a00c981080e81e5984900d00700702204825038842e114050300740301098a1038042e0103a499507003006070091811217000f41c011607032107110001c040303e401481c200c0400400d50a0207101e000d0401603d49801c207a15104c2c22a085981c0200040d075414001d00044c0700040b0392800700d030115202c0190125540c440c0c5a480c40c14041c041003e5a44005d091044440380075041d0440703003026008845500410460340e881c561611141d0300703585203514406002034429070085032507d002a0091a010007685000c10104880c54140aa41214404080340c1071841c2d107418020150b00c95400e4000c0d0140c0241c111849880d044013418074038412980c0300300b04109900c100155104903034040030f4140c051441c0c1c10040c0d101c1d0b0208030268004c1c0122030001d0396400b030500071192701191080d5600b54540c1d411110104128001e0000d80c11030088900020394140c05c3c080c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 702200773 1250 702199523 702199543
    0x20c0102251703120f07080f180a140d0801030c091e051905071e0807020a08130e06060f0307210507091502010e06013005010b15070816080c 62
    0xc0116902c94910211300c44000004041e110088104410001e00daa44582c40c0383d00300064003500c03e0315031100c0079922444200c26007041b15610a0f22146020b000c03024045001e804592030907584444c1100030308442104e0f09010140c407601c1c202c4801c0002000b142d000e00000d84500000d0764406905e040301d041903078025280305140700315074180c01744080c11340d108003078000d00d203400c180d004650005802283c0d2402203400c1024045100f0015050ba4000c0c00080100c66000302d0542c0d503020000c000c0201c601d000d01801d40d05a102500040081c14281c0494081024403400c2a0840e42d42e050116079651420388a10301124000034a0102c6665074000c03d03001f2450341e1140d002940c203160841ca400c5541e003416074216070424034402c601c03210100720981036981740d80056614520461304004000d40c00700340d400f1400000040c001c00e108040d8000740c80c40034216001c5c0201491f018903141d05010315a0041c280034820031582882c40e0b404411218060301c154030282c1003204482080c2e091040e4a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 702202023 1250 702200773 702200819
    0x90102010b100c151a1918061403030309030f0d0609051510032c03130803120702011104060c0303060e01090b1305041a040302070b030a0c020d020c010225 68
    0xa400801020200c4010144400300c0b0400c10174034080f100003201103190b1484d50180c10000d94141c1100e90b00801c40025003201084204c00c01280d00b480c1008142504c5040480300c080c810310380081c130300401200c1c003402991000758103003007038a500b1450582c0901c1c220200c103031b960400002c0542d0035004913840740c1c1c01c44a1102c2c0c00361051007440300101d6078004903c101442e008805282c001403180e0251910401c140624141074006649491440b4211003511045022200001c054000000402c603d40d0a03a0001c2d00f2511103900030303820317160034a02e1a101480140024045070f403240c03c2211065009180c003043d0b2607a610b44441e003985007a000500b50742d481d00455103083c14400b019900300c84000104001600e060748540d00c40f060310503526503096042c0320103d81414806c01080d1701500c00304841039524100b1081a40050403c0351116015020395450041d160740041a0300c0110708040c2c02500405400b180740c40c01c2d0100006d0100e1002680c810301150040210b500050400307210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 702203273 1250 702202023 702202037
    0xd03081f180c020d020a020a1712070c080d05030610050307021c080709050609030a0611120f0f010b030709060f0302120c130b04151d041503020103061514090102010b10 74
    0x94001341403008148914040d548000900c10050303c89020000844401c00580d080c040e111040e01c0b8104a610040071200c2d41e4003052400510604c1c100000444004004890301443c000d807040d610f5000446038503600071000006001d0b00d9010b070700155842202441504c2c20405914070001130002c990070702d800014074070810000e2580d0424611005400f049035000c2c100034040c2c0000341d9a20740307044001c105607210000344100080080a641d103412215480d40c41030315004148907560301044a117409a02484400055002074081c110703801000c05550389903109060200c140c900d10700c0001c40d00c0405a0030824540001c5443d41043d000701519159143c1d99100d00745c5c041c216200c40e4200d00f0720000c1c1040708108043c643c804600c094aa14105440d403003400da001c3c44190070303100c8501e54200c1e040c401d110f141c1045015001043d64400d8030100165a00c40038211504c002c14001032011400080d90407400c0750311030b4081c3c1101c0005100110343c2140e00c00106030100c812600714000702d10300e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 702204523 1250 702203273 702203291
    0x8160c11030a0c1707241704121b02010e0f0105090d03050c1e101104032102102304020d0501020f31172e0b0d03081f18 53
    0xd80034458154000c00e00802c000d506083e13004902071b401c00b00701e203102501d81116214050041c54803111088280c007000741146010305000b044401151600800954403600302055906401084800701d80c044e90f4030b0303071012034074014090803462006441e41404020311021125507503178101900014440da40310b07134a03400031000c22803610f007070790400c420300064021820030319002c0010700e12400c0704d4020000c601032021b422100400e2180d600060b221035913103900c1e0300d00c0200b000b080305041d101701c1d4222020484091084130460380340c0c401510f40c02ca071600e0100c42c820064001c00b0703006070008080c9545800140d403114220b0380140b00e04d44445102051510004450303402103100ea00c280010b01c10602907500005180311a00c1c00b54601e11701649100c03502d0224200715020501c05030403100741c207182402480340c042c241c158207906045410032607410840e0070f040d801c140550b541a1500c0c00c0c0707030721a5a2445281d600c1014204296156140300007008115000701c40c90b180e400e408006a0760031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 702205773 1250 702204523 702204539
    0x1b180e0f06360f0705071b08070b041d091905030d05010807060f0507030207090e01090209010915121104020a0c0615030b0106110c0f0a030b0a0f0c08160c11030a0c 72
    0x50000c811001d860080109254006007151b001540c41001400998407000c83e03840400416000240940700700325010468041e900014815100b40c0010000b410005120751340600070102c401e04820b80208900b00101d04a41c041c0c50350081c4200207503810802940c90349130440300c01360b0020180f0f5024200400000341c205040140c01020351626902c0e098181c0c402130742e1460030f4803d4600243c0d469036910030f41c400a6110090050380148a11100c0d40d4490360b100281c080c00c5040c82205c00c0440000441c020446060341610b03030310061408100210604010007034119200d00010b21583c0c90800c40040e0292280c52441d0300602a0503070b40324114200188061416081001441000c000581c0c80701000a014504084200c1d0315075108070200c0b020807405015a0b00050100b950003050203071640042c1c00443d4400c0d00c01e4020070002d200d9100444d0707000c10a49000540e080d02e40a40e150040c42014001c44060081d9030307141038030030f5006c00b003485c12a100350141d0ba17450700700b4000e0003501 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 702207023 1250 702205773 702205879
    0xd021504140607030206040b1008010e011401080f07150e06040303030e12311511011802130b030c09010b07060515060d0e101b180e0f06 60
    0x140701901c44074200602680c0196650f00007600141c411841d020018030480c03a45411900581490b80003486104010403002e40038200c504070b02040409010300210f0300150000c1c01c20396604400009155281c40e00241070314035010441254200403222600da4480e0320b805000700011442a40d000502603450400e442c1010080396500361b1041c42080704151941c3c880d1500c1041c518030b20f0210992221b40180401005a00c0c0d000001cdc01a511400441c02901319201248908110000740312007400e0f08842d040070300c0e141600035070107203245400a040c8010b0f980314441c5540d0150464a6580c2c006000440c501001d900c0b084180074002000d400300300040c02000d0b04540300c0807091140001c0400022054045c0e000920325040d6901031b10403480c6020080c500000d05d0f1000c0c20080340b101c04544212a2a00074505000728544c0305e1840756040500c02c2e6082255000c040584281d1503c103041902c1755005011607a000f6506000da00c4400d000041c140802c403480729192800c2000390031503403095 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 702208273 1250 702207023 702207059
    0x5030d1d01051603081f1706010b0c150403022109040b09013002040c0207061d03030d020d0f140a0c020114040b130c090228021b0d021504 61
    0x100a11803e15a0b01c2c1010242c0d10640c4d03d030500709803584d1042054003400044000d002c2c815007038500001101071510342a880d4680400040d11416a2280c2d04540d0390310a40d001c0080c03907480035001c11a05982c13240d115400a10038410744e444101c0c84031490080c443c074201d03044951b01c00025800007510705445152803000080e1002445585021050203010864164490111108040d8490303134607503c21441000c25401441003200f11440e41c1c0095440240303000c1c04011850514005804640c0d240f018010880010011450001d412207690003940181101ea46055110024a81e02d1b80d13160040344415208250302020034600fa40003281500c0154019a0559150480314003a0b40000b8008982c488d400440c02c410903141d551002204480d0f03550302400c40e103042c400c013003030554a54008081c000c0701100454941c00407602d40e98158030b10b901d02100584c0c4846550b4032400d21501104401c240d000b014418496616000708190807680d104249500900280a100d080c44c5112070b0089 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 702209523 1250 702208273 702208277
    0x203041401021906050703020715050403080903040f180207080a0c0302070b120c2b05060907031404020405040c05060a0c060e15010b09060403140309030f0619020d020405030d1d01 79
    0x4541150f00341000c500000e8000a0300d8551920300040c4258020340485a4007a8003802032440c000012440382c00412081e40e0440028200c1004500c95034000404e0701d041d50f02c84080a1041898410344410358440074100a0070f00e6001e0004074007091851024200e60342498940ca504100203180c000e0401425400000c5081401d101000c03844040a10300c90b480307501014100d03a0781e081c04042c042410894483c2d404040c038030f004460806d1500d50000d50250806440c0c0ca0242c2d00d0307208040c0d05540b14100d40c1e1680703403c4440010094680707504030315042801240301800c43e0b0340b1000841c416502c01b425a5000c180e03001c42260801145200b003003054040710005d41072541c0f1001c8115000d54061240e0b070040200810701d122295541400c031f60046134000006010100c1c0030303000644a40000c240c40303109000b030249851181c44046440c03031250307400c1c808070700b0f0310354800ca41d4000a400010491080503801d02010545440402003034888403000d80340c001c0c0f005050344803442c0d480b1a140440e41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 702210773 1250 702209523 702209533
    0x20d0b060f0a0602030a120f061d0109020703050306040b010c17120a0b0f060d06090510080105060f0306130501060f06031514131e051021050a111201020703020304140102 75
    0x840b503000c01078820400551a00400d134919211f00c0708040e1014481c04800b00380b401d40001240c0d151482c40448420000c0321442c031580e42d90b09a03034224094010f010303012600800000b41e041c5031a52000c400402e05040607803203c03075582c840304101602c0000071083c140300043c00350101d80780020315582c40082c09000380301300b080c3c450200d00b91844d0900e115014030400700f00817000098940095001d082e001c80100014a004804030180e1038540c4202c0c4065440c00f00411031074188158680700c1914050001d0100f6158840340e910400280b1000391219513035028042020584440c188005003d240d801144940b080203401c42d0400c029801418404d28441207444c0d2a11a1201eaa44040c2c0188001600e040003e41d10b04000c071891030710a070744903e40810021400525411001a600710401914525074240044a076070f0342c2c40140505142d0254100e200000d00c56041e03c44460700140c0401c0a0100070240c0e9401d80c2c10105080b0050780000c00c0500c2400d0220b052102d07a40c0e02407005203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 702212023 1250 702210773 702210779
    0xf12070306063b13051603060b060a0903080c01060b0c24010609060c03030f022701050405090606030601030207080703020d02011103063a1a010b030f070507050a020d0b060f0a 77
    0x210351030498141040b9809a07000000d8090325600600c04c407965002819110003849500384140c42c0440b90000322402440c080d110281030a0241c1543c074081491741391500481d00303680703ca00e0346400501095004d90748604002c211104280081c101564252004112141002c00207089402400390301c80c0e6410944001003003500d070b01c9417203c0e00300c0303445d420000111016410105c015061804a406c51280001140102030812000c2c0f0140c100030130101c084940c28420044440c0e1155124065010a0800c04507419142510017140c00078030505005103405c0140c0d40c0d40145400045045e80943c0000503d415060340a0180706c004c01c888108561543c40c000002480c05481c184403458200c009611820742100e0356001a0620007400070349400d441030758a0f143d10f0710200e0160007e4900d1f808000098543c0c0d6420a407802102c841c005076000b682c5002088500b500310000548032840392071410700160305ca040766a81b1682c09004104118a454002d010807850103861103401082665020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 702213273 1250 702212023 702212099
    0x5090c150d06090b10030e150411030d05090f12030d05010e01091401051831031701080a0b0c040504293705061201051009050603060f1207030606 64
    0x9412840c1181400a0103e54110f010341c0761528110580c2070361008c03c001e0005110118035112070140d1b0407000c54058080c092402c450324001c000500e60400f00728008001d0a1502009841f007284900c42220300700740c020a07084c41a144203900c0180391001040050020a81c24010544010107800d000301d80741d403401e0b011462003000d044e13084241c40c00640c04241070041034843d843c000860b02002d50500030071051007000b2074500366403c40100720030600d022244404580310030b0496550f5000307486268181e4961a030340000083c0840d0000c1410400442e19590b80d00c00e40d8181801c000441da1540050400c6001402410640c00e118056694100060020311402e801016013941940d41c0000560b00c80c51001d842a508440d40c09100400d0091405104000640c100c2e00d00b1505410303c01030f150800d8402e200c10f03002d13194119030100002101418601a491482d040183c0840e00144401003600e00f44195604101c2c3c40c680c440b03a0801032543d000c5445c0c2d008450000034103074968190181c3e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 702214523 1250 702213273 702213289
    0xa120c06020d1d1b2b2111060c030105100207092d090c0510030b12010f0b0d0b010306180807200109081f09050a050a030207120302030a0305090c150d06090b 69
    0x1400d20810210310440a40410324420307602e1b400b0020003001d542c40f541e82036544030b54681b4000040d5134846101004d020014120b4028001e00c80394a14507420001844551070040b000001584601d88001450340740300d00c624841001d01290030840313690b200401c003a11104041190f0b07015424440040040754a00c10380004890084402001d8800c0c141c50650103440c8590b05107510064229091640c403030190008001c4c0c541c502d9040000f04405810050750b04000e207400391241039200014000030b002c90744503d0480d140a0589030f0003500b1a5100002d6900041c01207686640181c2c804105a010101a4001c0303402401d060080505140c01c05543e000a160380c544144007507001104228802c3e8000303801d441e0800700f0343e205c82180e4141166142000c0000302c0c014803560314001500343c409541e0f10740340742d810350240d4600000604110003900f1702501e01d4032039000e0502480315030f42d2103040c000300345180a005145c032040d8000481c07088600692069100e01d00b400b1030b004d0142c4c3d800389 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 702215773 1250 702214523 702214549
    0x1020d0509060901030f060b0a030605031608030a0806010201090b0c0711010824041d0706020709020a0806010f0207180b0111071a0a12090309170a120c06020d1d1b 72
    0x85c00007001c0120140032405000190b2040c4030341500011040d07000c9a043c0c000c231040c5e0703100f907003115460070300380800c103013030303900521035007000da00184031a81e40c042c03140400e543c00c05414800411301400b9a240c040c14103209440d01c40181d200003401c0420444509058100c0d0b02090804108620708040b00c640301082007108290380352105000100295941d9000250002d044140d81062500d0000d48503500d00e068010040580700380400012800ca841c000c4820009050f501d12541e40c54590054030080c5515010f04198001e942e408501d070100c2d0200e05542111040011039114280300002d040c26000061110351500821410f00c12942407003101c1c012010003d003055034901070148110303503041c08070302c40255140c2848604420305900802c403905860104111100980c2c800c1940c07692114100c131700400701d68820401c0307041103018505242c031844c000c82003d440d212a00018808a85a04003284840c001c80200034aa04d070007007003900020b042c10b210460700d0b094410005190760140203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 702217023 1250 702215773 702215777
    0x60e030105090c03031603110106120b0f13020d0501021b03031501080f040b06030a2015070f02061b1005011508090715051b06010306110909060603060301180b010501020d0509060901 80
    0x1c800901014440c00c841044952384c40000c0000980b00c802c041405000050241d50990501d0045038203a00c015003c42c0c002c514552004400050036428052000100d5005a0709035600380441502174054000d1054200d4070400a19a04e11340500004075945642201e14100030b0f0300c004001136920042652074000350400d020000c540d84a45c000b070304d8065000001800c554140c1c0c500b103a0b0550101c42c911540701c0031108074000d041101000a55401849005410316100c14031010150a084008009005078030101402036001e2443d11490020300384000d0215641c0d82004200e0f0080407200078144003076910b842012410710444c5c443ea01c800c103004114035072016520350840f0380e004404a44030940341d0b003030085524099003034413a1100001d1009441e05424012090300c1003132170303408440e18076200a10178005500c4213400c1c456580c00c0140540e40565a0304010f000e14001c012100091510495400100c0d6050074002810005107414800a116040c0710040503559518203a8204020078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 702218273 1250 702217023 702217057
    0x30d0b120a032a0f05032a15040303061a030f090a12030e030d051f06110d08191e110909071b0b0a020d0e0f06010e0a0b0901060e030105090c0303 64
    0x400c43c242ca915080c2e58000c2c0144950034241080000200c041c3c80300400041032800d09502c446489940102c40c0706c01260690400b40d08840d40e903140400305900180a46000079089440d81e48002240e001039025146070b0b8004810840401041846141e00981c8100500040022907542c601d43c3d00708240a0360a050303c0b4454001b050404000741c13034024031411014403042c01c2000750081e41240b0484180419842004041000d90240d00014401c011080082c900d07040801002c607101070340502000380440b40300c1caa80844001c1c50207000d181e1300e2000070b90b500d00c003d5179213054222004500210420801440b00410994416451980c03010003828010b1800903040030106062500442c000c043c0303901c40051180011507a0f01602592041c80d004108492800101c20383e00c4100141c50007107a4841001480034820441090780c208060303850100d104c1c8495000030384c0f0340400760044800034000301c41c024070b00d01d42402160780104004000c0d10040b0002c001194480c40f54520600700c1d4598 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 702219523 1250 702218273 702218327
    0x2010e0c0f150f0f070b04060c0e01091505190f09090e070302060901050c071413111608070807030302120a0c141c0e0f07080607020316030908030d0b120a03 69
    0x880fa0458510394050560243d4907442e601d001c1c91861407e480c1030320b00030b160040301000b07d07000c2c00014150180584401009501d094040f41081c42100c8102e01000014030130301e0100c2c84400001c008032411600e602074001c04540000b00412481c2c0e0111007034a0401400040b01500030450f44e0030b0303075016502d2507507810403400166114851213081e0140b51182413000917040c0a548aa0f10a260049440d407018120080440e030035a118034280c9140b00c60100400c01141402006030307a200c921400d82213081200030344460310107401420090b0040ba400080300000c00840815455101c040c2da401040070315403c0078010003208011a5030301c8141000980da40b50300440d605a10030700c156045040c0403004640700800d86641d200340b4185514854010082100c100104806100c0c403100d50040d42001c48204407c00890100d01060f420302c58642c0e4085490300c8144001d055600001070f010a41c995a1018007000c070403180388001035604441c1c003000000740d00c00e003007030f407080a2505404044a4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 702220773 1250 702219523 702219547
    0xe09130803071403090f07080a110d0c03050a0c0915060509150c0a0c0311010509030a0b071e0c0c0e060f0114090d03020a15272102010e0c0f15 63
    0x14549403022050074002c1308005032484006400da030351410310320980c0d8000e55030302c2c0d08aa0382d490329100102190858400a9000d0602e24000e090039400741c941c0c00740e450b50300d03182c40341070060004064a00c0d0000450901148105004980040c040c01c584091800d1800500400a0203001c0707005110f05401b00e0051a070506550039200361001c110107542c0d01098510741000d80340384074482150301c40b00012407000c003980110103031038000340060040d00140d0303d281c0d0f4071646110020f0050003803001200d4003054500050121003101038140e2660041c0d000316080c00d150285a540c00200b0300d030b80003010060391741c80e40c1d100600003000a0038410b80807803136828902500c0c003c0b45103480e0400c06103081081415800540c0c0c00b8494090b201202c41442400301000981c0c04990500101c4500351209100b011620140700c440e6034081c84c20083c01d050740003892038120003110612030050791243c0b00e40321840b0b424405220040022203a40000c044420003080d42545203c9502045850216819410300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 702222023 1250 702220773 702220787
    0x90b09040f0e0c0118031a0a11160b0a0603150b04110d090b10270b120715080910090816030305040b0f0f06100e03060a09030e0913080307 61
    0x4a5607000c2442810003008403690354494030a410350000b04140c00c2d44034450070300c80c440404d4070740160b1541846900b07905428000740002d0040014183d0321500d1300c61518071400540102094466442881c031441d041c102118900500403101c2c03140f03000c07000c0000610344803014406205541c004581003003100002002040c0546d030094007804d0000b03124054050b580c0c45481c40c1482400c1c40c1d0195151415142d0160f2035074010001c00d4540580c194007824090310130325040000440f8045407080740384001c214240c1910f40c2103945648112001d007c11000c46828800740032240c81c00303c900d4500990130035a42d00e002c80b540700560f6940e840341001e20520030200c800c8045081c00785001442107242c002d00030f1004441c261030519030040411003170311031003469500625511550240d0358842e0820850710200716040c0c0c0c000e00003600c00707007203442d20180070300c5100c1c1c1c4141100042c2103400e0304020b81080c4030301700300c640304001d010100260596220002c000c0310f034120b907682c1d44a0b540d0060030f941c20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 702223273 1250 702222023 702222041
    0x15010302040c0e04110306010206090715050d020403021e01080a090c030b0903120112290a0b040b04110c071202030a0b0411060c1e0303060f060706090f150516090b0904 74
    0x129003403022005c1003980280c02075000701c0084e82103403095502e41d02007544844a602602950680b1001c5240d81544540040c04400a89840040c500b9607240d00013551414103c60200f554140da540220441d80c0011120f40e0000d040e2030b050051240c41d56400d42443c00c1070100406a00b00b00c0d010620080c0208259603150302001021245540c581801001c10401c0d8881169410f081192101c41780041c80e828843e42600e402210ba0691034840340b900c090300f21680c0041e0459075840c0180740c80c0e0380d00d01620071202d4042c941650342e007030301d0040f0a09090340c81d048880c00c01101c2c2402030060305c000400404164009140c550380e031321a480c01070480901a107030190710890104002d40300e04c8000c1080b00e0b00002d0b02426075024024800d1841c1c5901080314460b41c402e500d1106810181000300042c015640316090005420142d03039244181c0180c405015269846401030004070300000d40302d096000410100c000001c1c55180a0041080f003050144400c00c45000c601c1400c2500c1c0c42d0031036065 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 702224523 1250 702223273 702223279
    0x30e071703090a030f0b01060302040b0409020d09050610061b0302030307050708040321020f160b07030905030303040b10060503090c04020a030b0d030f02070b040b1806073215010302040c0e 83
    0x2541e803030a141781283c078174200598800341a1800001c0c0349010740708031821034010300c01550806103009101002508a1103c00d064252101c00d100b001800501c00d05214540783d03201407503440d060520080000d5074a02c2c450700300c98894081a400b098001050f2a07010030740d4900b90f90b8916407442c140d0510f02407a0300040007401c07010503444d006800d02003034003510b80c902d43c2111a0307107402181c42036079549004081007040207141e03403c3c0410074003c0c0c010000c0c0350290405002c010740e5180482d145500407038040d61140100824828200700c580690001445189082410b41c104560302c15185c00900707401034410b560018403148618001d4100c030f40c0030100201180019030023810060604043c004002c00140203050b4080b48580c80082520f041d60384544c500ca040186403100a25203281c41e0204e00d034404420f202500010b88450251114402e03840c1281c1c030143e8002c6401031a03508400411451904034a05401092007000c07691303411290100d0f0f021440b80c80c00030302941d03100000a40660 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 702225773 1250 702224523 702224539
    0x50105040809091609050f06130906030c050114030a180203030a0c0201030f060b0d051e010b0409060506041410030f0213150927021603020a020102010b01030e07170309 74
    0x1d101520024246600054a40115980d241110a40b081c0d00e01e08521020a0700d42c0414091030421002c82460071001910443c03a00c2c003000501c004031030240d03100c8608151242c400384100483d1004480082c1028200412f8005003d5010300840c00700a00000069030740f018054100d00080324007415103600075090b02c1e41c501e0f860700f000f070445004510070b0780031904018504c1d981e10128441d0340111004040b005051904a104a201501d40030b05110710451010461600704070200c040a4001c2000d03901c9070f95503500e0180000203030b49a580c40a885010700784420010707410002c5200070070a41c2118805005c01c0c0b10b0800f0703001007043e03040300400c103032010a121b00901210610340c2c0a0b80c001c081078074400c0304c2540c001c0f109105c05000740000000d002d8000070991101f4030641c40134910350355000d810200f05511190401c00d804000382c0042e44081d201d0003d5580a05c0b070030700c04403000e1900384880c00c891918103a680a00e0301c40d4600310303000c10036800c0006c0b07018025510640d0000341492 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 702227023 1250 702225773 702225781
    0x4241215051f0e04110613120812010b0d0509120403060b041b0c230c1017040f120c08041208070c0b0903060a020c070e0c09120d0207090b060403020d0f050105 70
    0x40200c42d0111005c40c2e19181c080328914461074040140d0b07940640143c3c1500c8101e003400d040503e85000c003081180d00c05414400041c8454100c941c003070180501e50119600c6480c180801c9003940c81c00751245580e81c104408030030b8040c0845040707405a1b500800003003100c0311502e000c200100945d00d090511814019074000348030f030f400041002458010402040011a40707860030f04920140f622000042d170100800314628188500c1404600300c17030b0304200030092455100146901400c0f20100c1d6a0b01d6406440400c0010404686803000e51340d1601034001d40041e40c41034003a200368001d102641084041d00c0e030400c01145c0c203c826083d40040902c0070959074891a5109400541145202c0d002d240b0000d11040001e100b9075445a8440c002090300a01d4428100d444140281215508000030003e04c0d000b900d515102e04038025000004002004030380034003e0808200350001c000880c1010580c3c0040c0d82c605080d2011f898045840640502c031520709206014140d0f4001080c03542008200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 702228273 1250 702227023 702227039
    0xf0102101d100b03060601110a050102301614041707080f0d09120f020402120103030905010c020102030f0901031d0f0d0c0b04060507030b04241215051f 67
    0x31a480784040c0048500c90880042c00780e0680d24035120494041d44980c00181c11036102e50945ea00d14201ca205594441c1101c1c5c8800b400c5e03a0005614142d00340000f061030164512103030750424031000410507040e290400120209000011603589402c01405a02504041c0c80c400100c034010001c0c103a4403008a20164061621089980b00d070310031034041e40c00707074085212010500c0540785600b07548000352141404802c803a070b600158403d07a9003040344010240143c607244002d05001c409107400000741d40c907600d0000c100e2007041d00b00c54104a90b885030703000143d030000162610001c0c5406d0003503c410009004034024003c5220740c0021380f0350881c0c8529072810208040000d0801e42080d150b403000901015110f661400400038410342d01d40d070004000c50900d900147d042085494003162025200c00004c003036404084000703450a00314040f4040c903150100480c0700a03d500c148440c2e03030400545a88801d04032400c00002c215072100300140c02010341d080888188801c48050344e10403500c4400c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 702229523 1250 702228273 702228311
    0x409050f010c020106060903200a031b08010b060f07140d080703110304020612130204020f1c0507050306190f092721090504051812090f0f010210 64
    0x310803194a04008a4010b9106024080541e80c00d9281c4244551556440f003164102980c5007840c43c40c400c981801d0241d85071841da82c015405000307020842468041d400034011956030044466a244c1885074200341c651034151210321311080c0700c03283c89072501d04005071100c14400b1001020300800092042054101d011980507103482d070b40802c1a48030010640c0c40c144016503010f03500500c00d010014019070780c0c0381d440e0342c412845449818000d01c01d60114040e600201c0e4401180903010620b204490082ca00d1203440341003200c1c1c00c0c04203080442000d0179a00c00170740390f14068003810042032020350b101c00300e07100109058076403a43c13001d5480c20514000c0800c021107003250460f6018405046d220715a8000c401030b000200d0102e90040b01150015083d11070798410148250040700082c1e0340e07a10300c5881c3c416040d030001c120145150402c114281190001c0829403180c2c14032008036117854480d100e400e4070005650500141a4080050b40f400795040d5141e49000d0600014881c2d00c224011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 702230773 1250 702229523 702229543
    0x30a02150c0f010c0e040e011e1b02120409090f0b101a0304030801090e0c040603080307230405010302091305070f020d0306180f090206041418070f120209040905 71
    0x251501c0e06042c0589500342d680c00d2841600091070070340c510010b85010b9202c040b041c20034100020381500d4242840e1861500c0308858080070341d840c0f1681e121301c0b0303440c800449151003e101410b0401e0380c0c604800000d000361700503140307000c0d0740b20000c104214491092040c02e5810880740700712443c0200703d44a004115002d80c0c1d20f601d0031856110102d8040d2400d8a001d103a1548640c032440e0f0a01c0a24002411450703100402407003116298242c40d2210b1088070041e50051a0066491a240c14043d00f548120801ca80c0a4100b102e040008171290b2016901541c00910700941c0d620001000280c4421040c00d40c05540c0c0e24281c00d0088040d04800c1e0407404c1d503459001e55003258004181038040740d9180c4100d03070380c020003200002e80d0800994022038080444020004502101c0e401107116a00160441000e102c00340c03110030058501225844440304208100d0f0485240904000304402a1001000e0900080e20030010039100b05070150b4002c042c025108103d140045c1c20701c0c55461012003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 702232023 1250 702230773 702230797
    0x120c060905060a030504060605060f0c0f03041a030403021005160f0810033f03050c0a0e061b1b0916090621020f0a0e0a030507060509030a0215 63
    0x14005145030240c408101195402450142000306018084c0c3c00f41800030300c11078106a5607d4040350703584d00ca1001d032040c180b04003841c40d11400c4428801d03140000310041403026030700620082102640004803200854a81c180d0b00352a0b071124913082c1e10b0000da6075079043c142030810040110543c1c2c10350f400d900c4e14800c0d50703c05078218881d100c00d07550003000b0784e507901c1000074080b070900c0450007405440319004c800d0621340c00e6621801d004012520a800e00d004500004081040c645641c140202a0410b16098505203400c603090b001400402514500a02501020902e10103140c00b0f545020380031501760040d10070080449080f080341c6d282450304513102ea022030012404400d5050307010300c00301c2e0305600c42c850760038281441a2020300d0085100018141401c542d00f120201a00240288100c0e0f012030f1500e5207209800039160710740300d44410303005000d404010804510700140d100c0484019051880d40d841025002c20309003840c0a0303001e074209424031842c0a003880d06400619100e4001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 702233273 1250 702232023 702232043
    0x10303210603031e03141308220509100e040b0a09050f060709122d0f03020a0309050105030907051c1a01030c0b031527040b0604050a11030103080a0302040b0412 71
    0x1034805070200c400041d003c0042d4003000e00020103640b401100c0700040c9026129450401c0103100384c00501203a00040402c2802d00d0b92010030207414040307003150700020826903010304c99040c6001100d011000030030190000c00142d0225400031414780c0000300554002c4143c8a43c13405100c0000d0742d803003040d51000e00049103514006004544070301480c0780b02d0380c4000841003020880b043c2c4602c115080b11403000c606481c004520001d502c90000c450b8441c402d4010b4024070f40e00b400c010300845160780c80782d418820200100301303948101040c82d00c1600c00031100c20f5804034402000860400449000422000700d5460014900320302c404018102c03031080c08502b1255865128143c0c880c001070b101c80c0d90309010b658454020b881c2c41618240107804040c2a0320301c1103c00c0d400010902c030281c03410744400800e0700620071603090602805500420b010030a0000c4600540400554441480081e20050010800c1a41c142c42a0115001800c100b0320190b150f036151a84050211001107080f682c0c49a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 702234523 1250 702233273 702233327
    0x9050621060111070506030c130311090a0507081f0b070c0504180302060c03040f060f0b04151518030b0106050a110a030e12010e0318180108030301030321060303 71
    0x4607800e80204103007283d000d040707450714080030710007a07400c05000d04442e8142800a05105003641d96044010b60266450b40c5540031a442400b0520001070300c0d0840050030035082010b02a084041c1c2902700842d800040b00800101c401c12414446540080c41003101c000b0780c050a1008409550003911000c80b010030100c1c0300e04201021a00044000034050f800110024400782c00900140d940980982e1281a400c1400c1e600c01041b2442640c0381d03a0301d9035442c01d070702002d401c0c284150b41540940f520421001d50800450315140500c0d07500c00000c11100c0140084040c048001d04402542e200380c4080d55940c4a000c060704d43e070003c40340c1c000005e00300445024103ea00003941c0c0080d68241d2100c1c0740d80c100c184103000c400480b07121106c1d0031f59240c444a140174401080104101004c00e00c0e400703c1455094100007103c4541c3c4140801010784600600c030012010003103d044a83c10b05016505025480542510112202a04010503d03102001081c1070b00282d0051488940607003a03c0c1400c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 702235773 1250 702234523 702234527
    0xa110a020d08031e101d130813030206130303120b0f100c050a0b09210904050901020c07090209040e030405130b010c0c14010f0519030c0e04020f0d06290a090506210601 74
    0x400c1f038030300e00035080c81d08a00c0080755912000706024103003000100c04941c1c5039004601d4a50005050b0814444c000f0f07070420030315070301440106460001250612181c4202d40016030307000440c90503c0d1140c0d05040d5181e141c540184c0c8104096a4000d040e500e07020b94a0504030003542048541c00f00034081c0070f4256003032842000901c1c00c100c15070f542c0707242409005030600c802800700404001c0f00b5942000300c030000403010030440c40108411240503940c0c0703003142d05110a59183c10200b4541d94414072050116130303641e210400e1011000d0500080e900c40e02030040320840d20314500680f0200c50207030040b49a500082454907010000c2e00d461200b020181d074122400d120b2201c030958045049001c040b02c15100c1c0d00035400b08030b07441c60446207075001040001c040741e1150f56070905640000036580d01c0320320a406940018503900007802904081501101159200300a110315100400602113054901507458240601b0018045940383c00d0507050365005c0780c800b88a000c221240c0440044c0c1558 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 702237023 1250 702235773 702235829
    0x2011806050708071e03090312050a0501080c150904050402060909040302010b01030c050a1d0a090c020609010605040e03250c080a021f02071215110a110a020d08031e10 74
    0x31030fa8034603600d010175803040114002c1601040860030410617a50321181c00174180038a83c05221019000a041e501d010202407030310a00400c528026850540703031680f10300c4103100765043d0690556010542d03585034030000e2103c0c03080512540d0b114048a0074441459415840102054420b80b420811040b1101c01990039001d0041c01c500042c100560354400c0e5041540c4580207020060090180c45485040c000107413002b01002d81d0051f40301004021126009000340d00c0103201c11b0350200308911182c0114bc0e00e03407040110360004400d0500301e030fa031200f00c1103110010040d00b150bc00314044d602e80098170344420314544241e1003203514003002448002d4903101d031008c1d21440d80081409510300039007244490110701090702c0c049049840320010340721500500cac889019450000f5030b11010701d10040c0044200002c4000a60f00ca1046200140c8400c21046d4019400c2805203480395075030407a4915040f861107510384800b80010a1000302c0c0144100c03541a00d06146500c1040d81c200e0301c00401031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 702238273 1250 702237023 702237047
    0xc1502011113031515090e0c06120f040f0b0f0402091b0d0b030c0d2103060807050d0503070507092f070204051e070807030506031f0c0201180605070807 67
    0x100c42c986003c00c001608551410880c500c456004503d40e0380040450030b0180d4103074820780b1810346501d10305202080a0010000019040b40c3d00c0741060700014403a400c100004008a00542c0030f0400304050005a9280b10a9140d01c5207040c0d075545410b164905c9060000e88049004542c40300100f040301a40d080088000184285141d09064501c8141700c0a4000c9015040d010302400010f0b01c00b540380d149803011071600420190f1501210003143c2900345000c8544003040501d002014840c804010903840101c607012500d0b03641c41c1025003805400c520590400411621403d000002e1104554016001d2251048060307542c00420040003d0040c81c0c04429001c001d008010b044010700c0e01c0d510035a04004800c00001c0f0b40141c3c2c0e0035000a0311030968503240812401410003410030b070f040c0101503000000303402a1803060b00c7e000c4501d010b034421160740710a203a120214110014801d620103060148010744025902c4018103100000f404140c6183e8002140391001400c0e00d1b00460180c00c1c9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 702239523 1250 702238273 702238297
    0x819020a02100b220b060c0109230f121b01020d05220201020a0b09030705251a0d110d150306060503030f0d020d181a06010807021510030c15020111 65
    0x542c128103900f44c004c203d03040c50300e584818240203089101c2c2c400d200d01401103101c1d0610001c071170020920341c40e2540c103121040200c1da0094500c50496003002c40c400a861a2802030f26172190211000c2d00c201c0d040140c0c80103146c0d8404543c02984005079003049015000250984a0004111044042c9041000d001a0144c1d005d124428005480d0720f2400c0d6105064109907410b101103981c65605104c0911a00040140a03400d014281002d045130f1b43c0003450300c90040385861840009e1086c0030b005a140c004500d995440520841c4005c41c0c1c2140c81059540300c3c00c22030f04107070116001c550b109130b00003580c1551074031001150310704000044a228000000c3c4442c20f00c0c0c403007141d600180d032050003032004640d05c540310311111140701c00c4051030f0300d0f01c41c800350140848502e10b1042156402004a410071441d8401d02c000f95801040c0320041c8244056514199568040d182004003441d44c00148481c001503000540d8030003240c1c0c8140340441e641c0c001e00229200030b6450046010b80100901 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 702240773 1250 702239523 702239569
    0x1107140105090301020d060b04030c0f0303080106050912250e0601140a0905040c111c0e0609010309050303010608160507080d090317010b0409061e060819020a02100b 73
    0x120540c000ea0161021040080c0098a172440c2c03041407a00f5140c46070f0040c13080c01b201050900070060301303440030805041640c01c0300200f82e1440d140204110410310400c0140071002424080948030326401711038040c20b030801c83c4e22400d00d640c0c88075142c0c0210854202d450710722010100703034032041d44282c40c01890144e580300c00c807180e0800c0c40e41131540000703003080501c00ba6420008035501c990042c01c4151007a6200e4442c03c1d020148110300744402c2d20300c0c240d56034a550000d802040d40210800e0100c03002034644035200d090481c01600200725801c00a0207a00c400310000980c540e00440040c07041c402001070a0610002e940143e03014000d11000070070601c401d003d00f200848071039000d4101a4080d180803410b00034000b145003540d41c42a00581030110300018140079440150040e80d00070104126000c0700b9000e00f00700381c0426000b901590003000400c40114440403903569920741d501c0c1e1064011580d5075036000d00696600150681e96108500300050b132110740c505000812095000710384412 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 702242023 1250 702240773 702240809
    0x1202011a09151311190e2808010603080703110607080f0c190903020a0f031505070c02130902100503010e04061d0d0309150b060d05040203010f0f09031107 68
    0x440d01c501c101031000c2d00000b07160000e12651a60380690941000b00c604815603894400400b17a204030410070768030040c4840000c01c9000c94464070035442d40441070f80b8608140b81152031500a440d0602e9020b900503608142d00401404585402015414440d44424184041e0b400d0302d20340322042125040040341d030a400003a4207902d0002100d500c600200e55052130140c1441800c0102c030ba0b140b4000c0c0020710303000c000303108504002000101038940c500202d5462031860340c510340040f202d8103204c203a4a03101c40c007080c0c00500036480c00014540c010702040f020080100010700900b115042a032046105402034802107018100b02ea06a44200408102d199a81c1e11100082c1080e40020011910110b42c0180046011300c403a100c801c180e40e40c0032520100d2401c0208401000721400700c04546417080d0140190b90340c0040b142d9040c800400807443c0c1d510380c00068010302c0700e1064845030905004950038030500ca648a400424400d889403480c4882d880300565441505000704207030b0014500f03603a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 702243273 1250 702242023 702242041
    0x1b26060705030f0405010906060b0919150e0a030602040e100f03030f030207030c05070f06030b0906010917010f0f0b011704020a06031e0903051b0f0a0303020a0e030a1202011a09 78
    0x141d0740700f8017071000840d030200142d41d080d0844616502246444802080b07448032441c0c9603040b02c1401c82911305502c8240e041c0039200c581e55030307524681020f0000342c4000c0c3e400783c0c913840c0102008541190045454558520140710000c0301141c0c1d0800c140d0b0071210200703032200c1106511040d69019500e5040765507680788158025405400d0603420312029040d4100010004c00102000c2c0c40e01e40034003221280780c034002905840301054911300c180000020400c481c0da1007198042122b410259101200c0d4200b0000d0f401407614111500c040d504010310302e034604100c0d42100030054020307a12070300c41c404103002c00c1d83d0214094800a51000341c000c81005154441e800c14220541060101c0043d05640300d00c04040714400c80003140410700204c4d8550f850301c480c3c081e00d20100309081c0509203456000321410f807143c00440d002000c2c5540420107e046910843c0f0711841850003404440ba800103c0c100000302e0442103241800640c28051010039001a007021540324a0b0064840860b07a00c41d4010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 702244523 1250 702243273 702243301
    0xd020a0312090f0809100e0f0103050c0f07050d260a0b01020708030c1005010f030312020d0905031c0c091d1302030307030305090601050117131b2606070503 69
    0x90a075007607848250410218000900d0f0480c02e51140341420790f140480c1c000d10004941d00c4804905106a10a0f94040e540b0303400c0043d11045400d190001c1c1603519000098030318001c2810042c60040007240c40001c000c0001046a03580c40c0a03212951413200ca001000000001c601035090000b00405c04103248182c1c1d0f030481100a501401a94031550b200c2410b1481c60700300858018007640300348840c9120207030900c5024007401c0504081030449040d5100540a91040c04180d9660f55000510380c8000c4060f5015200030750303020003a2640c641041070408070000307612200c03c04035407030325001060389405015030408441204c1d423031802d4a40c000e2003010102c84014151000c14445884110045e9000c1c0000c114a6110303403000221800c061281e43d1401c4816089541445405231460115581021202da8000314072068000b91001c03615142651b544c01d41030245a5050102d00800c1e5040780c0c21450641a80c0700328104c031003081010080340e8580d025a40355000c12020404520f000f540c00003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 702245773 1250 702244523 702244547
    0x1d010509030a0318090b060a0e220903120b0a09092a03030914010804120e1908011a0f010c08281205091905070e090106060f020d020a03 60
    0x4009091406080200303007031800e0050b049001a4209074920521100c540300840036102c1c10740c042100d0801c4d03401142e0b03e4842c0f508054240200d8903503c400c2a0b0b20f62038001c01341d1903180003122109048082d94405054421405c80105951601c8400c003904144505803504800908401040345040001401085610001c1e100180c0d8907201b51002e04d0201d98020100464580c060309481c55420018200406600200031082184400b48010ba91101e24a50000d41159100443d8401c42c0c9003135641121104034190450100b031034131b60000b000d0196030000c48210340001c2c0501500d642031241d81da0003405500b907224101440780e449551107980c0420600348248400d524011104000b41d42c100c0c0070100501d11000085d6000600d42d501201d040e09108480f0000d00c0306050440040d41c8401c80e281c61480742112500081c0c0500804000b124010460000d1103601401d103079a80c40e01030000e5001d03e40200e0308c3d581680c883c0f03500c002a001988202c13a4050289c0d4026a81c1c00c4640f200c1900d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 702247023 1250 702245773 702245777
    0x3060c0e010e043c05010b07020307060305072312090d090503060630030c0703061d06060f0117010e09070b040806011509051e040b0d15090f0c06050a02070f05011d01 73
    0x901340c003c1c5181c09110301c0740a0107107011006d0f12510240304041c030340003042c2c11090405092a00b03100c06c441d00640009150180b0106414480c01516001c1a440c01801600d503450000c54091240e46038000c40d010651803185c0e920109415151300600d81e64640030b0360981e801103040c1c2010407010f000e00c00400c000040181500342800c0c10b1100c4a49560480e0350101c071079800c4a00108100701030740c4254505005540c1d45c200070b5480b81d40c0c0d01911148000d04c0c55006100078030103000680c0c8102280e06179450201514851541c5494000400c0c110840d40403e6500c1a00380c0810f4510020060f1400c840d000002054107030b0030003402ca580c02000360030700001d20007861404110f07503071080c0801e084c02e041707122042450b0147d0401c003c251854070040c580212590b91a01c03020401400c0d000b00381512021000c118010985440b21404404100c05000c485138001c012560b5507100c1e00500214103240c0c02c40300d0310340e161342500031800c4141c030401c0d011424036059031107488164080c490a00c4414 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 702248273 1250 702247023 702247121
    0xc04020c0a020d121803030f03110906070b1b09061b0a12050c07051909022107020304030b22030c02040e0706020c280e1003060c0e010e04 61
    0x7990201d46038042c1a403086800760300a42030310040c5940004604004000c9414001542e461a140581040c00c150880f070304064a030601c90701002a1402111111a0003400241c2c0d6405181000c1462910a44d4075000e600700e80b00c03140900c520400d0668200300001850b442c80c1c1000320700101941003e880c018a00f0f8010b0341046401301d00350301c6042d4000ea00d20784500b5950106070146e20304145481c0c02041c0310341da100f48403d400e14504000303c07062b01c1a031724005a440650503034200c852581e10080c45582c2410104102030b80b0f81c08000b0303004a9114002841c5607450fa00048128040480c059045945660f0401004684130b011050aa180040d1000508010303031356846080180d2600080b0143e40003242c0b40020341008070b100094002541c040641d50310841740c6810342c0082d240710705442c40c030883c00402c03084802e403441c4600030369102c0000c010b180031442000d0020581c507500c4030301083c1d0001e507808a50529001d000c0702c004050003100e07441e0f1484118141c1c01742c5080b40460201000b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 702249523 1250 702248273 702248293
    0x1305010f0903030c0807020f0615010203071202010c080705070203120d09020307150908070f0b03060105131211030d020a08030c09190305160e22060903080901050105120c04020c 78
    0x300344035032600d4600954002c900710300c40210240c4401e0026200d28210b6110500d840303400d0340081010b0343c00a1941105504403403102004030701d580541d4001070314000603800082c960540552000c0c0b01c281d12074684e02027a03528a40107a03010701941001a40540000c848010002d295400074070818040d42e100265403869074000c2842c0501035040700d26418820248070000f20f4101701220001c03c1d07035500500c0c1c20741c2000801403490030350b48100c01c0891804800702e500d6a0240099610f0f000d109107818000660b81c1e8100035000004040c1903038100b8289040404a040100c1c0c849a0202142c00400450710583d40f00640d680c4000e152400f11501800341841c140e031500d4054000022200806003401d046051442c18401d100114608000d03c0d0141000180c0128912030780c4406111107080403d40200501c02c0110b80710440140030314a0404900101500f20b4010750007800080000c001582e00e400500c800d071425402c0c448035a9000d041e006c545441d080c0c000700080940310080d1411105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 702250773 1250 702249523 702249551
    0x614030903250b040b0a050114010207120309120501062903070c030e0307080f0d0309030807050708250c0b1c0b0a05031203070e0f0604050405100806100509060d0209130501 76
    0x10b0079542140c080c031740342007846542c0c481070007020301409524151030029200303000040c3d52516070348910b400720610742c8070301d0050500030801140140b000c88008100032109240840c000c115600421500d0400e4001480e01c0c10102c60110240f0400990007600d1911407410a80301d031450041d003181044641c28000d10740c1d880610000c030003040e5500c01810251400020107007000b000c14100d2042515103140074002c65030002402e50031582605201c0c6d81d85c1098182541c0f240306411001032280c0c01200c6400c005030300c094204564902584010980c0703601c400c911121807040f030744000c5081403802d4107126030310360310b60010014000003010001e91a5940c0c1c0800e0600d02da14041078107040011081202c410340002411807448012541006510150b074000384850045000b11409240d4690015222a6059440e240a08000c60484d0740782e00c1c05e04400c09a002143c0075281c000c140d0200030581c90305103019030080b143d40c020000c05040e640c40b00c07a041d90100449064510359240d03164444604 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 702252023 1250 702250773 702250793
    0x1030f06180c080d1704110d1a01121415150307090f140a0b030d030209040f060f05180f010b0f310e070f110a0219061403090325 57
    0x1101c00d8000c2d000340c21541002a045c09442d40303000081c0c50100080100280703003c03200002d91300045584803110541403c0000c07505034815a5280d07010400300012038601080b488c2100118840c4c0022219000f48542040c0c480d00805503c45d0044000c0c004642e0020204464015202d405012104000c2d82c9103040c02c250303002d50159000441d5140703003184900e01d00300c900340d5210150103001c1c0300d400056400f00341c0d00c07008001d8450825901003270551155a0b19040442100700c110300030712100d0707100c039002c0c0052003051003003a02c00c40244050781311410390703d880d0b98815140806080b400e0b81c40c02e812442c2c0b683c061015010820b9003007055600c07450780200c80d40803001707445507209604105112a5101110150402c0700001503c03410400180d500c101080c295890300c1c6014541d2010f070300c007210300e450f9407003100039801030150b07001e00989000210800100d0390903544800200780c2301c40150485100a0350120201d4000f000710903022035089400c1c1d6100e001100840c880101c0680300d0340d440e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 702253273 1250 702252023 702252029
    0x30c081803071709010e01020a08040614071b0501201c17070e1806030c1909060311040506010305221502030403020114010806190b0612040b0103140601030f06180c 72
    0x3c0080800c1c800c1055900c010703c4489a80280024203a1a089490704182802244615010001e84071981440e101d0b00c502920360f0035600204141b401180c290100c4849d0a03075004560001d200106003600c8552640c003aa0703214450742c0050078038680d0b03030b002006002c041044610284405101034261280c03554240c1c521900b030a036a05400c0007401030820101010354010601491552410b10504da80c0104130844913103001c80300da0a1010752910b4103140c2c00344a0340070701e160740d28098000081c040c0c4c0c0101440011411070382041a41c1c0c4540040d000ca40d0240e8050b60510019a40071000800003010610301c1c43c01a4800070b48403115904441c16a4011141100140d4441a5074020b44404244080c0503000e08000b801103803508840c28040007804507465121540c413803c00d103145807641411a1408203441d2901d0903513141c1418a81f00201e420300c02111604038001d03010070381200124845061742e9214210380c50010054031001c000d0039a82014001e10701100a01c80001f0320016110320003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 702254523 1250 702253273 702253313
    0x30309060316021014150a08030d090303060b130b070c050d080c100e030d0c05041d16020111071112070305071406070203280803010801060f06030c08180307 69
    0x1950710707a54000d007414503c2180018450401c62640140d600502c0046e922a01800701c07041d174070f0800c50028820029940c003030125800b0020300d04415014a1300081803a600a480500901d60790303002800091007070089070400242d02c0a03050294480e004013700d03406d40604040e030305003510313200040c0102800c40e00c202c44c0e8103000a0b00b444541d4040c81454903c607148030080103419440043c040c1c0742d00c40e82034041c90640da650200c0c50841c5c09030040d1409081ca081c400950315590128003024081c046d1052207010000b0340a4450325841405548007502e1000325146c00e10314180e503440300c48000003140030703031241d004000450102c10030007002004601850040c614285044241201030b00e102e44824001c107010081d110250b02c000a134405c22040103011014188543c051400c1070b032040c5500201076139800400020002c0054000303000783c9160040808400340e40c2d1905600f01c50480140308080359413440001d85003890440c4050454462605407441c00109a86941c0f040001000c2c46103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 702255773 1250 702254523 702254551
    0xb01110d0507110301050f15010207091406040615050f03131217060406050f12011104030305091c03080604151503021201080708060f06061306020102070204051b180303090603 77
    0x34072494410403543c000301030b070007008a414203422050135980001c041c3c8075201080da400c000c0c640d1081100100074000c5000810650342c000d09082010841600d61510590a040b00803031002509014811101c0340e548a4514045014540c50a0b0707400041036071a4202903a2094004a001d40c1c91a0071400516500c5404408411010007102d11010305518062843d201d402c0c0038a4130b840701da40d6901c0000b11686852042c0084182e400b600404050b8001d0310000720740081050380020140c0800c10301143c120281c1c507009441040071100a001c043c000420300030104945041a030300894190040500c0c406a2585900300e050545003214502c0c000a540040d03020303403a40441084a02400f28013000e001040c0c13810ba28103903601c5002d000705c10700000c01c402143c42d90741c0319811503400328042c02a0100c400d03a51200071b8000d41085038217901036800d250001c1d90380003031001d042d101140b03200d410a04180f506c95100d6150030b01002540c0d00340c8010004407030b8036511000998420606800300807 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 702257023 1250 702255773 702255787
    0x1f060302120d09081216060902120601080601240f0306090c0909050604110304140114040312050702120f0c010204030209251407030c02030313060f0e031c030b01110d05 74
    0x3c280900d2039220001582100c035061100c01401c0084810841c164601b0300c03d0903900d4180000100f2040800a6006007540000c003403c03280851040d040340d59a038140c507096039941c0500c01c4103401007400c0d114801038205802d11100d000d2142003104503c28600050b03002d4450000314102d0364070860500120300a1001040441101d0107100e40c80075068909000080040c10b000d281400058401000390196202c20a05820258081d0350300910300d080304501e9003042e0a000d403007004881c01ca504843d0034240013036040c2e0300000e480582503c0c012480c0749042960750040866800c1100c45c2c1e01c05540810000002d41da030004507602400e12113151400d044503a0b00f80640000480c0d07040790034461041d101d4069440144141c4000641608020702c80c07441e20700c002030a5201d00350303032108002e5542c000828500d9010a806c04100059100e030300ca13145d540b504140c1d566403c1b5200304207544d40741050149062207500312407001c15041c101082c0704001d000380e6508081c11b81250300002403004c5001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 702258273 1250 702257023 702257027
    0x10b0d020c2e020708030a09080c060a0b01032901120e0703050d03050f01030305040308030a090b2a0405090a1113120204050c030c0723070f0510020105091f060302120d 74
    0x30800d200b01201c04500c3c3c581503544030384080c0402021021085c1e13940b10040284031b144012100e90311840400d4500a2078500d10003c000d1040401160019161184091601e04200154100480d803409010881140100112190100807044040d01c0740c0303d4003200051030080010380b02962080d0058680c0c01342900e4000d04481c0c005061440c1c0b00c54031401000420303044412a0241c81e00100d0041d0ba03a80c440540c180581000000204121201c1d010052050042c41440007c24030011035200c1601e02e07107000d0782090203a1301910b5840801170f0b0100f41328842d1544180c0184000c5400700e4209003004009003c1c2d120140d01200100e0307410814081149400d00c5010340c01401e4050243c00c50501c41c5030341070280a00c0d41c00401c201813942d42d14038085240510049820382070030445245545500f05107400210701e00c01d05004451448500b00414010301130f1030f202d000003100030a0401c4c003a02c8000f44503001c41c00f035420300990b11200800036131281407002003c030201c0380007007014018a400c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 702259523 1250 702258273 702258343
    0x10905101e0503102108040e0f0105040507390503040618060903030c050c090c09120c010c031416060506030c030a02130209041d010507080f0609010b0d020c 69
    0x181010480d0030004c1090039611401c0e03802c03c3e20256622440000000024211542c080000107041c040000c0303070015090500c529040d1040a11007015800782c0d82e280d040c0425144141c1c0c2c41c4010804c0490903d001e800c40540d03100a00b0802c0c551b10b0100d40d8170103010b04030040030110a40f090f420000e802e201407030300714581c2d4160b040e044400c0f00e80f491518a009001510601004082003c0c0d0f0083d2400e0000030001030b501d0f054000c241840b41c1c1084200410942c0c0f01c0039030742d40688074412000d080d2040200b280c50a048040c2c41e000c55000f00c030fa0701202d03003a060340180101840144032960410941c0c01d1a02e200c81d20454000031141040001c140c64802c0303540300203100e82d0101200d9401a2140d5030745a00502c0c201c1800750b20303001c500c0d002501600100d854a1090f016200785601080d50540240c0c0c00340c0090307129101c40b078450080005142d0801c49241d5001a82e00004006980d000b00003004021990800103003010940c0d40d52a080141c001d00c40460054071440d280070080c0244a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 702260773 1250 702259523 702259577
    0x3060f02070b1305030901030218040c021006050d0b01050f1203030a05150619030b1c0f110105030f0f0403110d0903030807170612070b0301060906120513020f01090510 74
    0x520390f040d07554944e503c503540c0c4a04c0c00418105500440c100e0401e0030400507841d80040024003d100d401140003009507101c1210700304442582c280080068942098540c21802c0ca070003801d880702a078200014080780b001c84003002ca0300703d18a05a2001440014000745008052400300812142003120000e00704114400d1a207100705010804c1410f4204060f200c44c1e80d45a00c0d0501081d030f0a820f0001500c2e808101c5089825000c42e0f06107001040500301054200d00d2098007820075a0381800011902030104a0307104240d480078601154020280c0d00c20705a0040c880d140c04900901044915824070604650001c046240c040301441010741102071198001114070742070301c40d403a0710b441a41500713401904840c0070b0003094640000d8018180b201c04040c0410580c86a42ca59603040d00400481d40d0307100b0080010725405140360b22203924014030f80510f6039442c103004403660741d400b001010710785502c1281c1403240d1070200064540710040b449400c2c0c0c6054884100617000400484c030b1000d0040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 702262023 1250 702260773 702260791
    0x50a11100f0e1e031002030a1803170c0f07050c03100e0307031b0b242d0d141f140708040c03080f0702120a02060a0309020a03060f02070b 61
    0x1807031481607a4003211a040c003000c21501c0c403410300c915950218903c48004006038240c003584003200103e024640040d0300901c2143c60821070022841d041c0000500315860040004809400c4206e59100b40c00101e40c114034441151450040294000c80701548402803c9032141c110030b45001c41441c0602000509880c000000e0110009940c5041c6e1644034105004083c02074050329140c2d50286001c5112805078011040072031818041684094509400001100d280102caa541000c0c1880c3d021035a100d008045480c2017210b18958120b04038019203001d03134114074200400c6010811441448207060340f100c02030b00d02c0c044030b455034242d0400c3c003107401c0e00e074242420043d0300b48060340100e85503c00881d103402e80b03a54965152000031424950300c00790002802050f070b21165000380009050071482120032692101c0d15203045034451a030064003a510a1080c00311301c2107140690043e0807120b10007464100c00c0c540303e43d203800072100156007116010390b011070308804110120068130340100e281 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 702263273 1250 702262023 702262037
    0x20d030b0114070309181b0c050a20180109150f03030c032007060e190603020f04170109030e0303070f03050d02120f070f03020a02070b09030a050a1110 67
    0x480c0007a1aa4108030020403807088001615414544103a040502410161190301144c0250b000980c000d00310018999151240c40070b03040e071125008600440816a101c00030b8510b52041d51280c02208202480e40303c1c0e0b180207071030f1a100b03d54694010012410044c0e51f04545541041c0d010021150040e0207080c00d40400002440000c6440d02d508048076810b107098000c0741e03450326044400c5c41058610303440c6000000e10385496480d01140d80c8041d68980d50701c0e000d80ca10752004104a4079409403141a045400400a1090a1280d0014110480b80b00d004501e46683c4600f02d40ea1110302c40711400c200d13592070b01c0e07400826900101c0080e1301c400c1100114144010758a58024055412030000d0a01c1000203e801c41c58040750107940840e800154941d15500d00a030060203800707000c44e944030006d60040c80c81c940c043d01034400c0d90388044069009200301d6060080b504e805510060040360301d032040011800c001802042003198551065900c8161050300742c052080c8a20315000e000c2c244018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 702264523 1250 702263273 702263291
    0xa0912050a0b0c0403170c010209060f04090f05041104150810061401020c0928020d0906051008070b031f06020a0501060602010c0f08040f02060a02010e1b010f051b03040f06020d03 79
    0x125040001b041c000041d8540eaa4440a44050080c400d190700c080e089100842d071780f05075101ca1030142044a070124418070044e5800c0c1c1c2034004640049034000c0c0000b8809200340440d040c07a511000701c0c001e0f4111155100e50b1035442c1d203803414846c442700002068462200303200008a01c1c41f44110002c0c01e00040650140c110b000403110071005248608201941380100c500d034000c51800341d8503d1070010215610035407020801e0140c01c004000740c1c0d405080c0404941c10f141c80140c04c40880d49002c000c0c04c1c4003030401c81c0d1441294005002d8010303669441a0119440649403107040c010021034000b865120501d00d4441c0c00e4600c0d0347e016030250392600d400303da501038010342581c445a0861908415075a01e52030a116624007602c0085d4001d4030204030000c0e125015440059101b001008440d8144603804407021074008003882d8600203a40030403407400c0240240043c0c0038001d04079201702d120385041d106103441c540040c5e0000b1f18034076500310104800b940502460303c48074504d00d428425048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 702265773 1250 702264523 702264533
    0x910060b0a0c081606020a091409040c0527070216240c151103060a0b070804060810080609030a080a05091b010306270c08011404020a0912050a0b0c0403 67
    0x111950041d09190303001131510312000c0503090000750154030820454550409450040c200d80a074050645050b00641c0402c40700c1c94080b20b0140300e503034080b50b41810282400d0a00c00c03c07102455409041e00e000d010400030710a18091076a1040c0d005500030305040380041e0a03401c0043d8580d008030301201000701c00c809126814040d265114070641000e5416a40b00d16004c4807500c852169203401c1c501e425402c02c407240300c8000840c0100000c075000b00d2201d44483c0d6140c03041c45034084c02003aa01080100b002558010051a0303404a03891400a06240e6910f8005061170000c54074101075410005880342d039180c2045406800031051441000b15103802c22a181c1c1c4c07000e0391062220f4840e208074001c1720581c03182d0460005015640090340c2d002c80d45000c052400b10100d100b40710043d060510000320b540c45034040070f0480701c0134030031117500701030103024000207500c64850201002418640401d108919110b083d02ccc00e03100b1001800001c0c43c038202546076000140801d01000010003003000815 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 702267023 1250 702265773 702265787
    0xb01030c08090c1905040f1506031118060405100806090c0315211015081c080408070c030503090405011a0a0302031e0c1905040b120603070e0910060b0a 67
    0xc0400d13540b1941d481892000044c020200da84802e5204c3c0c28090a90148080741d04200c0208070000d040410300344d11075106400740d890380e80e045000c10f00240143e1694a0760110421b0050501500681c5070070340f6400841c403001404c442e40303408120b1490030700449080400a49070301c0180c000349070781541003e60344849803808098036107100340101032940c0140108000d003142184607110864014040d880040000f500310b49800e0b0075040c8a4040c0000c42d03000209107000c1100f005102200c01f103e9404040e181d01c2406001900d20780801d00425000441075140b40700070f0340c054001980c59403040020042500e005800010762400c1c0007401e074800d0240c0009441c0c0d800110304015849035900c42c42150222400c800490400e0340d02d0003403061510b20003008048124100d110062801d11010081d2120300c42d9201d2640d01c2181005080c5000b251020001d4014400400344e03400039a64884039000c005082e9507546607a0450403480652542da4891003000384124848582008101c11000c1e00c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 702268273 1250 702267023 702267043
    0x1406040603020a021203090c010e120607050a020709090b15180105100203130b0714030c030304061e050c0414010305010302060f21070906120b150c01110d0b01030c0809 74
    0x7054000c5103620082e80240059421085084070040d00c1e80761070340b0071560303880b0220041804182d2410105606080c00b4000da45004135040082c0a1500c500b001201e180d8040071103041140a09200411590001d005480c00a80207503544110784c00d14840e4074010680c006240d034032483e0150b583c044c82030402039000b41181da040320f0303250413011144c9090f410352241540b9040b042c80d20b0000441e8a03602000909102d50103140d1000f0082c1e2441c04680d038138403070400c01e034825038001d000090001d0701c01c0d0404500d10700e104175600e100c401c1602c2c0450aa44040d600c600c4941c2001c01c0c1402000d5041c03080c1c1031011000d203018051540365401150062007082c600c54500e0000003880c400f101070209101a60001a40f404e904a1030701840051130440740b4000c0b940015901280560720400310700441d01c0380c550080003007010300f501500084040c0e010a80c03181c000d5490726003688440031170001809040440c281d002c10540140c00004044490b00f002c55024004141c00788910542e00007041000303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 702269523 1250 702268273 702268277
    0x60f060e060607240f02040f150207080705100c05060708191e09060608030d0504110409110909010605220509011116030c0602070609050c060a050f0f0705010e03031014060406 77
    0x69500d1001c9134000780c076180900803692800028009818a00c1600800486401d03030300403003080d40c81f41c3c0c0072a00c500c1e080c0316a414176845040d042c0301a02d0124101518440c035810005000750660742c40034104442180c810000c00d105a08218a4414041c4d80c40e100306130001c02044014481000101044001903211080e20b6460b95a401084120361210014214038012251074444500020004e03150450382122840c0b00e20000e00c0542c04c160180c0740740c0d154051304c0340d204450a0300a11032401001001e00807190340312500002e998807016040038040003000c0512101c0d40e80043d03000b007036032406045070300180c0c074084090708001599800d48241402c090b051506a0249007001c0b184281c1c4103402070416440002c881081040d1940f151007040d00c944107403510000080100440c601179003031640007060342002074062114810000b08966a21212002d003803581a4503810f0841c1d401104044140d8000420301580300012240500100125000b03070506070b0131800801e159025a1084c002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 702270773 1250 702269523 702269573
    0xc03070c090b0906060f0d05040507031a18030f091003200c280f0c050613050405091b01110a050601080703030908010207030509011101020d110d060602120306010f050403060f060e060607 82
    0x1001003e00c02f1074000d40e04000c46030002d0341d0440c03811111400558045840a050208110152002009903101e810301071a4460810241d0070900c5034140c4c41c0d44000c000c060b80c402074803424001d1826001c4140889a901c0364803640350452992611010341c9604003500e0b0b0206049402503110410305801d250b214a8020f46401c5600d001c0d05840101e41295500c40d0000c142586c540801405d00b001300c84045a09000e241c40d079400c05625540d00414a02a078203031000c050040e54090333480e60403039112210031600c1c1d0006a46599080c81804e82105290b41c00440c410401d05500182503800307001a00000c5150100c40d582c047c0980c842e50791000e05114406402d10b07000c400c298143d540503183c6003024029445081d00d00b000513440b4508401c801407820318045107003032001421400005002100e5480c5803102c20040d10a501c2c2c0900b0b12007000320070840480014114010404401081440401c0c5242041c1e100280c40100915080c011031040c08010049103810700c29580800d55990456 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 702272023 1250 702270773 702270781
    0x110d0c050703080a1214150105120619090e010c03060506091003020c03090a0b0c0c0306070c260c0a120f05031b040b0c030a03051522020d1a03012f0c03070c090b0906060f0d05 77
    0x133158089541e02c4145114600b0011031030003c010340040b000c2402d180d40801246458008215850058101041d08240c0180000038414025402004c1c0195098100e03801d12440c8000148a51a540c020b0310750f800d000310f2040d10a42042100b00032043c800c40213080c0c00d14050000514203460314801404443c0c114400c02400b54186013400840d8145882d12555005080313081592040e0140c012a81d42210401c60f00d501c9205101c1c01c0010340050740e80a10b503403101c2c80f80016185200d0020041c5207010400040c1c0300c2c410100604c4007001da07002545c0c80d441002c50140c11540d009142c3c03166070009003000d65255951001c2075070954a1200307400202401d034025000240104401003100501d01400c6248980050440c001c080d10100c00a00403801d40d102c12a10303d052604505e8031b00301c6007442c181004040f03400980f40031b4090104507810002c50351550030340708126034010301107281d58024520450600701755040e8454429503030145026050711096034244500055040c600b42d5550201e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 702273273 1250 702272023 702272059
    0x1109061c03022b080406090f0c06020604031e051605011103040308090606030a230f12070507080c0319030203130b0d0c1812030c080a110d0c050703080a12141501051206 74
    0x700c0c0d0001c9e00803c0c0e05403600c60107599802c0c191402c5c0c010406240040504c8041c42c0d4480e40208010b03074402c0d042c6410160080da6844030f2001c100c0d4a03540781e4000002102040016610441c0665a0701d0098200102201c1c20f09074041c04950281d0010242e00010034110505202c0705039412500c0b0302d0b100c184e80305041c2003c0302c40403110303a94003404154038044031a40c0040c100c2c0300c0c010001d5440080d074402520b55182021030380d103505038001c91680311480216143c4440300340d000740150b0b03160001c08030001c00840c01d40d4125030030840000c030305407103c41d00e113214007007900342e00d403c0102c08010500e041c607400d241644951424804071500b99070400d841020300a50140c1d0056000c4c0d112590040c1c00b0705102c1c441054450b00b84941c0d5607400c2880e1241206041a64001024129160035038a0303810a40e880440300301d0a01801110103200c0f5a03140c172490758075045110080b0403505240e290f0302c0e5400440020759041010038480303003000848803040c481e00034000b203a120048804108030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 702274523 1250 702273273 702273293
    0x1080307031d04050703020a020c190303270306060e010b1e09010c0204020f03011e1a0310170606030106050f1c050a02060307030603020f0d1109061c03022b08040609 73
    0x341508142801c0c14020006c0d0190054500010a602a0303510300030107a040c454000d0356010b1006d0302c0c210030001040481d016a040000540c402603c11601c00107805c5041510406903000300c03101d6030356410410074084080710103800350403071803000d071f1810400c4010b4a00451501c010b024142d2800034080710f842e03000d0b0394001055640500207644846134440780045a130070910914001918400d00c0b4044080e10449000503200a0205250b000000050943e45c80d00300414031140311001010110392524222083c4558104800007406241b4040d001d0600350703081035100c5400b40c0528960315815690b00314801c1c0c14080000181d8000c139102d82009071402d9103280001e900f102000040c004c6e0643e06404c82c0040e00e00075200c4894001401040c4030618142140190000541c14182c01d05440c2030038000b5007094004108001c80220410921070740b522180080340940d00601d20700c81152208000002c1c00b11102c100c44020341004003016192910041000700706d10790303599190303041000082e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 702275773 1250 702274523 702274577
    0xb1e090303150f1309020f0306010501021c09050d06050a0609020301080316050106090e030706180218190221160f0f05040902030c0301081e1c050403140c1201050108030703 76
    0xc2000036040d621404d80c0d00030300b06a04243e0051030900308503007180c180000c1031030403100c06038020290024850124924108090a1001005910000055943c2d200a24000706030700449002603182800c2d0440d5049600a03072100c8800b41c01840100012100401030319101c1d6040741c0b00b900b284491307140182c018006500300004403071410700e244000c62000000760540c103110310010415178a4003c03041d041e203488258001d40c01820b01080203011203030302c41c10542022a4a0b520009004442c42c8101a600130540400e4180c02000742d1480100d0403454142c3c200c0c0290125041c01201d401000b485280502c3e02e1031700b1301030340c00c5c403004845104104580c003c100d4030408546030b04241c01d1250080e0320030b2040784d80521543c2d198400d103101d00c400d10b054007494103004041c0b80c05010200604a0b03901c2a0980600005100000204046c0c480c0702c0c05900d0f25074060b01c0038201c2c031010010304c00d850624966440c1e01d003000500c42094000b04913103d1507018107000501030880000c042440010f81 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 702277023 1250 702275773 702275779
    0x8010b0c0115140307061704290c190e0310020903030d090c15050c060f0601020f07090603021906050a03020d270b13020306010302060a0903050601030b1e090303150f 73
    0x490000343d00458103c14501120110155503400f0750b01c0c041140c1d9416101000054021140b0116001a504007014240701203104002c4100c00c000d4100554110021185c201c0b4022001a0014100c0c41c8810284040010350601603054002100801d654a0307118020110580d070008000307450355020410b45640c018007040034031803071003140f80c060001003440c803d01c00103451050413140e01038010805e80b0103144c640320003010f26039110b8045e0b003030841000d049541540100c1c0040304000d001886185d02030659900003060071403a500c10702c401d081c60311044820541d010401413101c0fa5111044071100c181350315015807601c001e181c5245c000c0501c9031010100e03410843d902e640ea20b41c1c400c41d070340070503028441c02c2c0555a0f400341800039610000030000d6150300004c0041c8010700d03159000e0800302c07501c2c0c60254000342d02d81d5203007442d240c806e8001b135030901d806000300f10303100c0d4941a04001c0b1140d022024402418440c0d242590fa020161118842c45e0409805541030740fa0b41d43d074101d4552000b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 702278273 1250 702277023 702277061
    0x618070309030206070302031303211812030c051602030c0a0e0712110d09080f1b0f0a031d030f1603050f03210406140106120e060708010b0c01 63
    0x424000d4010150303078008902500509001901c01c034020f2007681e00c6044040001d5080001945d030880b802e40300c48900d0184c018043c00e446d0703c0982c039403158280020030b00150658140e442d04120b42c840030080252070405050031400c891080e070050564400341c840109414402e002c034030010b818141c195401da5040400b65100060090719194214026402a00c0d003c00700032180f55002c0a5035034503108104160301c00c202907241803c184e4003021800d0300230500700b0f00340203851a540d109c40d80b0a0242a86900003408040d900e100184601840700c0103034001044106407607540035000703603640440c48680d071814414031a0346840a01161a0b0301c5040b000742e511040f02c48000030b40c04085804207a40d00e2103040c0c0702d06c020315000012124101031031101d099280f0520b0899007202103004104544c1c1540707401105030141420b0159501a0880391a81c0e03861100c84800141124041584580c43d9400305040c030422542210b0a0f505440003961055614401c01051030f0142104c40e031060704940304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 702279523 1250 702278273 702278281
    0xa17150403080f07080402031b0103090f03020c1c021309060f1415010c111912080d0b040c23070209010308040f0f0e0a0b0a15090305070501050711090618 68
    0x4010070b042d00c03602548210440f151150703038040b0307801ca500303c030002c6d0503500c408404132111706002d00f55082200705140106040c0030075540d140d03001002840840240e806806441554502810072030f0000805600041000420f90000369101d10090880c10100344e96040050074861603822020184808800a0040901070058444107520403194044805e4034010b41c24801e41c850400410415040301c1c40c950b003260001c0401183c1c07881403509a011900307103140000c820074400f008140c0d4a004d200074613205e4543c0ea034880c050300e2001e100701d80b0540c940301058401603081040f0a4071000151855078489801404418861042e0b08010790710084d103000000404c00c84030007e00566441c0501c10350110345e1076030b003012902c1b154054050800100400600003050607400108100001403540c8885139403038405071600b50350551007800081c02200b0a000317000c81081580000c107020701c2c00ca40380051070345540d91011203891683c4d100e1124000858a155034101001c002d00c088820700280a0034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 702280773 1250 702279523 702279527
    0x1119050a0e121528240905070801051507030c141209040b0102070302010903110303040332030f0d0e070e010e070f02061b07150213080115050a17150403 67
    0x2d1071200e501001d03011000041c1280c2801c01044000155100f86485104446a005406000c02c030415407114a801e170200c800911a15203034000410007000d0000c0e0b2400d100c40c0080408270141c04c401e00920096000c41c001c80d41d00b404071900c564051030050901d442900d0a00310b081515280740040f48501c0c0494900d122400004010071a81280d040100d00146801680c0703402c0079100c042d01090b00c01c04200080340c011040702d0138008006041d02d02d040d031603680e0140d690fa100c40401212058035030491135101a440c2400000fa4115801542400c0060307056001f5440364094070b550454940f410452070230001c00c1500301620700301c0051044d0303686505840741507a8040b6450000a0401e580280b041800030403030600800145412418260000800021039800341008942c501e040d042c42a24402007880517003603a10400c010311072800e01e049202820340b040031120000981d90424100104d545900070f8004445c2c2d032a80504980008014903810a21502910702c100c900600130801096 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 702282023 1250 702280773 702280783
    0x12020115080d090f030c05091810141e07030905030c01020a020309090a060b071e020306090d090e060f0f030f3009031f0b060408030a02011119050a0e12 67
    0x10718180d60307050f0000d80d15140010120b0342c40c40094903540320340c03a080c4000d040c503881c2c05901c13601001d009403108035003a00031850080c804400b0480305030b50380c0850303032000c0103000c90300d070803001e64030804414045140301d54403141c3d00a845001810b9403040c002c03040100500c00d0f0355034601c0305002151900280c8a01940301c0d807001342581d10032080c41d000036900400c0d9110340405e4940045040f81450415901c50007144030a80796032505044181d000c0005940400c0b80038403e80c0c8410240141c119860000f07408084160000b0080a00070020444c00d034580460540c501d542c21101039501c4080b42010a04000303540c86011698014100f14440240f9271410010314002040d50882200c414000301c1c85a5000e010b01060741600541184524480048450300c0425440000050200000000151941e0090b070042441c0d81001c81e4130b400300c0e6020312a11080c4140d61052a240240c18503414110a80042c83c81040c4080402d4000741e26110700c4480c0248075020340402020201c083c1a02d0f40c507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 702283273 1250 702282023 702282043
    0xb19080303010e2211010516060e0f0a0b060d1a0705030402030d051c1505060c06180708100e030d06060c0204060b0a050d050c0702030a12030608060705071202011508 73
    0x20303140c00400b0410010794000001340c102000c6240030202c0380b5940d204201505803518160400c039080c00041992030b0b010300034510f201d1089500041c1e14412414440c200340607034000c1e80c85904404c0300540415210002503a220034111280546041d03a8500300c20300402003441e491040900c0300400c009580c01100a41c09540218126800b5940d500300c210354038803038a1a50345480715207041c5440d143c101d54012051007070070300b8440300b0619140c0700803c0c0a0740240001d2200c0f035200c60103102d500d070109098001d8600d0b03858040c0c4101428410000d40c0e402e103114241c0101c03075440c103116280d103405009980358200300040510103e0b80d9800008c06180c41d003107090f031065140c48400030b4600d0321842103c022401a88030030342403001a04004005010051406200032401c0110800582d0240004110b040c07103109420042c11401600a084540c0c942000003182d01c8502800f0250b5002800c0c0d440c100e40c803102c007800c410700b1148128058250301d2000c500c116581a004074004002007914a00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 702284523 1250 702283273 702283289
    0x10213150915140304030e04050a0f1104030f12090f0f05030f072114340305030306041a0d03031d1209010f09031b0609270b1908030301 60
    0x39542c40d21104481c4426030300c501030101c1c115201000d0b00300c44960245500c5406410125108411007012605940086480380140e039620600d107140300044e0300c162000c00d025040820700b0075045a0781c5d0307940280304000180c02450b10605a29009100381c19a0001d082c0350002c88903015030341c00d02a050607115014030761081c000e016605506d00c03030005244046501c05803280420728400d805599080002ca4829101440c400c000901402401c020b00d009160a0b054500c0350f0500011040c05c40e1514903804100011050808001240f0000240c07074001208684c0010007154035080828040b02c001c42d4107411020444542091503010743c02207008001c0041d810081c00d45501d803151319030304103242810240c603042c84500c80c51351040110515040700c81c10302c012000c1c0c803902c0c0e1100008041400c60318090703c180701070200300c0d80510b03200010008229021096132140c04c002c60180000b0303440c0c003800356a403400754589a44001048849048007400c10100030b031a04112a1207074824069040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 702285773 1250 702284523 702284537
    0x30c0417011416090501050f1209070311030f0318041d010b0a05030a05030313060b0616030f21090302010209060705070807240e01020a02130209040b0a05030d05090301021315 77
    0x50201101c1400c550b44030303400e81c4d07040501c42c100b200669050300850030100e500d0b074040c440c601001d0b40740e100c1140204030f10001001020b10314500341d005208640321181c0640c1000b215048080c5001003581c600001c10781d2500c0704c50041d0381c0031400a14015449141c400010354846450540650209107081026500861421b4964040c140e8520389101c0041041d0300400010350070710982c071075802c0d00340d00c12880450303a035a8000001c1c03d5074000f8200b032049610030aa6035410940c000220684071038013410301e9868260300010001c1280c030f41c081c14405a40c4c0b920105010035100794110782801d10002c0a6588943c940c2c200580d81d421a07000c0c0303902c07a110b08800843c50034a042000d42c0ca001650031860325840300b11300e0403140c0b00780b2440c0d42d074154415807040740c3c0142e07550405501e41191000d0300588460150b0208420740b040110800c0c0106040d200c144081d46000c00c0f408080001405c1c196985c290b203501081c020310802d25080201e9041e81400700f03600e0343d0900140c0c800049656402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 702287023 1250 702285773 702285781
    0x10e011d0f0601020a082b062d030614010f06031b0f021c0315090605030618010e0304060c05010b010309030905040902060403020a14011412161b1103010f060515030c04170114 77
    0x20708480e00390041c0b5803596000c1800806103212740801c0f81501070034140281b20240d4956032401991000103092049000c030720010300070340d0b06581e08103004140382d2a06001030701d0360b08050041550f1070141c45040000010081e001c59008004503410312007105065845150140c80040c0140140300d84400c0b818101040041d1000d154010752043c1c9400801412403a280c0340841c1c52805c81200d08101e00c0e54a900388828a00d0301030020304001d162584980740503600500d070072421944040c03582030516150040308404070341e20606031401c0e15000c0d6400500720640e8000030700e03540601d40c4025803020000c000458004a0004a2031041c02c00781c0328146012034203003d00340c0901510a0030305200242c50005001c900140102c2e00c0700c00340d00c1c188094990028170341d5040f085200b00d000e88800349442080f24103800c0902c00c080444a01050400c03419091100003503038100c83c40e040603211070012020801001c1c692088cc0c00402c00070b005003044640070314070180a010504035101c18034044100103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 702288273 1250 702287023 702287107
    0x51606121a0a06052a0109060b01021506061b030f2101061d010c12030c0915050d020306030c0d12020d050c0a0b1b070b010e011d0f0601020a08 63
    0x180c0d40c20078002e19584a40d0b00b040c8003100c09030040c40e226035411506003905c0c0e4070f036844c1c5403c040050360f00c0800811103007034038108003068886c0020658119884821801d00f90945a03050b5508030408441c065503030554210390240c0100c500100000c85d000008640010743c000400901c288012f04e03052641c84121003202c2c1c50010001d01c21000400c2c1d041000e403081c6000d800d6002e845210506001d210100c0b90307119401203d016804210200ea52400002c1304143c000c480c020040c40c48039a10180143c2235240249207018084800d0052078004c0041150781d542801a41000c203c0a84144080d1410f404c003036005541c0b414803080980540c1e0054801148207000301c0302e65030301c0e03c17005103041c201e82d0780c6042505a0041143d4030345158101105007d208120081520078001c500c02441c5c0d50405018a210480607400003046102e141d82c170f9200c1c023074500c1480758404195844442c8640c0c03a000144c1c244540410010181840010003130921406260540706003e8044031110344071040380c100c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 702289523 1250 702288273 702288311
    0x7030605010c0303110409050a0f06080606031906110f0d0506190302010f0306050913020108060f030a17070203120d1b021f0b1002010b1201180f05160612 68
    0xc69000400b01c403601e2010070b000790008548020345042e02031800f90b440e041c40c41101d005585c01c0d55140d80f10382000d45e004003140250805005c800300500303900d040100c0004da84180812810000603c0c408140c000e10605030b0004d1200b0075600c07021035841007565021022036008000000e0010714201c0801d010f802c09030300090007200100c200403840c90550f0015038100180e0b81e4000d0405444020214640d2614144680110400c407001842c2141c0c920001d44555001002c07280541c101d100507150316600040c08031b094036041011007004641110000303015210340d40000c0c1d0907124102420b240b91100c4030040c556560129802c000804449441003100380004440000680c050f84031120420000000120060212040081c4170034440002c15100c01055107042c0150b55500b07031400260805590b00119003260034000c010030034107040c41b4002043d55500182c4038030103c2c10b004080080402c02d041802861703442016040c1e980d040c0c0240200c0b941d00161580d5800c010b110201c207064806 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 702290773 1250 702289523 702289529
    0xa0c03121404230f161d1305070b12010e0f040b0a0506040e0a12020111040e070f12050405010e0706091d06010e10020a03090f03021f030b1c020306070306 68
    0x4441c0310645440d16186040b0500c007052014940071640ea1807101003081000b001c00340c4400c0050303c0c880d0410b800075402c3c1d400c03da11800d2001100301203184007900c103000d00c0c1d0703001d0110002e0103407400342c1381802e03480e103001c0c1e0b04001007200b00060b901c4c0b0104040348216040350080c11a071051031382c40c0e00c609000c120050314000d24401d19180490341d8031805030807480d4000c0020300009020b03008800e24528204006106aa04254160800c0c48007542805007545504802c008149003a1600e60000b1031a840148024104040ca048403507901d4440c106149151030502c000b4805400d041c00c199009040e84c0c0c126001c42d126501001a044e8010300001044405c00305001690780000981d200c40c00700001e0145040200c950005c11f000c3d43e074500c9005124034207a00501c0400d201d450090290b8116810a0781024040c9000b000161742c3c5514260302020b50000010441443d0507040c0c0140034480c50103a40500d410036903d510840c44002621158001c404990094498003016021242940 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 702292023 1250 702290773 702290801
    0x1903141005090604180b04020103240801050606190e06040504020720010e0a051212070c09060b090d02130f06080c0f0405010602280c090204061d130b0609060a0c0312 73
    0x405d01d00f0204072883d907a1640580181804102c0c941501600101c0e1408820302c0b0408148100c81406454401d2280ca0fa10142c140c070120324103c20f8090310048404140d10920410003000004030458a030300342030b60014003000e0000d64480c6194030700404061604d0394034811050040700030080940c0300e01803802d0300c801c025002108990901c03040c05188080d0310380c40b40844c4901d0003182c5d480480c1c180140714a0340241205846a820000b1150550784030b6032100c1c1918500f03010b00011565002892248543c1c11a920075642007181d4041d4054200d1915800c0140e1a09200086c61000450424034400e0100c59601c080c840840c200310441c0c234280900d50060b0303c01d19030300e12040400b00c0c1c6d400445021500c8081c0b00e007890b944004075101030b9008815525000b00c0d00300308864008200c03020003040d0855880c0c02c104000040b6141c90f0542c068940d216031502c2022880d40c94410441c0c0400d40040e0a0990350304900d9809851504004004c0780011080e000b4140c140c1c0003849a40c101610030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 702293273 1250 702292023 702292061
    0xf120f0d1410080115060917120a0e100804210e031f0b0105070510020708070c0603090b07170f06010c0b0903040f120804030201050a05040503010c0c150b061903141005090604 77
    0x1029103001e089180c85a4030b0420301c55984080b5081d04900050185800141e8803cbd040081210070301405807000d510045c00d005e02102840001a062600f2b09581b00328004881d0080031481002c840e0003040103091030b098050f0300d42058851084d40640c204041e5010f03001e0100c02c1c0350a00450351441010350240a81d0070200c0c00400111140d0002c18030a030140b6200c5041c85843e40311142c1e001f0342c550000f00400d607a10300b004104504015078951000c0c5a0400310558641c1d201c8558019100412803400440400000382c1540e0140340c040e16842d40150300311602d0301c1c2010f081a500d500c1809208951098a0030000d41411003240301d0441d81d9101d44103d0070185103a00554842c1c114518084c10b1040500001c250341e00e0034412825a00356541d504100541142007241c0700382d180c20f45224829082c0740081c0241d031100c1f0b00716038500180c240300b080d08007802c6404034004c10601000600c0025401d00b480903400180010a0589008941000031520341004100c2141d0142804120442030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 702294523 1250 702293273 702293279
    0xc0c1b091107200612010b090a060c0b0a15090603030302030910090f06090204060909060506040518120f07050d0f120204030201081f0510020109050f120f0d14100801150609 76
    0x250f181d581c003c5000b410540c24800d484001c2a180c40f001d03002000690400f11300355056190500600d4002d041e5414500380b01c0b2801e071a40100844010200a0340381e460b05542406d032140c2d00daaa40040c6904102000000c3d143e1500a010f9401650340310a0b078031610350b1990004403035102c0c04041d00c1d88810103282c000326980e20b41d0041c0201c0f1009a03841940c0380b20008028501e03025032000544104c50019076440d00d0400c20040701c0e1f0144c03241c0c1c07580b2200f1103100c1c0108400148104180c4215008940310840c6030101c20345842001030003061390090358000703102140c2101500e100342c425600c40041c400c50720700c40b0384124041c0d403101900040c68003020501d40e0062481c618100c8404100c464610b54442c0003081c403050300c00100d240141c0d5901803200901105020a041c41004035001e0803810b1102c041c040214010f0442821510038009040500004a030b849800c0410b0800c840c0245c602e08152174007100b2140e0b108460195080046101062040b95440029111151203e104640c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 702295773 1250 702294523 702294563
    0x503071b0c09050405010c11060a02071401020703030501050114030c090d03031503080d150302030a081b010903120501290a0e130603051905030d0c0c1b091107 70
    0x448410000084011244010464040c201009410b105601241c14281403402c60f00311070342180d440041044aa8802000000102d01c40da000400c003000542c4500050400340e194020f2000b1408843d84001194401c05415410040c101c410903290035000b8000007545840d01e22081f41e500030607003420444443c0504d00400f142d08c03001c2c024600001c91121a0982c0001a01250800da87c1175201049501c4006400d0040c032214480d1144e0900c034207403550b40440e07031720b8404401c02024114003049000d0303880400300c10700340e610301070724001d21040c1c2d07203424044c142c0c000400a001c0c070a42082d00105d0380306200145100004900c04003031b45003980c40301480320940c0016248070b040150300c00c81c41c03010742d98040442410501e0254005a010320790302d8030605d0407030840035001d401d11405650308046100841918415212a103020a03903541c0c107081180c0440955a0082c020f078048198100701d180401408800e403142e20b4000c0285e0040d088442c0d180b8003551400402440300d4008950140d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 702297023 1250 702295773 702295787
    0x12030a090309030813170102090a05090a020c161e060219151e06080a0b070509060f0a0c061a0d1415181b0f0d24020403030e060a050307 60
    0x103400780c58910341d031586070360381c00649078030910305c144140742650710a000b000320100d400d408500b6280000c41c030f09034501000c110a1240c6104603445002524002200740740290122a1000c0481068849445454130050751901041c01100c00b0381d4804900d00204800040701c01082c1c444c036400420711400e044a84602940c6903110441d5070860f508010110040b46004803040b00300c811440801142c0c000c0b100c04c0450b84164050120355000b8683d04000c240d041d0740e92604141c880c42c2181e03071400721101041d0240f0a9614111100c0c8002640d440c440d50300c0300700107a50390312844091152103044503410584442c0e03032480c0c075031000d9407072402c03c0001d0031180d003410a20320140070340313071422201c01341200840012500c047e40c60324000340c0425074086c14800c2803a20384181382d036488440000004254404c1242d04584e005107810078180c810701401c51070300041503554410341c24484211030902e0b4080e412521044012074215510808103281140c10b85101c9030b05a90303142d041d56245241100c0703217 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 702298273 1250 702297023 702297041
    0x403060209130c0c050f060c1e040302060d090620040504180c0602030316031802010302160b0c0915030915040f08031612020702010f0e011403090109120212030a 71
    0x403200654611024590b18000e140100000b6103d05200c3e25003414114104188074111009641044040041030316800342980c2c02d94007402584405803004821051503482030b070b00080c1d4440070125440a50414940040b498a48201ba080c0b19020503000f01c13031480010740c96841010941444107115a040c154040360884581841d07010b0600315503100c94601c4161500024016000002045149030b1a240085400440382c6010030020440c1601c400c0c00c1c00030104000d04150300064080c5503100341c100180700460300281c100324603040649240c0456402a500b140c0100103000c0801150f458103800e6034416085000035003c1c02800540380803204000800448062001d80704034000702e041400a14805d504a0044250078460311901810101007120407440c054010001c080050f603000220f07011241e202e003408182c4c01c2c40440142c410300d005696010300d044002c01003080344441508010185400740c8450600d07154400e604a031036000008081403080030801c0440e072118a150710100391 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 702299523 1250 702298273 702298279
    0xf03310206090f0d050a03020c010f09060e270a0606050c0a0f050f03071217040f03030504080903030a120515091b0906030f040c08030a0909020f04080d090e010b0304080403060209 79
    0x420b41078002030340c09014050107503170903800441d40400709501003200318041a02402c0c81c0c141c0f10001c50004245401c0c82c01010f04000d0100c0d0350710307500d464034621041c89c100e03c2d85011103460762141d03404a070103104072024a440c90401c01c2c002102d0340128210740b43c04c140b1602030514104542c0750f0710000c00c11660b04807150700c1030300b01c0402411400c1c030180228038800e0b2000c102d0035400c0f080040c10017501c14000341841c8108010b0000041a03079520109803a414100850749039180c1c18001594018800c540780c1602001079009203030396202581180f4205051010405a268014511210000c49190b5504951140046840305024024403440d410010304280e02d82114100403400c16007042d19851400d43c0310b041404104142855201c006d4250600114200142d410b0010406801c5200d05015540c0c00101c01c060380341c500c03003101c0150108208440d5105400b4800a140c200c80d1b1188030348500c0701e00b002080e50b11211044038000ea40007400c00b13091a041d600d444009600c8074a2640c1c4c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 702300773 1250 702299523 702299539
    0x150603270203161203030b03011e051f0611010e030307050306060c0c0301060b041d04020105250f0524060102070605090315010b0315090f2206020f0331020609 70
    0x4688580c3d40003400240c051558100401410303407a000c4c041e0381014002074031070707410300c4c203007c00e2822020700d0f240d0701070074900000c10300b900c0343c48040d4002c2013010b00100c99404000808076060707401c004011900c01c1c03210000c00c000c1490b0501141c590200761800c1e00014020408035659150800140001c6894503040c1c8840004940000c0e0841d00303541e01102420304049010060f44040341d40c21700d44000081105c070a00d00d410750000700b09214080c0d080c4968208000090006030100d151000e109501045444c1102c1c0300b420220341d208401d00801da2402c6024010001034201003001600650040c0c00800c0e4a500b0300e4030a66981c1c100d40800740e00340c400d0408070528010342809050003849040070507a81c1c2e080108503159050364084460b40226424403c0c00205036107449002d5005001440284016484104603105401941c0300500701c140041100000c009400e001180034052446411110145003140040c00c010300401c03440c440d003e11034040d805030514000420302004010f06040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 702302023 1250 702300773 702300793
    0x1d0405030c1005060a1e06140d05130b100f03061112070e0a050607030918060b0c0c090f04051f1803080a05220311120a0201150603270203 61
    0x18602a82c1c514107100007610b8400703200b55424000f034100b026020ba0051414601850f944011050b0f515114201c00c0100c45400f1400d030100031000da42c0d0006087d1401d00042c28030329400c04000b0220501520107944160104400107441c074000c0080b80d6100104980140c9103848410040004894100d682a403c0160111046003125000e1054110380c03600e0703107054180c0d010310241c41c031260001130051504000359804603400003001e0080b03600010700400e04a1090300100c02918407640010b26500c00440c44c214144004241d82004007002d40e030100003503039100000510080c081d42d0191a0390002c09000c1082441c0044203020f8100c568004a07010100030b40350407421000075003d0700003d606800f03009614005d4011070b5005000c8a4048840941415010341d003000502002018040000702c000482401401a10020311000115540f41e00c2821400ba000e40b4445620b50810382c0400f0001c50420b000340318200e101f005000d4410000c500050403186440b503a44001d9a051250700307180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 702303273 1250 702302023 702302047
    0x2405130b0d12110105010e0c1e0c0102040b0c0f0303060d0305070c031212050a0209031e12040f030506090d02100b120102070c060f0509150d0e061812041d040503 71
    0x2040000b02590b40c0c09846040d00d1101d54210360040e040398010360300420510151004150039079450401840d500302948681400a0120f4400e0000c04241c40d40082000900f002d0742c00044c000d4510300d072040e1805448200b154503141e01c8116186075020240c1128000401e20400c0a80440e42c8500a401c142644944031105002c0720100000002401d8020818a880840c0181c54021901080a50502103400c0000703403580789000072b030720641c0309640e440110410308102c64807040c0c00c8d401d007542d510381c5c5400700401d05007100d00090316a40320b4000491510000010480c40c3d501c0035034040e210305051111010060402c0e0343c2510790060052116201050081c801441c4407441032181d90a042c0ca08040a03100c110200740c180c00b4044280b040c2c05480d1281c41c030040c01d01742d0142110395039201c031b17400c510014100301e0340c20f01e014802d1100f0403c41091800d08141d000b581c42c0e04a484080c800b200342c14443c131403402340b40c800c3c03441da001d80c40000c00301ca00da0b240c11a01c01c1080c0ea00b4041c208002e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 702304523 1250 702303273 702303293
    0x90810052a03070201060e22170403050312241507050f0f0d11150703020412151d0c0607050c09101e0b0901200d02012405130b0d 57
    0x1001c9401c000401c0c880d80b02c1e0240300314001042940e01a54240c40c01006801c452880d44d5455500015111100c4041012003000011158688041d81c0d498a03103074144155250001300960f0101402c1d44049100448010501600ca580c0400b16038811042d03002808910352844007174540302002808010001641400410510700c8010024501c0c1c0300d03441c1040e854999904626400c0c4007007400400094a0041401c25400c207401d00c4120b025101d0103001c0b0300034801c41d844641c0011110100c002044501003581103402c50310130f010710651b02e0421040030a12500005d07c1b40302c0c3d001075000305ca2820108082c0a00034050821745040340704004c04101b40c61310484a0424a0814810030b01080d00c4242170000d0200504880340c00d501c3c105010303202ca80c803c04002c5070502100341140e22011040c01c11218840030101d068504041c42c4d400040d000e080c001e20001c0c1d14a8000481c1c1410b8490b43d9245411a90001c1c64080748070215502400103000317407103100360440c1c041504180800c2030100c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 702305773 1250 702304523 702304591
    0x80c040b04022506062907020307050607060e21041a07060504080a0305070212040509040f0611090a080a05150a060b0a0509030f01061512060f0b0309070609081005 72
    0x10782c500d0310b00ca030b4901341d001c4401c5600403000007004940061518459031101c1c44184208030f812070356a024600029180c90000d910803035001c140090041c04110700c80d0043c818100d004400c654480404203080e914055516040040c0d51000740410880c10340d82c00c1044c000c4c0c9a202840c640b0340089511108241da20481c0e0070f1b80e4051000586a1580d80d00d417207280d85c0110144081c00740c2c10701d1404580e14a00c2070f441090303c41d81e039540100d410300c400c40d5910668107a21842c1000b00035080c000c0083c407900401e2001e40b1404921000040302c601c00b2510a000b107074071402074070300202d070303031465541d240c0000e010b484805079a030340049050300b556801014a600d0720f44459843c0e900e400b04040c079215a01c44403280741e03410701d2010007000c05210040d00c00f010007800c2c0b1540041c8061b1024000304242d5202410b4204c65150001d07030919038400541c001d006c05001d4502641d101c0030f0a039a9015144500b004541c416002d490300b580050307110301e40203004100c181020100c21007030700420000900d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 702307023 1250 702305773 702305827
    0x3060d15061d0a0203190903020c09071206050603010503070303031e020403030207030c0b0c0d0e010e09010f15050c030d09021507030f0305010f0303090308090f0901140316080c040b0402 82
    0x30025940300c000c1000d41d40d0200d50707030f0700c10f40c910324198030325020340d201c82074480c20841d4403040d92008144c001e1201881c12103000e403a0218a161400001b0038119812060380103141c41c0c29804162030404004487c180d44018000b4030b01249140d070120000e1040b0880c2e812840d03880d01c201440319005000030001140294010b001031030542c24004032104840c3d11030403e4140400c0602c00c103e201050701c3c8075505040c00e1989000312103c0060340d151001d00c100d6640182d012002103120301110030b103542034800c0070328803080007001013000b41c030b10380720300c604103d1258800c2c8800084491160080300038184050403902c03a4201084000f6000c0c0c00443d82103011440d44080388504980c14132800340180060a1080040c2d447c51314040c002c4000350001403d12007000609a01c50b07205c0704041c01c0c40d040c024040d041551703540e0102c5c07080408880d800610038003a5004408080c9607a01c0140207580c1c00001030070341d5500040c2004010000058200c2e0001e800f071000c0c06079810003241080d400141300c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 702308273 1250 702307023 702307049
    0x50706051801032c1e01140901020a1e0903020604091b02030a0c0b060415030f060b06040f05010807120e0d1806080609040f0501060311011106060603060d1506 70
    0x1603000348905108003030701d41010300d00503410b08580240c1c1ca50341c3d00c8240112890b94100d108900c0e55042c558800c204031303a0100000c02144030060154040005000b4580303800c80540c0700c0d00089403d0780b055410074000a07071605940c191180350142000e1130003c05080501d00301d9643d40c0410071982142d40140c8050b651401d0360755002106515807010000d061010314a8041d0200015065201d11180a06441da90744009211501c642e031001c440d00e081c80b03045036243c070364030318020403001e40704482283d0f00790900701070441c9401c0000949080d10b00c0f0611010392507042c20011255807000810b0081009400c201100c81810380784942203000c0800c10207429090380c0c104015090070b08005480722007208194082101c2c1c5e510000b01030300407404440c040c03504e031194101480180d0082801420303a5180100001c2040044155001502000c0c1c0b00d06414042200e04540c0b641c81c1258110380105040000402d1442c0150b940010b05221f0036101422003240b900f110221b50301c9805c6440b1041403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 702309523 1250 702308273 702308287
    0x215033319060801170a08040f06021b0919150e010609050109031101050708070c0e0406050a200c0109060e0304091d0c060d1107060506190b09130905070605 69
    0x200d2030850300070a5240304940441ca80381006208060511031510300c0c0e1122001c005116105000c24113a99406c201201c0e11943c450101d41d960324641d00c0741c1009440741941c00300400e524101d04071110b100040451109950341c1c0142e140d02c401c42490441c155507520300346801c1c512820300b110064000e9003060f0910f5814014050414011031b00020305009040d0010070002d81100c50f04440c0000c203103416074a542d43c41ca0806024020312074003d00b0724030804800f00d000b000e4043c845d84200d020700b4003484240c8400804008031280e0796034080d0800040c03002c0064002c89080100311000d1a2400045c5111440c0c40f01422922002c18410369600001003c01c5095030318010f0400301c40c0c1400030110582d8042e10300c00d03130350002152181d014290106240440c040c01d98060b0314000d4511641d00d580c1c13601c61803e10005c19007181d900e0b1046692200a20b01d44402500f01001c2d0340e0200d0070070b89001004410043c2c20007455010404480c0c030341c00d40e48001003091002c20024080c1e0340360305480f080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 702310773 1250 702309523 702309529
    0x2d1e050a09020f061623071d0a090b062209030905120c09011404090c15021002030106020a0305030402040b061204300c060e120a080108010902150333 66
    0x481c450084c81000d041c8400c01c40c3d1600c0c0c4801440c00c07036001d510568034411400440f16400178440d01c9401600070003c4c005240340302c0350f6010300032608030f8201030460380e03540c1808000c403001d1540c080c10000d0428000740f864208201c061280290340716801c41e100d50150a090117884142c1c60840000d03814541c2000a802c0910081c00044100030107004908110004204090814800e4035681300d030403940c480302c60b05c441d80052451500700000469464a819507041900f0ba00206c460040c412944003032181d8001d031023030764182d440640c0170f045000b035a0f0b01d0403078403070308003500590b400b03039a511609a10340d60b00d40c003c101908110b4602841071a15040001c1030302d03c80031070800020300e40e22440c2c90400e4140d280300000c9502c0c1c106104040ca450929000400c22003c0030034403840f03580f60b4410109282e00c0682000e0040b0360750251103a0b2100c17141402d80d030400100070342210341104015981c040800180d5444816944510701065aa001c442900e07140300c001c006070800002c2040301142 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 702312023 1250 702310773 702310789
    0x408010e0c0a03050c0d060b0d3509060705070e01030b100e09030708210403050c07090204050f27010308070204060b07030e09070e0a17012d1e050a0902 67
    0xa07508807072001e500341c5141c840710384807103500e210207104203080c804000c00c022456200c0e801026001d40003100c0400340385400c440000380c00320580c840d120702d2071091031301c0041803191007081c07501040120304180c1401d0038080030341c210b80300854260050795404a034081c4002d1040d40298042c4010502c0307410b140c80000000a4190042444807044804201e0000c0b00002240c030000d42c410245581d540300000000b15101d04641201c0d4079074684814003003419485030260203100b1042042d10348261751456042c007284503a114140c0c120954401107102c601e00084074402e0400c0010001a0702040007403844c00e402000d80048400f00c801041c03800a6040c83d2080e44040e1086411361752802505813000b802d03c08110b0500e603c14610840051640b80c03158a56880744103000d801e55000985405100f80d98051045205080350301c0d04101c1c902c60144003c040303000caa04e01c15800c070340305545088440902418107240301c0d0319070801d00454000200d44111072081c0c0c004c0100150030903003481041002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 702313273 1250 702312023 702312043
    0x50111030708070209060103020909040b04230a080a030e12041a1c0905030d0c050c010e010501031a04081201090b0103050702160533070507050d081207030e030408010e 74
    0x103544140000000603506004a800160b0111403010450390784900407000f85c4103400701c061f0411090710912082080d1502c8060003544500c2842480e03018100e045200460000040b2413194030103542080840c0381480280450112840c001c12280d09820302180340c0315000202d05014680020108422175201c42c410341d01c03c02e106060352500b0398104407901d49141c0301607511751036a900d4058004109040007206c5415600a01c10b002424032000085c0c440d4202400314030301542890380e001c09520301813107024183c80d8440c441c4032284001c1020594138010040044500c102d08004810300310004d80c0429000f401c10301c0010039004488070006040c0d0380f001c2c1810055600c0032058042c0140c2e00a000000d503a0300707076461101f4840c1540303480d100d010b0504040850584401181c44050290130080c07110b5809030084032030182e44d482c00c0c01200d98628070060800340e4103110f40701d501202c400800340c120030310740f6001c24126074003c7d1290560b401070380104000e0b9511920060460f074140102208 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 702314523 1250 702313273 702313307
    0x3090a0302061003030807110c031603110609091612060f0303020d391707021908120d0b090a150905061e0105040308070501060e061f110c0603100501 66
    0x1504c0c03035030350f014000031780107020703002400300d814114501d14408000224103a038008045540103e402038848c0380480355070005940108807020700304440d042c920200c951140300681600300c01c0d6151541c141601008003031000c100083c010b003944400601c0d0089038050612008504d60140c950301e406407400345801c200c54140310070000c0d050008210a00300b40044041e500c0e2028070008618990000500002d200034400030b802c07104c20b202001054094060745100741c4207000c400f07041501115104619220b4802d459201801007000c0c01d0b14000600301c040d05509010600ca0a10300000b040c0150840f18164040da55400318040c1c100a0070709507000740041d040800681c00c0040c08140d20002e035003404003620840201c0c9182907442203040324000c5805c51405511540503282517806480144521550700741442c01050062803e50b540740003009462030442082800c0d41c800344c940c2002c000b0641c45900600b00d05600a403a228020b605c11078140034000c0b80d03242094000b500010081c41d6540c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 702315773 1250 702314523 702314551
    0xe06210318010e0d14160b07030e0a0e13023606040905030d110408030705030a0201051509040b04060b06071412040509040b06040204120f0611030613050c0c010203090a030206 77
    0x658890060310004c0c3c1d074000c00c0610195410684862038082d4a605010310048944800203910011801400780c1c9486079880802064070002002a504000d009407078601a513040415802468006d11140f081c0c80034002c101e080c40c0d56110356030329412101c0c40c0c50350710b040a61442d10000340d221580303612080c02c80d002c1210107141d480d51581c3c0e00500e82c0303510449584c0d107902c808000b10802a14000c085160840741c0e076084a140c00c07a200e4020207100c401560805000c560019204030004000c030401400141c41940c030790704c440b20040805481034414951b1141c0003106034a488004001060144240340e4460f9203c01d0014174240035018000c030004d000784000d11107584c030104250b400030340010b252845170b110400041d000344a070340e009200303184510500404000c00109078046041c0284c10401000c04007241e008180d01c0f040345c00da54400d0000d007850300c0380e1842e50303c0640c02604107088103003811030700d165050032a4020b0b100211703d6441a09007030f04050b41001034990011201a6046c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 702317023 1250 702315773 702315797
    0x12010b12030a0e12210d0501091a0609150409060509060a1d0703241d070912050a06020d020301051002011b08070e030a0b150d08040e0621031801 64
    0x100f50408403072219104000d9070ba0b48808602040200c4103440060000c805910b02d00d00594030096030140c8000c009850030400001103403d0300c3c1c45030303031aa2581081e2051051103400100302c1c1a40c00100117650100c0800c84c0320220003100030161018181000000a59a0521080200b9008001e201510802d2700c0541800b0221040c040005070040040001315280c072000c40c1038015040c000e034000c1c0e85d045020450440d0b500e03c0caa4050450348103098014441c0e2100350040101402101c0010100c1c0000804210380d103350420441414002c034151171240c001035840300c0c05d82c0e10580806c140c1d5500440144030350314000d0040000d1508a000811055084015001c80480c1c01c0304100144100705000402c054040d1810038803100005060302e400c681185080c0002c4441035684039030841c01d88100e600c450809105d00d85c81e1a420070103280c1803510f04002101d02c8900101320a8102c0c0f00c81640b4800040c000003c0030080041c02c0c061610b8050f850411078450a04000b01d81c10022021040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 702318273 1250 702317023 702317027
    0x30d0b09042a0320040c0305040201081605120a02190903031b020103091e1b0e010315110a050406081b0a1d1306080607080c250212010b12030a 63
    0x100441c0c081802d40482c80d4140c602d941c0006a903500c064100108030000240b041300c05003416018950845081011004402c0304800729101258001e010079580004105500398034401e0011500301d86c0790140c0b81c020b00041202c110380003510040c01040d0040b0710104481018140340429480301c2c505064040c1c40c64400a00200741c4580310220041c400840d1020369100c1c0e0848241140c220368482c038000d66040c005046154000d20644009940414401c622000d045030007044410f000c10b00c00e0b0613421601c40c084903420f001c80824480e82c3e1603400e4429000d04a0181200d10000e0702c1d40340d151454584007a00125004144207501d4401000ca065042464010790302c50315034918040348941c04d141c0000c42c42e110001c00c4140d02c000340039480e9415561a40103070041d204400240c0300b460321043d10aa80c408007c4c1c0b014840700909001030130880d03840e01d9249001e041c6000b0080c40050082d000f043c80c043ca410705144059454031221802230410700c20500c41420114001c41c5440000140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 702319523 1250 702318273 702318293
    0x3052b05030a0f0f1a040605010e010c02010521040f050f0d05120a06051525030f0c050c04020301062d09140109030b010b0a080906061c08130602030d0b0904 69
    0x840c2d0b50682c0c507003c8031180905940b00241400310a1401c01c03101a035082e04100d254001d00b407040c840c9003004000b2440f9485880c01c8a44d0b5801a111450300c049580d005551a030030000341040d000c1094214082040c41810140d402140103400c804005101824290f00780444859140b08950005540d180301a91000032030b844100fa601c2008240e450380c041e19000f520840c0d000ca230780924800000b00d510b41100c3c005107001211100003881c1108035400310700b003c0d0700144002c1c0228422421961409015100c401c8602d840b1324183c03842d4186000000d801c980084e00100c001841001c03c114a66450041960600501a09029200e00d6030740d8010b01050f40c0c1d0142d000003004101c13880d501640a40c0d0a80050f607800009074009684401c0f402c01c0c035400015508001846640101c1c84502001c0b03080e60040308060000c1c1e4189241d20098041102400c5d0116000c00080101c00b030005454000c08010740710310b81c090b55a0308040385a0300d058030100c040841c07150141c82e0501000946240d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 702320773 1250 702319523 702319531
    0x1a010b0a050307031407320f0f0f030a020301030b090f07150302090a0b3604021c0e0c150a0909051012030201050a060b04030302060406090503040f03052b0503 70
    0x54029601d0f915508110040d000b00300246080410b60020701c4032030313a00f100540c030010000c40ca5030310f804407000c1c03160911024030b000c03481600501080040229510030700144a070510881c1028038010342111020683c0d40110781d00180c80354003100500800c8a02c80d07460b03800807402c1c1c00610b51083c40300313447e54030790801d4880c8410030740c44068108002c50080d0180c2d842d82000034162008036544070342d02034455001d0000304180880d9010b8078020035003000e1010082c0c1c4100c0c82007103030000f9440103000082d844480c41c105255542e840d5040c640346240501c001c0d1110000c05405480c22541c203020020328240401002480c0030300060010603480440303541155070340b04010400382c03510751140d40b0403280c94021001803034400f4440340c14140c05402050003041c10180402c02d0903503483d441c0d0a140114000100103810240101c0c0c0441c401d6048507190303074003c6065074601076036a024926811250380c003c50781d0f500005003800d44802c0030f200303149030141c01c08015180d00301000002051888010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 702322023 1250 702320773 702320777
    0x303070e130e0c042d050a0c18120f0c0b0d1a0609010804080d14010e01050f010e220c020d110703020102060f0c0f12240f13020715091a010b0a 63
    0x101c03106a45504070140700c2c1e40000f4560131501240903e17000140200316842004a0b08201c4c1c2000c00c13a109540d01e030550941e100b401d00059007085211940560122800d4030205805010407000c00c03000d1452800604103588417a9039261000804800c0e1141c4001ca644440f1a000100707407203889000886007145400d2811031015690391411500705e0103441c060790045803070300282181c0c2141000070765044e1080b50001000301c0e070ba140201721603107200118480c001a40d41458039400c0c21b08445201c0006028030000d20341000b2021040c04480c260306140300181d000320030f040a034580200c0840c010b4040c100252031541d084d41c0010f580d03101d0142005103218104000030b00d842052400b65082030780514407180d031341d10140184181d104016180c004080600d00035040301c3d1010b0002000001401901c2601504071410801c0f80241a0049403007400340c0820640c000114440030000d590058040d00099040190038035080d200480301d00010f2031a0b4200c010302543d69400240d61030380c0c0d001c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 702323273 1250 702322023 702322031
    0xa182102031005090c09090a080711031906020a18050f100c060207110f03061e07021005130b060604060504140a080a0b010905090c010905060a030603050303070e130e0c04 75
    0xa1000c207150041d040c0305141290f16200601084440c04140280050310884000c072180d140c4140b41529001c0c0c09800410403981089820001004030600034074030030000f41555003002110782003400060544c4030843e00960b001800510b01600014031102c00010b00d101403e0903801c0501082c000f045603001e082c801c2c00c07049100a030701d511034403950707804036032004003551a0105441c0c2005000601d4995900c41c550046002051303040c0014064072401113218110003419621b0084c2c01101009070200045021301a6818400300b1180030b101e00503000c0010051414805082c0441e1a40018000503c01c8001f0002013140507440300a1b141510809801008009007134000261924940e52000b44640146c05180c410710015002c205e049445040c01480541e43e51424162600d158105107404a43d10030380078080c5080000c00307400e400049090005090703440e074440ca45035410481c1c0f02400101960910503240c204440a204c0e002c00302e1030140007a50342e40702c950340c80302080e480540c061640d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 702324523 1250 702323273 702323339
    0x50a060506060f071407090203090303070f110d08060f0409050322051e0f04050105031203190203010e070905010507021005160c06180f2601060503010f020a18 70
    0xe60002c503000c1e00f0789003a910781d07154507034030f00764129182d03484e264400b0303009013a0001201d0754a0b0003181c2c4070701c0510000e10300c1c560352484140c440c1f04480068008000000e10b109482080030071502c0c088a40c50f84542d40a85400703010020b641010a2469008500348020100051400019140104210168a40704080340781030000c044101303a00a950094020007892501904142c24112465040e510300c0c0380444d00c0310502041c1c074420311940c0e416520206181980b03012181c061500031120111165120070000f00c100166002038008403d288011800e026000350800e8940e00101006c7c20510705085c070316000200000012011002408000103000ca02000600141142954844058101c1c59211400203054001861500c201962011004280c5003860780b24201140c030060050407100e15524203003400c416032030100c200199210000800c1d255000c1c01303400300d2079034980001a1100d504a400500034141711030807501e500d0706000e0500c0b1a40442050301f80c6001c0440c4e0200e001c41e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 702325773 1250 702324523 702324529
    0xa12110a050a030806010e010804170a1103040e060a0e0708010e0a0b10021b0d0b180a051c08010603020a020606120c1309050601062a140613061503050a060506 70
    0x1200d4500400a001d04a20241010741103401e041c020842a40c41d042c0003945ca80054452007001d40e006000d1800f81c80703d2142c50150400103228462040c44c001020000b10518645140c009230409030325251004208805030800310100c000500c040d6800302000e040c03d25014000350810f015400411404100051048049400011011a015151044520405a0003521340e0441011051a41d03201d07590645c0c0d1b4604880144030a036000010001a40c0b42c444503500301c00b1608040c3ca0460240003c000c020910901400c40c0349400d03c80b0807000d400041c10000c200d000160040c0c0180f5105204014a10b40d000a08650010040e1050076210781c0304a9050310b08031300b0000c1554040103918080e180c00c00550031014120303101c0d504884070b590701d03010141c5200f4944003882040480703445410129160703901a03a11854014800e03002e00004901c00941050012174080344c044105a0b422000c0207245d10428001402607000700303804508694172503860700c02d8010080c00103038940010948550f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 702327023 1250 702325773 702325783
    0xf02150702030d030c02010e0708100b0a050a06030b010e0108010e0f190f0b04200304031227030908190f06060b071406010e040201050319110c01020d0501080a1211 72
    0xa50020b0441c0c40c480602d80c0d008028101074034808005500b050703a85c151002000940d138094034800380261400f0101d1000410003000414034156100307040b1840090b550311004843d1002d01324075580407a100c03070041d001401b01180e05488504200c0c484004001013072000d0032450b00031400850506027921586803e025413000d41240701c200510340540c80d007202c207660340401ea058a05403400c2c4009590f00380081d840d045441c6260b02c00f00010000100000e00c1480f14510003000c0000c00100010369035481c040b00000c2d600c0c01e1540c0090350072403c0c103046d006050360b0010a82c2000070400f0b0300540b0300c50b0900c49030340b5000404024040c51b064082018980110019040c91850709868412904010b09011003022010303100340a070000104440e0001002e0307520880d0180c6505103140c0b07501d520380200c03100e001250300300242c4e207001d610b0300b40030386100070300260465000250716000031224201c111a4180c0c090807003544000d04410000300c04149000f03905200381403010a040b031722030100c2d00b48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 702328273 1250 702327023 702327037
    0x21005070810150201141003140106030c050118080d030902010e0306010602071206020903430b0913050a23130311070e07030204030b010605070203151e040b0405060609040f0215 78
    0x888a0b8007c22582c24980207100c1f0491340100000f140030011003142c3c900300c403c1c9000140082000c0c050030f02440d4000d0358001d001c030300c01703210303186011396a42da98504100c012858040026200c100480030f560303003d201207258a808401810440d4540000a5600c44151090402e040d030b010a03c60140200c541c151010724802400352240d080c110482c00400490131541000f40c0e20500c42e18801c0202d0780e00503150040e03425805201c0d01c9080125156807600811251a0f01c10150284011000385500445008082c2c0d0500458140f1300b00280d8048c44921030010458114140f0400c201c140b5104106e00c0f00c00d406042c044061a84200440e0608407590007000c1d90740900814400c4096150b801042168003481c003a40d403a0340c0f01d041c01c80f0385100e10640607506a00c41081c4442c499203800400782c01a004000400800c008001090300f260006c035400c0d1403000c0b80314104424040140300c400d500400844010b0040e150035609c11300c0a0302c9001d006400ba8031861540b08d19109664229008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 702329523 1250 702328273 702328301
    0x1302070606080d021213030206090a081b031902032d0a0b060f0901030213110412140f0601050d15140c030a0b011b08130510021005070810150201 64
    0x4552110384580d03880e0340f1402041c0051150b0340140c0401e0b200300c0e0a40c1c0b005000b04075041400762a58080202c2030300906210399004281c600c0010341c1c0340080100c5200100d80c81208504409020205410a42055a4002440c0c20b4034070080051368007041c104c52026401c82020307081c1c0c0c04c0280000d0a10300000c10444a88101c910100601030307000070784d0388542c5048400c000b400e0030800900c45000000c5c40025004002c00d20200030010468000483c02c15454030000d00306540c4000c0c4249903801050103580c0d038545440442d40e992010304c100c0c02103079040b1000b8007071545040003186080012000182c12418601c001d01210794a68104803040d102d000520400ca04003811841d11691041e18256001481c040c41102d1950241c2402e001c0b034540da4003d66030494050b00c032a15291702c0000210b0300010740290211303c81c0d4603136451030716441300381c0d004021680c98020f90508880000d0000000d02c0001c10401000c14800d0700b00a0582d00c280c1c1144200115030141a40545078410010b40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 702330773 1250 702329523 702329531
    0x5010804110414041b0509070f0c020301061701240b0a210501090b03150723031006140403020a14030a0f20010c0b070e0310050403080a062313020706 66
    0x6200500842c524081d03805010705d10322a40004a0000501c15503100b001d070070080f0400060500ba002e2641e8494102050502442244017a80064216001038001039072103400c0700e800c0d40700c1c0c50091041043d919110703050401d80d03401810710529024100d129103030085100086044c4c013a4441c500004118084802c0294480c4460499601400302401040d11442c0340801c80d003074600c0c0002d02c200b0429001084400f6a441e803600c22a4080e001c04c201203840300c044401013081d05030641c006d45c816413541e1018040c060074040e00a100d4000e4144074036450106010900140e0350340c0f4030000c12140d89580c580044600ea101180c100342c081031021741200403045900c0103228401115a0b160901031100c000346981a030015200d8000070f101c040d1103148a0400900a103014030b10320030040d04010f04444114002e40703841c506465003210304500003500e240620024520501030440a41440c1909000507050030f164000ca0542c844412403059204500802041c81c966045803441904054284 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 702332023 1250 702330773 702330791
    0xa051504080f1b0618010e03030412050f1e0606061308031902240f1e070201060f0b2b02190e030706030b060417011d011a030313050108041104 63
    0x980340c501c00701050b000303c081031200a00b549400001ca4800109010b0b100c01503c41e0400115a0701d0501c29072075815100811011512108090070120013034440c8004281100c21101140c1c113042c490fa0f4039041040e4110540c2c1d06100c804174036a50301450640c0c61a484556030007601000700e40e160b2044c40540000110304031020440030400c0c0200b1840d0702114103464248040084070b00c041c044600c150386246000c59042e15050143d19000f01212100c001200203011100710000412740e180c2000d80c0d9030305800c008030100100190020080e82100c10304007a203141c4d080b0040181074400580701c2d00a07508500650016a056032201d056051015444140d00d49028143c0c8a11030b40583c800c1c0318410000500b03910034014008400c90180c022410a86054248041b01182070091003455498400c2454009d40345008850301103941d400200c1c800da20f02001000b1407000c42c0b04c1704c0c087d400030441c0300e034000039852011040300c5007840d0100f09030b59203080c41c0400924030381c035065102d41040c4041c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 702333273 1250 702332023 702332053
    0x50d171b030d11040602100b03012d050a060b0702011209050706020a0c09110f070f080d020304150c08070c0317070801060212070f080a0c0218011a030103020a05150408 74
    0x2030140b451403041c0400100d800c50000380c0090103144501d00c0164004c4205105c071890a4200d200950000350020409a41311140b00300702e600c1c1710001088099a0b04000180e1003542d0140315080340c0c2c118802c0103150305240c0c001400744140307180030341400388130f0080a8000340241d11489819421000b6105885c3d03c40000a4a69100f4101a210401d5035240451407621034420100741c1e524003184180750514100ba6100c10b0341100e00f0968440c02801d1101c0045480c4800415050301750060060b52440d10740f800c00f480000e9401c1541c000d51a088414450a80040040d508a011400e0802924900349400c4075000c55403040e5100c0c0180c0c4500780805e003a08411458144c4086400340e40c401d034200b100521490103040c00103000d40111000300f40c00300701d440300200381c1c0020724a080d0f0031070005600401e920301d65180041102d6003040c40100302c03507001a600340010384000c02201e840d5516640010706006054000e2610821140300d504a843c0611030481d002030100f64152909104401c03d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 702334523 1250 702333273 702333277
    0x60806011710030609051c0509120606012a050f16060215041e05010e0f060604091a130b01030f02010f1e1103040803070503070c090501050d171b03 65
    0x1069001c903010a6a01c01e92010104009100d00d007068000c0c1d40c001d01d182c968401900d0700c05d5042d5418080c02d031442c0c80003545074403000c0440b5115143e00d9903440607401072202c2a026040045095049002440000d0f84d01943c05000c0c0d041c00c40c40e4030201d44586a407010900d02c0c003000182103105445542c16003400110b1400016009030380f07003101d0a60b0f201403e903124030070741c000c41d01c018400e00005030000700710803400040c110180c00c0c03400d08103440c0c2e51941e08544030039802c00039a501088000a06960070041e080c3c0c4101d080d1001c0c8038006455845000e02034501580b00803050420000031b00500c11b40340e9002421b900b0014925682d6540d003800303441241400410fa002941c0c090484500a0040350360419a0380744009042d0070b030080c09401c03a07810501c0c0c03024039014082040002071101d800c00c090320005000d50301a40c1c1e100c520b454604600d11581d2b10142d11503043c013004001c180d0751101e442100780d0b08511031b0011108d43c503041c42050b110312086010b0301e0301c0002c08c1d41c03500c1c140080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 702335773 1250 702334523 702334531
    0xd020409060f05090c0a0309030315080f0d03060b120a110f0c122104020a0308040605040503071401021507050c031209010e01150b0a0507231203191d06010608 70
    0x302c01820340d40750001d1014022085600421562080100071280f40c802e50008009500030310740000d1800c00ca98149501005540c0410780d142c4c40b00007060461503007801042c407071000c04d0500300b24542c5000b9050103140a00102540100d060600203140c080c050780005034002c0a010b080c0c0d540e02c00007007030b13228035810096480c1002d00c51011180100c1e15424116080741e03814035070468007911400000299041c0007031040b03800c03815803003001000405103400790000d04103d49505881e40d01789401d040c03a0501a07445000b21b01d21b0007402425998012600d002c0b484d122040303c5044c2e0351410002d642c18460b8504280e210b01c40029124480c17411242c00b68001c810783c10091014401ca10304107402e0302e9070014200f0028140300c0b000c0010342030384c800624202c40103041030707400c03c0c0700e9440d514502141600d105884003001001400422828006800f0307140f4840030f9582107003800c901d1220540842c5440c00d540564400600c0b02c82511014021a0300c0200000c072001983c407401e0003408158251 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 702337023 1250 702335773 702335789
    0x1e04030b07030903140c010b090a0b03010b0d02130507090b040b0d14040b0f071206080606010905060a02190c03020409060614040c12020f09030706111606020307030e060d02040906 79
    0xc0440e40361032081c010760042c150141d80b5403098180d180c101020035805079040328000d658402010040d81c94420305144100390011001441c0f0315420103150079109491403840c81a03502d9144000140d407802800070343c0e0401540c0000d116030700d6082c00e40300d283c07031a008104840008a4001240d000d060000c04200305240001d010703030608948940d4036107405940042c05900c000d400110007040e03558030280d10015a283c0b5040303d0b014070080c0000ca0365142c010707060a030010b0003000340658000d00d00070300904003528258507103011007000a4840031007014645460a043c1400411300c107103c4591805140c0003002001198414600722009024601c81c0d0883c00c0d00703080c48034101d46418800c5081c80c1c4101d03120f042c3c0900340c15000c04020342c000c45910544030390a0280445c951030400110000c0c01507511906114481c1c072003801d00d001504440e0b01d80e60b881c1100d05110b403a03130103c140c1340090742c9401c011068480c82d00000300c9074001c403003080d003410b480803a0000e800320403a08a07801f1542d0700c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 702338129 1106 702337023 702337043
    0xa170d020c0a0c06050a0206040303090f15020d0b03010213050607021207030b0411030316030e01020f010f20040e040b0a11041518060e040c051e0403 66
    0x40c240d62030582c4460703048020415999246406810941040350428010540095440c0d800030402001c05807600c5c5003208110350300b010304440035881000001254050303409080290041440d42507024104401640c45003010b00c00c4480d00d081200c00c500680f41041d050103041d912510080380c12404058860354450750a1014a001c0c620036420411203080c035040280f103a05440e00000d200350401c10000007075200c040803681c1c001d40c2c14180301061522000c0181c1c106007a904540c01154202681344102d80c51603400b58014540d8051210803403401140c844e03403e8004c80c040e003400c01240700701140200e244640d60b00e900c030310300e02d601003600740b2413540301c03a8690081d42c00380c6100c8254540340c943e1240c03c4581d503e140d04a29403001d459500e0044014082155006400d014036035980100b001640f08000301d034074130882c40011803420001c6501480351688948010340d403600790 = true := by decide +kernel

theorem cover : BRFrame.Cov 702158273 702338129 := by
  have h0 := BRFrame.cov_init 702158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 702158273 ≤ n) (h2 : n < 702338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
