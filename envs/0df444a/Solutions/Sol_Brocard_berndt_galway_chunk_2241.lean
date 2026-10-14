-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2241
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:06:05.649382+00:00
-- url     : https://prove2.me/submissions/1fdd4720-f6cb-4ad4-b234-801b381cb5fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 402877697 ≤ n < 403057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 402878947 1250 402877697 402877711
    0x160b0a0e040f1104080c0d030516030203040e0403050d11090d06051509010e04140307031d03010f0f230c07080304050c04090b041a0105010e010c1112030a020d05070236 74
    0x40030400b040317940400d0161903114841521b0411440d485a91700428502c15500721104950705400d0320070605108001b03039400703407a418154100b181000d0401500325000b2000c0e8031345141c00c01000382c8580300c0540550301202c2e00581040d0a0316640c1d681c1c00040c1a00030000c608072504605060800c0d661031a1031030081c003c1c10302417055400c01d402d01c000c004041910240c0f1540c0100540c5000a50041e10300300c1d50032360482421005201c8000190160903840303c10300c00709003040e1040380a941723070b03510001d003030902c2041d04413910000c5000c2100b0f43c481151a285240700c1070120358082030f8180005c540c8648148140c0d00301c0d020840c000b8080301c15405c400d44a106040301040100414071194101015403845408101d41c90000000c01c01580203061030704010603460004200310a002e5110b800c0500103003145110102124419030340c4c0c000444100042c403810344c0803411640a842214000c41c1c018244100c0b00c0c04107100d4240e9585d6503e0910059040342e283c0d580d804803e0520a0b004241c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 402880197 1250 402878947 402878981
    0x302010203030a0e19030f26010e04020f09070e101e0e0303070b10171c0f0c210311031501051312030804020a08030c0604020409020114030c0705160b0a0e040f 70
    0x84c8100040009202240c078102c805c408c80c0e109072105a4200d55141120b0310031056003980e0345c8501c046000c0f01402c40d4282d81113003a04e001e0103800d43e0440c4102e600c114081c0d407014101040c3c0081184c0001401c0ca28400113200d951842040c03d204184105e41007001030116841e2506650702c03600c0441d001c4800012a4461007014841c803400f40b602140d10212a00c014000d010007a1030b61245a101c0c0700c00791302401002403084502500480501d540180c00c60070346010000e0205c03100f0030000450351741c40c0c0000e182020809001e03030f044040d203004283c00c0c080c4240b1406208019921035024035501340d0b420f142250005003034462040850303181c6120345d035103c051341403070b01c10300003100c4043e000210140c0090250021310307140000c0e015403003901242e02080004181c001a02d030022181c90540b01004000204041d1801c0311001b4203515200d0300c21940b40000a5070740c3c0c4c45031354090055020200c01004803156813486161000405a0b0081002a907141e060b801e00c0115070307242c07044d205001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 402881447 1250 402880197 402880217
    0x30d06061206080c010c03140a03020d0b1206011a070b070c020a0e01060e061c05010b2d0a0f031d0c01030f05040201051c020c011d0d090302010203030a0e1903 70
    0x1540190000701a00035041c090007000d051034100d0f034540504510441c10402c0680010702030520403142c070300c3c000300402e420555130141303814020040d6004142036023003641000c40b03101c464100166080c41d40c02c41c40025002d03d0b401c010b0b210b0001c1c14140e201d250640c40910099002c80d44a41040340140032584440745c900d021031060054a240c15032114512100d610b004200c21030700244550912403084031610790b9440c40a00c880c8101100203a900800da00e0040045081c004130401890082e0403152403455030448203071a9001207158503085c0040346418068200400c0c041e10f540c1e11822400c0c24040783c080000c1080090400313504520032885d601c1640c140c800c40d42c25200e00007140368000c1e0148001d20b071640001e4607134070818111b00000d58460782c25220715605075054820307983c00c4800a0080d00d01c02c094402407403201070444110341c06030009000f4064001c001383c2e01240c0d07044e00a1801d51f41c0e40c840c440014522500c440442d4003841864101d007104440c0d54030102c92007616644548 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 402882697 1250 402881447 402881459
    0x60303171e0406020c150117010603120311040815071209050309210105090706200d11120d0605130216030509181e010e0702190312050405100b060906030a0c050c030d06 74
    0x8150100d2040c92a270345405030600c082848043c903104440020b0a012407d002103001540d414400d50307000c02c19a009040420324094480c4920b03600894841d0703603c0c0052000020035204452456200600990082154001a013060030b104840c8018146111001400c030014445c01c1d1403003100c1c6007146802104080c40595004502c1c141ca45900164000502c02c1c164000e5076164982e90010060141141d0494100f0b0701c1000b0600056a200304810345600450702904003604060054500c81c052851900031481c01c82d10a85181050340c98801964190302d0701d003581c103540b00c1c944403034000032000d1440580c550048411400791014010484598600144004030200180c02810721641c030541030204e90b80d0300013102d24034041300b0f8000b03144080d0686000d40d590072000314486141d50925007080184100410500c510700b2200c1c4044c0300340d0440301e082008500ca00401c00c4c0d4000f5061005c180c031008907910410115000341000341c42c3c20342c1200914515007160714080c100c261501410b200d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 402883947 1250 402882697 402882719
    0xd020a09052a1305131113061409030c211f0b030d0c0b07170a0c120b060f1e0f040321050f280201060303171e0406020c1501 55
    0x2684410502c0d541032900000102c20544000c0c80b442d4440c0a1074100d5805c4005143e01c000741800700302a0b0182d0328620340c4051021420244504030105000246400128400d49d00300e801040d4020b0103032002c1818002001a1140c00401002c60759110b440c8886030010108640548015000000d4141d622820b207003200b502c4c0342d5104075000e0340140001e020a941c00c000d1980076039602c4142195543e440da41d0032600c10080c40d078050342040f00001070101022240d44070031350640082d40ca034138944503800e001d181503400e5242c80c41c1d001541040340c07a00540c0c0c03070750160005c851380c0e1900414290a000d070017081a00804104044850700140400402104240005400c841c0780342c800110204004068440e0003030280d9003803040300c0083d1040f07036020348540c00c1c000d807040251388500040f020000240201210300080340440d5602c40e11081000b43c001c5610f101d0b0075484040200c0148a06201c807900d503015000b140c0345c940903c5032084024041c0088200c1004130009051150702d054902d0039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 402885197 1250 402883947 402884011
    0x1205040e0105040207030206130305130611061807060e0a0b07081903180807060e0f16060905150c33010902120a05070905030a11090601090b03060d020a0905 69
    0x300c10f5104100090000c0e401044869218414421a04480800741000e0b01c0900c200340c0d2400510114080c00702d0705542000d202d154445030081240c2540c4d9410419404101740f41c0c030f00c1500d03a480400200f044c10300c15240001d10302400342c02c0701d1282e44c1d0b641c4484c00580100600322400100455030800c08480001140820182e034a0140402c0310046550091a10307402006441080c000030220184001e58001f240580c0d01c18003140c0c83c58480c840425262030300890014180c8030144400694117115294070811745178000e006005048100f0104525640260026101401079600c05540c44565215640c11302c0350840083e104a0b000340b49041c0c00201c143c021000003481404080488485c00401c50f0780700160318400507642d141c8107025601c207a040c0c0d0200c1d0f4107210b00703103820341004400514611003941c169002c0000781c0380d41d001554024840c1c020915417620601c005011458000d0020801d54000f07130000d04480d0300c5001c4034050362012100c0320302c01d40752110703140c805140301d00e0000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 402886447 1250 402885197 402885199
    0x1050108010e0a0c09051509310b0604050907050604060c060b04021c050403090510030905010b0604060507150228090f0503031c0e070e070210060f05010c0f1205040e0105 75
    0x552071400e503844242404c414000d48910a507500c0000349810314010042c251080020003040c001c1c606010300060003013140c03800c0340d0036100e00982902c1e0322014240381c190302a44805e0a0301c455880a0030b0200601008000e8101c600c0342c000e0006a039110200140040c1c100c0ba5500301e040085c50804c1c400359104908294042d070700c1000040c00c0c000c43e805034046c18400030750b030100d00c40d2a02d040c1203072034401d95040079030300401622200c1e550740c0c0c1644c031485001d03205000a01090035a8010440300c2c1c081c42c0300c0c42001c04c01c00c014140c0050081078101c02c204015240043c1490100980e00d44540112425501c030031441d02c04040940c1d8100881c2001400e90f0194540c01c0360400000c26203d011b24401d00d05a00035188410258500b160090030b01e50007403808503800d4540c2c401d1000c901070703002d90b9540b0140c003550031401801d102e01e0242c802680c1030103468103000c03490400110307000c070303c036010640e032044071110305000203548a000c1d500c00041c1992415211030424502910004040e4412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 402887697 1250 402886447 402886453
    0xf13060b04090c05040e01050f011106010b0d060e010303080403120603050a1202061311010c0501091415011a031323070609091401060e060c0a06050a05130c05060915040801050108010e 81
    0xc011000601e006e2906548085c0c803043c0d000d0f1008001a01c81c10349200310040240210340000c14421741103405400c2030003114509004240d0f4441c1028032081342800080e001564000015020901401c1c0c025420b0f9540003000505603500d0300d8090818108000488d9840500c0800d5504a64100131154220127002d03000004281e05a94ac0c408100c1c440c031030f050500980c40134000500900b980210109508002091745004661502c00d40b82d01e080424903c0c5039101000204180c5a1300707600d042c0800501140510f152200c08540c03000c00c00e800740448100d16948201c2c454071400884540040c80c03400000d100300350070880c0150404440b80c010413a050315002101c1544220810b080d81110b845003060040d4280480c0800d072544100b440a100e184070381c416203030400070940d2082d0700c0750034540340400443c0c94030802680303411240780001e07000c011046401e001d545000c4005044c58a030040114042e480d02540c41007007500b05901c407402d0750359102c00402c40c0101c28040c4030145021407002e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 402888947 1250 402887697 402887699
    0x711010e0f10181a0405040507080c03060918030c01050105010809150f0a15140906042901030e010f1e061a1303020607081309060b090f13060b04090c0504 68
    0x8a406080b16609807020854000c10742c0c102548000b18030805090004070011002510144440b0b480e03120b80315150082e4644000500720394400c04e039050041010340100d51564a50300b0030081c0e003140103030a03500705410030182d04148000800c02481c1d5104060004034880d1300d0b0000140580c0c0340240101d909800074050704003601c0c13050b40e802d94442100324000503103448900c2000010702d01d84600c00540d08401c1d0002c24001044028900d50031811286420703290389000c2031205803945035280d01d40c0c0d07910085000141c48000450b584038114189130005482d80e050690b0380c2980d400c5955032000503641c000303003140c0d100700d21080618040e03680000d21031149048000140380d117521400151500d0040352044034500c2014200300110340003800c46449024605010241d81d1020070700e0700e010303880410000303039041c400e015410464030208801410160b583d81400b50610710680119444059a140c024188890380700e420007920030507010648540c10301c540f4504503012600c05001744441404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 402890197 1250 402888947 402888949
    0x904200604050d060e2409070506090d080306040f020f09041803080403080c070606180f061421010608030a1107050913020d0c091b03060510031107080711010e0f 71
    0x1408690180e0083c00010030341d05d03080d00a400d000000d8030f10300400454140b5007441c01c0c0c00061240c003e10140e4152201c0b15614010003c15120710404907070080035581010000c104040b01455102102a102142c909110080141240d110150391401d1010100e0060302504041c0720300d0761440c08840000300144400d40f00a804078000600c01410884424005865640c031141a2a06217505c51420f1054a4841c0c0c0e80f00084400c0042d0103c00a04c2e000e007031b82d2015030130301582e012668404459400019104144035003600020020907000d078000320940046182440bc0c88001c040010165442e543c00d01001415a014442205490751080a090242d540c07521034964001180300c001900c15001840440d50354000300350b0103001c08042c54000941c600464008a007d0340c0b8514011071050010f00045d4121640ea0003140c2d041581c0c0104c81c4c0384c09001b41d00070b144090410100c0b60820900f84d50359003040d0700003201110500c044214000711942c0040008074405001c0340c0703003034070052084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 402891447 1250 402890197 402890209
    0x40c090c090e0f131b060311090907230d060e010e090c0409030c021021021806030901090c0801060504050a0204120b06040219020f060c0f0403061a090420060405 71
    0x2824030440303032103500c0c0407403c04c0c1d0072400900b4503660300c00f107000580c00903981403030701d00701c00d601c11800880c1c1480700800341130034100304907001c2240041c034040b41900d80d4141141d60310f10200800e603075800e02281c0031141101e044042c0001c00300701d00001c1400d509105110000701c10617400740d00124100002d202252801140301403010300d042c1e03400203170844507040899034181e00000181d0012036043d10707118560782c00880c0c142403000380d1403042290804400303800c089103d03141d003080303c048211920f0030b000c0ca0035000847e00700910030300101d14030782c2c1903c4208413a21f056114401907952140c04100700d0400f40101039200c0100c0e9011810f02d40b070a046207654032282c1e00020720010400000a003a991030344d045c4e4440b114803544480310042030035000380d80c940405a0303100300d900c218000a4400628501101c8040103130f413032941c0c24980385079142c00140c41d01480c0c02c0e4101800c02c152000c2d545602c442103115501840b40030100609990004005010741203e183c01484200b200340050b445403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 402892697 1250 402891447 402891451
    0x405012708030c070606080a020a0806090c0405060a03050f060a0501050f090105042a0e18070903080c010e030f090f030a02010207050d0809060a030b1903030e10030f05040c090c090e 80
    0x100d0035582c0d896a403240514034901c108100188903900c6c2c03080208190f48001b820036a01882624a41d0095031035a641702c2d96284111444482603002e05900842c50915400c06a00301201800c218609078880e45c0716410301d40001c07440c01240d8006410400c10724981e0003040e00408040e03941460301d054442c04144085414002d050144c0c0c0c5903140c07900d100d15140d28403800b103c60900d00001f01d00300300c0d10040019a070003130340522448003511020580d0a0150084d4015441a11414800d521b0340d40c3c8c039043d6803c00721101d040ea540e1341c20400b001c1c60050005040c01000788030790b0342c1c1c1e500c80a010040980c04840b9018007030b43c0615402c40050740c0009500060721000c8070441f103000c0e0140b030000c1c514400e280da641d40006003c5418405543c150301314a6021000b144c0540320040540b83c000c615000381c0c44003400080342c0104240c4241001d8080c6400c0310510702e004504005500c0002c0c06907401a1400c8560030388001041290000500c42c00c41c081d00c151400e010000d2406c02d03082e040100c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 402893947 1250 402892697 402892703
    0x70e0702030a0305070e030d26061807110a05060423060f0a0b1e01030506030312070c0c0519030201020708030a140c070806040f06050a050108030a0e0a050a030b04050127 75
    0x14803804180010701500740d1b00c0f500d40300141180c4581840500082c00041868000840384250001b0042071790212090184034000151002c44070f400050610740d41002c01401c0602440843c201001a404050040342000c9000380b000f000c25041500c3d0000c00c207000380c080300020a6411420105001000c03e0705c0350400860030f000c0c820b9403035030340e41c0308010f02084007030540c0403c074000310301c0c2c616100480e2070141e41c0098a00700502e54130700b0203040d1a4824040003104a480300710000d40798900a1078484021402641c19180307098440002c03401c241e03a41020301e0f000c030003c2042041150380c100581e101416408010b50b04007403500c440130b07025550300401a050301d1004210340e070748400308010f000000d01d002800c9805c0e030309050412000c0509011425030b0708904180c0010300c4100a405064120b4103400000d501c1c1c919801d40c00c4401043d1010402e84c407042050000500303665038540d42c00518040c0518040350306003071132b20700e00b16508050700c840c40d000106c40d00c4441103904001840c1442d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 402895197 1250 402893947 402893951
    0x21203090c0d0809030312091605030a03050304060902060408100b0a14010c1406010f24090501030b030c03060711010b03010b0303090111070503030f1209062203090e070e03070e0702030a03 83
    0x39140f510b515980118840c46806100101740140c1c0045031a00d401e00958840040d18001404802032420b490340500510740c156001000c6a40041e00c6040259401400340a0010340d012141e8001030345a40264400142c41e8411324410048020610651820300001c40701150320625021208034900d00312030b00f481c144200c1c001c203502881150300f44655071740a44415504150f841e00408116207046000c0c21030a105034480c09900c524a0304c80030113103485907803200c440c90307032030302004601802000d00004e405d4010319070404096142001007501500391519040261714041c6a010700311829050102e100c0da04040d01c100e040e440103c11120000300070700c1d183d00c0c0a01006101c603d0506a60b10460301440009803a503c00e80c6070101511040c0480d07030314440c503034584045450303950109952110070404850b40a001c42c05101d1b09015800d0300ca0306112490f0359491460f4804c8440803070381300300801d4001380c14017900d141c1480340d80060309141209076514100100001c2d03032070141c1121241410307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 402896447 1250 402895197 402895219
    0x1018090e1023010605130b03090a050a03320d021303120519182d09140709030503030609070c050f0a1502090121090206130501021203090c 61
    0x350090245188408046030140920340c0d504040b4100803402440409a4600381d8002040703c40c40740c0101c2d803115819460003100642041010445070f80017920010181c450007001307038001941030000d4800c5a0080d181c820400d200c2080b00410b520b0795000e803154409801c00b4900414144030207480680e41c507080016140d81448486001e50b2060b03410250810711640d030737200c100581c4500140b08403c81c0c00b40c020882010700ca070542c0e0500000381856070340c0344072a00c24401011907001600b0070404078030001d0310006483c50f54103801103450f0011010251260215601c030f201e40690355800c000b00e1314005206614540310291a40000713003110b48940501c4010861081c4501c0c5d4010016403c403066481050030340058035603071801c01000301c40504000301030040d0b0b17038120f2003030701d01106060b151804190b0100c0c0304010300400031655041c0480d030340c5c40b0200150320f40e038020708400380380c2daa1016141404c00b4000381c1752442d03800c201400f042d410000c108543c0c0b000700340107d04200030350b00c02c1c1e00c0ba = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 402897697 1250 402896447 402896471
    0x50f030a080a09080a050604051209010215190204090213050631050603071107060e01021e030d050903070515010f090b12030a09030212060c0307140d0614101809 71
    0xf8100754011011407103880810300c02d00c0380102d5040c1c0644d10034001c07102c42141070f042180783c9000310140d490250b00627055642d2001024502240d01c144012410301060350008111412030b0800e1700100380090b408a4502824410046030344e018100c202c07962410800d0880380c5d440c02c036508804a03130309804080079400e201200c540c410b0300542801040f4035100c0c03504030780c0204100c00814130840580718500000884502400a03000d4040040c1e02808007000c0b00a2250760b1140462403808040c40108081e01d50350400344150b80c01800d074017010713690380c501030304080707180c00d40c4000f40b804102c0751034004000c01510f0000050072905ea061000c1405c0003034400280c0543c4a40848407024000069200481c0d540f15518000f0b4900c00c4070807549181070340302c01690b550411241030003000010030200e070410b8041d01c026002d00304e0300311491f442c1054802d100001c1e14950740c020b9107115402940c5031400e29110a210502e8451440c0008601304145034200030708504d0301c644411184d44013034444030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 402898947 1250 402897697 402897707
    0x1119120204060f1b050715050904150e01090501050607060c1b26030105060703050c0708030a1d060304030c020907020717030304060b01112e0f0b01020106050f030a080a 74
    0x11548441152903aa541d10040c204100c020389101c00200041c4806900521406215200582140080c00c41900300602d21040d1200309110005208041c0085002030341c45d8013411001d5207040c404601d200d40340000c80e0b25030b8032041c0c02900f03035141400d006011940b0341e2020384d0101a002840800c4d99455070400f40c400390151900c50706810b9990768050b00b8000b400184c80550103101c10081e00c00c111841c1e40c040b1500080c01317020340c8060200440c1000c02c0c4288080c01060381c00e0070075074108555803641640303540d101c5282500821680b0071010340c0402c220a41e00d0541c1e4044d01c00e1071452602d6500100b9100d25868002c2c0b25401580124820318401c1100e43c007d0031002c091103003442c02102130541c0c0c80d003042b64222400760602004c0507031035110304a840100c0ca0713103c1c02030406d03455510700c01582000c0b41190064407003590248500040043c010aa003411240c18009201000c800c00242502d16a4002500991403c0a03108060b107001039800340c1d0030b400801490310f074070981004541c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 402900197 1250 402898947 402898967
    0x80c0703050c010c0c02030d050418020921060f06010f050d050c042d05010c1509050c04141e09030a12091b150903020d0f03140d140a1119 61
    0x5456107412a01d81301c094020180340a00c50003101158540717510b10000715003902c0345000311149000d030040c100c600d201c06500a400f16890003403100c01e014004d13140c00c14035400441d00c01c0c0c419502c15030070311891440e03403201d641d041002072070000c400b20340360040074103c0c0c8100c20b032102016a98070001103c4031800700982c0c014141002c1c40c4e000ea800c201042d0b491140d416002110300300d800b61000201980030741803034405240c0c0b001112404544240703110740146040c00080d180c07409500070a207165541c070b201c1c10528900d850600041818810305105440e91044c00d0003121403002c50030b00501000000590300c00c0100c51400b4010b03106003d030b6035005814641001040b051200354100c01c0103804981c1c42003520304141e00e15804080b11101107502c041c1c03600c0080e402ca031a080403038010400c00850758112502030305204155240f006039800d884c0c0e00c5109155556590b510000c9019003d960115412402c1c80f04140040417000c1c1d0b54050520030003a10324142c450301e580541805004020080f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 402901447 1250 402900197 402900217
    0xb0616020301201b0706140c03070506040b0103051b0114210a05040b1003020a12060b0d080310050d121b05060103060225261b030909060d03080c070305 67
    0x4808140092010701d07038000f4140403030141054071030300d0036207000055501c01b01c50050756608a0490042c1c00304032035502456200240d80410401074001c1281000514000c511403402c00d090b540c51b40c10100d0502904050100452000002c000d805a1f48403811796080f85480038615507800b44c2415400380700d40c0000d007032001a0100703010415a400300303030711031846640110a034108994501d181000039100901009512409002041c030000300c05001000c0414031034003000851240d40300000340019a2010103c0c2c07444000020004d815056400000040006441880c184100f59482c0c422100d502c0100c402003220f203290821071500c4004010310226008400e0741c1e25540c403800c0107406588400103800041c09204800c2a54030b5015803808107540c3c1040850001250034850317801100b407881c0c9401100b4070203210b00715802e0245502292721844500003076a40b80202d209002d18a1802810305114111000068000c00c1c0c1004026612064000c07242e41e40313901e9454207030340d540545500ca07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 402902697 1250 402901447 402901481
    0x60609060a0f0314010e07081c090806040c03030e0a141201060509040f0b0c07050604120509030304081c05030118020c0a080a260c22090207051509010b0616020301 72
    0x414850903400114841c40024021b0101101c40c2c1607490b51100248520807988e881b185442c0c00746c2c60303602e182e00d1000714240b5109147d03568078401e0300c1c030b0250305031016503010711050410020103070445059608281c0075580740341032500c1d0402104440d07070200b200034020302c1d118400c101301003000c3d484940078140080840a241c141400c0c0342d01d05c0c0480e440d00711460400407001c100380c0b81c504010f484410f1360204c003c10907a6110f9840c50000d00384200a4010300005210040e0309503130500c00340003d05440401409840718100b00d81018074000384101e0140101000140182c4185034040c2c22210107000001d81c2da40091400d00345810860900a800810046641c3c0300c1950b00021154207146c0c2c440c0c040f13109a0300c0c03402051000c0c034182e91914084200701b00c070b600107881ca04890190210a0f000d403a03030550740c2d04522010782e031000400b194140c2146024020031b0b18074100a68200903514020460b2020020200302203100b04c4092225802c10080c030034045540075040012100910a40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 402903947 1250 402902697 402902699
    0x2070507060c12021f090515090d02120301033c080909090c100f1404080c12010902060301050108061f050d0b010e1807182702030702060609060a0f 65
    0x1000b800924501e004a42140c080807400354914400034005010361052034203500681c102030303040c400410003a0004c07249405030309800c89095000c101c00c103100c0e404540150280d543c034064001d05140581c4882440984180018400300706080c4002d80391086103000317103650440400a404400e0030070940c550f1100405035001003000200c40c05003203100c0303041e03551400e280c03104d0150b5070b1601d072050a40390304012140c2c1c0c42d10441d446009408907ca100307080c40c2851240743d901d425100d43c0590840310065111041c11055818500d8040540301000d1008200048039030b40065410320040c03080d00e0421013800046007159a50845219058080200c0001d18881284015000d0b80020480000f1903140c00340f2900c455001319140750101000518580c92121a2000d0041c506c50140c49c104c00c000d107000381c4a40c88071584e0a40b80281050740c142c800320442d002100034840300012a1ba40d0844c0c0184207001e012a00000d0ba241c102c6411134403a0420390b6182d01045400307582d41d208803044806800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 402905197 1250 402903947 402903959
    0x30215040c17210310090510061404080303011401030204080a0507091a0901180b030601030b010e161709010b03032113051504050a020406081005090601062102070507 73
    0x2220030212906076038030300c4400761001e40081d00c503500c5468201c54620b41c4801c04040350362a038020743d44222441c038011740194840ca9200c080b100c2c02c5421249000030100f00303200a5410004280e411121118001e00d01824040d403183c5a00040c0b05903100300418442110b5540c1c000c0d0180c5010305200d500b01d580011242c2499641c5c0c481c0ca01c41c0c2101d1724a03107101010550071100d400c54840303401400e00342c4245d180000803805181031041c42c5c00b440e580c900486140703603001d010385d6000314000c10610340954104842c6802018010f400956070b00c1c81855080c44450b000004494900b402011240b802d90311058528054003003840348c3c80c0d05000002c0c08414040740b0030b064051051401d84900c14580c3c0c0c5441d0f8290160506402400710703402800301c4d5840e400c3c0c080c1820f910a00c903505030758036000710340d0106050320395135040305103142c021054160340b8086a200d001d074440340100050002e54902500600700e900d0030a07c0b89411103011190201d4900c042c0c044445259000c0b040322242a5600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 402906447 1250 402905197 402905213
    0x905060c15070806010f0804050106050607120f0516060504032708010b04150b1605030304030e040f090b0c0702010207170d091a09220e0f0c191203021504 68
    0x52031030000807160700403440d05480f401d42144182d10603150b07464002c680041c1981c14070b40c000d0049809648410780442c141e11b408000c2d10403141300703440300100ca8044a50140402810600d0101001824065010f000c6904032826500a400c150700280c143c41c0c60408441d5013021100003042d10440214403c0309020015880084841c00ea008028400381d280c20442a11a45240030b014000b510000f4401e52204400900340714100100c00c3c00220b0f0340703a4410341190002c031020b4001c103a900c0c2042c201c2d400c1c1400b0340d240104440b031b410841070069035504841540c014040b55040b40c0042450b1045900811024020b044010206d0340300304402844a5a07642c0344150329030014180e00400603a0301101c03541502448000000a42030083c61130034082c1002d0100d2003401340d0103240c00a00c010708514452445840540c4015007001074070713145998644241c94101354002d04034862280d50305100130300030302c00740c5081c0004580911041d04080b031030010302c1040320281086150501042100070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 402907697 1250 402906447 402906463
    0xd0f021f1206050619080601050c0706090e070503090d050c03070203101a090103050709020d0209130b21030f0c0a120206060108010f23030f030d05250c11010905060c 73
    0x1c030000303200305a100c2090043d6401996003102d0840e21019464038150300138980d803907101c10103142c0203040403612000381d85030440326480840424049101400702400031a40c0071740c0007003141005461400c015a010740d40703205c000c20003401c000f0041070400703c3c40d00078000c0341d02d00d46c3c000301107811444414008100414122034000a00d150320358841140703081c07002509040307903000307009000c200d1b14080210300694014001c460844d9420000b523511313552840410304070f0392842400003031041302070814442d40c20714000c111098141450700814104d84000201c803d04900040e016445021107880e207031802c1e1039140300920a00e02d00f070060744403550000b00c0394800d41d026070716050540d903107111041d58005180030704101440101410031030180c02d09002a030000340541251516800512a81c1c2907410007020100115140c200b441060400c80c1002c800281800d4164468105940e02c0038014482d00c6078010070184500380d640c500c0368011040113000f050090f03e85541d03599040041e0b600c2e2070304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 402908947 1250 402907697 402907727
    0x40f0914011205071502070902030703050601020c0103020903070302010c080705011806050a020909010e060a0803180103060b0a02031b010f0501030f0302150c04050d050f16030209150d0f021f 84
    0xe2400040d50044030502450350540102c054080c26041c024a01072007400c488100d01944110b4800180d0302200c3d02c011482142c1c80e5400241c181000b900080c100030407941158100f500502c108107582c1d4001c9410700c02c5a909090900b10006203203400500c9014080d4060304035443d0154188901d005406100602841100c1c02c1125903904507910040b4000e000c1010382103610301c401880005c60302c0e07810755000030000b0503d043c141d40e030301026880d540c880c0e080211418424803e002040d605801824040d040011496060103607900c0002c1d500e0050342030321604d0702c008070100003140100398032180151143c1c4c60144200e40c1c6074102524542d0305800220010312551825200450302c02c001b56015400240030f20f0f241626040810014648406081e41c541c000e041d03501c1c0301442c0800052221210000541e000a881c5004218030050010f01c40000000e24070340303240749a0349540340c000c3c6c0240e018865400c60303180c1b4000711f8100e80c0300440c030240004007403074204d0010350800d01800e90020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 402910197 1250 402908947 402908981
    0x60801020403230a0b04020102011b0e03071d160c0b0405030a09051002060f0c12040b061503190f2c07050406080a0b06040b0603040803010f14010c17040f09 69
    0x7a00212141108840c40f02c0380e82640c11142002002440300b010054001d801480046140131211948842e03210f4001c1070344000c2041c662840742282030902c80c09006007500071100350500c078a00314201d41203000505090750004041c20b00040d490081c15505403407a00084211958a1f01703203005a41c0b6030000000d400451100080060186411031805441c49516406010075881e420781601c500c1201030300c100384000051283c1c80f450300384070a21910035401040c001c0e995003086000c0c00b01c00d065150000d04800420002c004503a040d101d14a00c0d45060440c0c00114144101142401444203200d104c2d0041c48d88042c501810301860034644c04515143c0a660109a40760100701c00c40e80c00d80701b01080380d04061440000b140c01d020926070f100c4030207803000ca1003200d1200080e803980d000311030440301c683c402f1005010316541c0e04400000341c01c1c122140d11301c00b181c41c00007070003030410250300a00a035450801225400304560641c0c1c0100040d04808644c1911548184040c1c0710685884450f00307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 402911447 1250 402910197 402910223
    0x1a0702010c08060a03030c12030e0a08030604050c0306091b04090e01050a1407021510030210050a02010f06060503010513060b04060c02030c030d0c0b0a0608100e060906090d051c060801020403 84
    0x45000e840b560200d035803581f01d4a04030144d55540c1d1001f60640d00c90700e81415034810f140804600c082c40348600c030a01c45c903201a0390b03140110801c400c440c009481c04904a8040c0100220758844144150700043d90502ea02012645100b003607440c1c0c4241d4000520603030400c400d034005410705410590044c51050024481c00c1441c1e140e0070000c1d9800c6030041e005910181500080c1013104266907081001303003038510f1340e603901d030340100e03508039600c00c9440c002540000b0100c04c2260b0a20840c02c0c4160804000d1183c41e103060301c000d14900043c0101882000d40300900c10456006c4e0344050020041300ca1450340380c41e681e0801500039000268207900a00902c4c640c0c011a28012407140f500a4154943c90010041a2109410140004c244840450b61100d002c02c10f82010001e200c0f09900310400400d2002c482e1146604000015244a4081c1e0150083c0310041c040401d10b040368580502c2e0241d25002806a200352107040510303154070052130402c010503106019001882542d005900c844560 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 402912697 1250 402911447 402911449
    0x2040905010302011e08012303061608010e06010906030b1206090c010909060821070b130c082b091707030308130f0209060f090a06060e030d0203161a0702010c0806 72
    0x74003072440e00170001880d00700041c88542058814a08140001e08160441c0465180030918144050302d0080d2000d9080011000c4180c4c030800d5680544200f0304190368608000300041e001d044240190340c245510b489010304107490310047c0000c0c4003e118202d4409041001000e0340b600200e040090009400080105000009000c0c14040714010b20003411800356620904441003d5403500c0e03401c040c010404040401c200c07048403400f610303010388034484048541c40c180480e105164003032030340c0b900300c5164403600b00c3c00c2c3c031003841780c101035004925640e0448000c21190a0038981048030100b070501140800d8610004903031046c0c900c45c0e103401c0d4154441203000b100740080d5030310042c0a02290561903005083c0030542c290014000ba020022030345e840c40000c1e02c0d240c021108143c405607292810403903141c1c032011800c9a00030540141640324401c58000f52030744102d040403c4503400785000e041c00c1090300b480380b03803c0c11040c01c00070942d4200664002e0107003100a10113800948844042400c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 402913947 1250 402912697 402912737
    0xc0d0c0f11010e06130c180204140f06160510020a12050708040512070c0f08100c03051003060216172805030117070305030c0a0b0109060302100c0501020d0204090501030201 76
    0x4651001000303241c1640c4510003008817207505101100c4c0800f0b81070700041c40003403440042c8501d03500b0701c001686960600300883c0000d00314054452284c002c0780d0310008940c407400e0446e030002504e4095058007141c182009854040400700b0080d1452000900c00300042e805240c1071340d083d441050501003501c40d401c0480343f0070b0043d10701410b960080b06150300d0440c590801041c5241c0300d0008090542eaa500d5414480e000c55440080d0703a030810004e8003c88400f40c4100214180c141c2020001c60400e200350a03501030050000074a070075030004126411450300611061415440b000ca4142d43c180b189012415400803590b80c48047c0d400000200020348081846c0d80004040d034450b81940e2070090b0409000310b003042e030a1654098a1004004142c05000030850050003000401d810340302803814104003d816072007041d0103898040c003480165142d0450901008007458981901030860030118020301c903040401070707528800140080d1058081e0803a5049038000d80314810306c9110b0f081a155 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 402915197 1250 402913947 402913961
    0x170703030e390a06050c072103030e06090616140714070b030f040f0f02030a0605180303010f030303240e1503010b090609130b040516120c050402030c0d0c0f1101 71
    0x5404003808201307000030341c41140074200d1b0000440c11503030811781d2107511585007c40b20b09481000c00e580307426103043c0340c0c00d4010030321004e040d00d0090105191000e0841d842d520068170200040f2032941b01c02e20000c8c4200d840e4002d0203040c160701075803010301c2e1130300c4204040355142c902e038240110500007515640440070ba038883c41d014203c0500d21ba0769555030082c4100c082004a81c00164216241c015072801c100300d0502c1c0b840b6080c00070f141d003030030307800248044100030450907940d20810042c0010b8181c001048201da03490305000c10007800607000544030800d9038800b010701002e10341000500701000c4459070701600c5020300c0500c83d440308c40185400c0c1c8442d07d05542d0010748103004150242480045141d004264010010000700c2d2946c0350603841c0015101030b1045e80c00901c1c581100444426404001e004014a20043c145603a8a1138000c1400d8816280309550110000d4484140c4001b00c1e58201c00090080282c821485c4000d002c911074070700c0e1440020001310219500240501c103a00d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 402916447 1250 402915197 402915199
    0x307080a030c0b060607080c100f06030302031b010e1212060109120b0a0e0a080304020f0307030f1502070f12030f0209180a0e06010608070f020a170703030e39 70
    0x6081d402d03151503100380076101030806500b10000700400d40204940078050034401001c2c0025001e003100060300c0b0b1068994400e1100c00c2249001d00070000070b600041103461031003182c4d448070500408a40c8031801040c40d4042c0482c00c0c0a4989038005091801c0c00802900d5010041400c042d203c1200444000465010b0f8090601c5100d1000004ca000d4a0a06070b201c0301400300481d10070354000c0fa2909103006180200d83d0021301005000461500a08208503640c041c0c00500c052495a151480e030003001c03503400740a01c03030001990003100350769804960041e074100803840d4804a0b289040d0032001c0b0414172610009242810600b0100301c580201c900c0300500800b15912200300300050120450301921035041103949000380c40844000b070081034020403581d110380b41c0c0313464981000340c4214400b501c000115000b901103000002d2a44c0b55022806545504107600c070390301480d0a070005c10700240e04000c507103d02800d014042c4a1590100c3d80c3c1009910b030303070302c0010710000048904504039201c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 402917697 1250 402916447 402916457
    0x31e110301180605010e040e1006120b0f04080f0c0703020a180507030506030c10020709050a060e01060206160c050f070902130b0f03060d1e05030304030e010c050c1005070b0c07020307080a03 84
    0x1b000c6498160481404003943e501a0380401d881c40c40d1810481d80107511881260814801000600070314046041d807004110403040300914046d41d490086200d000e030001060b0341c012a28030001242005a0b002461b8050000040c00ba01e4011200c844011401841c1040d17091000251411b48070b40600ba0050130090000d090102e507480410240701021601c1201f140b085200c00558102d1070300459020b20304495001810780c2c10b290008079140c80c160002c409543c00b901c280031200400740595494410b0703600c0c02011113084d6250190500908804035551440f600d5000b20f854190782c1d006140701e80b1410010200c01e81d4030503010000707019101500542341010301c00241d140c100f0602a02c601c0744522800b40710802c08501da50391421403210309480561003c41004101034110281c4910344c0400d09110b88000d17841c0d03407050341e507004c0f505401d40148194aa58014a40111b080d18035407603009403000325031315002526491907000030780180e00c41c0c841c1e0640010000400700301c00940541550b10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 402918947 1250 402917697 402917717
    0x10b010e100212040f0302040e0316020d03030b030604030908070819080a0507020d0b040227040f03030213121e05070b13031203021c050610031e11030118060501 71
    0x2007101d1403009501d01415406612046a442111100100041c1913080c60344a8036904600510044407044103241c82e150303004018595a200700d85030084015941110203400d1403c03d403a0880c0039003010101c00703230980304000a0008040e0000341e0441a190190101c40300c00713590f1012260f48440d4110250000343d034504520740030514540061801a4442c2001443c1c0b0300d0543c0450402c2113040c01c00d403111402c00d006d200851074824091030807500380b44507a8040c402d205003140840c4001400080ca05a4445004010140260152038299900300580101c07180d03074040120820b03030694811220211141e109801200d20b4804817011207404c6002480b59500f098080510307588041030200c40d9040400c030000001c1c0e07603890b000b40d1079051680e000d81c9401520110808880406003007075903450501040048544a01a5454088900d071801103100000c0301116014410400d1a024190341800e40714161160709400460480f10301009a4403605014051030044070b1442c00f440e8001484044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 402920197 1250 402918947 402918949
    0x103060f0c032705070302090115020105060d081c090b13020a1a03010611030910050c0c030a02060d0c0e040e0703121b030507030203120108011a01170103030c050a0c09050f0603010b010e 82
    0x200401c130700c10012103501d15126000203000e560268040e2204035070881c0c800301d5a660a018042d0420410341d0301c070700710304500e9030b40d42d409000b035a081c07000c078501c4a40070314a02100c0d0382101e0b15643d080006a01301d410000c0a402c40e03541030407801c5c0c2c05499514070004480d50700000c402c40c0d069080400500b983d00b0420b04503908240002c5030100d6100038418811280e0310704080c6003011406444087e81c43e40718900307c0e401c1011024003180310703400c1810001c0140e00d81c102101c1412004020014049080d10425141071044141140e001454400c1d094001000001e00c103041e2800b955441040c2c01c2c08a500316820144001d0240141080c0000103000030700400207442d9a034401c1c0192410072201035041e5184502c26032013400d580c1e441c0c1400f0318041c02c1d10604441000020302c0c0010340d042c071b090030384d01d40380d4010700c0002d0030000d442120406215040c810903003566405a80302c2500c0b07644480c0680074000c25a45d0440104094000c9101031a05203d10384002d14180c480d10243c040c000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 402921447 1250 402920197 402920261
    0x1805060d11040b0f0d0b06130e0a02040b071407051c0308130f03030923060c07030516050102030106081302091f080a03120e030f190e04050103060f0c03 67
    0xc00c6400d001e81c800d02c40420103800002c0a4904104002011074032078855003a090291002d204d102d50240908000750401903c2000c0c10406a0700d6036080140c03103864400882000b40300e1548140c50315140490b2207800c05c2001d0701150401c43d80d00c0304403501c1c3e81d2540c0030000242000f880700714030307081e0015500000038044d0103c01e91080d544a180c03016056035840300c070710220031744104400095442c0c1b034540411421149403040c0444500b15a41d00c50340601106981d0034000e0040d07004000301050442c101846130003141d26560303410340009036520261420354081c6d0828011280072403040c42c00141d100080903109a0201e800403e0030103640c031400315a4070850480010004000c0035007101041e400810040041d103140309594940c486d07141c80c1030034001c9941f414610111500200501c80103050700d101622a6454000860b8807101101403003645c000790490202c0380c0003802d0400000901009910242104001b03020034049a03803402021811116880c210f9001202c0b00c9010882e446154 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 402922697 1250 402921447 402921461
    0x7060b0102070605041703040f1403100c0203120c090a150806010e010e0906010e060f0c060c071a0702010207150605011106071209020d0218060112110301060531061805060d 76
    0x100b047e2071600b0b445448104406406401001c00b12800003940c1c0410b0030b04200c4400c104401c400200401004107000075100e21501c0c1c0100c0300c07141f80d1004034645101c00d108984c44203500921103042c1c566030341160000150804205400300700300d200001c02c00e500452400d4010030059403140360950000b000c110861102070200741c10422800044a0944c0b80d010040240d0658031004544400729203220b2440c100000b041e001d5045418004000061380360042c140c000001c0080b0202e8503600c6600c01c9009005101d40503110b00101e410340c1c1c40020b9164003240a44500381e03590264a20901c850303e948150603201d100001d02c2271101064103418550041180510081c14110101072540000c0c50049007a07002040079004403092140543e004002160340301054542072200c5031203c0b035144481c0c041446040305014000401214155040088a5000c507501812410350440d81e401001c0000490040710082501d4484cc038141040030313080e4104846c4010003d5242882c00c1c03d140d005402c10b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 402923947 1250 402922697 402922739
    0x40f1e030804062c06060f04142a13030201091d0f190501080114090f0a0602070809031c020706050c0a02040f02040b0d020304050606010c120c022407060b010207060504 74
    0x301c4035032903841020410095016110f42000303054030b04080c6c2c100b005034080c50030b2640c448c6152102622040c01002e2825520400c141c0300c5c01400448420309104c0c40841d40d946105510000804041c1e184080c00c000d41034a00030b907507140b4051b4669090a0010408400d80c4200c3c50b02400065004420700140350b81c41420342031000140c841c04400314064501c00c4e048000f5994440140034089400341c1c02c5154001c00140003419002d107900c11407034031680d820700050501a0009242c1c0c06122030030782102e8031303a003000e004c817a034460141d907a881325141d85a0030a0010b0003500c500056071032180054409014426010707240c550825400c0100800340c05c0c8c00c0003c0540c080c0b0002856000c140c0150200e20040400035a80e0b14003894003504201c1c00811060504c00a02c1049000c15010800001c1d00e210a040441d8407428a000007000840c50044081e85948028800400300402101401d074442c452a030034040c5a60131001039072505281c0c021900055801e12042040d00311001e032a40c24104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 402925197 1250 402923947 402923981
    0x614090f0f040c080114010e0c130e0606040e09010b130b0f010509040f0c0207060906080f060402070f020603090c030601091a06070606260d03140105061b06040f1e03080406 76
    0x303540e00d812403d5848000751b00889021481c01001003515102c043c0398410301410245152003080341d02400403c1c6035000d104003040130701c80015240c0d200c08040300c000d00a808440032441c605802c09074045e00440c90914000ca1114000d4041c0c0c040d203000306110184001c00300e043d40100c4e03000441e4a0b80014124550150b01d50100d07030014443c9129544954904e03a014050403400e1202c064000400e60740524100281041000b0211000042940d08882c0c01c507009a41c807042401c00700d80c0603001010103903000d200001400f9400d00d0001c0c9070114043d003541900c109a980e045854211070590302c0c9003c7c1241800c49540052401e44000c1402d24131509000403116112010060a00052051144901e000c82c405200c070450400444e24241c1c8180340a111403082c059842d0501c00c410310416001e4a40442c94002038464a0014401c40010780f00701c646030300c0c2c2820a016826100311003030b903002440d0a0342c5134048400c056000301d459007580b20043d4940311543c0c1e00c401060a5440340b50462 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 402926447 1250 402925197 402925199
    0x14010e010e10020d080702280f0b01151103030405030403060b06120c0403060e16031401060803120604110a0c02060a1b0b040c090603020a050d0221010614090f0f040c 73
    0x41d450b110100040801c03540181210521064068032200340605003c3c255400132200b00203200000b0742140d01d4242880306489480c0c110310306003601c120030400040c1507020010000c640e105841060104880090b0340f80c90b80164030a041e1a2a07210965018082c1c2d0410881803010414680018510f018045d0905240c282e25100380550804260341c90706016000003400c10601c81c4a010754a030b80e40450000d0241201740048400c0d05807924400100088140c4500c2403488000b90b018800418289054940e640905291020203020071030300c4a1166261500c060244e00941080c2c5032918810f481d1303004514229000c02c045500044040030822403003d60203034000940c0b041c03203408140f1440481ca05410710746031043c25816160001200039160000400259496002c1c0e20116102503c0008500d182d034004251154030100b007484110f441a50500f1810304154850401c60301e54a22000e0602041010486041d00039214210036038100804189228130310a070b0241c0083c03285803070322011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 402927697 1250 402926447 402926449
    0x603100b0922051209030c040b030a170c0d020a0c121502030903090a0303080610030b030d0503041a16090906051f090302100906090b190807020708031611010914010e010e 75
    0x89880c0000d04440300a0200301405d1a00b0b00300450f01301031004980034408001c04501281e65440c0041e406008010075510041c00541c2c103808a031540440d410a60b03005401080000e1b64490801030220f039907074000600041c1040030820484012980809500711000ca0100610f019400c090000784103400200240c0f541d65072840803000c0114469290024146400340c208401c0960b8410540c0500d030030801c014400c5e6501080c1111118004d04045803252600c1c1081003a081ea4007810384800d002440c144110070169014105050b0741c1d0f90781c3c15504a8840281300c069a0042c42010780010b10301002c40300f018681480605516040e242107002c07140d60b07400040c079000480e4010170204030004400e12800343d0040242c009807000084851500000710060320328000c82c5820002004404030104020358401e10049000b4071204044a449080314001000110514901190055030302045c6640c035502842c410f80c102c800089000a240700100d0054456090664203503040003001071801c886 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 402928947 1250 402927697 402927703
    0x13091a1b07060c03140705030601030e0312010b0319020f0d0b0402190305060a06030905121e0c010c0f210506060405040e0f121c1a03030d050603100b092205 69
    0x26035010700c00216103410070803c06400c841c49641503c1c20281200200810160040104c0343c000c8000c1c600060611038440203c0c0c1036020343c22070020424120390000031030100e05ca000d0740c000c51034081c02441400200032034008904c2400c58003076441d4024041a00000030660190404410180006d403a0560081190810381c0700c00701d1103000701c0e5443c001e03c0302a040a10118026001500f4204030014650300d900b40d81d03604154041031038810008800112081d142003000b2400c00009085454502001c0c42c40d018010501741000062108041e20007034a20491071521401103c0300c800c2c800207601a4824080e000081c80541c10400403c00003800303859600c59110701150581c013520101740b1035695641010080c07040019528818401d18030f0703000d1355152007044003031262800581e1048034825428241104068240e01d4003000c01d20122103c2030760030540c4640402c406490140040500ca4801c86041c04240c0d60440380c0700002505443c0d010040050200701062140b409080c29a15289 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 402930197 1250 402928947 402928957
    0x180b030708010f05060405030606060c0705120d0f0f0503040f05010605030f010b0a050607031b030c0b0414060c0a0c0602130b0403121b02090601120906060906030213091a1b 76
    0x10025440c400100190001050b0303c0e0060b003402c84445140c2403400c00001d13034502d030181002c2d11400c0000b40141e0851810010003000f0031002e403120300c0070a01e11007460b0300ea000c48409032005c00c4108039001d075054410014400024290344032a800d61f140ca8407144088240a082101c442d981c40c0004101d5035410003198034002603410010549400754801e02070022456800b060080805004007000a038002091030a0302040203400040f2000d9424221001d4845007005800f484d8140e003032100340550418802c551400c2c3c1d40496080352124042d00c2403501c5140700880001d1a103001e420001000c0fa0000e105a1500004071840c80307403201881503156015910032a214140901e2121209400c00c50300315961031480c1401107110080d40100329202401880071b810404000010007210080e544030380641504001c081008584030300c0c100005002c03c0c04164420360b211140221002840d00800300034680c4160f0101c509500d00006503404500681a11040c40101c240520201c1074100688 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 402931447 1250 402930197 402930211
    0x504050c0307080d170c070212010902060307200f100c09080706030c0f030506100302210f010807080a050c01110f0102031f0605180f060d0203191407020d180b03 71
    0x10281e8001c00d28054160140c10070605c0980b00303140104900c550400080d12219030f010384060300d0301903101003100e00401d69100000d60002000c801d0200166201c44051403004030b0445260440b02c0103190150303220481314611080381e108a400b501032095980081590010074180103a0707194903440c0160600900c0e41040000179520b019048940364070a121191030711060408205504040c0003107002071a03e1f902c810141a0002000420f01c040100500109001500c80c8007603400c0001202c00741403020701c945032092049800c04034440d600402c0d940c13034007540140100000d0100030015104100c5400d00d000650240d2040c20403950000e00056104030310021007030803d103640f0340c08840008229044001000400d01504d20700030341c48100103000031821603440007401c00c2500021024401d8440741d440c1d0305e0010080c0300c1954034484d403490644000d85c50510016401e21943e02202d2412a990b000581c82029140d003850300541002c20020301e400303c4151f1050721041780b24a1548152210 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 402932697 1250 402931447 402931453
    0xf061e0d110103051b03010e100510030e0f011134060603061503021e06191814090c03060d0b070c02030c1e0f0f030a05100b0f06030403030504050c030708 68
    0x403161a40e0f2611559034070002602d02c21424211100040103e4041401800140003251002c250070041405001d030007054020094100240407400c010060b124907152114107210b400304401b0405018002d06c00c1c1c403030882505904041002000c1802e045c03a0803070000f0750b47c0c000320f0624812031094002c0301016000c0c480c082982071075841d1840849902955600900010020038001a07551070140d0f128801403142c0302600c4040f400000b64240318039011051008203080300b1112954004104450040080c071446140c250307103c94040a40a4000507281c2c443d01c190001003076189240c029540041c40a041d14055401aa42e00e021806050b1000700c00328500340e66803030846c41c0412841401c0e50003a20300300c1e1b0070840416404030045110b0681803180603d80c2d4a02c0d0952250074040c0c85400008040b141c01e41310350300380240c81d6041031011a003450b0a003240c03001141000e10300c50300b04410203000145540ea950301e0880007020060002c451703c2c0900040300066513820416080585040d0001e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 402933947 1250 402932697 402932723
    0xc030f0705070e01050117070905060a0201141b09060d0f110414030d02030324030a0309060206070216060c03050d060312020c2e1701090506010311030f061e0d 70
    0x304070302c1c0042942c8150880702c4036a0040c06266448000e80c0c400000400e4161416140d2560079101c43c41c003508425000340004c6011003080340d054004683d60f08890307540242c952207500201217886070515806400c00e204100300360044c2045401031800d540d52072800214801c4122918007510450300891901d04804641800350010400c0c2c000855181100240030303051100e40b019440c0e0000515091081301101d02c0c0364030f103200f000c03000018458020262140c1012a01e00900801c203d40510001846120009a282400040d0345080d001c81c2106201b500c9290400440720916008021001c00c0360a101c40e8018203205e00500010b10320855171a0819964007d009140141042805228070580203180034407159140c0c01c0d907421201c0d00241000e01210b03840c266001141c1031203002a00b10044000501c0b040183d11590166500743e03824450086a40b080e580035000076989074000c3d6131001c01007999407820b40c0000d40007000301c41900c81e00c0d0018500240d0400982001541c0120300144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 402935197 1250 402933947 402933953
    0x3040504050f06130c02010f0e03040e0106140711150a020c03060a090c03080a1e03230702030a030c12060f0e0604060e0703020a05070605191119050904020c030f07 72
    0x7420750700410050001d41c051808000007031004205110000250b50745050706a201c0d8800c0d000b512036a5038420b000c2c004030315540e00e155925800b5204010707401c1c0f441d00000c00c3c15445440543d8040c6480c94545e07092910b503403a4190700d130107a046010752082c0303c05a11161840c07064042c0c0342d541c0c2160090b1800b000c3c241c05050822200800f42100c2510b4594131a000a500303121400a890b002035900380c0300d84c80180240c0c0c01c1700700781500f2801292542e000010155060300151890102002c0744807184070005201c944c804002c3d17400c4000340c1c2060140c403c0031071107a401840218402e180c807400e01c4c03044032503510031588160440501e54038240020720645000c403070380d560010000e5404005051801203620320720303500903000004054002401001481c4207200340c8084540110080105003406c00444230800301c1411048900c2c3c0c2001c40d14100c0041c1c50095403018201e10100c0c07005600a07201c00c490b40d0303100c0300b582540300750309100c40081018104003600f00c402600c50020340d10300c0365003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 402936447 1250 402935197 402935201
    0x60201020c0106060216140312030c040611150a0c0216060320070b010e0c070506010e011715060f06041a1c1e23070806010e180115020f0a0503040504 66
    0x6002081175510040d00b14041180c0307110418212004c480c02054404a1040040e04011070058400342070440401400140260380c0c008000b1100c050700c445c003a4200f40c640310794860881070b0788100045540c00000d00500d00d00d810010700100644181c07403901803a40100500902039070420380019039140d4a00a04130002038001c1016955480f5039402d0007100c1d07031030011040050007001c0789040881d02103003250b03100c0c2050340d0030b41d94020191040d0b5a11100c148210f00000d04c20005146241c0358500300000f40461071070205400c0e10071000c400e9591030244013501c20040c8129030000b07410000044c200c020034500709030020028070002c1da10b00360007024255070070040e5003140e8031905d8810b00003185e900109004050300080340d404940154100b40c0160f108010b030800380c0610b0003c008000841e0307800303460306100e103000340c07103908030600e40f42c090041c48210808190040303001c11005001d10400c00942c4080d810142c41262483d144107444282440c40e412000c590980c000301e02881a0314042c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 402937697 1250 402936447 402936449
    0x16060b0d2904020303071e140a0c140321090d050106060806010918050601030608100c090b0a0203030a0b0303040512101a010806150426060601080610120b0a060201020c0106 76
    0x51501e000303400d00380c00103500c034844c00100034440764131850011880d103107035001400581d400103407490b0110084e06006071688051401140c2c0c40802040100d040f03201c2404480c56042c01800402d043c804940c0c3c44401948207002000d130506060041740080e0ba0303444c1030301d8400381c4140008200d10345000005030240402034441414400c01c80f4050001d1018850b40b408a49103186002c5000e4842c180103034000d10454215071810f0054100c4a5051642c0d5041404400010383d16000c3e6160383e040807030020301954247c1d00050b007042021410507284c9402ca240003040c001c0a40f8503260340c4000142c0d2024012100c0c81882c1c01040c80c1a10040080c0b00d032040128030092502c10028038900002c010b2003008042030f00c60500030030341074195162181610007605d10072208480d01c80042049404900c01008198007900c51000040c1140d441041564020341003d0104040e000200300c040e24182c003902e003600d422a0361001c654110fa038800e082c00005156036000141d43e8044168510709403205 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 402938947 1250 402937697 402937763
    0xe0c0a0501080402010807260906060a050406060f0c1103070807080f06130206031902030a09060e070305060606070807080403120f020c06030106050c100c3216060b0d 73
    0xc02d504000250742c00203589a400612441c00c022085000003035484044041d24040c180e071440101000040c0900150690003050201d0b260714034039680300704100645981307004040004404200da405c00602441421108920800317480b40d01110101c0403a1808000742d2040743c1650011703100300b0030a90b060020480c90140c01008d00340030b01e000f02c90318414640c0c1341c5000313000e04e0700000010030040d88400c80201500344610155034074280307541d20a0140101c81c00030f80d145450103103815131030762000a050045940c40b0014000716500d00d010004c490b0410a002e40c1c0c01c000c10403050000544140003000514451880300003120314260009221903540c0216000355030180032800507554450058074110f402600c0c00603a2604030600890401c50369000d0030f01242e0416405c80c1d00b00c4d400031485a401101021464000300e8a2801186428010105607034a21010011454661804010054089c1c001e02c000700384e0070280c0c00402c190403084401604e00c0c1900c0c9404041d0618003929030200410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 402940197 1250 402938947 402938957
    0xa121803080a050304031b030305060a1d010905070c12021f020306090402120106030204090f0302120310050d020d0516051201022b11031f05060408030909090106090e0c0a0501 77
    0x400d60303403151400e1052201d204180580880024201072080c15508016a41d5000400803605140b4002c0c0c0908410380e41e10703200b1440d11070302040807001d103070300395000400c1020710381c0d4940d1a05030f0030001400301408040410140034184804140c10141c0c810340395400d5401015044106803016088401104042c0f118600400500800f03603220807030103403c141c0480c3d0440c21000c056111038010512030f44003d41050401402c541400700c01c6811a41e03440c020707000d43c1e84028440a003246c0610085444d5650001440700a00140c20204048412144080e006043d030075425180d0740e00d0802624460030012800070018005814940c1d4034040c03504144000b076051884d500e42000c130002c1c0d020000681ca14028000d0050445148c110f40341c54071952000c1652824000c1001240d102c0c605850512215035000c0010031342450000c913011601c018014504201d043c00c01c110411001610480f0203640316100071454040501c01c514280c0500c41c002d00b00d014108040c40031500060740801d0604c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 402941447 1250 402940197 402940199
    0xa0b0d020d230f0105010512030a0903030c060f0f0507030b0a0f090506031e030c0105010f21050106080102040b09090105091012080c1009031d1318050a1218 69
    0x41c840d0120703014407681c807a210100090710159100c4004074500628091486243d15001c8248410361009059941c00e0b60400700d492442c862682d5030703100d890b24200001c1c00074581040403a10401c160b040e041d10921000c902d07200c48040d0070301615044507135030040540d03420500500b16014415192002016140b80e1a281d10381044244c42010b03510891090719141c0000500e81c1c1e07401d0040366054100d2540303038550100b00c0ca003c15a41d800c1546000c529610b442c00100b038540c010a030650848600c012114804060400c000000190306202128950b40711100480d45160a00142002c1d00f00070704001e80750504c0340304001010006a2106000d011680103014041d8a2040c0c0c4009880400d58002e2054206250481302823203941c0d1524164003400020030610402e64020b480c003035000e95114202440a80994501040c80d1035101303901021000e84120072049580040c403034840d0400946030800c64548800b42401800c0304111120040382c1c4601d01516000300c3c0c241c1060081220721002c41d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 402942697 1250 402941447 402941449
    0x141009030519020f03070b10080c151c0501080f0d03020f09040b0a03060501260c030c120a020d210504060909051504090f02030106060e06030610050f040b030a0b0d02 73
    0x51141e203005842c469248000c00c1011030080246444881001c0100c0355981e4242c00c1251644034141d8065003609500c1034000b815050015440340980030042c1089600c0c040070280d044c5503071040100d10080c2101009803c0250000d1003080c1c002c01011019102d01c0e0b0500c04854103042140b8000c40a01d4410301034405500000015503400c140103440010301100d04400145801d161603000804941c00c20300040741e1f100d503001040640c0804810701403416101e10b5200c0e80c4851000410b00d4255001c11003200092400c4a603002e44c05c8206000d50f00e406450741c01140f901010807000341d5100d84540d0289000307090140c0828407003040351a20070704103030405200800f0f0074002d126a090040e250070101d40c004628451a0303914960003042040300794010700c0e02e64036481601d50140d1195182080006d04e85005030b140158811009020500d180e072201d040104142681504400b000b600303200c003801c1e60f00c81d40300030405403881d07001d0141c49290030000c0d07806543d00d981005000e182d45902c00e03401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 402943947 1250 402942697 402942707
    0xa09030c021915110d090308120a330f06020a0303110d0f0b1e060f160f0804080d050f04090e16090207020f270406110714100903 57
    0x48698100c4102e0000c030700790340e50050000e6041e00410710400304102c68400140d0002c0840801c40c8000042e42e01410750103400341c0710040d140c480038107180003c0060394500e400b11600c883d400070240b50001080142662003145020132400168021034040d058401a0991034440c00c0041682e00d282d00c0409052020094903480031141c0181459112003400e80501030300c809403002e42028410800c10141c00e0042c0310040c0c07142e200401c0c010000b0003040e19501c40c0444641e1058800a00707101e24002c20803180c0010783e40320300e10803120450810100c4e0001800030f82900340c00c60041211648031400c041a80e814800d81030b00c010b00b0306c0801c12044520788940025101120b0018100049901181c4013050500c011000c5100c41c0491480c008143c004c09540906911402038070080b030141c411100b4820700302a850720700c546000502c941e9000400010402c641d101e4410b0301e011507401002c50301c042d6643c0004000702c0d03c14590b01104002d00d80c0401c003200d0582800842402000569200545 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 402945197 1250 402943947 402943967
    0x1b020106140604030c0b0711100806180603120a02030706141f080a031d100305090c01020f031e04090f140c12060f030313030602040501080c25020117070201050f0a0903 74
    0x1b4981401203150400c0c00861035111007801000703056941340c4803000c070000700201800c50322248603c09100100c4000c40c6078040b05882050050024203c8411715054007040d9000103848904621042110700c00280b424042c200b50550b000506d80980c0c144100724090381d501650641d1607288a805042108510000c2c000c44250382504100010300c51200a0706081554002c6c842c0c0c01c420003c1001c00007640c160302044c89050300070180e41c043c0c11103800481c4c9448808a01c04410351051007603000525140483d04059298003418615140da00e08801d0190758144888180b00b558030f85c48581d24402107072980d640500060038243c03900d01d52020300c1d650b40e00b014101a004480c82145808141ca08104441c00c0024448048003402e07540e01d401c0000c1e60050140500040403800071680600c0d012050f204481a651090b001101040080075510012250700b43d0400c00c80d03005404015a24410007401101e0395400801d461030092400500d001d40136004031815407402d0602404260321402c43d00d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 402946447 1250 402945197 402945209
    0x130e0319080c0f030c040509070807030c03060302030a0b0a0e06070309110a051309020123041401050c06040b0702010f020a030509010c1103070b0613020328050c040e04061b020106140604030c 84
    0x31380700e4648003141041d43c0903580080760010301d880d041c401415009034074148a1030030740d0b50500a4140512003141a0303001c0d440020b415511032880340700000c2000300001d41c4640880b40010304503407201440d624119098821901295865005805001c03180c43c0381c0541c80c0041e0307641000689048041840d405c00011448070303d42e03a40075402d04680c0324860403144015500402e449440b00015040006d078010301c510b4204004800d00e510301c650181d003e413420408048054406945c039a140c403035081e54000c05070400c5540c4c4400443c00b180c0c20b48090000420a40c0c2c0000301403400103415800c40d20141441e10521042000c00268041c000040312011648440c0f80515070f1510008a0201d000000b01040c43ca40040204550340c100325150340384070961800490325030640d141814003103500175622a81044010041442401521080d03960060b02c02c0c0000200010100c4107003000e440160ba50a00503512130000300071307081010701007a41400044640f9440d080c0f5640d100504039825200341 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 402947697 1250 402946447 402946477
    0xd020114010b070c05060a090503100e0a02101107030b011401031a040c090f0305010207050706110604020d0206070b090f240402090606040b0c01090b09150411130e0319080c 76
    0x103030b4208070b001340246008200240140707855040e002c8000d002510140070381c81c001c1c41503502c00c02110b40c3c3c1340901d14103c450400074050744c10058082c03081c1d900901d01d24400340010140c4206407440c040000c80010350090402140329414000e00d503c400c051010002d0415040a4001c83c036800400340c07048040c201181d0002c0ea280e49100242c0340c1141d43d510041c0d03040c1604000000740107040d00288485407080e41a240c416440d21000c0d11441001e120181c150790040380020014100050031100d514002400d150030907d081e070b01e0142050b41180c00700086e8101102065441c00100044038a00b4151030b07010340c2414100c01085903940000b40b001c0d100b000b805000c603105840d488100c5015001c0310218503030f194800f0400f207000e014031007011101842198005100381030041101c4070405490308504c1141e4071140c0b01c00240425047c4941e07444100210714182c40a464400e100344d80510340007840d103440c0c10b1080d05101a120b0551141032006e80c504001107800400c04885000744100c0007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 402948947 1250 402947697 402947707
    0x60109021b07080a030314010303210209030a05100c0e0d08180607060209100305040b15040e030c070315020f0409090c1502061009020f040504020d0b030118050d020114010b 76
    0x3401900c4455221051079501071440c001c200d4100100c0c400c100f03240a501c0a01404890400c051000802440042c002801040000310454500f5100d1164945032500150821059600090038101c0c200021a101c0d0300030130040799a10080d0040d18151030890415840c404070501c00b084c000014100002d241c9400003a205c0440f03d001024090343d4980a0a0b440d03ea0341c2a00d802d000030b60140022030711074051000c00e880354a110380241885940e1005412106484410a001901612000d40c0e5402a15020300010f201d000f000a412807003404402000c00c40d103141001403041d115035500c0300c0520300420488407010072042c00c41e000c8803642d4500295500c100c2c24044c45e0480c20741c0084d10302c24540c944900940342d0020301c582c0074601d400c0c1e24007216550f50382200300302c2c0b0a481e071891107400305000402c9a80707065030140080903c84003000c503070064810000303407c440c00542c02104054524281200307001e402c02500005078140d0001300403c0700d64190038000008140300f900150440020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 402950197 1250 402948947 402948967
    0x90f0112030305100f17160f0501080a06030209190b04110403030f1b08190c02030c040207020d0b0c0c1009020102060606030414011a100305100b0903120301180c020f06010902 77
    0x556001481c407005d202600036100d048101c08802131003280181803003441840754000000e2940001260380c00007814400c18030b000010345420750001c104107056941c1e400c000001d41c0340c40d10110320074800742c9189180620b19503580e00440d0005081c69001d280740c005c9504858a0801c210340640380c160600b503a0700101074a046519503c1411700c48480e04424a100c8100300784180600103d03d5981c11240c0750107403211007102d040714070180180d4980e02c200844002402c15500401c94107001901ca40c00b011030365207484004c80002d4607000c3c440380b00010380000e150414001e414928421140074045080c940d00001c0d80da00001c0c1107907201d420004040b400300400d0000b10001c1c00c103030b5002445220344040366000001c491502041c05070f4800c10740703010424400d02c221441120700a40c00101a130400092503083d0f0001c0b000c060701803003200814070311021005c000d14000c14420034550b40c0b05a00c41101b8040e981310100140c2951701c15105001f4002000c12100c0c1501c001000058860300449 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 402951447 1250 402950197 402950221
    0x606031b16061d03030f0712231e15130207060c0e09011215090821011e0e07271701110901120e0a060c030506090f0112030305 56
    0x786540e90881054001202040826042892140070103240d4061007102c900140d61070384001c0329281c0004182e00c1c00281d019005014040e064840c0001c00298001b0403510030318256a01130003924a01010400c00c07540404052410842840d507040c0500141000c001c2940701c038003842c0c05c45201c1c14507251503008040e695819035078030303076080041805550044940a8800500d801405006404101c008240f042072440c8140d081a880b000000320050180702010051508501c2203e4600080107000c00c0c1c0c0b540c1020001400c000c2c2030322001f142d4502441003072164613142803444128040441004060020014258002c1081c10919172283d03181c00240980009030040e600540180c520110b81e4100901c01c1d40d0310f054186008002c000070f05620700c852030180d000c1c0c0c4d0340000d03000c028503d03050f80560010b031100708400d4100e50f0400081e54404081d20301442d040e800082d41c0d0300c00c100f04c5203003200c400c54003d0844000040194101008101505080b59015040c1078030741012604800d528 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 402952697 1250 402951447 402951457
    0xf0a1e030311041203080c0307050702090c0712051c09021008070c0209571e0a0315030201050a0c050c0411130f15030e0f010507030605030d080606031b 67
    0x2c200c541c0c0b9078403030340e5000800c1d600d8001a0005100c0500013565200411304617406003015880f4035051900c00e81c00c000d04400020320011040d6000e00c02003000607000440d90929060344d032120b9881c0c610148410107801c0748107000c6083c3c541440042c0300581c9446203480c1c406940d030701d420310740c0395199801641c1d503200c0c01303000941103040c03102001000f407001c40b070244d0306100c04000d0300e141b2180c0c44051201120740001c1d04030b80381c4003481500480504180d140340003100a40d001030401d5500070700751601c100740c0d85402444100c0042c002e1601035040c4151280b0318005084801300c00e00b541c00090a5004084094050041c40b50a075001e02000f0058003000300c80052003172084d00803420890707503942c015140b038003603071203006002081c543d000b8440310b42a59001290903030358907002039084025200790040c0103401d010b000c4684203800c0e000e005444c803500c0d50340c802290641c90300d4107051074907192041003010070440d1800e2001070b81c0c400303086035040005074610b40b0040482c00c200a8040c420 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 402953947 1250 402952697 402952721
    0x3031b050f010f0c11030a0c140a11090612120d0603080f1206060a120209040608010e060106020d020f1b1207060c0c05010302120f04110604060206090f0a1e0303 71
    0x581c0040750140c1405400c1440c440000302424801303481e86503003d0b01d20251050100f42e50303400c244000f091143c403800b22598901c1c021210303980682d25030b0002d1802d0480a100584082d201d0140600302c1e420211080f940108054503d01450700c2414020303900c170821161a491103400029200d4090303d039640080000d5908421040e58403800602035170103036800003468096194000c400900545041020348480c2c0c0002c0e210320b00400701c0b1048400017544244055940305503182c0c030201e030829092040000d07a410490003030181c1c0d410800064075145444a0001c03c5501148500000d8100400c0240c0080307812200141241082da00181044210a030304401c0c0d8030903070500003020382d4007550943c1c51a0184204500c1e40c2d807110011000d07071058002c520403402d0f07124045800d903100f203001142c1c014014110989001d499800281090744a58403040050b4069421301c01020000d201903003002e200348008041507042036403030800d960440c0348403408007801c041740b000502d130190700312041c6958 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 402955197 1250 402953947 402953953
    0x7020604030f11030d050a050a0207020a0603020702010309080a020f06100518090a1e060e01020f040509060316090f0608010605030a08030c0c030d06060f0f0e1005070503120405060c03010501080103031b05 90
    0x80007403805d802804c0845290b00454148404111a800c0c0c03031084030450b0b50042c2a03480c1d060300380780701580030b540050390413030400d5652442d1801041c076010140403440001d501038a50018484041d80c83d00c44081c000c88809440b00104010540d0b074455992040a50b081103214a643c52401c528203084401714040c0c01817520102a4080d012600d100d0070049105d05404c105031700840380c40340e00701e000c1c03030f100c02103c00000c100620462402d1840340798054402021505401400c184070116840c1e10b40c071084d5400c1e11480c41703085901c0d0724004c2e070001d004004003c010f4546403400083c0c1e514003c0c0c4001c0e05071180007000c22803600005c021640351900c02421079079185c03482d004150080856224140026288030110850a40301e195002003c0c03000f96200325003002000c00b042940e0356426101003e12408029100000c0c009002410101c5240c4903502c2403031525060460410310010300b404da0348001080107201c1aa00250301e14152501458100c1c07402c1c1c0c0006054030a05c400b042c010301588 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 402956447 1250 402955197 402955207
    0x907052808010501051504080712020d050703063e0304020a0f14011d0a05011404050a03080301031a040308041e140703110301060b0d090f0b010b03040303060b0307020604030f1103 79
    0x41c8150890790480b8001e848010083c007207805412050b01036030140303030310541180004218030b00e0a0700b1f981d120780f40001d20007910036906940d024988200d0342d004440340c1d82c84405106d030701000315030800008641c2140101e410301128940e12412903c3d038814420030040800800c081d500d5541c1c2e0700000e801c4021060345410380b0782d040c0700003000c014480d803800500301a00703180c0751407551807003c5101e6101414100e010b901b404015100e2040059050341c80100c1844000b03440c2c0d94103203d417001180501411680d95055081c00c0811184440100c40c2540c20f810610002031703405800e6079801608004926140c11040d51984041e9255403409450004410780c504903445000c603211048a2041d21450a58800c00e02403500741c400f58801c02141d8501442007801e10305064000c010803511445000c038000302c0540d52003010004c00c1c0c0281e00604008030400040540510070388001c0d004d00d090701401c0d0301d04240002d42c0c40c81c009000601b00308401d50707a2960640034082c2c4050407400c101c290787c0c480d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 402957697 1250 402956447 402956459
    0xc0333070309060f0204060c030804080f1201050a09060b0304170403020d03080603150610120f020406050d050105030109150209030f06150a050f010206160203090a03080309010506040509070528 85
    0x50710140c03070150341203071420f40c4400c844c06032882100d00b03c418a803516041a040d9032001c1c0c4004c07000520035600c0d0802080405081c0442400600b0604040400ba600e0795040005200711303403030a40c02c00004036103451018400015410107503a40241d020f802c3c22400e0340e9010340007902c1d010b180d00c0203401400c070f0006682010b801c070000920031034080d01200c0d8100c0b00500d4000340c128065a0541c0c000700103481d45c001c8188104503c1d00c00703080300340707020a0440446002c071040340d00603480407002480100300c81d106080c0c140070326401041d086009003c21075054866403012001c1c0046190302d6540056080c01c1e9480038040d950316109030304103903082880e10b100d0b5081c544107501c40440c482c1008450102c1d10349099046140c01e2441a03000700480d668101030f4200680043c0403506c10f611060103102e01607070724508181c0c050340c801c1c0d002c1922800d00d020a1420364501034080d6115030b05182c2001400c000020740901290811a05401d074880350000c0404640001ca52111400d07103030907404584 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 402958947 1250 402957697 402957701
    0x30c0d1e0207030305090a030815010309120c0b101410020c04150f2705071404080a110f1302030709030c090606171006081504020d0510080c03330703 66
    0x80c004c1e2014415030340c5444c180303a200c1e603c840005000c100c035903010510007400c0c00400c00900d00b040c100029410301d01c0d20303100005664610300e00f0000f4025074001017004000f103403030340d040602260142c24035420035090040c961808e503001401600c070705250b1706049200b00000214042c014204010782d205140100641c00e4050241c4405482d0003400044c081d01c1e403001c011214a24142000d8132094207001d81c00141001410762001c11030040500c05030a00c010006000030403c0b10002c0000c20340e10714068882c1544000300c00e1041c100142d610069469560841e03010490720480140c2d281d5640d0403e50b142005074001400400c4a400c000c95010440d03031160007540d0881c0c598451901e101a0101e2240900b125210111200340e003003044400c2c00b804801d500720580c0c101e2154031908070004a82260803d0001d4820603441303000b40f01c8040c00604000028000090203850010201004a665080b002d890015580c0304002103138000c8a13000001d1a0044010300020060309004c01c000300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 402960197 1250 402958947 402958957
    0x19060e09190509010603050706050901050306040216210305010e13020d170414030f12180f100c140f151503010608030415080402150a03090236010b030c0d1e02 70
    0x1f920303110703110000c121580103400b9568800c2d0141c0d07d080c9183c3d528010b010103508860700b070305405c2070b071904c000c40001e0400201c560507000600c042e50f04160762400090a5800603403007a070301200c40e501404118824982048101e580540d500d448454040c9080594038040b203c40041030030010a0104284400c0b14429031103000440403a040c18402c8001180c039021080300b00200003108003c03855540c1d15130451782d00c580c21300034036070f0321781125402c04240c442c0e41d214508000100c2c189840410405140406503003818000e00074411881c040c24407503901d0344241068855882c80303000151103101c09584109414a000e00240600c9a4840c49a603698100b0300419072800030702200c0a010b0f511418032a4819600200a04103403500301c002c4001c01da00091581d010162600c80400150f100c1d0040b0021160340502060302c0d035160103d03909107056182480c4850302d80d503040108040084c2009490300040c2202c0c03190351b1180b0071810480280b00024184540722560343d003141d05144150b0182c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 402961447 1250 402960197 402960203
    0x1050c09010324051e0604030602030f15010e0f1c1a13120c02060904090506011d04050c0f0a0f0306020315060901021b01140f030619060e09190509010603 68
    0x1000c1d40343c0504520b811118207803000d20f404401000c0420a6141082e6003013114034070801349403014455400401c82e9030f886074005607580f940000601c0b00041c520b0055583c03081001d400c100b02143d038900001c02807011400060711032a5021008266940ea00d032203440b034a80d4403070141e40400b516280c661450301003150b102c800c844103840011036982c402011104010b5210825009a42c00510240d640c0807070010160b80184081c0030800642e22a4410740100fa8091b50060001c0d40c94851950070002e612084c00e4203610140c0180f00000e20001180c0c030070040101c40c81032011590102260742d000072030780719001c02606250008148001507006600035000c461104442c81c6060092054a10030213440c207006070f200b06501071303c0305902e082e00c1c10b08440525100413200c00c82c0382100b41641207040c1c5190210030005c180100c925140540000360903681c25804403803454007201a00c98012180414001d5000100040c220201100341040c00004200100a1420806030403402020680022 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 402962697 1250 402961447 402961451
    0x4050d0615050d0b0c0f0408030c070311060a0c060c171303181211040f0608100501060801050607030e01050f0c061e090d0e0a03050607050d06050603060a050f030f01050c090103 78
    0x104030b5061841c2542c8600341c000d42d0f5050356480c1d0580414407588200d06642d007030401408040380d1200184001d12401203490014034a86003941001200740941300286842080308000c0110150f400404815145800c0000060030450420303080d144001d001c03d0408411000318100190a5040f16041e100f25002c0d41d1040c20102464541c60b8401d40c0c640604504188212035010000e0303503020380071061140290003c01d821309884002001d9903c283c0042c50315402080c18451202d665104a0340140a10724284a03a54901004143c042c82204401ba04002d42e501d00b1081c103034020380032901502003030480c260f42c03003510511458440700103480407200135140f82080b0210820b10540300c2c0c05241d410001c0c082c01000742c00300f91541a41c83d01801c1d0098180400003000c035009008407480307030100361581780c1e0390581d9424a004481460b040144035500a1042c0980b507203a0969040640d5001d40b1b1a5248030480400a460301005041d031004070b6003084e00b04140c0e11000300140403003900070380302 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 402963947 1250 402962697 402962699
    0x60b18131b20010c080c0306010306150c1b15050c0a02060316030e011104170f0f0d08010b0c100c20030a200c0d1403040f060e040504121404050d0615 66
    0x80ba40c00d90751400850000146141d011076407417800c00d0020f54004205050010b2800d41c0c51800324041401c1040000118242c481e0340414800301d1603185c0350412104503884070050400d20b003448074460b52174582c010860f022404d00d508102c10407400c041d140d001403c240d12032404c030385060030044840794071000082c01c09014001c0c0750414010b00c01c5821104500904042c01c16141c0a107004107002d104800d44980840e40c5005070081c0504c0a2548481000d8900b403040d228014154800c1a440035210600402240050308804a40c1075240e01113500c020a42d0240b81100322007010385441507100d81841d480103080309050020040a040d11207442d401030100035050701d040b0144080d07841200f1030300901842c01c1146041242d074140d0900c540706506445003066455403458100d5000003006e201071100c203007d131541000710368040b46030454040c01903144c182d890b103c1c3da03250b4070b51850501107903013826072080001e1002d40b005003030050300304a00c1d01902c1c1800b85c007401e6508003214030940315182c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 402965197 1250 402963947 402964007
    0x8091e122d031003080f040506030f090106051f030209060d0e07090501121110020f0f1501090911010825020703021201020403020102031602060d1d01060b18131b 71
    0x10540f4801c60b04403548841040c59510380c0207490780a40420000b44008020209035130351003c0c040d5000b10400902c02c1c2403460482001d500312449030f08000d21401e6111041c014006000a140e284007406103000b50b00c0f01401700100d1103901445410215441c1400203503035060400003001c000f1a8a48903080c48a82d0f41d41217170f038000b04030815003c0c0240d8400c4400c1915820008559801001141b041380e890480502100741006c1044213290395540108900d141c00d0840a07c1060252994040400000207584c2c3d84034851030101005e1814041c40340c00149680000421041d8a2103a90100003500341001100944511560200702d20640d02d12820b00c48120317051007581c055035810f030000c5151011880e003480c643c0300d8020040381d0009c8200019102d9040c640110000501c00c201c9411840300441c0b001c0d420340d020b81c1c00880c0040030030f021a80c512007100e86908410741c2c1c280c94480d07841c101a2518005040941c0c026841902d42d00010b41e4425407007019a513445002071005c80340164004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 402966447 1250 402965197 402965287
    0x203070c0e01080a030e0a0b03100e0601020c0901061d150a030e0309030c0114190c03020f010b030717010905160303180602070e092406010e0108091e12 67
    0x20083d00342c6940031980760740004c5e002d0142d07a4000705c0010503800515584004c0501d0f503600171150b584a04ca450318080040903091034085410040c2400904070103802c50b008524014414400c0c4010042c0e42c84107242c40380d41d80b951134110100050101600c000c100c0c1c0c84086554000b03001c0f480000e24181d4000c46007080031040d600c1443d1f00802a10590542000442e884618030f100c182030f10008125403c0088260584140310284580350007100d0740c401c0c20080c3c2445c28001d00016103074100381c51004140c3d0049052030648100180b0f000c0c110708480c0d0920300400c1d045000901e60300c108940381050018414020302185c1c4a0380e6103c90720340d6814291541c41550340b083d000545d0200d4401e100c0c400c080b00f03240750311154001c11501e050074031104c1d003e5540d20205d0740e411105510001d202503542e0002042d04d5041083c2070800e61428418421581c40e504030150070100036103454620200b61007401248841c403100000a034442800d100d80301c401c0d90309501001406103500e0071110004c4814 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 402967697 1250 402966447 402966449
    0x21c02070b0f0c030d0218090a050f01090e031b06061f08061014120105240304080a03060f08030310060e0102030706150f0e1e0103121d0604060203070c0e01 69
    0x2801c0030304081a00c101d8400700d402445035404540002c0c40261003010842c4040c0008803100018002d855500c43d05001e48544090300c845485820a02000b5015101d00b403c181154646c83c0000303221004084201c0c00c501800100c41a0404511551840719000061036801408125141c400700d85011044a183c9200b000d600310201d84500c001418070715200310f4a040c0d9502d64101034410100814480751280d0081700303800c460900f0390005108508000415104500e440c804201c500070f0402004070903030000400090010348001980301e040b51103600030400400d083c41120340341d03a856001d0b0340d40781c0c2c108039030b5150040c1c00c0b03030b8000903014481c0310404500d80068000c1c610308407050315110080c14242c84a890b242e42d40c00f41c00501404010003c80003800c00410549050a200f40c0d00c0701207480481000d04039569203801480411240d0a00803100581c0342000c02550600303507030713420508151894041e4400340103d000184250040010410700b4410030030500b0003504d80200300c00403002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 402968947 1250 402967697 402967709
    0x203030601080403030902010c0b0106050c010608120d090804120b16080601080c091801080705030f0606060a0804050f0304170f0a080d021b0708010b19050105090609041b021c0207 79
    0x602c4000c2004203009a20181c003803401803520444080060712410740454083e07020f00000b4100192900d00814284120030150490343c1c0030b80341001c80040c2da03a0072409005010042d40707a46581090400c680c20045400070500ba0403500c0140c030450030440b140d4581210035074107607454403003041c807001d1003405000d201d414161103000c0c81e52101c1e2085030040d008071491613040410081c0804442c3e8401c0842030003843c0f040020030b60307030b8202030526040100c0001c1d0100e856004009000169540a0640300c03900e0a0b49013024290781c50b41445450440b030b0080180180c0400130300071641702010a40c1c1c9942084140485148800303122700d42c1d581e0b412010001e84569800e00c4a1131005e0400d40041c0000150101c0512000c503400c00040e0804980b54400c80f01690b6400c05000b413030600d0420404440340301521900028581000030700f103845922425403081c07100186d41a15681c4a602c1081000b00603420030386d10480c2504040e5891000c038860000c1000a01c61480f640ba01c0003441d0300540346 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 402970197 1250 402968947 402968957
    0x712020607020d0c08160f1b141e06090a0b0c01051b0c0c30160614041206090f030809060c27030a170a030b0a060c120e0a1d070203030601 61
    0x8010842c049407a5081100711403130040310401c00007080e01c418104608c017a00d103052080c05450088240903500081070154000c0c0c0c04c40031032120710003002d284070007117000c2559110b54610013103000071001d0405800c8004045400302e08030040000c158020f03403140c40726929081800c6102c44641840380102010f014055001001c41a62400c101c0300c24034900c04a0541b040710864840540c422240448119031007682c4200b00c514115a547c102e07503401000036007042c641300c4075401e61240c442e03c03450099100c0a0300300041c4d270301003001950040c00115001540341c5148041c80c035000300311395002d07244052188902f03408140030007200030403514003a2066010b81d14950107541d882c1c01040202540307540c94090142c081c004502e0101658a03071002c000d41c269644d40400d0005002c45103207120ae503014508460781801010780068040c0c10017504203051910580c5900700485801c00c8002032035401014118001941e8008150040000340d2007081140c200d0350b038036408076a41c0c0030494840c0c0c0020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 402971447 1250 402970197 402970207
    0x90b010e030a11060f0c03070b0a090c15180806270d0e04020f040803070c1202100507061d0c040516140d0b0d350d110712020607020d0c08 61
    0x703440c5000d03c1c580801d01521060814200300340225041d00200444c403015000000c18804112000a415030f00c0f03802400108100502d9466104804099006800590f00024001d000f1f20740111140c410140c0868400c0903000d45481405072922400d44241c041268554050389410840140103d1200312200003801440c80103070044441c88050081031350040d41c2004190300380b440c60360007003016002e80c0c0019903030380c107286c6032050048645610943d00818100705600050f0748228243e1080380380c2d4136102d40c0701d5105050101c010101802004a519103181098040d581c000c606008190707c2101d0400c12a070720480c90588110300c3e41d86540000e04a900b800400c0c0c2c403c0d0300074110206100400248a4807000c0108544a104500a866030310408005080f62199504d8440d82118075030328940c070120210f280f00b07200c4d01603406401612a1110b01c9240156042e0084d10f0341150000c0d1400e2227048000000394803220103880080050003207011504480d4041c2d207180b20500e50140c03000e4540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 402972697 1250 402971447 402971453
    0x91c0c0204180c050915061801050d050f0106180f03020409050f070f150e01210e1213050307060c03030b040612060c091208030a0506030c0a0807090b010e030a 70
    0x20920106049a02590707030040e1150100c2079440070102c00303204106041d081402e100030800c1504c8018000b5040d0340745000800345c0c1e81c0380c03036040c0c0324500c00d40904000940400c10050b541d0b401000c001221240c038180400c000000c480c81154102d504545412108200741050307400d5004540c080c3c5c00503400c0d49582000103050642c81032464074016000d0700c1909040701d01090034814a03078400000281d00d150140803449030803400a50b548010308013403042d50140c1002a04c480012502044501e800c8101d4814842c090b800421654640e1000d48001c1960040301000540110210100c074103030a40000c11a81000524942075416589448490b08400d80d8202c01424050b4044c541150300c806000070300c182140d804034505485004082101c11105c0c0c0002d00c00089540b05001032140484064007040e01e0704d0459410080c0b07108081100da80d100003003403420071000412070300505150380000304174201213506425035044107018000b02015034011a500c41c0b080d06050ba05401481c620f00c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 402973947 1250 402972697 402972707
    0x903030b060a0c110d0507080703020102121912060503010908070614090a06091a090c0111030a09031b0302032b0c0c140a1e030308010e09070e13050304090c0206091c 73
    0x131400410001d00a0a240c0d561800c00829a11504059000c07140c18011980c05200084103e540114018148006003104400c420b002c44c55210920944901b00604c01d240c2d0f82200c000740c10003800a0014806500d8024030551129100344c0d850f902d0078203400f840c1c1c4400005580907800c40c82c0200320006c807680340c403402000c0c186411103426000c2c00d102a220810781c0c032624499000302d0007078041d03450100c001404a60890780150f07034980003044000c0c1031540107000541940e4000d9541100c0701c120260030324031038405810195040c032508068aa8641c55080c00c9441d54991032107480c10907486800a0740c0c50100704000030000c0241038824088941b41d070306d940c00c0499009181e50303080f55880c0c4101d68203201010020641c0303410403200740281030300120b070306004042c060040c046900e490404152181898040c2c103101c407085802181c48044040b0082c20316641010680790340303d40c0d0f41d00113001411098600c1026001d403d00040030142c0125803100b03039059680703400d0090800342900301d036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 402975197 1250 402973947 402973973
    0x207050604081b0a0809090717070e0609090f01030c08010603020f100c1a07090e010815190f050114091311060c0105010807060809070b0711010e0d03030903030b060a0c 74
    0x204000f00d031880c503200d080c04000d00b41031940103000466480318890140002000c0042040003480b40300744500f500000f081194130350021403032a1192201019000040031481554007803580a40c008090003c802104040d20303048a00c252541d82003d80c1d80d8050300e00365411884041d40c02942c031984540c0c903081000e04c00b001171800740352200b07413040399070f46081580e13190700c145040c0d0040100c06c2011181e00444400c001d45111003e030b0841e585440c81455079281060b410103c0c40d070805002c298140c0101000060540341c0d805e050045010384030345000180300134402c180308482d07405182ca07058105403400c10300a40720321101c110b440c00b0688501031000052508660020400c01c10319292050a10956001c0c103a038001034101e031132078108020b1400901529050322071b00081d0b0100320b90080c840880342d0f40303940b000407d1a041e41c03c1700165001e031446103009130407440e854810420941d055116480e190701c42c5d1000c0012a1407001032010900031003010340046100c26002d0780101e00e044400403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 402976447 1250 402975197 402975217
    0x9061308040909030e01020d090803030117010b090a0c0f0c03120509030904240f0501050a0e0f1206061e0d02040e16030f050f0d0e010309030c06020c030d0609020705060408 76
    0x40d00d000d54400c0104119120f9440c140d0004890680c405515a03042c406074840452515000403440d0425200315120b22061080030040b0020f003414159000e030a402c04002d04400034546416844d2580d005c102401c1155001c0e40000c6032240c0410305903003c0e0302e4624299405545207000c05901300c41c08002400c1c05072001d149403006000c4070400c0d90b502c3c005c141e84107103500c00a03104440302c20b40d00040004039404c55034512a0700c3da0709001c6643c0c0030094541d1260146007000c0000106000303e0142c010741090b039a0000c0312841480314650700010418000c10068807074001e1010030701c1a01200d489c08078500d5a000442000302801342c50190400400c500017801580c0301c1c2c041a90030104404440e6108480d00c11801c400307042407190900100c041b802d42d02000e440c0d401b56142d4014100c4410070402818596121562011301d4410356a091119902000c21542c0310503c2c0c565565075000b145244e03010504180000c103400d400c5001303607142c00b40e20000920349a1905e42d50070310941c01582c504 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 402977697 1250 402976447 402976463
    0x1514010f060509030c1c060605090903030402090a0e0a140f0604080d0c02010221010602060c0306010806011b020a0b0d0f0605031c0c0b0c03010612020703020619140a060503070e090613 81
    0x100317429a145140000c1980404440d84000c2240380f07000d009445e400c1d07000500ca10152803c100c0010008002c43c0c0d0310550496aa035480c1c1c1d80d1180f2074000b41481041c100303441c89268889800c0068444441e80f103000c0c120210b50b1003101c0d50514a9441c0821100101284404d006600c940304043d0007981002c0b03142d00000d420000d681d04d603030300080841c0c492105401e03400340040050680502019800c080025005442e514044001030005080a41090304000042500d1104000d6100385603000702ea000305240e008a43d185141040394000309030b00e289652030842850843c074218030810045641c00780280481c01c0c0582d04102e890007403800207005105052651400082d03d41c1d00461086120340184c40e20303541440070041c0703450761428051078094030401481c008241c0004210ba8881d20070242c1e1940c1012110a035409400620814902d00b282d80090001145850b0020307002d40340250121003400b5039549d200104140103450400b6541c00410101c1c1505502406540b5194018408 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 402978947 1250 402977697 402977713
    0x1006050a0e130629160312050a050106080c0c07031e1e1506230112020c0a0212071d100509010618051504060309050a02030a1514010f06050903 63
    0x4524542145494442c11542ea4202405028400542e000c080c11101c0c030000711104094024081c3c07031050030340c2100000071442c004410140324040c4140140c3c903803001403015090041340c80c000780c18203020b07072000b08110000240c14460a10159151407002000030b00c803d40c5592500080009070100319003a400c9080040b0000c50101f006e0141040304442c04070800e20110304129088030003c10700008500d0410744200001707011030002ca80440e68a151100c510b45003032005807480c0b000d45000e079004600200d03c4820041003c21481f008a000741c0d0304040e282302452209840c0c00f164040e030b0000200c2d00d510340303c1c003071f8083c600903600c403240106400c8020b48031800280140300c00da0128000440800070300464040d19402c03c40100026034041141f855000f40300000c03400f0b0303030190b00c08055490800f00280201000910181e513000790070b83c0d840b00154104854902c003141900084981028071058000440005441c100d642030022011454100300c0101c4451f8009130559515100c4e07086 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 402980197 1250 402978947 402978949
    0x309090603190c0905060105040b04061b02040608030c01060902090a15021203151011060c1e0d020903060903071a0402040f06080706090f08060103080f0f07030201231006050a0e 78
    0x403520502c1400b82c00b00203000342c82c04824500fa030390006e0500b4100141071204003c02131101d800e035020746045003451031a0b141010900c2807540d25101010354040c1c1414000a44020b0100051000c0c6d240c0c0c0c402440340c6500d94403c8002d91003491240d50f08210341d0103003008080700d126010700040b1450303c142e5810364007002cac41160541003524401d0500d00440800d890318030b4401e8000002850605081c500383d05c4914280351a200002c02100580d000080c41a0380a8044200c0700080c6c691600c41c4ca8403520200c072a84025000710017424020f00c200c4000c2003002d880001560521507020601c41421184d0188082d1022005402282c01503251031824405800328000c0302c015080c00802030440300c5c030380480102184a00d9201039184da001c1c19050103c0b04020a0160650350000423a6941d41c1456405075654441c0c0300640c040100f01242040c10140d06410100e6403011509581d0b99165003002a9540140c0c2070f0b42c11104200c0c2c003041001003900401c007401500301581032800f00080094 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 402981447 1250 402980197 402980233
    0x40c030503030f072601030b0a0b060d0c020105070c11101101020a0f09120b0c0c03070503040602060118062913030807021005090102100906060302060a0c0501060806090309090603 79
    0x103510508101094800c00240c02e6000d0b10362011958045d1600706102c0b00107000350560001800081c0c1001d014100040c20300e111038003c1e440344203024048980d81c8450910503801450004400c0005500b440007196006128403c0b00105d2130300100c0340b1aa1401c1c0c10200800071a550aa11061008011802054060a10140c60b55890944646008440144000f4002a42038104260b0940b806e01111b0120700110005540000b11900b40d0741c1e079642c2d82260a00c2c50140c8a002880d40c400003401080507680030451504a07003140e04549450341a0700780340000c0d00e445d8003a45901407103110350b0b03032518240c81c04403200007400c1e016428948141c45a541d0b600000941054916600000e881e10450a191004c00e0654400b440c180d401c280f52070740001c0d10341c2d060301f100780d600544801da83c2c030034000c80c0e1380705100440d4001c0506564046a050187c201cfc1000c5000f91001c0d480d03c2c0c0002589240031036002d00c2001e8003405146031030602e0302040410358015003c203415124024000b01c00001c29 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 402982697 1250 402981447 402981451
    0x30717010e0402030c0306130b0c09040603030915050708120709030b1315090b06090907090204261204210609060e0d020705060d020307031e270812040c03050303 71
    0x140903151201c1c0ba050060500d08031170142c8990183d80218200b002861070340400d00801c81d031000240034070791a04900c02c0902d0054000c080e5200c0d290040010405070800305100071918030020190441030728020a83c2d4501408001814800080241651580b056203c0f1a4014128108000302036100d8941c1220980100d800c201d01e05030300709001c0b040c05032030501e400302c038546070340d00707010250311640c840002c1907010700a140100c0c6040003042c04132509000340c401400c41c0000454980303a844040c540c2134201c1150000c4000080c0b11400384904002c148180340b400c00e03010382490103141020f02001c05049074203140940034000500400501d1170f0090040060240d640401c100086085d41c4d42800c1c800f442c000e05641c4140c0e0104902d482c1c0313506480c140c41c0f80000050f12683e034104145e001d01540d00425025010703141540d0341c9950182d102103c1a0120020000c0c80241ca60074400a076031803020142048500380000744401c000303000749541c400e02c41c900c4510380658940d80c0c54919001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 402983947 1250 402982697 402982709
    0x1d2203140c2b030b06090d030c02030a050a0c0e0108031e0f0d0501030812060307060210180b101a1e2b0603050c150a030c030608190b0708091203071701 67
    0xc04a02c0c6803a4680c94022100d0140084841a240207004000540340c605412801028012440000b9044d0351b02880703500001d94000007078688680e10f92501c1a05810280241c4140e102e080001241c007080010540e0a011201320264484070a945c42204c0c1c0ba4108020003a032054081040c00100c490500030103009501c51401c0c0341d211420480c8404103424000c4c11180a640301481c10029180e0010340c0040c0c010510200040d070300001e01c002885640030b02d001230b00700d001441c248144185d05010000403102482200c407120010150785864520030628510403460342c1c8000486c845c3c484000420a404884580700070000e10000030300b0b1400c8085a6181001d541c5200400c240881441107201e0f001007100d6041d0b960b41031200c10541401800c4102003055503e07140c0c2800d09020760302410103002c0c24030460f2002c0401e28840e01e64580203d908407580d100e481c021803105402000c10b540180142c001521800385c0450500200e03410040c031000411070001c00c200c00d111030051140d800303411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 402985197 1250 402983947 402984013
    0x1e130c0807061106071107030b070309060912080907050325090e030d0605030c010516060b04020d0e0f0a0c06050a1407110405100608060f0303041d2203140c 69
    0x30307003c011541821310003030100b428002406984a0075040110340482544d41c818114500364403041c40850080000703a000924003450004400240702c0b00c07500820074030300f443d628904960f607040388060f00c03920103109060301a4098100440030407000d0301c502e075080d48008040440f045c0c0d500240b2050354070114081042d500002106000080701d4050880989025002041032000d043c0c0002c10510505101c5108a00c0050300d05080000715046000d45c448014015502c2c0d1946070b05042c01400c4102d05400031703229026aa1503045c1001c601c01903070343e030050780c049101840c00005443c075901641c501c6040111048603000c13851180c40c05884c416009540300295006c0342400d000884001030b1440d142601081d07001c021807a40b040c0d10b03136440003040d140d5280c43c18030040880e01d90300680d0010584150440404c07600e00100b0b002c194450160703c1480584038010b5052007140c0b0a00440150002d540c1d914821a80d10890006110b954090740403102440c15000b0020303512002c0c40302d002810340c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 402986447 1250 402985197 402985217
    0xc1115190314100f0510030207020a0e0123060d15210b01060203120106050c0703020d0609050120030402041802090405070e0106031e0b010201060f17061e130c080706 73
    0x410b1210990f540051016440e4054504044081a02c22140d10600d03105a071114001e031b0f84d01d403194060382d401e83da029001c5400725031514640301403441c0134000c1d5007200350401072074500c0c03602061300104484009804a45003054203041440680440d054240001d2004900004c400d6016060072007002c41071480c1680c0c0305c82908c2d082c4120032040e03010004652080c4407040b007a0780c3c0c83e0f041c44e0444446080595481103040c0c89036040c55450341c8081d50003180010381e02c040c0503d68202c841160300c200c00800c8a0010701d041540c0b840c0380320303040624617082440001e005060690144a005102d0f00100e0707105017181e400901210012181228180c10400040003030702081b01c11240034103940c0c1014003004000404155000707003a004c1c100401c2c1e8407140c050110764001e600c1600600106c10394041c40d00c0d00e0346662522000855120781441c8220000a480c40820035000300e070940506252018540700c0028000d62503a09007802c0d43d445865403030004d61041d0070003112008180c1d5450741070500f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 402987697 1250 402986447 402986471
    0x8030a080f060f010c0203010e03040b13060203040608010614120c071202060c070b040c08030406090f08161707150306060e030d0507080f19050306100c11151903 71
    0x41001034005000c1c1c180340014451030b90b41d0501071690521081ca03041c5060b09890001034050521001181c02c103001c005008901d410100004003400100d0b04140e140d0380345c3d035805c02c07650b80c4101c0c421040010715080043c80041c2c4a508003408440c490120641401d42654580c48500d501351100c0078203002c0064590200814a0510f402aa440e070029084900c0c182078890414454003034020440000c4800040411045003080d80180940408594031a521200041d00c21a2280a05000402400c2c8001039102c1d000032a100d49032011004c042c841e034a0515908904400002c4400781c81c0078807030002c034007030109500b44812420650303000709200e07241602c054114411509100e000307401c0032000440b101d821000b02e554481e84a508150758a9121040200701d02070340060f02070450a1101662500ba07000015500a500c115028a0055004542070703e4440c21454000c3c83c0000990740c0c4441481c00156041d070030150800710f0340c500901c0d00203055074194007000000201c2e547d00c01036001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 402988947 1250 402987697 402987707
    0x3040905100617010503061b0705061f0e0106020703030e0111060408190503041713080a051006090b0a030602091c0506040611070302190c0909050c030d0c0206030a091a0108030a 78
    0x243c40758074204052a505100100b51185802410700100c84004400f010f08400d0031811100002e4200c010740784075041002142107492101003050600e01c00740b20700411410014203599040310340c2d46e0010540c50313255550a4807404010b00901c0d05122183d80805200c3e03505001c40c03403142c1d1207221040d5880105090900007601d4005022003009418010080003990104905100354504024280c45c0c514200310030400c00c105407c01106402000d80203420000000b856415441030f500c030078448203485200324000ca8220b030040c90350000c4601010000304001c4c0d0f00401203510054200b00d580c03401c82c03d0500c80b060007014200c0c0c5680c4601e042105011084c86200341c40c110300700a540c81d141c0252030013592103100350b0421954440d611410010070100083d200000c14402c0c10078825070620741041030700d40a100d6040e0340203000e141040072180740b01c0c0c0711419a07968000c0c000c1d0704607200c00b0050700040001070411034640d13401c0c0050000c296000c22aa9000740110306c01542d81d444c003c800100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 402990197 1250 402988947 402988967
    0xa0806030d050921030c0a03050309010b090403080a0522080702180f15030c0d08071208010f0b0912150114040501030c0302040f0b060d0605010212120117030409051006 74
    0x802c4814040c81699540d60310603a0304840c02440c40004507034a0010707144c11072154000c08013881c07207280c0c68202095040000784d44035404440080207400c2c001418800072000c21540240081c80c2071001400c4509668000b0b41c104e002c03c1e0749014078094440e207030003030700d942c002080d02e0b000c03000700f0f04004515110320f05070004d00a18070080d400e030400741c0709100355000260403617043e040500c03c01d140c151004c20171030641c02801005105040e0380d5042c640410703030000009560000080c80182c00b114002e4403414100c451002c0c2444800b071502022060030f40225030070681c003848124a05500f030a041040c500c013400c40d0080f212965240c81d1803010013095500d02c45000d90b05010040002c101c81406030000c40b5016034001c1801d001002407032000303000f00340c410342d4406030110f000c03540d045c1b03507a1180b4240c40003a001c07501804243d0010351954020021249418600d00c0014050004404c007403080030784100c400c03241825120035595050b1482128035100492425004104142d80b201d400c003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 402991447 1250 402990197 402990223
    0x180c0f0f1401082202030102040b120703060e0601050c0a02121501060323130204050a020a1b0b04060908070602030103031707170c090d0203070e040240060b0a080603 73
    0x100095880c80006409040f00500d1039200455005104945900074140c01e60650f80c0180210b582e19101d4419070b01c99040050103d10703884503c1d00281d0200e020340f04200136207918045000c4603503110001181e503903002d020b50034580c1c028507086c600144c03540203000e00125400303005442d0820002032541101d0070143e1103042050b083c024100403180c5c044030440d000040c5210385450b10703518600c030700d2010742d003990009400c60311305010410110003a034040c007040c1d0704690b96840c02003a9020030f0081c0103803045002e4100801000030a00041569004107101c5101d4044c01d41091400d8032880e080383c100742e0064011405900e4010400d040b405849644040d1508080581c0302c5a00440d1000f2680102508640080011160303483da03102c50340281003650090403a046251100d00c0c400311280d068a04238003464079251240e05050100c070b011b28058602808014401c0d1509030101e10010307566900c0030760b40341d6030300300442d49002c00030040404902d56200e41440f810400b090510f40702500380c0c48 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 402992697 1250 402991447 402991469
    0x60d0b121219030e0a051606020a030e0409060b030607020a020918031c0609060f08010501120209150d0c0305011a03011a0d02040204050a0e01031a0106080703180c0f0f 74
    0x1105030110a000352140110b8200002804a4800c02c2c03c0d401485507608588141c4110314514040140c00174034024808006069400f080e5034907501640c0d103042800c030080100b030180c8080820750800f64021003a16000c0c04000c40c00c004008017003070414000707071108401030304003101100c290f0403c070b42c820781c001074011418104520901c8040e038903030007264800312050300002d88075099040250441c6e03014000b10320341006903035a52544400c00300d2031841001815400c2000028404208803851500b454021b0255000b40d0703580d04941215481109041c1d6200c41035120705400709030b170022400e010f18800d100001d46502e42c2d0040302d0004134021401403007603040900c01b030f8003680c0d01c0c844001c90410030350b800c1c0398400c207510004003e40244c4d00000d4000508000000b40080c004600078102e81c003900c41c01e1112400c41c83c140608007424083c00003c42c08500114001c2c0f4032a511000540c00040c0c0d00350311911095848040c0100244d000c00b51f0500e03503c800b400400e00c4241c0c000002c125001c1c41c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 402993947 1250 402992697 402992713
    0x10513020d0201030509011b0908010e010216020d0515040602090f120c040c1101020307020c1201020405010e0904020f04060303030b01030b090906040f0321061d070206010b030c09060d0b12 83
    0x61001031a807800030704040d100d0010800301c02e0250000040254904051401101001d1004001020b20700c80e804c0075609000e007402c0c0300701042c0b01712403101103110402e54414900d42c0030f0260b0f01340d450303508440901c07600c0ca2421200340b40c03179802c50285c2d106001c00741c1e58070650700c10403100d0140310000600c500c01043c0442d08002d00001d12000c3c3c500103640c04540e1481c145130944460b102c5961103030055000000308901c1650110710a1100e0708100c465404084031202610700300e020728096580410340a40c18034101d440e10001ca968001d10091038501e00c5001d1038080740582e02c0750351045010903120b1700030020940c0c05000723034030507010159480c0c02c0b82e1419000d21aa502c40c0074202500c1034404403004024148a481a68420040188102c0003840072103003206c010901c500c10240d000c40c0700301d510040c400606000b10f01400c403a900402d03481c0d0924541040c035600107008000810002c00c0300c000503495800190240c8400c2500000700107403114103028401c108031303546030b52540240c0c1e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 402995197 1250 402993947 402993949
    0x6150e0f0411071b0501081e04150609021309050a0e0604060b01021e1f060803030f06270103140c030d080703020d051302010311031b07050309061b01051302 69
    0xd4084903420840d000b207410001001400402d1142c0b80c005000c003c400f0550b580800c0c1201007a1044036001e0741c640300a681c648481800600c50496080b0150005c0004940814104007618240785121100022002e94540001d022030340300081d044403c050f599000c0003400030a00c42c09600008000051001c1407903c800c194442c0700080c0004e16444d6502c0d540032082c0d108200c403501d02050001da02d54101d00341c041d05070f503a4a00b620210041564606c0c2c0c82e800e01d105000780e000710381001c0000d60075604c40b644441d054120003001c040d0040106c3d5188603c40001400c5a41c00c803120f0100e0110715410b508000c2c114246101d4040b0107a480200743d04020380300000c5100903a800d9150603503458540590031000b0744161546811400e040c4824005440c42c02d458a0040038800d880c10030860b44c401e1505041e80c08101d81c0d0b4002a90940100c01c02e03001c0100041c0150352040c42503901d0300c0b040000265258000081080c0643d0840e0380f1413102c00700912501380c0000040c42200300400341a8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 402996447 1250 402995197 402995209
    0x10e0901110a02190c05043611010305072c010e0d0c06050d06080a0803160801051005091807021e01020313020d02040e25051207030f031101020d06150e 67
    0x120400f42c541070300a9081c00e100c2d01e5014403021b440020300034419044085c0011500b02c4403040345802407803046545414442e01c6003c00c1d44850760080103c089800b07102c006400420000b0700d034900b0b21070300345207414601038101600804a1080c51404c4c0350702d61990700042102d20f50000103401025100100c00c0804c100704841011541c051803d03950f20019005d10901816041d0b202050718801c200c010b404011004000c2c610034a03a00246440400b2040c1e0100e0701600c0c28801c09400400405d200f45880b031043c402804a802d000d4210000612040034410305060216040d00058206403010640300c03146000d101e10750210f1200030750075424282004071001150ba2802442200c0981010342191101d42003007040c0985032050350b0007401840c0b41c080031440200e1900e0061a54010041040d10740814180060700065000308489400c1da5074031806244a68002d500340b04041c140c601c1200781c01d000034441d41c2e00100d000304000b490038030345000b122a01039482c0248003020344185c201c1d40b181 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 402997697 1250 402996447 402996463
    0xc020319020718151e090c030b0904060b01050721170c0d052e09060f031709010e0d030c0201090e0105100c1502070f020306060a06081518010e0901110a02 68
    0xd100005040400b0000260f0481041c1d0040210001d4078114039400c100b40c24544080b201c606c8800d20000510900480488851303501590b40300510002040208a0507401000b245c0d01c103041c443d113440c140e61101d81800705409035240401d04a0300401950b10340c8402072581d4460200740d8458203003412140c100aa0003580800003034156a64000b405020f0f000180340c201c58104091344424030b41d51241d0b0ba820a40324004c2c4900d86040c6540004e0390f0000e0340d5141c003100c2e000800200c1f500fa00ea40c0221940c0e001c118018100039000079861a6030b610301080c086810301c291a4050421440d20000d8031400c00355200f004049031000041001b0707119400620384104081c80d0801204015140448481c0316811552081a1022541004002e0320f4148114076600813422641640d4851080201004150180c82d0019860802240030030701c160036001184400241421140400741e80c6240b04c03090300b6403108803400081c0d028042c44034801c4c0300f522140d00c1c40070031080c600107030381c0d034069030b42c0e801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 402998947 1250 402997697 402997739
    0xc030e060f15040c0e100e060904020f0405060c03030a052a0c070f08030d060e0c07080c030c1009120804210201020c060c04060815090103020d0201020109060c0203190207 75
    0x1d41000034448080d400300c0c84021001c01001007154484c1010001c0200041450043c01007400403c0c40500301d018400740c047c1144014010b0389000c18134414000030350008030340007040326001d01000c1007659030070300036002450784040103549902c1c01820685c1528006010701c042c2d1002d07110b6031010150721141c0145508144d0030a199030304c0c00c90303960600c0d01e1450340c48040803c00c851004185150080020a0b01d940340c1c881c1482250f4560800b049502c4050715aa08143c000f000500c00260240e406030902600c5401540c1c14003108880e1700c0e04107100c06800e00c840b2903440c0d42c990b040110741c41840c030b941c03601850301e1007075403816070344100c1c00d80300043c0c3d41c0c01c41d00c2400c003850250314401d40444240c03811000540e04682040c111901c19038106001c1d407004501104002844140103403e1000c80502c0102644456403841e02481101c903100001681195207a10389440840d002e030241d0104450175a00569507a003a1306020440e400f41500003404641102e48204050b444491920050100b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 403000197 1250 402998947 402998971
    0x108010905042d151a01030204080607030e0a150b01091d0a1e06030506180f0601030f0c03020915030d030204080a20031f0f090203030712140403060b03010c030e06 72
    0x6140d8142c401002c001103001003007000884c20600035541d07940c0001ca02803402407903800e90f46800400560503030182d405981403d500c2000061002e5110742c200318802d101e907506440b01ea401d60380b1221100607681c020b00401a23100d600700300366560b010401c000104803003004015041aa084041240c5e40e003d0200c01c1c1080e250449a541c41700f580c000c41c00c00c2c503c00c0004100c100c1c2e583c64980c1e25038100303c504010200709041101d284081c04146c000d554030b01034014094903800d641d2207021940194030705588443c5807650100040c5c0345c00300e03c02d01550700041c2862901008108046ca004142d25280742094014070042016001c001f4101840c0c40c2d0020100c0901c0111032100500000043d090b6030b8580b20754462030125403c4058007014005081900384105030302e645020f800c0d1203410900a4040d40104110b101041d40e20100c840828054548005c3d900325010000d916500b240d00213a07281c66072003400c0d03007a500d000d101e070005c0001c95040034400001d1140485448400c028025002c150b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 403001447 1250 403000197 403000253
    0x409080306013618020c060c070302162702090d0f1509030c03080a05070507030c140715031404020109051509030105040309060e03210a2c010801090504 67
    0x80f10f4540610aa00c00b90100c041e0b00c41000e2011502030750b030920592035000140c40380c002c0070606600031217040d10b604000a265580342e400381c96843d948600c0e42981103000700c42c1c021006190460b0580f0080182c151074488400310044a031030794401b64858503410038410424004151a0260644501c5810408900c2002080c0c14074400b004070b00130076250041d26042c904010160402d08809203d40a03036600c1d21140c4d034440701ea80c1218829100500841d40c20711403078000074820b1402810b03541c4940c02c410302d07240c1c40070359040c50403007241c010070031445101d004000940e9052090388582219055802060304054002900001072030061500400a06104000c0d8000b403d040701d9400e48042c000f04414074042c01c00070001c2e20240660800242c20300e80454052038002030b02e02d01811410306401c1222034040076120540e00c00c60b080020302c018080382035000002d40c00300320f00801d11402a5071035070b031659000414000e416044000140d2401d4180702c08902c0702c14007200c90701700341c3c02008400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 403002697 1250 403001447 403001477
    0xc080f0906042a050a080d11030f070f02010314070809011401050a0b130b130e070206070e0111010b03070906060801050d03050403030c030905060310180e030d15081006060e040908030601 82
    0x4507102d400060b040f45d5060f000013002e0780c6c0015000c0c10800150b88031888008810300d096200d100d00d200b052400813080c006100868640301c03d621300030f032050400150800d21468114001c0008032401c1002c210703407004101c0803920038042c840750003c80c02840c503030340d43c100300005406400e10b020ba840c4d06a00450280d40c2e001c0b074000b62102808000c072801c2d844c0d0076002c0f50f0000001003401002d41d11101d01c804110080c1c00090298042c04032504c03500d52001e504001192506041740300c40712190340360038550311540c17414058040680343d1042e001c00c0c0a8240f410207090f0a0b410b038407142c000c10082034900003181d840700c251030640e6030601c0c000c0d00c01076050800300c0d4511600d0708a84d60203880002070061001e01c12000c00200c405c00b8440340d00c9521100710301401c5440320411130805400800c0035510760340407903100d400c1d860344221a01c452151500d0744146888404220004910354480040c8115500035032088034641c0116070502c40543c596982d0846404013522107414801e482a1103500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 403003947 1250 403002697 403002773
    0x7030306081015150e010309050c0d050f150105010c03110709050702030d0f020f0711040f0c02060709050a061709011e060504050f04020901030212030d0c080f090604 73
    0x70301c4003030215020052288030010042c907000002c0720301045201000100c800c03031000a6900184192214208680000015005071400e50011580d030701500030300800a43ea0130440a4400e0b000b078000782240003210340014a0134160000c05611448101c0042205e81ea02c44100e140107030b03251400b1140d20003015006c510784007050704003e50007800c260410030640da000024101d8910210000e100c2c10742d0b0b8442c0c400c120b1180380011611031901b004a400403502c4c2d0641c8034a00c103409000000c040d142c2ca80c114003182c0e4000c008600503040300086c8a240e0303a000e07210300d010300303c01c4a5402d4440d03e000c0d40a00707101e00181d041c240c60008000001d004107829031140381c1d0300000e5180007402500d80131044d00288940d0160724441c1e0301c1c0c000400c07680b6a500030040d00c569404ac0c4111816400c503000c00c079640880d25154811840f0800c01018060814000c12011280544500019084c480c4448124140040401e045603200301c00304804240c6903100c201c082003190a14041c000d2910350f00101c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 403005197 1250 403003947 403003949
    0xb030604120908011a3a050c030102040b1e03220203150a0518120f0c032101151b0222110d0510030b0106050307050904050906150d0308010b07030306 66
    0x25880d482e01d00c02010307006540c0c0b50406181d4003203a10100710f40946c010103046181900d8000c0e00040e1a001030a84000d00d00d000782c4003a405103088440c0105010002820fa90140c1c0001c09001d00200b070f0408004440030700b840c41140c0b07179114642907141c0b03600c4248410180000900300e980b070020485065480600c04000520254100309980d45000b0072a14007038602690507820394941c581c84440100400300d518a001489240300358900b103440150031403260001c00840f2400c7c0010403002e52048001400c000424440140100456143c952100d030034410481107207040c45181c403405107001c02d21000e603510055048800306050300d003482d22510003902c4041340031605407a00348941c807e24104409449103000a80c42441a640c503030105d60a113a041c2d1100400c211022801400703098000c20156034041094501030b403c24000c00b00040540714152084001c0707810440500006140d0070f0f400110714401034410030081d44440d940108a0a8148600e02500ca00403c0080415200ba04484 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 403006447 1250 403005197 403005209
    0x10080c03190f0c020f0601060e060405090a060f090902101b0b04060f0c200a15020c28031808030f0c0f0f060f0f072a080426010b0306041209 62
    0x5400141000c0d59842c0000172a01081c8110400003a6940c4281c0c03011440781350181c030060070185000300b842035462018001c4200684c031584041803034000045098020200240c020451501d18010702581014411200040180807c44000c900021078460702f0350b19030200240c141d55440c1d0a2010062540b101c3c1001a1403c1003218000c0c580c4c400040002e00640c2d01b6003200d021442c0d20700d156200100980100308801038401da000c1e00c1c0e120360240114904000a942d10610062440c5d0310b41005100b0401c20100300a00c200705040d80720440d410040b907494800200ca41c10b218078181e41e4042c0c1d800642d4660300c00500d401c0e040e0000d11a106c00c02c00300c50121105108111005070b180c3d81d08580c02c1c2d000c14202000a50008040d0171801d009021980701d000141014011610b4600081c0480140018603080640c1c00540340070020002400c00394008403034803206042d0002e814074030000f0980b0384e82c1001c03c81c0006941c085401b07601305034046110305a50300860f4090b114060755038441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 403007697 1250 403006447 403006451
    0x60e10032a140f040603110d060902150c100903020c0d0206090a0e011503020f09090408091e01030f02070503181206072001090b15030109080309010b10080c03190f 72
    0x21202001082910b0a8004852048800703062506010072104103120203003030806001d00300309240c21309100034610540142c501040b41451500495803019040030021003066002030210070341d51090026400e503c110342070500480e04140c42c003c0da00c1c407051881c2407240c00c102044504540e113000449103010000380100010a81d07880020f461a1803d10802e203400d2007070105609080c4c40782c800c84982d2280303500c0302e604280c40481402520700e00100104e07064042000303980060380c0c560003c9028078003012286c503100700310300000405985c0c4a80d2400c040900600020000070300c00300c1a6110000c0c031483c983c81412020f400204040d00411050013640104014000c1e4030340e0060095009840c055440325074518500c4455007260f00c2a40e01402d00d0b404240800e07080741c8136480700c5802c4000200042205035640d00c44c0350f4036130b0095841d2101c0e80c0d581d01d010f500303c1c1001c2c0700501c0c0e1b00c2c4c2a4140050030745446040d81c640740c4002001e210401030f942010204000c201d07408420f42000305941 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 403008947 1250 403007697 403007699
    0x1611012004080c0603010e0f060f0d140708070b070602090303040b040306060906050616030f0302190c0210051c02160f1505060303091305040501020903010e10060e10032a 75
    0x103181103030703001e402a44a1400303059102d40081c1409000c03241220500340300592135645044280c02c50303450107440140c1c0b01c01e034500c1403486c40d612840900c80d0301e40141d0f05455140c028182d010310300740303041c0d100c5045604801010014140080309540766281c000b90090790b140d9031000041d0030b40c4545e03003080c2c0a110000c2004010300109901032010746034222010060700e5112002c014040c00742103a00d1460400700340c01c00001a100e4010506102028200942001004400064000c100c215944001103500310309500b0742c500008103085c4440c290600c10314265034607002c07600143c00390b44a211410b80002c0c2e0303110b19600240003181c190390400750081d500d030711519103008841445810401c5484c10000131565616011046601065004244100c07241c10503d004014040c010070543c1d01d03560901030f01c1c110791820301807007500c0b6034010082c150607801820100c3c00c0758095000641142100d8007003029180c070340b60b05031050300d0700302903864111a2041d004585011140409094044101780 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 403010197 1250 403008947 403009001
    0x5060906031b030702101a0f0607150501090c03140601170403020a050111030a150602061302011419200d054006020f03030a0b0d0606030b1e161101 65
    0x260044141864046c1400b850881c003c14105002d40e22045580c80800c4054411851808400601e9000d104845058140342000d2030201261002d030311028030192a14100fa56595140c41100b008030007811121000c3d00301080020184500102243c9200c0c3d01240498103142c020450a015250701c2030080c02890710b100b985211503001a1303401c0c1401803c20b8107540026240041d20b02c00d0b10701e254020f00250391000b0002c01e4103050002e003641171100011001030701501084c020002070014503042c0b14826611a0300611250740d00707800d9044d800c02601e410480c1000820701c02000707401d600d00349860f41e03d12f240c048044c04070b03941d00d01c903492480d042c01443c40c441030260800301e8020076030904d130f89543c692060f41c880b002c0c4640088942c10410000f90410141e41c04120007900c05000d4241c0c0c10b1096980c1000c41e41c8030b8005480806040e01040b003904421010b141e14021003000c8054141816405030000350300da0030a903411701c40c1c0c250f5040c0c6654425801250480c89400303003981c04180f40a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 403011447 1250 403010197 403010203
    0x120403030f05010815040b07110106120b1b040501050d0e0d080411010224090c09010e04022103030703050c130b0304170a0507173a0605060906031b030702 68
    0x400750191401c0400008400c131000c124188155509030052080e035403141d0341c00e4010032005010405100c1000d6900390482402d22490001d05410780007011030b401076040c8070004840080c00900d0046180c9240c0031a810706070144c1d01140c07c00c0c01c0c000d4440a80c00e803c400074056006002055125034082074802e1507000800c04e000301d00414121a49039100c02c012070703c940c00f030ba041030203180c00c14406181d0038203180000d5910100765810b40d9504082d04000500307000c000e9014030f141d171003e2414001586000d8080040c0b4010380da0b5021074048503032244075101c0c00014062001d0640d55000500041e0508084400c0c0700c0300c0804c00d040d0f180c0c0b11103c036900c0350001d40b0152204c2d52400720080e0b280003c1c07070440c0e1510600703445181c10700e240390340c1e818902c03000402c648810000900c42c03411681d407440307000d4080e49071611101040b01c4401c1141c189001542800c5a8002e05000c0c003000941c07103a0084460462003526115030343d41e2a104c4031440c074014a05036014841d400000c010010380d005c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 403012697 1250 403011447 403011461
    0x2150d021c05070c03210c090e15010c0f0f081303050f0703020f0907091a041502070f0b13120b0402031009020604050d03110109060b0f01020a08040506070812040303 73
    0x10040e000e0504031400710001c00c4400c00c84a0a0200701003aa541002c6802800ca2601c55129500b11043d01040140c1c0201920f0041c0001008214100810b120600b52803e442d9401080103910700080c2d0b00d80c40000f00383c500e00300301c040c00045490b0b00385400e000581001743d201c07079041844143d98075a000178520040d9814481540c0c0c40c00f901030091070051002c52100102d070380040030095201075002c2000003c2e00302030000000d000e0320b071000040b00018480403400702400301000c5510f0390b15041c4d032401e00c0d854202c01703002107401408050040307482c0710103988107803604446080d49803007100c401c3d8001c00d00c0c50703003168407941c400340c01043c2007100c0d0314031981c8168402d030f05880038007004a8480c03040c3e855a14000b9440202440240000d04004601c00781c102d0103480c001c02c07100c07941c84106003190360031030003510600c1c0c0791403041a40303040003507541c40c0d041c01c00c0c0300401200d010380d280c29036039000368040c0310b20030340c00003403500180003002095907505070412036551598202454003800502d10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 403013947 1250 403012697 403012717
    0x50d050a1503031d0a030f140307050f061915091d011e1d060103030e0a0e070f03150501091a04030503040b03150a0513202d030c0f0702150d02 63
    0x4e400c00354045410311140c00011a036000700fa04204005995802019404000c0807024034402480101e01040c0308201055003281c2001c082c0c0014240804450603080c050364070491000e062021500b110b104005400081b1800b80c40700082800d41074031140b08801c80582c291a440d070030f103860003035841000f01c00c1c42c02e0100361403000c0100598203003030301c580101c01c401400c0c1c1503001a401000881e00507144254080700081c403800c0000d480d0701600f901c50304161080f030002041c0915110806800d4841c5032071400100420700c2101d0b1800340001c041c15440d0042041100342008809001c0d108401920003540d0f003c1c06032620386803030720300001181d04203e80710b42d00c540340c04040760658108241118280c0d02d010700200e900bc0c0c0400c0042e0090104050354480360140c448296030503c423a5005091002d0038100c2044049082074892070703038009540381b081e00c0d100040003800f26a41c512012a80c4003403840c0f481984508480c00003d1503002c540781120400f40001510108040660340145250300b2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 403015197 1250 403013947 403013987
    0xd0210140c1506130e030403170f0a03020702010206060603060f0607021519180e0a0b0f130e06010503060708060114090d06240f050402090d080a0215070c03050d050a150303 76
    0x1040303a543c281500c50030014403000e1b8000304000e001166405819651500307040ba6a42d01d4001400e0b444981584900c068500199012071454210b40e41030105030f402000441d0214118148840082c2031013640103101d44c400c201c00100b00b400c5480c0d4901503544841240e6030b107904d07611a00c0d5441803038603c6002c2c000024020f14403603004d124200b070204040e9000c8400c4d0700c03c96592500018010080b09054650002c1e1a1006042d02d0340da8035000c141c445a04c0401007101c00c07840d00c14518002068010601c642c004c02d040291090740000d0740360380142c0920b02248800807041040041d84280c03503800c0d410008141014040c0300880d080400780a454030115018101c00d1044c19903500103038020403c49180110b402c12840c902600a01017401000f004100442c40540d0341100c10703032000350b004015821110b400001c105070465016485030b050700b001681c5130542d5500030b01900c10600f0200031181d8880c080780c50040d072940005c402c103000740100500541c076030801904981060740000c151071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 403016447 1250 403015197 403015219
    0xd090501090e150103052802091512070c0f060e031201091401140402041220010503010e060d03140c07031403130b160f060b01030b0d0210140c1506 65
    0x4031081c014070303114090f109079a92000a8003801103001d0070300038201c550f051801c80343e4003003541101c0003141c900c083c150500696403100c074420300ca0b20101545490385081e20038011443c05040c851151a40300b6841e103014501644585085450210b00c03803005041c092408030700342c6480c40b000004191240b1422150040d980ea1000650281c8458002c0c55000303584085c01042441e03095030380e518004000a002505103a1686e50382050540220740c10f42d03d248010182a080311070381051804e91003400e1070420300d590b04194240401c0000901254001c0f0340300c8110b0000e0500c2500300741030400071900640e5455109418007642c403c0c2601080e0346a0b0154000091460400001c4814400420042ca24503503d00482ca41c3c040c1c2009080904d165260034400c0001000310010201883c4500c000103416400507000408507001e12440f02d0085040004040141c2c0c0c8103c10142d06003080c0c94000c180062412202c2c40c0ca010300030380080240315094000c400d0074404911244a4041903c200c1e180b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 403017697 1250 403016447 403016459
    0x1704050f060c0d0f090815100501090501200114011716060207030f141c0807020d140d27020108100b040e1003050a060603020117041e140d09050109 65
    0xb40b007110000e15540d8854030b0002c3d05980220300500072100c0b1400d01c802c0003681c0390106c6090008142140c640f00c42da0304200910070142152080c00342900786886641c2c14108800600180c1b001030240945a20300d00d203006081000350040d0070990100e010602143d40c3d61600360089440244204c0000d000d052900e81844240550620846403d50b009100d42465901d504003a540c0400c002e23030700c4254150010000540401820101424800d4000c105002d2030800a00c080b1010f4a14000c54000e0320009812075802610369601e010412403096484800482100080c152050110b601d649600111040710001004440c0c000d8000e0703c0c0c400c8190780e9511000c0e0088418040e11910341418041400459140080d0300d5010540d00700009000d602c0f62999841c0007000c1c00304550090300d0f44014021035a12440c0346108907e49000003a003820725130746441050006441c130030018200746050380705104415070b000200c003881c141920200d4404010041603034942d4040d540c085003a0540c00220 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 403018947 1250 403017697 403017709
    0x1409060405250c0b10080f071503020c15040b0901060b03041a1b0409021c3c1505010206071103040905041a0a2708040b03040602071704050f 62
    0x8561000088078005403030309840c01035900c00d9001d0b0384042080034603c03400064a403c007201d00581440000310b240358508044107141400c42c01ca440c820340c01c2401c081040c03244142601d0310100072410301603110318445180300e1420364008414280103804605202c20303c050021164001c1c03112070001d01110361a8420134140d44019540200f068200140049000f00040ea0340303074020041880e00c0700d0b504d0070546407120b9a00b1540103413806542c00111900060a50306489000503a071301d10901805c000d0042c0000380e204c0060004108106011228a034554110580c8403001000e0404100240c0520423249010760140100360245c4154004950760358041e50f00c450080c04c01e02d0045140904045422015050141044a0b550400c2c0407503941106620b13442c0d4492540b456000034190074041c1c00c1040d83c110001c0d0100510418003015010a908000705c0e402d8074a1000250307039035203580c50b115009114000c07000d0151f10f015480e28080d04205801402269422a81405401c903280c0800c08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 403020197 1250 403018947 403018951
    0x602030c030417030c030c060901050612030a120b030106180509121801140c03070b0c030907140d0210020d03060515270a060201091403040f061202070c1409060405 72
    0x5407640180300c200185440c94900708020512141502e042a260020032403071030b0000382030f904480c2c0106040241c5004c3c24821103074460012030710540707901c00710070aa50f160300c54581207600b0025158002c12000310550800c072881c08026001b004140d55400100284400c800c202031209420328002c62910b160000710703c800c03d00c0c032000d2603280c600a440504091301c0300b410107605220324000c0780200b0769036000c0600441c0e8441400b45541d80c105140026014100a0104801100078024803094000000e981d4050702d401c05602211505000c0010300c600303100d090000d500a0f220710070821440d0f404141c0c954448200d44081c000507840f0020006080d007204043c9401c0c150a1145c842001804d038080d400d160382180c0700704064200440800e1044001e1307040304002d41e45406942080041e91680710740f40900c2d64018608003410721249a02d150200d100d80d0042111000180e0680904d580c110380881394498420381100340d0f00d2040e1000710024000981c86a0300110009041e42814081d0074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 403021447 1250 403020197 403020217
    0x18020a020c0d0614070c120207030503030a0b0d0c0305010606020601060804020f04020904090c0e0108070b0c1c09090c020c120a0f080a030e01060815070f2f16060306060203 76
    0x1c142070029809002e108890039000759a00307034803200d0b0f400030f500a4510080c000d00c0a965a80c01006681c20804800d042134035000c0d0866000171010000300f00013000f80c079080a10f100d030120700142408002401e540001c50054101140d09000104002055000100316009602550516039072039406803464001118040d42240d030f00308a41110f4600340d07004280150006100003502509a01e4500000b6050f4105070b44000011005001c002410040200185031003d000e0303113400243c85802e91035034405642c005001003002130b0302c103019000d0000d0350040c21303140c07200f007150401d800402503860380300060043c091480f10801c01e20f840000308400c00002d07001710040d02800c0e0f899880000580c000c403465010140d44004d403e8248000b0f004001c02000d4a10060141031003020030100c4010000d007058042c0300d03000c001c050085c1c1c0c01c0403a07034250200503e04c80303008005114030905843d04104418106006042220304030720640300c45501590031641d000c00c5000c0d250001a640c074402c01e41c904d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 403022697 1250 403021447 403021453
    0x90b1602060c030a1b1106090a0317040302030403022e2d020c04060305060603010b06090307030809031009050a05070e070914040e01020705030715020412020906030a02030607050418020a02 83
    0x300c80d503060200454025000e14000030f60442c51000e0905e6800c000c0326010000f50400842601c280020000c103504003070500d01410035002c181c1e80241140d01c102d4991054070301140d0020b42414002e0041e1801542c01400755110244640307400b069500c40d40182030071100307c010000220302c0c822002002072040d8400801c5004001004c0c0300202641c80808208503c20034204401986907806000d0055104000805c0242404d04c105401c1d18109880c0c180034076014040e508003640c0c000740318000c590300301600c01d980f04030000200c3c0c180792100300c1a12116080c24680c4042000c00030b04071082c64014410f4440440c0c49035072400d0fa1036800c1d41c420b000a1480403060080f02c0c06030003064043c54004000141441206142c00d007641c00ca85800d0b142a04003088501c00e100664440c2d025500701240118603203030424200c183c8603200c0050280c0581c040b0350000b1600c1e20200104001d682c0c0050413070340e40d854407050007000741e03120340245240508401003441d407540c5a8000d82d10081443d03005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 403023947 1250 403022697 403022701
    0x60201200d060314010e0c06190f0203070209010f061707080a0e0708010e070f0b1204230f1b09010518042301020316020a020906040e0a080d090b160206 67
    0x34803a21a04000011802a0b55070040000016081192a881c280d0114000f05054070390034283d038140500d0b075001034040c250030030941d50003903034000c240c400220701410302082d407c9400354101e14501441d103009400184027030000c11503d420150400c211417681c1c0e10160300c001150303014111000c00f0fa840e03002245e1020007007036801d400c0d9045004c08500308070031a0710031a0f8030250503080d0f44400100c02c000b40c02003d0f05001c411070b10326002010346590155586444250010400010070041005d40000042c2503a40c032100340c480e0040418181101c00c4880200201008980300d1003091019008100342042c100c0322410220000c5048810007086a400c40c10281c00c0c0e1043d8000c0100121003402007254952038003440c4124134642420903c0006850345020b42481d281d140203100310b132042d940300060220060743c840c840c080c2d001e201500d011400b00294180c0b5031400c40ea03018010240c00b40030400040404442d4844284580203207004e803904d0303c0d1410380c030341d95201c0000008016084480 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 403025197 1250 403023947 403024001
    0xe01090b1501020c03160e1e07031806090308090c010908030409051b130e1803090d080f0a030f18051002070c05100806010f050f0403031d090408070c060201 69
    0x9000c20500c1c4060056401000500c0c001a04042c0e0740c5e085c402d2a03901e4a0000e0100c002c48006099020a04544c01000410f1460087c0c1696800a1010781010f40720741c1c07200b14181034888007000b403550041c020f114803401031401a1050714100c030b80300301910a4240444003984508030f00400c403140031001d186064141008140503090041c01524112520000a07401e90601c0c40101207241d259880034041a08104a000302103401905040142800f41002001940c0c0401101d80c803000c103c1b030443c2e81ca49035103840b80090240c129008820034012981915103505604544600c1002d10006c1202003810914502c420070409400323030282d80000d0b1220025201603004010300e6014a0300c0b004580ea031080040c0440c07234140358000008200740184012540c00518510385035102d0305009051070714079100c3c0807050150b4800a81000551607201d01d04125902c808643c3c0a400741c950149498a8241074a095001d018100c4141828540c00a000c51061082c20030355501040707a040c964035584 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 403026447 1250 403025197 403025221
    0x7050d05161104111303060e0d17180d030609051b04030201050f0702130e0c0f031b010311040602011d0705010e0f030f0d020f0c1e010f120603150e01090b 68
    0x220034075402130b03a078800080790008803c0281680941030034025440f641103182002c02d4400c00040010380750f0200b252034032016006241010703880300d4a005181c03169105004201103402c10240c0d000a401400c0f800c070b005552603085032040d20000d0704140281d440d00c501450001161030000740303040f0403c1c002400191710130001051207a0301c50f00e80b02d0811040b6000a00611401e0700b401d032075160303220440341e030048050000c0300c0c001d4400c0b105000b80159100c0420380b142d01008440030718503412030301d020442e030081c1d0206050320107200e030180e00c84c0d444070710181c000c01c901d80640c800c4251320005001c00c018002411070607100d040e0b4400700784da1908428800d10000e83d01c54113a150040c911000c00500b0100000141070415a0007003996000f25245541013031001401140540030b030b08400c040001d0000004100003000f031130320310b980141560049400440607410141c032207080a00000c1404503091512003502e440c3c101c1080312459260b040703822910a05c1c0c0c014580300c03c81e000203c0e002851 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 403027697 1250 403026447 403026473
    0x213080610171606030225050a0b061503010f170601030c050907110a050c0f030c010c020d1b03080301030b010b03060f0111010e010c1701080105010303020312090a021507050d0516 79
    0x50b0202c0d0030501c0b440925800b0442290131070b0000981c041004038480628a0503110b2419101d96402c10020803621001d4513007039096009051100d480010800e6911150f8800504d071400301c00c05616561180690b030802e244a1142400d803410103120b0300300715000480c030141205d6124040303260480c076020900906003070052144040c06450780082c0700c056028082d00c2000352280000e0000c50001c0702c10442505c1001c1e03580c0f03011380d0002d01c140082d40d030070a440c100c190341c04031800d40300d515442c585a84a80e4100311102170004440c1c80001c20040f081c0040c6051340d00c10741c4810003907a01c411140903280400c50314294414880d00301000a5409031a424464800700350010400d200760300503407400c0d125803444440003d0700c02041070f0701426403102c2803805030160070002d200d1541356440081d03503800788006c1210700034000c0c0040b502c040c0c410401ca4442c00d03406032105501540051140c0443d800c02c40741030b10301c2e000b1041c1c0003144a100300c080b981d03584440c1c04520000300d120744940d1210559 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 403028947 1250 403027697 403027739
    0x50f0711190308061201061203031e0c0801061209021507021f02030403021e010c080f0d0c030203180106060f180509040503091c08030f0712050a0213080610 69
    0x5586442500591070891120005019403203841e0f8074100401884030214808440e450b40d40d16086041c48510740510040f4855a0149004582c51442031990410060b1107545102c0c000d18100f00300c90709a41040209048415940700c085001c42904842c0059412401c1c00030f60002c2e04100b01d0b424403101402a2a40703e0000c0c10000b00515118000c0101e407180c480d904000d603102040420440c907085c4000800c410100d20b080000c21030001c0041c100d40b41085000b4845c03103000c40c2e4800c1c0002600150f40302c00f40307480014050f440c86050b02034000c0d4402d561210310f0741c0340c3c49000c140c0300105004050890302c90b6560340c0f41141c6800d0741111400300740360780d111952901020004250303550024503800365004e2000f4540c1e51884001b00320f2440481000100101c0e800304a504c003042c183ea003503e5100403641c800c622680c0d180035003196000c24025090101a1a08091042141a5501400c2c2480b00324242e04da5081c1c903410120303640d40c1d0880c3d801600f1030081c4820b02c03e420b5443c0302e0320480c4103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 403030197 1250 403028947 403028953
    0x40518090f060f1803041802031305100c03060806100e06030304051e0102010606080907050607030c0f060506150c0c04020a020f030406080a0b060a02100903231c050f0711 75
    0x480030201c1c1004030039103c1d040000343d15070500c5450001c0c500b041d4680302194005615280c5420443c40b40640704250095019901000240140d100081c4160a03960301a003070343c540f842d00b016048001c3c0740d031400290000e03142c801c022521083c000b0344180513000d1100c000396041c1c03506030001003400000f06090703090701050100080e66114214175981e120302443c00f5600c00100074000a085403d2580140100308904090041d412408661030060b80c03001e0318000c0e80c5002c00d05081d14100070402000704065802843c0005005095001c3d50103460111091240b00381c05080218082c040e000600a40307401410312982c40d850641d00404941c041b6005135188891200302190941d081070340700f0804280b00808001d842d030094481c000d195401121118108140020000e40d5204041210800c042e56441e11105150080301c4a140e0108040212400c81401d078916181ca50095070002543c02c8d8440380042034030b40c141c0075241c81030034201c071907040d0340e074a103102150341d204000c0b100280382c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 403031447 1250 403030197 403030213
    0xc0408190f02040b0f0607080d0f02040302010f0c0515090c010f030204050310200307020318030a12050714190201110c0f09070c02040f02040311190b0c01061502060907090204051809 80
    0x2d1108000b0f407084c98000c0e44196101e4218490709d4050f40e21408540c04034510411003800180c0c1c2100401030580460b00d425006181c141c034180d0307e005d030910030a05414680d0310400518480009180761001c00030303a982c103543c01d9040015004c0c0e0080e8000c0ba54103030003542002d40007402c04c0c0c1c0300821400d50044c1c403042c80c07001c00805440031f80c003c0d40e503000142c00004002d40b1044d006024604a150240c00038824180c00d511401021141d80c40c4a40c104040040e490381840750810606600d08040c00941d2042440c0c88146240005000700032408a018180b201c043d1400c041220621040068106036011a271070041152a00d07004000c1070600c208800b146004d42c54038401d68400540000c0c0040e680e5096080c04401070842005240c403641c24441c05c074110b240f4404850341254805100f96490f00141c28049025050b41d4000440460f0352043e0035901c1a80026058020000035007581d00b6203890307554407004d034451401030940007002d041158074201314003024681d111904000785c0b4219 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 403032697 1250 403031447 403031449
    0x4030b01150c0c120f020a0b07020a080d0801030f050c030f060a0c17040f1e15270b060301060b03160e0607030905100c0f0f02010206060d0308010302090c0c060c0408190f02040b0f 79
    0x1004150000304075023002180c10403c600381120765802402a1000400b0002c890880050000b141400010f012600b40f2078404200002041369020003c2c006043d6007000e8aa4000c441d901e090440300040c60364100140380c1d4541c0d009100d07620b120400c0c824403038025a9141c460043e00481c040f401c994429035807414040140802d40c0d6501c40320310901c11640c0e82c14a00281a00340c0d10303601600203140c181180d898481c562901c000c0c4801c158030008002e00c82e03843c0c0f40024010070300c6070312070140c190000017040300c070841846a181c440744443d120b81102da0000c074140075150091240c02400718204540c2400700d440c0c20b10105840d04454500042c1c880441c1c2c0d02d40c00d40610806c021180d0f01c0002c0c41130400c644e01802425480b000c1030310114840c400a1b2002050110180300181c000c80516001c07620568004040310060901402200c125080001001d60240d010344580700050003a242d003c206440109903010116400500c80c101b60020340d000c10008003500040d840c2c1c004605542c120741 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 403033947 1250 403032697 403032709
    0xe060a090b0f0d1a060306040f020d0e01020d060e0c27100f090b0322050106031b0f050108100905090120090102060a0203010f0b1b0304030b01150c0c120f02 69
    0x21180d0301c802c2603038079020801450002c3c0c80082c403004265003024842122a61144010b5a03072209044501080000e0f640000304000c1c41429070302c1006500388410100000e0b01500140a50306602c00100720059503900c244448000c15500b031001c43c03804101e844071030f282d40a8a00e0081c1800d01409401c210300c1400910207802c0032040f100818032920001c0e01407a00092564000c0600c09a000c0c5145031460a16096010011140c001501c01c0310340310042c000d0035070000300503651103050440ba1a060502c00c0100803098824421614403841c00400c55501c5040f40a01503825414103611090070941510b02400c0c000b40385850640d07846140c0700c0c0d1544000140010121040442d540e2030384000002414054018800141c0d81c1c0108010405070a0183d810412a0080d940070740c0c48a160000c40d01490a084102c00014400490f001c014800090070086c101d0380c070a0807040854150107000d80d07004080782c001400031440c01e041040392443c681484201c01d403290110508182c2640e0001d40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 403035197 1250 403033947 403033957
    0x302010519030b0301141603060e010b0a05040b0f1c11070b091f0203160201053706080106150c030801051e030a140d0516030e04061205101b0e060a090b 67
    0x5103080340e281440503071f48415017205c10000e84e624044c0607250a10900050001061085074103c0c14000389410900d4400c00694000d0300398101c074030750740b00580550074203943c2003040ca44107200c0000c07100c0390240c0344900c1100642100b62500c2820f240a540382c1d1581c41c0310080074403c543c0074440c0f00c1c07200b01d02c800080b41c01e00c40d400c0200503281e0504410000304100013920702002d6a240c0010700458110b1841c0322044040401000405e03400e03c003000c6098042c1d80c0950307101480c1440d1010a034030700190824401e031070000c0c03c850b10f94402003200b110f0b480365403040a000301b84884014091400e0101e1030b2506035280030b801c80303000045c901c0864500b03c2408001d5801e03400280702035001650900c02041403007654039020b820100c00c0d9120a007030580e8010000c090081e450103078111600ca1782c10660003421a440304844800490074500c1c0c84841040389c000c607503454242409140c0e880505090a07601007540c66003000c60845040c003400e503001800040c24411038031800100c039600300d00201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 403036447 1250 403035197 403035221
    0xa2003010e011512020f040c0e060408010c080a090209040f0618060f2f03061909020309010b1c08071e141606080a0f091203020703080a05010302010519030b0301 71
    0xb42880f1a003c1e249a402425080780c0c03110004201c285000d80c0d540801128482c00c101c0d0002043c84104000740c44a140d034606041d0458000b1034001406001076104030003c620f40c2c1c4a03444c8540d54115510200e604c6840000d500c50148000b0401103583c0d603540b104c0251184000103030020903290039030031403d455181103e2981d11020100d4400246004041d042401e00c1140043c10701c18410301c008480501c132340e50b2f0b8a5140440054400e945045031040300800c5100f26901c050748440f41000a5401214410400e6003802200c1600b42082d080001c41081c40d0107003465110801c2c1d85421941e4881d02c41601d5000789129407010510640c100384c910345204103841c44011002c03010352400c0265000c03201c00b254420341001c06c041a0051103455022020b0900094035001e00c01c40c06008044800018201c0040c541544010582541c01010070074040c0e2148600c82d0354610b120700558409000080c00201c06208109805048101d003080300151803c01080d039100100120b070845d08580286 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 403037697 1250 403036447 403036451
    0x12060a09020a0506040608160c0b0a0905010b0a0b041202030322051e060706090302030c0111090a0902041208030c04080a06050402040e15010b131a0306010207080f0a2003010e01 78
    0xd041107107001c0e0301c0b800082c4000e403602030616240207400362a00400401020701160001000c100441c402c545442585500442103045030a10030483c0c0000d011b06013003102c196107000c4080344d441c54030251100850310113800c0e151416050418000e991440408100d81520080c0a801c55401c010f50350f1114401c802000700202503d02800c0003903840c001d1525101600341c600300400591070f2076003101c18840c0c11400c081441044d9107422031842c8243e026050b865464400c4103e44401600300411008508039a42c110b600e840f1800340d01244524440e24602d9108280e074100003400e19406994000700c0d4110882c280340d03442500c4c50504e0110042220002d83e00d004000443c5060700c0b81003503c900703400c0203281c0074003142007080240c1018080c01c940d00c0404550003c0040d0711520f00c1e00548003009032001e01200560140724103030025184e09001d4000c128003c03ca500c000992228804825001804540c90544444030212003e0780e10868000f0301d01c42e48180c60b142405190301c00b45000c400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 403038947 1250 403037697 403037711
    0x30204080327010c0c03061e0e010609051506071b120b090d0c05031b01180b1b0307020709020307090302060408100b060306031e030c0118170406050a0c0212060a 71
    0xb042a04110b000001e040c400d00f070108401085c102c09000040c1d90b0b0114000030300400c0100b040c0340041e04000d40c21403144c100b0300b0284210b001908041c048034101c81041c0819116402041e0b40d0b40f10307000c1000c2d04010140040808540c000d800c042000004ea15000d015a84420340d005103802d0050302034030f0f0110200140645203400b000624241071091901200300a82e40d620581c0b40e02c0f40c01e0000c40c50a2030154404034030b1300d0a5210620807060705028602c84d100900e00300301a0242111110b0040c00340f151151511aa2802240e1040c852580500091070a000d1800000d40020304080c08001d00e90700c1c00700c01600d5440081c00030f00a8800200b606203c00e82d0400240c0710b811140e64020f900078004e1102c5610001a2b9052108160054491003006040054a14000c0240c05038031076013070040060300c807441b494070740c0b03541030141c0100640481c890840d180540b046110340c400240c0d04000071041e481c49503100c4840302d40300a00d03d03102c030340c40f000e40580340180c25100c42100c9651000c3c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 403040197 1250 403038947 403038997
    0xf1e05060109021305190b04080d030501050f03072303010f0f1802010f0c0303150b040302010f020f06012601150501020d090b04030212100e0c01030f0b030705060a0302040803 77
    0x22a030040682c00825858141c10500b40d11034442288243da02581c15558220808840591030101138420854503586403582d568000e660703000d0035203008011074900b400201c0c4038105000840b40d0079001400800302c45103044031500c0700c61034410300002041c40484070814145c0c1c0a0040c03000b070311991f00700441c0300401400c103003088a80107140c81c0044a50494504011b0340c0198010812482500305503a48410700d003400d03405016101807400102c0c0071854045040016a030162081d28000c5c0e80e100c1c05000200d0702a6552081882103591a0b404180100074104030b520f0341030300c00070704400c1c4201403042008410342034032513403481084510b42407d42030009507030400900c81008803038980011098500328006096100714080a4000c0305500d059a01d90711040091040000c40004200047d0300358181c455201c440c0070184030700090903c828500c41c0811801031900c090310007006010ba03c3e16140400c03003568014100d003410700d50240030000c1d00100c180003500c508001903400d443d03009402d107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 403041447 1250 403040197 403040203
    0x30f0702010f23030601030e010905060703060e0c03060d0821190606081807030506070c0611030c12071206031104112a16120501050610020c0402070f1e05 68
    0x1202d1010031507a0041c4821045201c080305001c1500008803540e00e48411004901422000345003035001d40c2030914071020010700191306407282c0150b5508000e0244c8860006400c480241c80381e100e500001c0c00070070040d1134100196681c413481003103141d181588080b000b09004990260881940038000c0400c40c0980b180b50004840c01c01c0888100f20a0b42480006400c9000c060a010b00810241203044400c000c10000b000145401c2800c50b0210714041400030318016440008a440034104001c95000b500d1620603607000d54820700b03515003009509101070604042c0200600100540d01001c452000c11610a803000755003d02c0009540304d81800038001521000d1005031010314081003908110701b0f44180101558014000740300c145500030034030314513201c24100d111240c1001c50748000b5101103201c0c0c0000d9828402c40003031002d0740d03618042143c100482030020b4090f821056104402e40380c66801400a144160038603c038000c0c49071a8502d003041d002c06038102c14040041d4540c1882410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 403042697 1250 403041447 403041467
    0x503191803020f012c0307080301030c080706140306270c070b0c13030209090f06070806210309122103090f06070e04091505100501031113050d030908030f070201 71
    0x240f8003e10045e80e00d150700c00708541c2c0c00e00340d01d5084403000300d160450720418001c40350502e41000001e034595031a814050013403411841100010700c2081e000049941c05000e144844250304411142035907520b41c1400000032401007030420083e0000c2810111076440d02945001d080c071404c0c0c1031f440d1815441c0410124402412482c03a5a10901141e0024102d07181050140c075419103e500d0961613140d440f500d05201d4007072498080c0101e00802103500e034448107903849030004a4480c42030380be10503880f2868100341d2496203c03540080200e0061802c14000c5d070409030030900101c07620900c000401e0030303012603030b0942140440400018040002d0041201c0c0c401600240e001d05114105603202610444080c841c0601440d103407010781043c4100551410740079800c40d50140480d00d0000f507880300c05e10b498021940031030329081c1942501d20014080e14a80c41c00d180207070786200d04020401070216210482242049800139003c640b0010030720103010100b45119440380c031950540b00141030700102d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 403043947 1250 403042697 403042723
    0x50406030528200f031302010507061b0e06070c09020a0512012c011508060d02040e10050a020405010903061d1609110c0616180806091902060a050319180302 69
    0x107103e0010f60728540b4048903040a000301c2c6d1200365000f14030050f181d50040b0080945114900011282c00c51004e00955a5a816603614207002001c04020442580204a40640b8a55442d0801e2001c150142e0080c42212010b04005080c4038218500126000c001d0300315a02c0d400c04024491111118904442003503086002110300960410205a8615410702201c4080044410109a00d43c81ea0400d400016070090414080b141142c513645980d00359525050f0441494a030005100361154400d940507100d050307542080061568881602170480540344403a01500703148056071f03408040124800000030700c1c1403284510310340905401161202019000040020010380400800214440358441898181c810314035480030300c03c4501c0b500c0e0f224400c2e0302182485002c103c803040087e880b172044c201d0b0000c88410038000d00590442c03800c03c910084d0440300a1040380041c9000314003944d400f0304448181c0d41e500d41449624415101106a4400c5000e4000300c51824141d040c464001c070310711 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 403045197 1250 403043947 403044011
    0x7090c0906020319090b070b06010e0301022d0f040e011403060402010c080705070b0301120b100302010f2a0309031104110306060a0905060315030d0906050406030528 73
    0x300e441c002030344034881c2d03580111600c49183c10040c0180d00035400300c4040e00c1460680ca4940616142c2424a908142d4005010078202c00c10083c0e1403405000322070124410b451040d910034001d4225016180180c00c44a80104003800420144140c4d00c000d00020720724a0f926010951401f203440a61014500c07200f802a00701d10704020141c1d800200c2610640ea0044007240d451110341030035410f00a16400070b1007d480000000140b103541d42c80301095141c01100e80c0c010644840b050340892444501c4024045450900c01c1300c01e050041c030200101110300102ca1b02a030410f40c81600d0140b8000104801140011000780301b4880390b10040d80310754070150303003c01048029481d25122400010031151081000084034008980f01c2e50342040241006080581c513410f1420060350440070075401036000344908000303c001e440c0b081244c0f1040325a1501c5180c41d160030f00c60101c2c0a040c00402c0201c40c40b03c00000c10350940075119444000c03642903d0700040e60005080a2144030b001d21200c0380e2411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 403046447 1250 403045197 403045199
    0xe0c0108070305070806010c0204091407051306050a15571101050706140108060f0106050f1303050f060118020c0715210e0606061215060c01020c07090c09 68
    0x2a401a502d2074006c042401c01d6800c0500300d1000601030040d09000914240038020390361805100012010144e175012201d000b6241e41c08274842c0101e407031500c94298000c500a204104d00030303803842010010000d0f41360001007000e008412480781a41c0781c840d141081b0b941100200d1540591400704801182035144007400e0741c4005110104803c11040500340b03844020344843c40382e019030100c0710707000e27446901801200003c031210101c9c65424403910703155001d034400081c403034800000c0c0241601c03c503403030f054100244800300403803c0d0051180036101050384240480400d004001d0f02002c0340a8100820b4103604001c10301800c007518008a591003070040c4030a460f240e80c04600542503c00141d501e0051280741e40301140c1c041208444041422682403103408601465004440f0f1240b0610031507805403184820f004076481120a10075101c481040401ca0011003000c0401003603074001d1200b41000e40c00c0001d1400ca078014003410141e681300510400c000314407400360070903041d00350802141e06 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 403047697 1250 403046447 403046461
    0x5030f04110402130602061515040311060906030109020d0c030b0d0303050405011404150501050d020109031e050318120601150f02010e010213050f04050412030b010e040e0c0108070305 81
    0x1400060001849085090200d0341d041e112a4107a038088210b03a4503107400d5681e0b030745000e9118030058468a14042800ca0b82244508104800d86d030340c2c10001a80364034181c80c50f16100d80700c1c8052403009612000400c840c0c58243d961002440c040d10322404010796588055031403404807004420100305040c2840401c18407070351940350700b4622982500307011449607100c5c40c00500410000030540417440031700341480103104056281100d03024940c403040106036241d00c104042036102200090001d6040d0a0500020760f00d80c609507007a205620410007110103030394405007960070841541e01c6d110001d40b496a6280380040c08a00d5085d15800a0b00655040c503490b01525040e2110f0ba4040c840d81c58a10562180b00354401d802081c0307100001c40d115026540c881d5500706180c4100c1c0d00c110700480007104141b85c43d2055034051075118002c0f920030708000000b170380601003503d9800d0500045080b15949521345000d004036000380c0201030074240e2910700c0090843c4001404070301c1018900001c00c104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 403048947 1250 403047697 403047721
    0xc030c1805091605040f030807031205011a18030607050903010f0204081902011b060c0e0f0d1509080408030c07060507050c1e041407090512070e0403030204150f0f0503 74
    0x100c50380003101044503c6101c42558144036560185103110514407002050100000291004500c00c3c0c0da800402903a141080066550a01804a81c4072800114100110007600200071004060400582d01900d01001070b007006000c0329201c000c11000182d890461038280720b224800316010000310f01f41820260b03120b5541c03080800500d00c490803000e0301d205681c015940081e101c14000841d240e60940341c680300c0c000e80030700f0b4024404112110f407102d031079207031900c01712000d8040034104040061207904c034080000c0c0705141805101e0350b6a040d1201042003000203202070105440119500ca143e040c949241803035a81c44401000024007107040040c0b070100c1c401d002c10307900706e800010700201d08040c03481602d1103204803070b17015190a008602d2000042c0266203d0042902d40030740c0b80b6a0b5a090011003e031925519100b43c0140409000742d0000c070406542050092a0040c00d203501c940e041418a4243c0fa299008120700c4000414101c1c3e010052a09500c1d4500d0041e040d402d0481d45148 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 403050197 1250 403048947 403048951
    0xa0e010f09050f120d020c190609060c09050102030a030f1b0302070c06020705010804060b040212070c1110020a03081008151b130b0a0c1b05030f0a080405060a020a05010c030c180509 80
    0x101207400081440124004106008080e4008c010004034111340c1d2404070010070080390708a4540d42005801c848250254135504211041a00910b1504519a508800526800028004180d520703081c14100b17405416039210451119140160f441c041e9042c031141d04101680201c04560011406000c1c60740d1002d02580c00c42d42c484004643c00c0309010004010780580302c450100305410304104145640d10441010519005408a200d13010880d41446401c2844074280c1025a010040920010380300703418155114001c0e00490800c60b480e45c0441341800c1403400303010700641c00340052041803801c4c00044412042c0b203081681c94046480d5852001c3c100d140f00b4500c2820021402b221204d025096408a43e035102441c4c46d000001d0500c500c2c0c2a503101d00801d1b009108802d42c402c1c2c2c00d100010380c110042c1d08980341a051900d0241000400c5d40180b003400c045000b140902000030314240203055185180d9280807500c00740c410402004034951400050309042c8405003000b95480e1108510303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 403051447 1250 403050197 403050217
    0xe15010c05030f030423060c0a0e030c10030603150e0a0b04060b0a0906080d030902030304090b010212120114030c090a11160503030411031b06030a0e010f09050f12 72
    0x1103900c02290920701d0560003014098440030200000b0032040010100403020264100511210307941c9180c02c0007660780004907090700d20342c1000c00500940e07031700500e4100c0072100014106c844420004022903843d41240b00c0c7c0d003000c6900d9401c140200311740b6040040301d0f0300c1003040811040c0c151180c80390341e8a4000c600504400e50a40215060013145d4108005142c000b50803105119540e0b05900d0041c50741c3e01c208081802000c4c1c9109840d071107409203180d01d680080055080c9030804804000800030040b005055208600b2410746c120b04a601030400c071140764406480c01d61501d07821400c444200b042c1d040c0700703070040311f540341c1d55503551015180c02c09001d00c0d00048048018090350350f40d00c00c00d2054025002241d600304104070b00000203610503846144020741d002c40e0340702070551381c0d800c4048001d00185d001d24560040d08001c400b4644c00303411503601084001e0440b6000d4212007002c034100c10141c0e2100325003c10700c20204170700850302ca0310900030b103841510601d1084050249440d94 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 403052697 1250 403051447 403051457
    0x1302250305070f1e050a030e030a151a030d020a0203010c0f170c2203060c080c070305090103021b06180327130606020d0e0a0308070b06010c140c03070e1501 69
    0x40000c0c0300c130b00c414031000c140c1e00304c0805011200d9410290340c2c81180d00011000105420070410a6080210f035600303149a003c500c815051000c00d05041c09400d05c0c400d03294441c45030790452031007540c04001305519040d06030040e08106010b40103050944143c80303030394420301500c10b0984800e280e01041c54698800801440186515021101c4d01c4d24810085e0b0001c000e08450300007080b80f0054180c0508880c4903010410000c20440f2003650740da0000c450f4130203418801c0c480b03440468090300c0109110001450014903040b400e5500c10b01c0c495801d11203001950105080000081d681b02580d01c41101200044d8104071540b502c00480c55007840603405040060b640c0c240031626403090441c40e11802c40010700040d612590002d644c1e0300c0030100b0100007a40c02e41103802500786113140e103061fa60802485441c240c0c25844101641c40d0103401c842c10880c0304c070302c00e07800314458506040c014049500500703043d0000c44109890003105410100c2114181010b0010890004840040c845028204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 403053947 1250 403052697 403052723
    0x150d020103060b04081b1203070b0907090f020702011710060c1a0c03090607030c0903030516120815121b060f12160806100305090c130225030507 64
    0x40340a09640d030302c00f5184010100c3c1c007240c02607010400850b08084401c00c60141c3e413a810030050306044949150700300381c20421034100070070212034500c0d501003190b0040740c120039034800050003110180308072800e246a012030036404641c2c0c84505000103510b820715003805c50030410b005c2182101c840c07181a00344140440001c080100c0054600112442044400960710740814241e105c1d40c02100d50714044d001f51030004802d903000348141c02c501e5000b80c0d5548482c40c1142e0342a2901c0d40062140c4903e140312116602c0000e052b400045039000320790355003510a0510b40c140686080c0350a9540748550161030101000e518006540441603c219007202e49401000e0045002407003950a03107041031800107a440540e244444401c2d000300c0303450030001413007511004100da50311000d98225030b0008103aa40091500d01c26002580c2240740355060300d4000104000160750842c16001c0458043c1d0080b8040c01c0e01d8600c25820001090002e011070210b00003070f40c2c007c103d482801c80040050301240a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 403055197 1250 403053947 403053949
    0x60f02090a15020f100501030303060f150f050f0a0201090203100b032d03130f09050708070c050c041a090630010b09011d010f08430e0a05150d02 64
    0x55144d03605080025100c3e8419008000d4010304000d00080d8046410142e000a15005050b081021588864060f00340018003020840701e007046106140708100b4144a0000e000d0090001404141081d8000189001d03644c410b040c11f00f200d001c6413a482c5440c00c0302c41c2d217103601c020407c001198100c40307010000c850183c10a1120b4094010320b0042c3d407001040701004030130704a41201c241d800303644208940a580310f104005503081111010009607290303000c04c1c0c07514010107240d09410310901c02d43e00c2c2c2604513008078045500e61410050002c15400c2d8915640c10010b524542001d0b00361003c002200500c040741514440350550f148001e1b000c9060100d00220a5204450300040100b000c540d0356910a0031807440c469801844441c80340050001529500200d014011184803601900a42100b40b007803000300300d01d800000100c5941150a1411903440038070340e020a0400d031300a16000c900b405908440f0203002401c6500c0ea610b443c00f40300f42c90500c1000c40b03000c1c00080710341d418015490700c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 403056447 1250 403055197 403055203
    0x60f060e04200a02070e060a0302100c0512120c0403030207030b13050105010f06030b0307060e06070c0806070f11060c07140c041a0118120813170703060f02090a1502 73
    0x10100440700255000c02c84204400c004094034002c50b400c0300c3c4004e417104249000d6500548880740d0001069800304018100b070250701039280c8071410601500095900c03602d04044074809012880640095078100f03c804408009401c840102400c40c1002c0c00d40e90043c0d5a40000c1c040a4810419170700000d502681036641081450ba00c13800a12195035a0150700400c4070160090401003424264103400900300012100e08440ca141d84001981041100b401081d40c45094140ea01512212011a403001e080000500030344d4544c0d244080a0441800204403c4144951074500d41090307007405030366410b801c00e40d1403454121840b1190300c0c0060007041c0c41c0006c1c0c18412a045410055946440801300540e600c103640280c95800b0340d07043d4401c03000b841340708500420409000a000440101301610301a0280300d5030000c0c1100490b072507039420f5441d0b040f2540c4d0071416501814080c0308110160003204516162603a080d4200303130015001514018613030040c5403d1010490440021510030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 403057553 1106 403056447 403056461
    0xc0e0603190e0a020d05060702060c0f040e0c16030e01031d06010b0306060412240b030c0f13090305030f060d05060a0213030c060819060f060e04 64
    0x11903081c000601260604200d50311410440000584072080c00142890199004084a282040000340780c504010141e00d520081481880904c00c1400241d6054030a540e03074055980c0d8030302d207013035220740161002c1c54060b0041c0c40b8403409240d00b20010240360042a0f9050040308020098055116480703006844070b948540c1c0104080d4114001554001c82d0041c00c107450030f03580b06465410300d54010300c02d03210f5141c0c3d84c5d05a4281d40401000010841d02d500e010701c141240750740040e855074001002c1c10b005135a0001201c0c01656285000f81104545420420044d091414010b007a034100301d0302480ba480b035500100e80c3c285030030035901d09640e03070040040096540c0d4258480c00384d0440c04080d289406085800b20000d01c26100d00302c00b0f008540c2d522035a034607005584000d6042684811113000d0310b098414413141000c0b414600c15649a802c000c101090407002150041ca00 = true := by decide +kernel

theorem cover : BRFrame.Cov 402877697 403057553 := by
  have h0 := BRFrame.cov_init 402877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 402877697 ≤ n) (h2 : n < 403057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
