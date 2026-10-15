-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4016
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:20:00.082975+00:00
-- url     : https://prove2.me/submissions/8ae65602-b2dc-4f7a-b637-deaad929ca77

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 722122302 ≤ n < 722302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 722123552 1250 722122302 722122307
    0x60d14010e0c0a05031b0f100c1205030c19051903020d061205030d11040e01061116060f0e04110301180e01270c170f010f0509150916030b060f010c0b07 67
    0xd040403103000c1c00202c1d145070000301041c0400d016805d00000a204906c0b4030040140e18002038400041c03070300e012f43c11402e045c50104058480d00c159005144c004400d6000d501d8010002c0e1552092400c1a080400906840107400303540200d808803400307480c0c26804900d200340c0300100c85056400c4002582080c0d4141c5100b03000f0034040c240c03c1e0803503505100004800202c04000382c06880345030b55020b25003140c2c00c9454603104484007410700c400d100130070602009500c2081c044a0401c1445c2001c4c100401e280410010240e800d0b00311b401800010000c10014102c80c2100180049508104103544040009500300c03a84a0350b070840a180750a000c4c08038285028943d40b1103401010300004a40c0e82f10004407400c2880d09070101150094461240b6420080c400c007104286103e005010514107041516219482e000c2d005205d900c0381030108052000c10400400d008400380d40101c5a01d4032410808146d28040707450b05e1087c00740685024507075100700b194030100d6030300510040240c2c8a00d03006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 722124802 1250 722123552 722123593
    0x180905011424090d11030105012c150112150b07150902060a0305040204020c1f0f0b0901150908010f0f0c0c0c050f22060503160b0f03060d14010e0c0a0503 68
    0x240d4020141c0d45c02140301e55020701c00c29008244a0106050851034041b0841108103211002c401e10b440c181308016001081000c0c0c3d501e45a824a00003070201d240700300b008000d104041d60007011881d9008041001e04041c2c0c000d2001c2ca000c0c4031116012020704003128155010b03508025000070b810b00c041400103009401054005100420241c240030401e0405485e007003404811205800c2285410103038007089126401c07454000800174010600c868002c0749101d0410310800060381c80d061403c2150511501640c005000c4400c002d1003800740c0d9082d640c001e000c0d03016130000405e142a0303805191500440c1041c200c140d00002d511500340c5810304100138017034440507072501300d04c200c04c003191800e10702140c1800c104c08048000403198205400d051401080c0483c00142c908852000d100019440080c1c0380784903420907a040c0e40350f880d10f002ca00b8200f0307006001000d45e0704104041d8000071040d008160880020340c12119441c1c260b0b4204600c034102e511070560140c015800810410702400350 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 722126052 1250 722124802 722124829
    0x70e070e010f171315140c07020a0e040503030105030105070e030604120302130b070c0f05010804080d060f0306021903061a070507031b0602010c080c030718090501142409 75
    0x3480ca0300b80d060362501ca107203d0f808403440c4441c02211130403e41001401c0106480c0d03d21401d4042104040c0d4440480820002501079004200d0218101b000c55880c100a080036082c681e00c0180746007014a040341c0d581d0400e00409119500f400006030180c0c0c481d40700d24a000c0c4004004107001e0b2140d48806094200302800c11080540030000f448504800c1d030080c000074452603a00c0c0760307505c0b0b15040411601d81c0d04e410a290385019800100050707a406954a6005074002c2d44881d030b500200c2105500400603540402d20000192000005202e1164081c041005600e0500e08040812000440880303031940903400c1d240c2c68183c448407018203041d000d0b04105100703074101e4100c15160349403038401459001040807003103003002041c030155a0a0080b01d00a07142c1c0d00300441181000105604e242c000100300004002c403410070392840b656000102001041015020403484d611114040d445425509103503000b80d07a0143d412880703510f8401068010309800440c281050312904c20041109410340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 722127302 1250 722126052 722126057
    0x22104050a0503040b04060e090c1b0a0b070807110606060f0a020309151b071a030915150406170d30050a050a0b0a0b0c01020c010914070e070e010f 65
    0x15900c0380002c100700000d001601a07040c0c1241c4452900b5401840003030304030103080c066509581440710120504041c2c0b05080488005404600c00d405041407800e0000d94024115907404824840304641000f10742d8010600e650f034207a0712088030945541e0307518080e10301c1074002c0c2007040b0459440e01c1e040702520300ea0f00c9034416240313400e100311b00040a0400061007000c1d0510001909900042010303c0e40303c60006001c050207000d40380401c1c054483c2c80d070844171110070302c0c0000081d0b00c0c11410b000c599142d0800c14604600703400c01500c119039240d281c45c04240030382e02d040c01c00b080140c0c940b81440c00004070310004101d12600d0100c03c035840c0c0602001d99200b46100d41c60308000d0042c8000181f021150050000303081d11f414410b40087d41e1001d4060f20b00c40745415043d00180d00c3e00300700c1409440311507034555230350654484000d00a00c10700c0c0c0103071003a510f81a01c0350100400701001108032aa21000c0b51002e03612240d880400c502c3c266a00c40100b41d0001441c1b0b40d650040c802514170b012a070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 722128552 1250 722127302 722127313
    0x906010908070e0610080c0301051c06092301140a0c020109020d0f050601060302310b070b040209091504060b0a030c06050a030e0c030a1e02062b02210405 68
    0x8140e0a03150900740d03048a4000000f1030100199410300c0300d604c144101103440e00307201c607007405a035000d002d10040c09001c0c000c0346072132202c58000c064010310300c40503503002d1030800098210b4248048840030403c82d400e0034035100203400c080040140141809881d120340d1702c81c141e4460207000b070010701a81840308155500c42d6508005070341c902d00618000f50181d010280080114035026003071000503000f01052500c140301c0d50401c55030042035076003035908115006071504000098240030726402e510645007803074009060303020011f1010423940580d03c2130700d18160907107550b0740309612002020100c0050306200740004012402e0f07030b0406803884802a03d400490741d160b031101c07182c1c007040d60480b0740401c00004100030300d61381c107108007840c141d0403c3c0a8011501c0d01c10000342c40d018004405015401e444100040c0140c0c1d806103404059030003802956200e4203d1a6080c1188405220003451070843d1740b542c100054074000c0341c848a8148512032108044080d5039080d03c200608241c0da41d2091 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 722129802 1250 722128552 722128559
    0x15080d12020c0f011d010501051c080c10050106020304050306100e0c0715090b0108061015030f110703030c082a0f1902010b0310111605190c0501030f0b090609060109 73
    0x2e10540f8240c1007031207030f8a01991740d00c0481c03600f5a50107034001401040d1f040300010694000a01c2d4881c1d40c0e44c0100c00d10f070b031800d15403485494007424002c001c107418a4400001001e43c0c0000050003244c40540a9407243da98240d90032102d21014890214035580c4040040e201d40b024000500c0c80724400c446180070401107040c1141140c4080c0d001b01c03640c0148500610240c41d007000846e921000310210032240c1800c240d00b050003a0104c91054045c1500c0e0007403a500c01d42039411503060b900001100a80314407032820014003400070f83d010308010494810210745c007100c0001d40030002c02040c658121002c0d1000d0342c8948036600110740751500c0d4a0502c1003506242d0050348401d10520a42d0000c10f107030001400305410004000920f01503030780f501186201c0911041c2c02c1e288254420b028003016000c0d10305005003001c000440708810710825091f0741c410081c001800000b5200280c0c0e0070031102c0c180718000802c8407900c00c0d24648c0a40200005070803440d101107270607030000c810714080402655 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 722131052 1250 722129802 722129833
    0x30212030705092d130617161502030a0507080f120103140a0f121e030c0206150609040b21010603061109010c080901051c15080d12020c 60
    0x7034600100154001480407194a05140089890350100280102c140000c40b006442549011000e5010f0340ba00300a10200c0c03400da9000c07000500000c1411610300d0141f200c80780d200e412216145030792841a910100303042141c1800780b0700040c00f40e001503140000d030380400d0303030160891101102c9001c002c000300d0f030b0a1a01a005015680c0840a80034500e5044d440d004405201101740b524a40c0d02442600020039142295225003a41210360040c0c10840c80408032900c203031080c0c45000c4103040881401000760b2590080c02c00005650903285151074002c4107103031810406141c2c6031b0080052180e40c41602e490340c0507082d10700d8010040031010fa80d802a100710200844806c4159075903c510030001c0c0a0103024890100900302c080c1482c5c01d080c0700c0003a001c4081d503000608030030b0340455801d05a9015900b2900240c6e60084021503141d002c541d560040c0c41d04a002007030784001e25500203002200054902011021911141c40908440010784002e401085a00000d84100c00a0a58061 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 722132302 1250 722131052 722131057
    0x60302030a020f04330905060c0f060711010b22020318010617120c060f0c070501021b10050108031b0309090a0501030209010806040201200109140601090c030204080c010c030212 78
    0x100342c5200001e0300299102c40d41c2403031a9a1181d04604c2c040e00040000b98806c817460160748089032429181c40c0800e94503890a502040d9692040c41440c1c18441e401d5009014646d00b6502e04000380140040c55007413041d00c2851a495450061003480213254840440d006507900c203052044046043c41041d1a55094951396400341d2640007402c0d2245480400c2801440441e09000d0911458000030100c2603580300c0d0020000c4038600d841070b0103c1c8442c005c80044071162600103000350f4031543c10041040850b503020000702c41c644600e2983c034100340024014541201c0da505c01541c00c00030280c40e0004104e0600c072140c1103d0208011011542d652003001500940202c18001003c2d07044d44140035002c1c0041e004140154000340030040140c1e1b2210789080b1008150380c2d074042d180c492406840c00340c8003500c1c0c020404600c51015880314040018418100c451461081c090b0f501f0840e4247c08920480c007414450b60005204c0180300d500950384201d0383c6219204880202402c1c0c0d0f100c1c109038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 722133552 1250 722132302 722132309
    0x101b0804080f0304031509030507060f05060109051002060a0506030f010501030b0f090708250b070506061f0207051011100209012c041d1f140601020601060302030a020f04 75
    0x21100803405001401c0200300811041000c44000c40c030306825520380c0034182a0304954a000a5100c1c00c0319000c1521400503561707130300d82c840c10501c809040c18503004007400c42121514002080090005000e1400b0480180030340d5080e0080d01c4d440d113540d404440a0403000781029003600c507581e01da924150092085500850051140400608140c032100b17a5203400a48181102e50100b003007803040c1140031526013215000d0040c160130702d54001c1030002c02403581e9404920207010200700001400408580e40d0322404048030040d15003040400100b90740601000c41783c0040e0b00081d018070030303800d0080010b5040390050504054000010802615080e04d00501031901500850b4501041d60880c8528801022102200300942400d40e4a0400b03e0180715031240b15907211818006040308030450b41c1410918017090380c00300d502140b0300c1d070b0602002c1e2008024007480c003441c040020038103d02c2e0300e000e0b49050340a0700c556480c00320210065000981342291160f803c0120700100740c01c4c0380041c4001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 722134802 1250 722133552 722133563
    0x806120106051003060f05011106153c06160206031b0705071d1b07030c0b07020d080906070c030f05040909030e1009050102031b1c0306081902090402101b 68
    0x50030014410f002881c00c0d44038a049c403400003c500b12410303010500c19801b00f08251041000042c0b44000340c0038040c80b901d03040d55202d1110b142c81d58a040381c0c002803007142c1d1182d040d918144c0188103101c2244203510191010207200c4100c0c20051804c04001d54000d80740c4041d00c484003041d43c0ca002002e600040f42125030764803890b0100702c1c0c01e8401b00050351400c40c8a601211030f00d481010380204150480c2452034985c030008885081501612099041c540c02071040c40013803528600103503a0fa00f142084002040072900080c40c80340f40045c40700d12484a6642d9080c40c40d01a0b607003510f44070800d041907030511030140310208000b46c00348144220356010f07555240e60350f100c40c010712a0a03100310f0310360010044030107000e1140d81d07000421945e080d5103003060a1070b48070310300720034034200100000c01d010380240c1054041a500d90580082090b1001d10040d2108908242e000012001c60302400a400000c184005005880c11200b44241d66030181429040c15004503c1228210b41c6c1000c211070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 722136052 1250 722134802 722134811
    0x1c0504020907140403030309140d02010b011805060f1c0504080a030b040b0102060411061308070303110604241b170a0b1c170408010b011d010806120106051003 70
    0x6610340306a480380c000b503031414400d15000340c8065080c210b1041d400003400780b6488900880400400d0b2280c0e04201842c1c000340c0700101c4803054024068078440d00d1403800039003112001d92501d1303025180441110801030825260680c2000e8080c06034210700421b08400d11000c0c130b2109141c200307016003403040b80301e20100c661300c1f854840d01404688000c4200b80c0214a006060740050360006100307600f09400035018601803050748002407a45c442c080c13066107000b284c850300203055100002e1400a881c4607403210003058448986d415940c1700d0848020302007032005005605455030802e6401d81c0d000c015a004110504003900310280b817100c5030250070008010400001d2601c44038117441390040c01040042c041445907000244070100e00f4401904140003008411003000444c180c1c3c444488024505280c40310360340d40d001402800102005400b182070a06a910362047c048170140c0540c01c1610b400c0282c1d02d81200380240d401c110151031403599030b110030100d02941c1d09078804c8181e00407984c0200c1e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 722137302 1250 722136052 722136061
    0x50a1d0601051918050a1b1d030303070906080411040603050309010801080105010834060c060c0203091c0f0611040807080d0806100903080310080c0f0f0d05031c05 72
    0xc0200485021618220f00400062041c1450740c13110003044014110041110b448420300315004003010110040b107402c0d071804100225401c01c181c1c1045805442c19003c0f910743c22307414580c4a100403141c00f03000441040381403100364040c03908540c200340107801102d0440c0845020404803a02508207440c0340d440401d41041c00d6920400c014003412410300203000551400c0c441d180e869221a1406c0d440d0005141c2e8403080c44240c0a6003c8056000303a010345c94a680c4030805080000d90410981d20f26007400755200c152400002160380343d90b1702030b080e51544403c450014003620718841044400d003002c1f07504440481d40070701400e00a41c1508a00a40c1d4601c1e000719a440e244d40c59010802c980c0002007000280d40d0040e4005600440170358114a810311000d130211a2520250001813001e80e022082c003104010032000401900d811030304036156000c03900c08022a220054a03450390040c00940c800c107271400e004038041c01242c4141d04070707403c00500300d841060710820402d40e018200d03520740401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 722138552 1250 722137302 722137309
    0xd0c03080903043f080d02090402070b0a2003070219022404090e0a120e06040f064b020c091303030507180b0a1103070f0203060c0c030d050a1d060105 66
    0x11a1000c00d03d210b0304000c0c20b440c0c1e03145d040d14002c18030f007100081d602140011050715180c04440d9003980c00f0140c01024a443d18210004003501c100710400400180c000c80c80c86001c180c1164040c4505400801c0c0a5503494400840300800c044200d030490804115082210380f12810450300511046580c1e0300c0e9402c11513040b08840c84010744000580c0981803100c003080207a8a020b002d10501d01d48030552581c10400304407988641da10140fa22480761500003041540a01d4030801d8140c08511800c4142981c41e0b0141c0780d00505c0e15142412520201441161103d080c83d10044021401030350307090005800010b005940441e03042500b4121426003104150f414071500e5480f6000341040c00d0359607050004a58410124055000e020780d0010b0401c507038a000e002001d4203c00b08104403540c40c821342c50300003885c03840400102c2c024481d010210b0003100c1d0040035201400358510081d41402c3c4081c0303844024103405401e0303c1c034403655441807803a13880014440410802e10900104200d52500091 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 722139802 1250 722138552 722138639
    0x3061806030b01050f06040b0d1a040204050f0906131e0e0f03160f0804032a0b0708030a09140601140d1127150f030d0c0308090304 58
    0x5021255140590900000c1d4252907200e042d1041900c1c500d10440030440490614421a003104030b0950000c200121030300850380100545080c2d10a442d8408a50141031000768091409941d60002d05031250782d8160908001065100200600d400c0c0e40080c0402c00c0400c4855001d04802809000003002e401c0e117080b40104503130000210018800c800242081507160300601c043c0d0300440c0d8080440000348803040d103600c449941c02011199945680e03140c4550f01d40035040c45104585204202103580000304d20310318007214000307804240740180c2d40d524250141c1c002403010700710565a4040001054000c45805106045803001f00031179410700000240c0b90000d000200c0c8079090b5400c03200001001019a04038001040d00d4601d4990b80c40b00784415110071a1183c1c121340300b00344d420040c11550848a1100010303080e0340307488000c0186014162100c400306540000328030950003080000e44620001d0b94046090301c203a07410151603000e10014070002d0a1050401491005000c2203024403d10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 722141052 1250 722139802 722139839
    0x3050a09120509011d01140f0c060f09010b030a05060604020732070e04020607030f1b03020106060327080309030d0e0304030303110909010b090406050a030b0928080d1b0306 76
    0x501001701d034035800241030400da80412138040c030010a0200700f138160b65066400d2004500b05076207452810ba0800008071204568040131903003003540c040840d080c082400c00c02c07250004050701c4c0e540c1d80d1009000103136008000403140c0980187c440c203940141c401c24542c0100f62500b104403034021740c601180c9051015000700030300380c0d030302014400140c1c0c5940480b6070300d6505083c488550032003610241c0340040407988502140c001790130900b08040e0b0641c0080150340d4152402c0060001c402102140315807042030f1001d45e8814401c00d40b002c1030805024542c400030000c116454201c03c04200740581d102d8000707550055001041c00d04c109900350007500c009041c84484541894815000282c84900611031820f6800c00041c140826441c1c5801c5180642030281045d070281d0f50324500300d49031003012501c0241c03030f00600c3c1103401c14401203001a0710040c8030b140b2000c01c4584035100c00c5a80d81c0001481050780d03641d141004c616141212240c034494103640c0f4002841450640240301d800c02c03101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 722142302 1250 722141052 722141087
    0x131d0a0b032a0103090212060a0507050a02100908040503100f0b100c2015120a0908071202010204031e0203060109020f0706051b040f17030703090603050a0912050901 73
    0x101c5058205a8000d00301800c12541d0550b4403005800c40141c0061100b5032000c0d4010703c081d00c541d6008a000280700e402003285481c208000d655000e0100c405002d40310001006810500c4219465804c50300404d140600a6908500e4140d0380c0e0f00191520310040b005c04580c1d502c5107041c0340104030b1449000081c0b4002e403044800600c07480001050b00603409002010101071460384200500840302c1c2440b1068060550b5007207200200c0b118800f604050b0306094504040d07000074000a80c140030f06010503074081001d505003000c0e90768030f8160208090004046641c00d000c0027002c68001c3c006004000d400b4060f044100000380181401d111058018542c10b5004115407452441008121101181c10200008081d1a40005101a0407514808079420301021401041d10000e0100603400c0714602e40f154222801b408202d11384a020701c000250220301c0c480802c0058a000f81c1040350302c458a00000540034005644005800514150b040c00040f0040b5208003c0d580007010f0100c91580d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 722143552 1250 722142302 722142313
    0x3030612033c051309062103021507110c011d130b09090309010206010806010510050a032306240f0f0d0c08100e0907050105131d0a0b03 60
    0xe4a024000e0301c040c0c010b03000381010801c040c03080750281a502641400044040d01d440c280008001401900021148501e501504500088810311481607404030382050000701680b1844031500c040741102104241c06602840a075814241c405006062040001c2d07100c410713640c0e0030b05450070300c1c0c00c103e05091410f01c9400d140202803424100300c09001d5078011160561548003030b803a908041d08144a91580100d6580c5c00d0008031400170000d0108600282c0c01c4035042e07039850800d19606d0704284074482c0c110004401c0460b10034801c0c402065044a43e0401141047c441517484d00080d01008610082ca0303d000c051020340e01d40480310001c02c1300e40311098409101c203007600380d985202d1083ca44100e03e1f0006840000c6501103026034411081c0054100244555140c0181006e801200c1c0c3c241841c8c00040085005540e1540d118000c259050007413a5030340c1898015a04c940c018080350031001300352800000d600741207401c0c42203050000d00096500f424240d807484282c0d807039401c090f07200340c001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 722144802 1250 722143552 722143589
    0xb060d0c0f09051f090e0f0709051b19030506150d050a0c0c02030705060702030a020d060e01050a0207150b0307050301290402040303050d0b13060e040b0708240427030306 75
    0x2001d0803000c1e184070000002d101007a21520500c1c240040c01d8518180c004c8c0180002d0942c582d90000740308100a4002610a580e02c000a80c42e0744509010302c1440619003c23064883d07442030703208690000d0081c0c184c030405a50010300c08010b400440d2141c0d6402d40750420801e4181c224025950700b4409400d140450841a500081d20303603196029860207a00040340d1038040d03580801a280125030090101602c0e003107142031450192205a03c0300742c440d801d0101040c90308005100322140070390040e00c040d03411504010180007a01400c0180c1e5418460500b010800b541c003846407140f610000c070a10440021645a100d03000d1248000702c41c4150320500007080840d4110044544000e43c903640040c4224a000002c0c4c45440501e81e241c425600d004401b00b80a0050725142e4002c1d8000c00905500780e0f0b0301d2504407050402281c84000d01c14016030030416481003000d419046410083c00440d0407054880c802c2c2c0e502512082c1c031040d4480660501c02070640520074407010740700e141d48101e0720a11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 722146052 1250 722144802 722144851
    0x3020d020c180a1506020a14070b030c07020d05100606090b030103020a21290f15210f06430203130303051309060509040b060d0c0f0905 60
    0x10b0244500307014660440022407400320780c0c0c0800c0c040c01c101c0700304450894480384001d58440d1a0ba1003194217240014081955800c0001c000342240d841c14045417559130f84085803003180d004020101d03000308400102100095050003d0b49148500a50001c0e44a142c00c0c0c0007040c400c06548001314000c0204018030150300d60809c2041680c001030000b490500c183c0034840003890810344060107140045140340d000f19400c40c2d64402e45204840a020070340c0300d20078001d03c110802d42e12045a03459030b40000003a800c2809189021441ca60012002001c50301000c50a000c210b0300c0000e42600703c0820003400180324075908210801f2030000503103084000c1c0301d610039222454081e81030b10140c000c206c1e022510030400c03079603400c3e504c04043c00d10307582c8d80c0f07400b4140b50004a020140c0355280301002c64201100e11a090885400410801603034866846400e840e40003e000a81c20411086045020540840c0c0e14401406145200c0c20183d01e030468200071241c01400415900160f02107070700346881c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 722147302 1250 722146052 722146069
    0xb030a0308131a0117010e1b060d02031f06020a03020d2a030306081213050907180b040503162d08010c0e0f0102031c02070c090603060903020d020c 65
    0x661604208000d0b48071801c1c004000807010000034501c00c0307080882001d00d030040515a04a44441d41040c403408000c0c4086420381d1907180d4410001d9010007021805c1c2c0340040d145881e1860043d020034a0492460b5400e8242d900071a00c41180d88406082c9101e00e0f051080018024013152010303180750b8140390350007511451003040240810a003510b100c81b105095421020380103040042410900b4150f05d40a4040d0000b40b05480107400b9244c0c0c100d01a0190703000312440d0b4009080781c41121401d2404100c7c14103400343c400020041241c001149552074083d04030b0191156901c0c5c51340f00c0385030004040c6081e01000c0e9804044e056107404010081200f181d00303000e00000703070b5107411070340340407251741418007090348488410743c203106c07014800c140c0216032020040c40542d80000c0c1001c00d0381c016660307403080c4058404100100c2420080c024402d6010746103c40c410b001c1950050342d642210810346015070020b4910a607220541020075804118a107031804490000c0c1808019020028003104c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 722148552 1250 722147302 722147323
    0x503010e0402041116050105010e1003061e14010906060c080a050306181e090601030c0506030711010c170906040221011506020f060705040807050d0206130b030a0b040b03 75
    0x20803a800c0803500315541c0e6007020000080940c030f8143c840c101440b14184421103580180c81a519000c004128100b11181080c41180750750030900c01107185917618070040885043c55070103a1207402d2214000085405150718081300b403450748009504000c504c20484095900c40340901050b50324002c002081502500d4030b10125080c00d84d100d50ba0000400c4008000080302090440c1c1002003143c03a095012415805100001200707203143d8401c000503a480c5028007025181100000c0b041169152007001140d221906103070405807500c003001124203441c44c006052004c0b85001e100312a4601543c41c0543e0301064180042c0b0305800c040c0c000c07681d0450682250820750f00d80200d1201030710030035080f50380351a003029280490035a4400e4025294000010000424061500031a000501c69800d0703805a0307510388080d2207624a800b04004c51844d6001040fa00140705001407000d0142104e0a0f40c021f20070401425521b191500b0303440102c80d013041940b8030a03840c110001120303840001d40c09682 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 722149802 1250 722148552 722148569
    0x19090e0105130c0e180108070902070203030d110714070512030901120506010507050f030306180403140703090902030f0103120903050303040b1e130201031401080303040f080f0c0705030c01030b01050301 89
    0xd41d2100b8000c42d0784401d00391010340c00c80391859000606100409145d8101d89546041e04c00781074035045403206070302c11100c02951660050040c10f0898285c1e03030000c548406040021841c00b5070315070311420010b011184403a504e80101070200110708050481d04541c1c070042d409503141c0b202070710002c0c058100e207141505a0b03580ea280011620b03400f50003122449600102100c441d20112030040d540e0342d200300d44540c0240002041210117090141c0420b02641c1c1c5a26844480c240051840c00c160b004001d0603401c12205040000c2d032141248015801040c0b000c200c4200b56046080c03003003540e11030a840300104030410b00200003003540802a2030b00075620034500501c0741c0700e4134018010b80b07048a00c220f901e250140140b00580e05805144171800340700f030700e06010743c1c8040c0384901c1002c01c003441200c0168104000240010340c00d0519002402d100d140300330f00344052141901560b40008076464042d40c80960b0902c180d140c100844546460b09180500c019401480002c01502040c4202c500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 722151052 1250 722149802 722149811
    0x809030a0807111006150c0503070b0c0d050114011e0905120a0b01230d03050a050a03090b011d101a210f010920270619090e010513 58
    0x1a00c5160b140c54101c10140441c0d5002c40c400c40c83c2c2c401401741d4860300404e50313502c110758071140703008030841003403642c1180243d420214030b41c07581c0310f91000080c240d004d0b08104110f24210800ca52050301d002e020708250305003c07012184000b40000420070200f8a64100841c0512078043d4800b40c0801900d005441d119800c4882156440c6041e04017280107001a0160f000802c8400d4424994400030303000d241c0e0082c2030804901400b4405032254000b0b0005070080080d6040d9900540040101da000c6140c00240c880c0c2ea078071200301810302a0003059806201d050b0158810300075030800e03500880d803010369180040c54140408001c0c00158100e031410480441e6242c0079081d003038208540c65040b8441c80b05140760080c001381c8115801d0003080460f600d03009902d4075003d82035540f54582d22100301c19919058a422056816150001c1d0800ca51604015504002d0f01e0b80760140180c1e290061b41c109040e4192600500407071401d030015030000c1c2d1036900406c03069480300350450004190303180028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 722152302 1250 722151052 722151061
    0x4050d030c0c0305010209090c0406140f090d060b03010e010203061e01020708060a020738090115030f06230f0a020c0109030e0909070501050904020a0c02030a03090e070809030a08 79
    0xc0d4000c1d540304015100c150301032400010f10006400a0842007000c03580c00103039907617060200d50a40114000c200006503c80280317900285030500401e2514050b441d03042c01c140b07140000031044109600c04036005a155643c00c00c05080901450318489000c100940c02d40c034012020271401c400003241c1081017156060362640c2a4002e202c0b0300082c0100d0700a0b42d00502e840742e0a40c02070345c4482401c80300641446420880c055070441c05c212b0b0b14018441c02a0180c20021044905560103405200d00d135503251030800c10710390142c401c0320040d03100700f07410010352450b410131008880e400d101d5482100500c0300146202c1d0300814003d41d00c0741d0402d614440e103850303036290340e4003e00518100b10120340c40c041ea03100a06410440e009400c5c40704450340d001c2941c0b0030342440e071035034001c2c41441c4c003142003406030700101d1925030007505a540c140c0c68600c423110310a8000903c2c2c5510329106402180c9011700c10b0146001c43c002440d44291142030145543c100000100d40d280302e00000d60041046140224 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 722153552 1250 722152302 722152307
    0x10180605041421060f1e071d01050d151d010609090c090504050c03060307080706020a0f0f0203010603150e031e220807080114060a060810180203092104050d03 70
    0x482c4528610003150410700e000c655400d096402a00c2c6c3e4820028544180100041c0d0f24210300d110358500c1ea90510860780c0507c0e1011100301100b402818410309001a0324031405a114043e2180640319514500c84c0c42c20910425445040041499084101d001071018507041008a01281c2c85804000717003180c40200200d41c640784030740145500c10700704024040e800710b82e031000d580220011005c2d03840c00c0d036403080c0c1d041c0e40e502c461080030701503003060140c6008a19098840c22004e8003980912140c022103900003803c4072060f820888030040e0501450b0000000b41c8600000402c60000940c50680f4100d1520065041e600c000500d81c1c100140c040f000301c40401142c07183d80001e0403c0c00400391100c0c0707145d0302e44030035008654543d0328101c00f0748409071086103107501841025003403208480c1811800c9680c00030040400d004500d050b940000c10300c0f00c1c4101c2c2c2107024190540103859041004c00242040b055211204280348458003000c07444c0700c8002105d0450b6400c841d104201200c42c0f405 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 722154802 1250 722153552 722153599
    0x10f06081306060504060303030f0b0904050d0e1809010203160c0305120604020d0903120c02150703050c0c0303090304031a070801090c110a080c1c08040818101806050414 75
    0x44d82c006045c24400000c06401d030f00040801107010f0814400c5c040610140105264101c0d03003d0126800f0040e60381c07030070380108416442c4d007001070024080c1d525075085481a40000b030b52404110784d400400c1080803010303e401644640c240b40340002c41c1c0d08881d24001d00902868900340081403111011403040e40e60350381102e0321052210418090000750341005000a406a10a000c441e410102039843c09840407030302d00220318803c4000891521803040171001010002c1c00304510030820030068510a80400155100764200300007965120304500d400c6903004001d18a18a504c42c465080c003910680142e04181074856400d00041d4032100b200c0221782d4200b203292401e40341c0c061301c0b1401003440b814100500014403620200d4450410150b440d10301c02500d01108000a0351900c0414001610000105603038003955a011200340842000100b04100241030301d03010440350314440b002ea0341c0044800d00140b99a0900600f42440c20040418181034144414420392510600a60044030f4030f58 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 722156052 1250 722154802 722154809
    0x70e0d0506040303050711010209090f07050702030601031101090f0e04140115030c050306010e0c03131b09230c0403030c080f0c0a142802150a020102040e010f0608130606 75
    0x8407a000e003880e0a001d4010413054607290f001a203001c10140300a07505000304d42580780081c12004255441d804507107107503400a06041d003000b1040140201594040042070301840c02007081c1c0c81240300c00c200250070030345140c0c81001e400030b50f50401c00444490480b40e41d40190411030510500050291603401010f20b82500c400c00800b00c5408030034030212151503415a17106034100d4000740d8031030045070f40102007140d485c80500c90420001d90f603401e56860451101d880740e214000241031106182c1810b40701c0ea0070840c030301540d0f40c080e20038035100107081110404007580144074600300340540212602c10b90101034280041d8504c0c24040001c114201e620100185141584688519a4664660103220b2003076901110a12001d81c0c1d207100807450384403222007100450110f88485640220b00c0c44032000c10b07607202c2c0ca10302e2110024817598ac000c00341c0d003180d0783c0010707911402e28107000030824042c2c204d03095100240c0303014000c03150440255030300180f94515820f0f1070042490500040c00c0c00340c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 722157302 1250 722156052 722156063
    0x20a0e090a0c06020f011a03060402011107031203050406050a0b06030a15090c09030201090905010509011203050d2427021c090602030402100806130b0d0602041205070617070e0d 78
    0xa00099a40d1380800d00342128069074009001041500080e210004404003120354160001030103d4010b41c024039403e00c04401a000791440385030380c0e03150b05040c002040d2070308000c66141c00400c820003965115495100611450420107005400042100707800001c008050142e51401ea1007955410750041100070300320014203001c0d1054841d00181004542e20003217000c14442500072488040c140500d41c1a641f000d4080d07089a80392818210302c0410883c03081d0240316003002022120003090060711104a501a03811890780036102e00241e030524940d000041640c1e040c61414043c104410744100352741e60070000942c81d5aa0343c46024400209840d409900078074041c05d040412503179402443c0f0860084990310152040c482c0c0a0394030301e100711707107641c2e0080c8009130600842c8019441840070440252240d0700c99141075a959080764069003145070980030714140502002001c2044001a14840c40c2844403508a040ca941189201524450501c510066800e1486d06c45a5041c200584c100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 722158552 1250 722157302 722157323
    0xa050c21160f0b0a050702010e0f0303160212010c0c0b10080706121107050a0f17040308070210051c2007120206070905030a08070c09020f25020a0e090a 67
    0x70001420800102e1107690a80c508500707000840030b040e50700743d440301c54503138031501d14000b41640111080c4486141c2c0c640e02c07260740811880c46840c1003029201404068043c10280d428030b004100c0d240314420084241a0b05122003010041d9000d95841505540700440c0354042d1107541d507484000116412413140c620034413100280321a88170862184040c40303140d04019003001c850b40d4a09500c2200809800e542c000003840e0000740840f11400150303400f1709490415603581c3e01c007000070765100f03500c2a517142c240851202e0075449c10440b00b00505455042091810500f4070000a05e0140f0202500315103645000c11200d4080b0500b8035506d0002c44500c0325034803a085d01c1d00c05001c0d0030008500e401440f804c40003c0b0803901a500000907034034000c00400e900c0f4001c2d910451164048001140d0110100c000092076100c3c0f40040d15115424031803941d00c40031860800d00004548401a07055800202440c0c80513854040600d016502200c0081030a5a40d020182e4949861410020200503c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 722159802 1250 722158552 722158573
    0x603020c010e012316050405010818060a0905010e06010509040f050a080d0c08070206100b0a11031305011218060209010c020a090b0f2704020112050106020601090e0a050c21 76
    0x825000d26043c1e05100707101d80152121603140f400407880345044c5d80850307004c00042c02550702490840b40d1101a0581c54141408480d03a03880c100841601d40345840740d00c030385038001044821700826401040e804024071036585400c000078240c1502520281030040e0b98a441c1081c0a414000c101c0e8035504a1455a990004090360b0001000e401c11000000381060000c110418800301e8a00d0007515010900221103051641d0542c0c00e5101ca00e0100521413130f40018145070100b400608085e0545100700d15800b444c1000146c90000300ca0109034256180c0008020080e425141410280d600b20b04016190346040d401620300d40c5090b40e0196005440d04800190104d640e00130749011201900c040c10f281c6a10000e00981c00c0c01d4140320b82c3e0b03201303d1000c641150070040c0e40e10b81c3c0c410b0051400d203d9000d05112808115a0281c00141c01230300840018403240761750740141c600100d507a400070051600c1640b44d40c0e481e084414038051050150300d0109601102402d41615200c402c48183ca03a200b29 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 722161052 1250 722159802 722159831
    0x70c091404020a0e04031d2110050c25240c0906050a270f0308030a060b070803060d0602130f03020306060406030320150a0207060b0411040603020c010e01 68
    0x1045600b01d104410059020a5160319040c415001d1742d459110444000c04203541041b41c04a40da440300d400849140f4921402440083c0e858150b5804034040c1c01c10301d0b0a090510b054440082400484080c10400300e11040107481c0b000c80001d0740005941c10710240c07460006640c108000d031158600304600752030107410311298014900d81c03c407602c0d603510403903903460142c5040c042c54000d400480c0380031a4a515880410030000e00010354111724801880d20380314610b41c4000c56410a8070000c501108126a440c131a10a60700580708004402b17040c0300d1165250011440010402805211401c0e420000c0024540642d0a0600c0ba03800c01c00aa61711124880ca64510754401030f40311344070b4900801c1180c101849043d041d60b8041e40e0721038100701001d0040b0a120f0030107103402031521900d075007869030605c60260302d40150b2401c100941d99854500b462415283d600c071511f031013689800494410806030200b11001c481280c1809611080240040781c0108180c4030701c000c2550038843e403da030450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 722162302 1250 722161052 722161091
    0x1006111c0e03251413050c03040b15061b01110a0201020c010f0e030304080a1b03090602100509071404110301080303061306030c051c051507200a0206070c09 69
    0x1029000c64440f50700400282070b030526000c4842c1103000d04260248054400d40d101c5840d808000742c41000d184040c50051811104120391070260008003105000401840d614031f25003025982c8408560414607000280b03191144006441080005545031070038502c0c01c0d08100c91104101030f80765283e03480313000c0281c041d50000c0300c5080254a01900322011028070710503185046284401103056986550f00d03a1010390000740b010043c44441e03032440d8500340c902402c1c100c5c081d200e0b07070b5400c121514042c400303072401001c000c6900318241802e0030010840070015070202228150b685000d0342c1140040030138014018801c24403500341002002040c840d00000c01980181800d465a400707150040b4040c00843c0e9003070100404032061102c0070401490004590503481c410018100c0901700303981e5803d490180c625000c100d41c10581d40030002403580003015042c01c0300224261480c28041c0d0480107880308200308000744180c802040c1042480307081202003002d040106010012108503411032000305 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 722163552 1250 722162302 722162327
    0x60b0d021812030a0f09030804060c02060d020f0403140a02011215030b160908030708041211040e01090302013605150109050613090b06010c02030c03072c1006111c 72
    0x1070174908428502d131300c42c0e400d100440707030800070319409c03e424800c04690825803010281e80c000824400062074205510060407001e4000000c56940c0c0d00d035117001c40076035100300d02c1d00107541c0081e080100541d13080b40c04401c0301001e040c000102a81540b0450102c40070301e400141a4240003810400700d5090041b6402c20f4030301c0c6444210340280d90700d1030302d40d691082007802040c4840510003003010002c0c010145455510410001e5000c0700c040012804580d455045c014a581d120442401419020300c9072851040030749080e0b2510030503c55030364011149907244800038003500c0c001101400f80c1030013440d03100b0450103901041965541b0604002d00020350743d4a200e00088400c0352085a0541b043c0c0f0242907100105540a07900c24005544000c2940000c1ea014062040e200c032541d81c061000c40040c04130890007600c22204810035195095142c0403a660500c0300b6801d0005c941c0343c0380094002c84440d0302e80082020034150301c040c01c0409400b1941408040c80441c007020136008040c50000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 722164802 1250 722163552 722163557
    0x10804122c1804050706050f04151814061e07020406260a11061806040821072604080a0305030412020c01050319020705070f08060109060b0d021812030a 67
    0xe149020300b044000c0d90054400500c6540410001c0100a00030406410038150054006040541d2140c400c85494a503030210400a155845000701c0d98044804003400750421440d008117818400d008103502c1c0c452401e030050325025403017106244405650459500aa0281003807000603910a0141011103010f002d245010408043d00700c4110400101100c03c16048011031800b18240c0082c0125a0301003204220b16a0004200b500380e0344441000700000c003100d0004001d6803840d03a00c010b05070328882c0b060303070709260b4100701c031102180b1040a40401d012205000720140203504549114501c165400050940216100441419001809144108c0c01021440c00c02242c003013040340ca4405402c50a40800c07014004200d02440019520300c0104006800600c1c114003520b5451402d41103600c640908400000e05201050081c031180d8014480034100303100b04c6043c5201003440b40a242000e040d03465000c10030345280d08412000482102d4080d001c0300c0d03282468808551a0750001d80319401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 722166052 1250 722164802 722164819
    0x141e04120b09060402010c0212150708010f08030c07030308061f0305061305040b01030b1f0807050102010e06090c06030c04050d060c1b0519060605060310081605010804122c 76
    0x21440c2003c01d41d6441076505a4801b1b2101e030710f5608103d045442005450600e20654107140340c41040300c412140a180540c460155540c90240b64a2104e20903401040e00c41d00b00307114070010190001000000c2e42d44c5800c001c0d84699864000c100c6190080885070b125440100201c01560303010b41c89107000345801c4c2e49e08881d1450000d076110560318140c43c003d00c1048007400400206808400310358200c1d0040b81f1004000c03461501c03090b031010103508a100d00d6000414204050740e0240300e00945254081c000d00079a00d4502c45503a00c44007100d5446000300c00010004a001001074211000b80000400c12007203406241404001041d40304c00d1000890190fa0400142e5003175100001442c0d9031090040444200c101c2c1400c03161607080b10221181da81f45c0300041455920b101c051407140d1042d80c6000819440c004e290b82c90000982d13184050f2400810b0b00f803089980c802e0680380e115400c803c110745500e10a440881d00e40040c5451425110f100468041540018005003200f014048a80c01c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 722167302 1250 722166052 722166061
    0x1e0c07150f05070b040f0501110403060b0a0e0f011503020d0222050901140118091112011a191206090204030c05060a0512070c0b012c07141e04120b 65
    0x350548034000f4050401800500014001103405a800c1565480780001082c40032002405000d0343e046900101c503108d440b65260500c609002d03c0800052241481441c1c00d03060080080344100c0c81805035282d165044440b02c003127280680c04440300c1d0004004110755a4290200024030301c40300d035440c01e9840034141000507062034803080007410384050602040f0403003c0f071001550b40700303081d0080c4090401898800070f8000c80610416044a2504008503900e6440400907134101805030003030884030800201d544d11408070081940d0704080302e136005103564090060f050f0344123400540c41110080c205000411a9400c0b41c0241c821244a4443c00c402d054441080021600420415100150b414010387d0181a8a050140c0c1c000c0c4850810300190500c03600c803000b983c0c20036000300f254800350801c104000d10300034520050500c80700745034101a00303140100400104000041648052010070b603d03907111034203603d50394103803007450240c0d95965441c102948001e07481e203070940c2c072206d2040009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 722168552 1250 722167302 722167307
    0x7020d02010c020607030f140f0106084516150e1021091109010e1e0a06050a030624060806091302040207050f1209061e0c07150f 57
    0x80542c190300540540e948036642100107004294000e001151030340d60030324803801036003d00b90003204036100100c401e40c1414809841e015001e040030b007006614006200114070000702c0e40c0800540c080c403418202000b10f500c190f440d81c140020345d1560107140c900c0315100106814007400c03108105401d90315034805107002e403498002d03030032807a0f00f0411020414008902c106075124500343c01664108078a0000d0080d00102e4001c0b890844210450b13868500a61800c02030103070042c4074000300c90445150425511010b8186c0d80d4101140c800c4200101e400c04150390840000791801805814003150b40f8240301029003490780701c0c1d009403060320340030544129100780402c041c0c0d0540e4540c0c40d03958948005000b00d0020040c001100140340c0c03003d0100594581c0000d10314180110000c0110540040340c05062107040000761190f080108400495501d484050b900411440045070666030400100d844840c4184181e0700c90a010349000840c018058207500b500182c0c447d0366180d058055010305 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 722169802 1250 722168552 722168561
    0x1d01020f03030a021b06040c0306050a0c050a0c15140a05180a080a03021c1a0405060d350408010606030501180509100e0f1207020d030c052407020d0201 67
    0x1910040d0001c02c0000c00900c903a030020007108071207520040d0b03110307aa002001d0034004c06482c1103460445505041003880800d010705074020303007441010080d09101d0200a055071060100e41e406200d555190001404820341401c0b4210200413414801c80c00010054495140103d079502c2e2020700d45000705654410000b01c40e14459008401003c1038200c94071904a541c214011240800d03808000c0715207080650314583c4040c034460303230001c100000703000103542011a2000010f4000d07890281080201c0d074550030943d000303503000f0000c960140c4181e0748410803400c10b000800c160150702500d6080000310f042c014000c03118032a00030004d86032150011405e681c001e1291100e8940005004100c0c21159446035400c019030b10b0403120f00d000c1103a04c40301504e00d00b00c22040250080555060212014003114281041c0006202d14080d099400a880e11410701d101508000c000108d020802404101c111801e004140950400352511300c0c909540105c1103c0761310040c06a8560441d110b03005005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 722171052 1250 722169802 722169823
    0x9051903050f0c09061201020d06060c11030606210102043c0b04030213020903010f2f040918050a050705100c0c03080306010e04061d0705030906040b040206191d0102 73
    0x11084241d12040c080010b264240d04000000355406c000560800f11f0360b06c107050003054bea403160b030b8225900f81494000050301804d503d01070340003442001159562900007400449802140d1100d090341f0300d12280c02400366800018441d00b14001d641c02c0020f0345014404050014809803c01000300d03440e8028840a40c46403c072150000d000c140010714100004041c2406004070050916212038002400e44400c0844440d41035503410b22240c410104410307402c20000d010403c041042e002440b4000c06100c1e40c4907807120140d03158440000d070124000740c440005d40102c01c5801c80409800c046440e403810b4422280704107030062501c0c0495006210340740c00550001030350b000891840e08c416609134402001e440c104040900c600c0c00300d50b501d2194102400b10005080071002090398442504030b00039102d2414040103100b005003a845c00503946d640f00b68418902081525544041941030041214242c2c03800752a0015602040e0311070303221943d000d0740b00130b0020030402d040c00591b100c000044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 722172302 1250 722171052 722171059
    0x913080405010302030406090f1a0a0e100f0e2b0c12030c09080d02161a0d0207060b0a0b090102010501060305060102030909130209160e06040f090c09051903050f0c 72
    0x400c20a541c080c0c3c4c061980f05001e0386011442e80210b5451f00c20103a4040c00031148042820a0f4800f0b604c03042800940c0140164400c0090f04a22001a542c0382e000703818290502e9100d0300c08030950081900010845812001110300e4003160201a4484800046c560b074a80c2d0360424101c51003912413000400342640203450108506034000c001c8018202802c0c0410a100564800043c074032003c20064040c40510390146c02d4113042d03401901c1140c1d900d80d01035150341e911003101820389802030040300e84001d91084010b9403a02d4901d00000070340020308416501041c041400103140320124000c14250074264020441a138813a20140c08441081d60900c1c0113070702c14041d001440c00c02c0f00640380c104014280f819000d60f440e03800140050b40c21280a98000050411074a425030040104240c018003240c286041030308181b1034108220280c0b05440390f81d901c0380149441c65008043c1e40c03024107005002c0c0f00c502e41158050107074a0b50380e444215024801c0540e06010b1850116000200b1000203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 722173552 1250 722172302 722172307
    0x1b0108070807110a080417070e0c03060904030e1e01020607021f0b0a09090819090302131814070f050d1101200312060a120c05092a0306091308 63
    0x2040071030302d5000a101800c0688114140d80c008111721002034002405941070b04a104c2e0a022181070812642e070b40882d1030004140c080c0300c000a109400c0c1d0394032240c01e031140600c542d80ca04040307986610780c0c1c404640204c0e5603591000461001215400004400e8085406d59102c0720f1040303903542a440d41034048210340422090090380365421600d94440018881004203490b120000c04481e1000c1d0308a40c5282d00289000d50307103140402d80c0907848590f0070444151403440e0003143d441881001d10320749a1395644007070814161560480c80c2e2440c0c01107134103050082d071200383d640d880c0c0300c6020380034010260602c0080c0c0c81c0f9040040d1941554809a8002c82101a60064500100313946c2030a50401050f006c03c05203241c2040a40740c1185200307400382d10b07801d0500a20500403120380003c0e46940c1c1c007002d02004105078a892030b0440d002079034928015036a08000c2c08140200d0303160022980e41801501d04280c070b045010318000c40044034114415201d000300c03a4100c440300c000013001c13a00b05 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 722174802 1250 722173552 722173561
    0x503070210062c33090a0605030d02030309120a1b0b011e03030c0605060307030213060323061501020f0709050108190203060a050604020906070609050d030b0d02090a09141b01080708 80
    0xd4000c50031003240c103800b034034103201180000751a1107801c64080e0206c517134602c03041240c1d203010420581c110010380055403842c1443c0d0400ca403242c810002240072241d0000b45000d817184614211803407030042200d050121200780c60400e000e00420300ca0305550000d540c004101041b00002e01500b12035068840c010b03a0700e000d50b182c5010300350040c0111b915020b118000005a1288800c148a00d6412000010b40360708602d03090100030850507480780090b221204171000c0c1040000c545030061605026001420160342c0101c3c6010714503000380f160360050141c002003400340750f00709134140d4640310705030745900e100309011007910000600040d5040e40b21002217480d400041c2c2c840c40d0498009000913103032042050124500382d20a09040b5440c0c2c0c0d83c1c5552401307003e402c0c4640907040044c2d1409001e4654008002255181142d4019104400c680049125000f4a078000090150712982c802d0405985070345c100e80310303148041545681540443c808001d50300c298425849595192210a0740361107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 722176052 1250 722174802 722174851
    0x206040909060606021209040e100c02030a08160507060b0a09150326071509060606170a0501080c040c110f010501031e05100e0a14010510080f07060503070210062c 72
    0x3203c03c103800a0b03009064100382b141c0c0749401140840c0c5d03400d400440d942c0b49104002894074600800b40c50307031812511030185801c3da02c4400c480d60035403c0507000c02c00c46c292000150341510a58003c1070398515040d540c1c3c810b6102001c0c030380d040b240102441c3d40780707152104001c1200b803104806540440c504000c2a000100c00f401c180800807640e14000400400a5803404221000d941210000c105186548203403801c000c40c4036544000488030a100307952401c904165160032030f800f4984a507850340c113603c410038400c1003031481e04185081281c00c0401303800003c80c000c0100307001c182c0302e14240d4600003030f000b0b0a80008004c015400001003100f0f040519052000341520f4045280a0241002ca070703001c40c51200d408a50003003050000200750401844001074140700d940001c003d84c1105000904071030f408101c0500b101d00c1e60038416941ea448200032401c001c800030000603524600800414286c41c83c41201c0013620109026440d800c4d80140e091108a008603804010f54810b05480c0c1590704 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 722177302 1250 722176052 722176061
    0x315300106080a1137090b01051614010b06030a1a0904080d0507172410090302060d020913020a0e0105090d02010e13060b030618060d0816020604090906060602120904 73
    0x1c881a041d4404100c12010441700140c007104240310303000008148501845803040007030354030090a015140c441c184400c110002c041d82c0e009070544400b03140c100b00c441000e401844601d207004064507074030300c0e02841200040071011702100c4207902500445119040c0050030a000e0350b041003a59040010b6040d011010b0030005000208129002c0310044001c2c482e520020b004800f0180c0d035215030284122440055910342c0c003014402c4140d1780340000f402c1c0c0c200504070180c0e9015a005695101d5580c0c404001c1d1143e02900d5402c84e240310b0300149244015405400e500d0401c6d03441284a0225400454503400b9184512b5404004d02c20030400660107070340d0910507a1005403260808a001c90032400c12120507501c5545003100c000100301c22454003d040e045220411000340d809400e0140100d000c9018000b4003c00c060400038612115444203000c0480c226801806503560f180c40d1959040a0403000381d04450380350905102240c19030001c80c000c00c41c00c140e0383c038a80c104441d0204000180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 722178552 1250 722177302 722177329
    0x4110a170d0c0c170a02040c020307050c030c0109180905070602100c08060f041a21060105030d08130c0b030a0902011d0112020d0603061d060a110315300106080a11 72
    0x905c20484008010b071983d0181e00001c26164000c0d549408903828090b0400c0344090215106c2d0700032110f0046079a030450f14070010303242d210300302c1d00c0900e460007240ca00501c100500a40b451041c15400070b8041d40c00140b41c0201c50700004c051040c1c400a20b810b8504038410707035850b43d12000d10644d401480c185a480684000c0c4e041000042c00301044000c104803c2c0c0c1e501d00034042000a03664510b804c1000c1007682d0060000b90001d003106016024001d103070000150103e02e0010100007000203021000c05004090b01c504403c0d03580c1c034281002d038a07009244006003240428000303050392001002c001e4a20041000607155444a0455110002c0c000e602c0b0383c5141c1030311580c4840100c0418080d226440703014000b0f0b0003a900580d1402c03e12440d203000105600109428a01b510700d00c1e0140b041900c0e0010700e0900440005d682c42e0001030924001c0801003006a40f02c1c54072002c5a0120208880d140c03c1100c0080244946445009131a868030100c060031401e404103c62440b4100f449420045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 722179802 1250 722178552 722178599
    0xc04050f0103023c0f040501210e0c040f0207030e041112090d140c0703030f0306080316120215180c0306070c1e03020c0904110a170d0c0c 61
    0x2804003070105003007040d00240361401d107040d41101800303140c044030501c40789481c0b0402484e070802001800840b8207120b2401100d04114030340051007040c4401c6854046000d80c040b00911034010004040d9a6400040741414407803400c003042a202ca5509108481c1c080d40c1640e228008400b01d441400054900d91490084103d070030004807104e030075103a01660090030420f0103041c1e51000d002000b098020359002c003840702c0004020324012800c000a19000712a03060400d10f2202420504c2a801403085074004440c034000064803020b940003014410900520444003110300f00c1d007150040369602001124144c1a501d0741020401d1800c0c0c05901d0054007078480c0448000030050004a42406800c0d201100840e100d140341c4010850a01c020b0040f52111480303c81400c2c500f81c80c000e40e07642c1c061060030300070398900c2d02041c107005068a01e100050800341103006059518100e40c02212081c801000b12809084201998036104141c00e403412508105d6a109050a041510324040621260301c2c2d817 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 722181052 1250 722179802 722179807
    0xd02031b030402010818030f07030c02040c03050928020a03030c03080c03090d0509030f070e040b0a0902010e190503120a030614060906220e0402030d020705030d05090d1a090f01050c04050f010302 86
    0x10203d800d08009c10011307210390ba611020800c588180030035900c2e2500340c00d00385424202000b2030210001214009107811356611640ca42c548138148040d804e9021000c2d4010020044c00b105040e0086064039084e0321035500d5040d150381c3c40e0520607850000790740f018900d80082c518000c40c14400e5000c3c05c44084000c0541c2c030f00e0100c081d0704030315100242e0310415600041d04108010b00c01c0c407140e002d51201405000344000903003170340021704180301c03200718a11035003104600040d00c00208a1020107010003a08917900c042000b03480c0c04141e0001400f440010341040d40210b0a003032031748440c400303180c0041c1106051000d03500400405400001c50341c1100c03080448006481c8141c658050014032010005100c0343c1494014981400800c1500d403040d98804075080103252000290b0302d4031a1501d1a1040e1120441d00000b031740a0740e0140042d00070210844510010b4045080407070251044004441620030110102d80c242c4030111100c42d58500709000400079410054105000e10a05141c01803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 722182302 1250 722181052 722181067
    0x30304090207060c1b0203150403030e0f21090306010317120a0606030e0319050315040e0c01090f060c1506081f0507020c0604140a0b0d02031b03040201081803 70
    0x40407a00104002d0f6140c0d5100c2c20141d20280d080b003000d85c0c0c0061407410a0001c4001a00401d41e14080c0b25004514411010009014140f0135485a5101c0c00d15006403600c3c00015843c090740d03402c81e6910760244008441271208840d54030001c45800b01409400345ca045c0c2e1171902c4000762650a80c2000802040400c070b404c402d05074140081d4820034070000c0001da12424880003d00700c07441c850048038164410010084440641d04c500303940f0302098602107540f551031502180c5c41c2c07208200401d40050070041c0c040c0301c1100202b50440c64a10a80c0c07950a036550310360701c0100c2c00b003c0703100300b00114680404442c00f15000c240c100c0c0c0041d13420000071900c2079640141c9403400035010640f02d17030022116410710a41896005590b0003200c9440205152000400000e85a108a218407108441000292465a1035041071280148115024141c81d240d20b00e1040000e51b000b19050304001c201d00d004640000e034001d06a1340100c1d010f94484180d5903c1200e03401d100004560103410381d100512015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 722183552 1250 722182302 722182319
    0x603030c06041407050907051b010b0414220b040b0903090a030308041401060510110c0603010618050406060c0303152103020c0406060c0b15091509070c030f0e030304 73
    0x4602540c4102100310303c0c000c40c1040681403840031703006144030354815014400300c035601c4010b96144910303030031104100062198819004000d181d91498209007011845122158001d00f036038030440341c0d00e0a211019551044d111560550460020103614800d00440c020070f20308190198031a0190007202c1c03070442c2d03900008403220b00c03a51040700012110020041000400310000b0344490b804c0e4024403e0508000010394080f404108200410882056562680a0800442182b10009800ea035aa561105c100601c0140041c1c46440765030f200d14400100c03400e140c4550b208980030343e40d030740300119402c0d902100501041c40d002c903034448082001154030201c082100081d00c60108c04901c4102e040c1ca0068200524803d041d44a10b01c0d0503c10041e2680200c40c0403009603204540580c10b548100300c1013041480950520340000c800010060181c50501943d0060300f81103551f003c45030740c0e2003002c4454040c0200300800050041c140000011300521214415002c01002d0328201074071840310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 722184802 1250 722183552 722183563
    0x3120518090c0c0c0d03091802120a0e070e0606030a111c0c0201140105100311161212090c09110705060c0a090b0721030e1020040e0f0603030c 63
    0x6510307440b440050b00b141d51510410001030303000d02c29220260001901e842c080d06558482c820b40151807010030002403900542d504860401e001110441ea241c00e00450520041c81c10001740c5070700b40324400300481c1881e00d01a040748140c0004001a00e59075440c107403400540640100702808010900030782d1600703010050b2601c0c0e0140c60240c00510512422030003402d582800c050030064280d50f000500258440c11404540c1000e1030030007140d070035025000076081d803184000310007006e410390402d841009010f940e40200c1108a0307481b445054820301640c07044440280c0300504980740c100c410401e050703107604184080306100034510b080895684545080000c1183c0c0700a5106000502481c52a0032034a102d01900e6014040f9003401815030351840c204002d1004241d08000ca03506181500d0b1103500a03010070703200403056584061880703030190094001407196030111034406180c01c0c20031003410240c03000c4030708141704ca0940d6224601d60020304c0e40003604180d01800100070040030135804002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 722186052 1250 722184802 722184811
    0x60e0102220506090f09131b0513020a0503061905030316020a09090f06050624031005030d0203040b1608120106030507030516080702100f061a040312051809 69
    0x100245000004211001c6100141e00708911801003031103200040c2c1c6400c181c55454500036150f0041e01d4540c4032902c00c16144054004042600035031285000c44c100b14100011200103a400d100225440c2d1151416405030000c07110005009100045091828051407152681900700b14403425031541c0102e41190301c51246000d1144440303040400b142026011040101415001004180d002e681d800060700c02c044c101410042e1504003242e8a6500c0040426500d0140100c0300107944c01103c00318195041102c0700c640321511180c000420f41008100220b45540c3c580c040c624280c10100c0345401038101500102e16400144141c3c0001011f180c000d00081e100c8112401e0b036580f4011008058403401007d20701054205800c1c010400080840740602d0545402c000e005607a5160f4102d141030113040000e20500d0130481055081c07042c590204064420210b41700c121101103010b035a8281c400c910000741640d0442005a02142c4110003070304d0255404100c640f4400400000030f0740c40c0341d0644 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 722187302 1250 722186052 722186077
    0x22101020c070617100b211305010b03160612060b280c030804020607050c04140a230705031f0f0e011212030b0d080301080715020f19060e0102 63
    0x1c00600c90741e0340000484004070030b4404030540038039114420307845c683e41d03034401d084040c0f1001c01c4c069219503009590501c24890308158186605d09031552840c039002121090b00c155103814003200340c0d42408951000c0341c400721403a149540b03240440842c0c0100750030104407021680c514010801401c0c25004142c101c0704560a500c0f00344900c105e0b00c101b02184108213051008046981c80041e4010484950042d011586c090b100e0070305041103401c0c1060300381030640c01444c00e00d0140316840c44c60f0b0014000c8444010420400200f1009029214102035400389105081c3d400104040d00c078200840c0c5c000030041404500c45080f081c601d07034841c1c15030403040d4800c98051041c415500c031003d501e070043c00e500d005030380700c150103440712080380045511b010101620341142a4031922014005244154041c51003079480d0b0392150100d4030380d24540600444000307126404410140b0000b8904045e4046401a2074000c8548400d001300d50b142080443e80b01e034441e00060300c52802840580550401c80707 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 722188552 1250 722187302 722187313
    0x30212090604080708210a0807050702011e1206080a080d051b12070e041a10020c0a0b1803060c180a030b071805121f06050901060914030d0c022101020c 67
    0x98a14502d1154680d06c41b038110b107800d100c02040e00d42d2013207510750400c0560030050b40e98001c500040700c6050082400d221010a02c62000b100c8540c880c05409042050000c208801921601c105071988134550003c0c041900c180002c282103d00e40d07200d40d07001036101c0c4007000607001584445546405c852f82040d10020000d08010149420660303040210608607000c02043d62000d043c2101842c680c45041d0242d0b114128005246000708400d034401e48000b0004403081d5651030002c1d2080c0c0c000090b51454110190300c10030350f4280000c001c0e014001400a80c0d0a0041108041040100480b045540005965400000300e8265899030740540850f5a504086001d80c8041d05a124119440039018516404034020300c01008200410340060103070b94060070241c00a19100508490f4102550100201c000061841d4204100703800315200e01c2402000c4542401c2010348440444d21100301290440c20f600e0010314020118001c180d002d0f03485020011090701381c0608a80000c00c000250744c1c4907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 722189802 1250 722188552 722188573
    0x30507060206190b0108010b0c2109130603030903080a021c110115030b0c09040603211205060a0909030c060510060210061503110d110d06050607030212090604080708 73
    0x1041c5a54070b01503c00c9000384041582c041c002442c13107105220b03561481d0701c04200c0c240d1131001408072420b10812a0120000c004d107e1030101483c0c0e2100e002d02e0b200d00144007149078a16002d004080499800d515903c070454516118681c1582c0880403d8013107000340142c250080d52001440706600d20150703201030724032500b40201e50071101c0f10540000e110301080e0f0f00304000b42e61048106d0f030200c06c0d1803070151541d510707401213400380c1095080100421b940400700800075000d0b0f0440d80e52060300f0358034040302c4452035815004403242920f001d600080440011b00400c1940c0e0001203c0c0380c4640f50101c04035519071591001c82d841580c510700b941c14034000402116604000b4031800300c1d100301341000503e25254030a184990385901080c00e05454881c001d8a40c603224041d1216070000400c103204003e41d00038281c1c00c40d8005013039a00418580000440d04c2e040060641c0d82041e8150002d100c1801c00003440310305c0d5044481c0c80f0781d00c040204404242c81c00140800c2c8001d1803000002c0c81310441 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 722191052 1250 722189802 722189821
    0x30b060f030c150901030b120a05191502070f0206030a050403020c0301180b15030a0302151015031d0a060e0f01140408031003081603140f0f090604030507060206 71
    0xd038040024402d03409070707901ca5881d0340e50060000c503034070b203c000c02039070b99407460010303406064144c1c00d06500c06c81090502c0d07030151010403040341e0300c0e200b44161031b262141170001c40e522080001d8080d16511f03198440035032102059000b09412406001803801c2421507500107445507108440312500b403512142400201078040190b148060303030480003071210542039901c4201d64190b18402a09004601d000301e0070440030090300540010024041d01d8181c40d441c20040d40d5004c054506540038602c00000445c12001e0800074400d5404c0c00c8000e46c149000c00c107007140904100618101c6940c1841c01c3c01c0130f000d0081241c0d807540340c07295070b020540d40c0c5034001003421f040f0740d004511a10390501040d02041e04401c42c1a42d442076018100c0b589a4544891040f0201d85541000301850301c00500c407030503002031200340e00c807440c0b0980ea42249040b101225148502440e841400166410b000e282217000626024200c84400078000c42d080c650390340c450034079206007a030210026802c06014010601c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 722192302 1250 722191052 722191069
    0x20a030212070e0307090b0d02060f0c0f06160e09012304061d01050a120f0f02060706060e240409060e01020a0f18050603070e0102190308010609060201050903030a0c1701030b06 78
    0x381006c010003650406602058403040c01d114000d200e11000a02034048902000c00d135540d031840c039800c9030094040500714964400301510032100c0d211910688600007881507288104055024101e00c0c0c407070740b0381405040314040c000f04040d200b4031004001c5a480d21184504801017151020604089101031403041040c4410382200d809160b401e481889a10941c800306007145501c1454820442400d06011940031146d1500a6004100040c1c403410300c0050781250b4161820341940215585560340348000c206205000e040c001e500011201c42345181540c001407445009040100d00301086106036400c907803000c80321102203074100700c0032010aa44505c11411040d50443d020700554100000524a0f010003002d0501304400c05407409201c2c0d20a00c00c0c0e880e510746c46001180e02c041145006000c1036802d01a240002d150680005429403050040c18010004070002e5403440e00c1c2c80c14100d010b4042a001e030300c1481146114210182155091a8000e6007d13890703070255810200b04221160 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 722193552 1250 722192302 722192309
    0x503190b1507020f15180a1401081021021305060f0405070c0510020310061110110d05150301050a060e0f18060c0a090b040e061905100206040c2403020a030212070e0307 74
    0x51840c10400d2200b6023001c1c018654a51090804885558a14041d21011203d80d04910348040c10805803500e5a066903803426041e5200302c42e4501c0079034a40030200c04841d0200c5007150b00000300509041242881e501083c0c0000311450310b41c1c103070356558907842d1074000801881002a0f0340041000f8610b00890742e140003030321040c038140c11303100c03002c41d451950b411200556454141e0ba800825845641c50011600b403202000b100f800540b03002c2c5031041589541c01c10140c080c1d428000045e0007202c0d0740c4508400d584e104880301c00c6e00d49506001102c488001004190075520012400010240030031400740b19400d45c03094144c0d10307036028600070210459980a21442c41042c0024091011007000c0d8685c020f0040c1e410480410307115840d41394000180d44960b8106820710f442407516540440d050f88218003600b0349a000079030f5080041503080b01051540104a408800186403500c07030f0b0002d0005c061580b43c058201582d01000400c810b5003aa100008901018440400c50801b400800c00a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 722194802 1250 722193552 722193559
    0x20c030105090a05150603010204050a09150501050c0d0804150203010e01080705030d09151707170c03010b09060705030d11040905090d020c061b010c0503190b1507020f1518 76
    0xc0440c0b07940d41d40c1d0f0b29a503941c030017503090712000006607060303c0940c1520000d05000300030b1031141e69100030b010014950399030900741d50040030030301180550141048039581041040100b80e0300001c03000071035940344043c0085030442c40500d58440b1801080c00a94060035490610500c036500d841c20261131300ad19a4003050203504030b03000038200a03030007158410484800085c00386a8010342c1c2c604466106640b49540b070b0001c800010b02844a17400150604000c500b41c100c030841d505c0d101c509800b140002d10960070b510b4410000d20030b41d81400f002078030507180302e182200e007824140b98074070742981d0416038210100800820100b1020003240907079030300b240a40c00034141446540000030340790110b0015a034001e400c001040e02c500240c6400c1540c2d44507154000708010629071000501d6a0310a17181040c3c3c5540300d4540c40c44100c0070f44190225540c005200345100c48640380b200240da00187c100b81c1e40808800d00e18031150321509171020009050a580994484120036100c030301b0300074030150600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 722196052 1250 722194802 722194813
    0x90f0d0602091309031205090a06050c090f031c0e01110316030e01030203390408010e0115060203090927010902041503050c0d081c09030e01051c0b0105040510020c03010509 76
    0x20a40103a02181e0060306c00002081039a222046603160480081c4002d00c0e25261804010320042d40002420001e030b41280d42c0c500c001c0c04203007003641e500000207100901c000038002d183c01e8035005048151520070181025024007106282071b60960300180f64400d51204500301c3c840405500c2042c2c1d10201c03200342811429420f08406507505805281c075091840c3c203604c000d801c1c6001d440080c15204001c10f0708441d82c0c6a4032009032a01800304041d00f98480c0d0f0911030000f90203c18801007006456241c0d00450408030132104000d10000c018200510801c41218004400c0101003108003c5804240002c650081c240c410300085511060340d10514420818080c000110085080b21400008403060b048505e50350038106403d200fa42d0502c20a0b082c0007082c802484e14540040780624040d403201156000c41e5130064515106541e445607440a40382d00d000b40c0c2c0d02883d40304100480c41071404a00700340c0ca034404940252032604040015078405950000c461a0034081d250340300c08103070040c04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 722197302 1250 722196052 722196071
    0x9030a1223120402040515060a170105010906080a0522080921070b0306030309030d3204060c060e0601060512090c01171302100302210714090f0d06020913 68
    0x440b014000e00000e108940340d0012942c610420741e501044131034000e06142e40c500303d500740504054880b03444400c004130f40300700004456000d50080011612030f51900c00c0b01c5c1e5111001d000080500400d900362020038000200d0b600c400c1c2482d4503503041d210303100c010350350110641000b1184d180205c0c8011002011794480c80c002d0004505c070021941c0103000680c4a4955200182c198003490651035014490440c15040803036126610700d201111040b2500c407480d18501070058a400d0a502c5038910500800082081520500781480302c42d001d6400050003190507003000d81000000ea00040c006400850300b0024584100c0b09642c111106000502845540c1c200292462245a000c0251441840c0002f0500400301e400100070a0380140b00e44640c3d0340c0080302500075009138100d0810030544840c2035000302d071580d0105000c1d428680319110f001d508034400c41300c2c640c44458810303002500c5418100840c0c54511613060780e00d20071100580c44160a20a00125041c0400750100300e80c100b02068 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 722198552 1250 722197302 722197327
    0xb0a0201241404091202010501030b1305151e010f06140313030e150a031a0316030204020a050d02030939091b07050106051005070b0c09030a1223 64
    0xc90499900440116000c00302c01c0c005402403401450240501d07044070304540c4040c1e81903020328103a078896583d403416500e604201c40300c01030210074000c100790301040010400c5181081c3caa588418200b402c85401164036480442c880700c00c0c1e01c5650700110a080a00080d500041c02000150000c840e450440c603041c1c00c50040d4119408001c0c0600a820b440352269482d0140316a40d001d14692040b84d45000c0b4040080c002c06807451085000b00c0c0328501c8080702d1902041281049051840c0e000003e821a020080254000c070004014007400b0040908100b140b40051403154048102424280d1a14141e400c45502021440e400350348503400d51100c1d58200c26604030280d4802d558442d22655100155003413000011201005180045010310810205403c960b00b03540064621480c0c3d2441c2c81d00a403114011100014082c0d4202c4002502d03961501010300f208071001422211540700ea501c98060034286103405400080381051003070800c20b0f00c5125140e0401800a641d0b01e07261030703801da0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 722199802 1250 722198552 722198621
    0x21032a0905060706020906030f01260d121d0c10050a020303160c0c1806090203090d030f090b090f060112150b03010b1203070302060f0c09091f0b0a0201 67
    0x8051040b4404100361040c0309055050760041c0b82e0180500f666801c0003c0b0110b51540c0074814000c605d4038094442d0050701ca903403151100c20804200801c401340410038103650300c204030300e5402800d6549044c050012143c42054803025184140170301240c55404060041e115000c01203c0203202041100301189a4000112507002d107250901501c1d8160303220040f1941e091360080900002b40ca45004210078001c47c2450441d02c10b40c00c2c00b005119a0740f500d00b800d07070204075035580c91500407411809a072800380d00070b8640415010800194600315a81d031040340c100c01d4442120b598001c0c10941e44d2141c00300011405000a541c0e0b410000b0050354034140c16000d0001d07024020f03521031035003170030585094110f001d15510084c04818030115035074155550350010003040c1e0051044002080c803296001084134080c0c2606403040e0700d0580b6903000e2084005008e459903a042c480d40000c26240300740c0451070000303062400582c584d60320702004000c1c25241d05518001c201c03003a00e00b07009610130300c8584 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 722201052 1250 722199802 722199809
    0xb060409021c150501050a11010f0506040b0109080712050304180207140f03041a1201060e010905010c0c05061c020a02012c1b01020c06070b0106080c0408070b0721032a09 75
    0x900540d80c0030841f0381103414486000c2d07080c1e055820542407240900c19500034500c500000e40d0100426181d44004440300c1c08140318040941d00021402c2c004400002d0800c0c41c064003610841e8034055564448003200c90b007040b080001d141d80412088100070600a6801c525038944005081003101402e1440c2c032880f440c8140381d1030101c0d410b0044000340451055495840d2224401d10156948880c040c14941001c0f986600090903140086030706e42c000d00e06059141c0d00a0014210f450500717051180a601404003020b036801180c4203198513580900081c503880400d98004100c0e0800e01850205c1c20200c05030001600e94a04074903910307520b00050071081a0403008201185074400d40050381400100c070402500060002080406e0000d2080c045048501e165240c00c816568000150014000c0e07000d4007106421140b0304100b06600840034101aa010300d1080c984c00e1503074000c0341807005003011500d0100792103900743c035901c0400c9030702c100f1890310401303290846588440d00141020568003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 722202302 1250 722201052 722201057
    0xa170d031a041d06091f0c0c0507091512120806041b0315050402041a070302070b07061a06031e04050a06060315050a061a0703030b060409021c150501 66
    0x26a2401d034507141d01c0d2600c50401010b4810400c2c1d100396102c00030707a007403c64400603c2c0e204000c00f040c1c5508000030182804000b821440b82c00300c0d00c40320303e20040c000d9510f12004001c0c950a401000c0382c42072040c10000c0018990000e40008150403104000780668000c0400c1200d0030b000c100428070045c4c90816032007051070f20208030340d50000050000c21750705103060440b081c820808040d003609a801403402009500003141e034581c0e02d20802c0140d00c1079004400c6846c00c052490340c0200f65a8001d803041c60f00c40d00507039508540f141003030681c43c1c1026030f064071600d480e19040e94842c0c400d00ca4011015a082d610b9524610300710440c940f0325290800e00012204442c0006414041c5c10f110448082d940f001c010b100c000e54038108280c12011508243d2240c0345004041458020644903034000c690058032400d58030b01c044101c8180c15040b800041e0107041e110703101c0c5002aa01c1030300400c007800c11881c0058131041001085418900360384001c440213480c1c00c0048181000310b055a42c100e85092 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 722203552 1250 722202302 722202311
    0x509010e0a0801180b0901051e0403030f050a32061e0607030c0506010e010e04060c02032b1406030a020f011e020d082d0702070302031002090a170d03 66
    0x3000824120125644505420752070990091a0049405090000940200c000c89600e807512a1114200c54050b034405485102d0080c0040b50711094000a640c02802070030002021440800010180d800441c0e010031107079900d06580072401481400c103800302c110000e41641d030702c1e5500540c0c01041e1001d0481441a0340c024098510391034074181b100c1380c090002d01500d444601c02c4ca4003030054921040120b610707001d4200046107520680581070b040b02c103090844980c07516540c694000521035880060b045010400c01c0c08400902202400d60203590480002d00c01220041d08000721030303410310305c0c031a0022844180200350740d0005028070007907011602d441c0c05a10140069480440b203010f003101c2c0314140b01e268880d040e004a00e41140030b42580b03d540c0c00390342c1c00e508012080d0781400c031015040c3c1c001907042c10400f43c3c0390900c0c0c2c0c8400f0030f0040750406a2640c00081c58803e8802401c2c040310b0b0005208019414694440c5d8010118040c006042d051221000d6440700c3c04402600e040560b203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 722204802 1250 722203552 722203577
    0x3050a15060513030602070b010806090607020a0615050d050601030512090f09130c0b0c071a2b090b010807050409030f050906070c030b0f071b14010f022802030a050901 74
    0xf0080401c00a6522038401c6544424030300d030400d0600c90910030380c2954029140094014040458268861201c1c0c0e4041c200c2c13050256100002080e12081071910843c55010210b0180c8451038118034081c001e10082c8150343c55454144d141510300702e080003400d0418005d07074550742c54a40000c8016807044501038082c1e0344051540301e0100c0da031076001d80140b031100400904014841c0040012102000640d4019611071030003614030f10103904c5603084004104045c0002c1d041100c1c110040c581501712000030b01080361401410b80e505543c00340d035219100e10041061040800810f0000c1409450038010007801ea20040d1202e46202090f105100b030000f0705040d11740e5510204ca0b0016400410840255180c1c205150f840d2310445691200c0ba1070400801c1d039141c00b40311f20703181424252841c40700e02c40c1c0d20354411410030142d02ca8461150349440c00700c0c0e81040a800a8010a00400203560010581c0450580e095030320481e14030540d0020070840141c03950020846488803000c0c204960840f00c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 722206052 1250 722204802 722204827
    0x41e05090f0d09030c05030c0f040b04060302061c060510050a080a1b0905011d0f01032307110d03090804230307080d03110903070e18070f0603050a150605 68
    0x580c1106511a0300801200105058002c0f0b4820180c0740a02a0303445815140d01c241036444240c0340800740c3c04441c0900002082c61305400103200ca403c05800828186e03940d034042555500030000c00c041041039002c0650102c411403045000504003201c0c0041107500c3c00d100507000f4442c400c0098100141740000902000243d08810a148401410030b0610004000010a001d08900907070b800942c41010550140030480348004008000500e40c0c51003000900064004003480700e031281e0040f0802c1c0301c401c3c02e4000d00d1020351144140d40c40f51420940d9094016003000b120410304000d040c504505600454028002d907800e0781c201903061514890003100c0d820100c02c00c18800f580c54814950042103607000460000034014081c0c030280a8005d21490003806801022112074050707001860410031f40c0680500a500090980c0800c10300d4903050b4000d9050010f250052070301902c01031003c1241680c1445015071107008500c08100c24502c580c8174880004241c41080c0030803034003140c5041c5054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 722207302 1250 722206052 722206063
    0x15030b0610170406060e01090e071502011d0303070320090918030a0e13060e2a030403090806070305130b0a06081006180b010c150f0c120b041e0509 65
    0x407058860002c286414584400541141c0c0114080a8607440001550301c219000e240701c06140c007405009850309040d030000e144540120101d045640713403502c0110350015103d0501d42c400c0b040d4042c1d076407450820800b400b5a180080020750020b0030b001c0012070036103440d0071744501003030850b03021000c2d840d041c403402c0401006548121850100042031110640c119030340f000180415130310700c107010f190920800112211031140c6211041074000241c1c1d1401c40700ca00d0001d0f841500314028203001170213000803036504105c40445c00302e00d003c54107100707440040002e2584401a8641803110786403110624020168190008110f00202400b11705c2517001ca0f00043c016000d4113007125a400700f1204681c0c041e0110f44109140340400c02002e0100c1c11650092210922040c0c60f00703a60442e0a0f90349034510f04200c0000d100060f52401c031900801058011050324100507501c022580b00c8112040013141d941c04505403142d89021280104861071040101c10341d03c00040008050365003050903402d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 722208552 1250 722207302 722207327
    0x32303090405090609150c0703031808070803100b3a050a06050111032b02070b070f12090b0a150321110c06030420091915030b0610 58
    0x7034108000c200488100080407841007401100b100c820311074451012050750741c26101460300400410000c000b02e4000c0e00030a25952002c10b6020b6050810744582c206508505012580e0300c03000010302164590303131030244000c2d141c1081154508454240d40c04a1042c00500c040004001003003540b54090202e0713100742e4904074107102400645404115a4000d0640b07025281c0410304001500c0c18400d400010f4464505100b8400003e400c0e0701142d40c050640000c20301d1020703d0b000c110450001e0f18540700e480c000c0ca0135403601c01100480e800050032100b000507480c40d040d032400301364070302042c903015010790004541d08000616840d80b080c1c0c44d0191003a50400b4100e02c202e001c0342c4401030059441c111138003c184c1d9442080500d019005a200c10160b229640d000340c00340b021401151280c90f0084200c4080680141541c49003400720341c1c4408221650000070000c43c683d09000c2e6402e000300041003120203103031801642980d4410321000000b40056014800d060761198a1074003401401156 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 722209802 1250 722208552 722208559
    0x30e0102120c0d0c26090f0a060f0b010c0b010306181719050a02071e03051b270c031b04140f010c02061e090a09060302090c0403230309 60
    0x5142c2000c9040055100042c0d9849451801c0c0c030301c03418584961507008100036018045400e10040d41c0494950540103080015107002e004042042c41404000601e0703618807034180480c01e000c40341100c074121070301c1140107030502244000d00000250040c1420b8103403a4402c200096080d80c044401c1b8a6151608009020100282d83e0328100c5829202a01203889108140c01c4078100c96081202c10703000314403518002da4820f48084c007811010b081340c24005c3c00785120340c1c03000680d00d407107040c909810501803001150319044805183d080c58102d040800d44525001c401301c0300e14070019804524000d00074460740c2c0300840454034001d1640d041403c4a46410901c1d525607488451101c0311100240d8090322942d5200e0b03100c0610f500035009421380c603800030142d42c01c03e2807404881c460119420398041107618104014903e6944809040c800342060750400504903007184141306070194094854000e01805200c00c000181860034040402c140d114070386440f0103d10075240b032540c051101d14030351 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 722211052 1250 722209802 722209837
    0xc0f12050405033702060a11010f060603140a1b1115040b0a0501050d0b040803040317100906090501050a1a040902031e130209130f0812010f0602060601090501030e0102 74
    0x201459032001a421030a4101c0f2410301544d00c40c0088038220300c400000940008003801070861035070140d00041003943c0068004a0408850b600c400d080341d0035904481c01282c3d8035150031381d480c0c4000c1e5110f1f0780b005641c0303020800400e50001300c5c400041801019020040b0b4000811180c4174144200b036480081e118a000c142c2c04c00b0710b0070701e6003d40b00300d4200e0340440c6010b000040d145030042c0b1031000150800c0480e201516143c80e42943e40e800208240c1c24890003000001e1081c040c2c10699200b10140084d91114504095000d020744070b00b81c0c049214603041a0041c011075407100103032000c44460300754902c1c890400e038502d10510b010b036603c81d00c6d1240c408010400360282a1000080d06003090301645215919030410741c81810380b0600c0a908400801c0c00115000e01b1040242482d60244200610120082d40e8580c015800b103118600c504020500401543c8280f40901c00030341b0301c50014043c0c3e442d0481c0001c201100912034541019180c40340c1840c1814207604a4904074034a240038031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 722212302 1250 722211052 722211073
    0x5040606020705030f03180d03030b0a030b0711010b0a1203180b03040c050402030717060a170f1e030319020d051005090109111b010e030703080103020f010c0f1205040503 75
    0x3500c40a0500c1014000d00410a10312405c1d00080100c4890720048111201c0d06c20340c510a00c480281040300840c1415500c86a041942e525008410000c0d4400c0d03490f41751a18000d04000c2c00210b400241c0d810707c1e81072141c1095241d6600032450180e50b6100350414449115040842d44080c4040000403043c40c0754001080c0420401d008510485c054040b8a1401e82d0307400501c4120701c4200d40720b04c00200e22041c2c4961401c0c00307038420f64011000030940702c9950785880c1a55050f001c2403c0c0c2440980c8090b0a01d0032a90301404400808020101e030251300d05041490a41c07a4440205065040d402011401c200102981e0503600b070381500345c000300400e180c9025210020342180c02400d1107018130100001d0ba03500240248445d4000c0f005019080415a402c01c1c600c40d40310012a011954071022085240c0c00704002603c2090f0195880c40c016500d140144891003001b50401410801e0703507071100001ca99032400030080f0549c0080011000031505404490070701407504066414040c503280300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 722213552 1250 722212302 722212307
    0x9050f0111272e090609080c121011030406150303020a150615020f1002040f050f0a03021c0b0106020d080408030403020f0d0c1a071e050f04031a1f051905040606 71
    0x80307a019005440f21884aa00c0c5c1c0e1056440340c01a03c1a82a16403100004103060708040c52040903198a0504a42079410502d4061054650350040110040e5000c0108030070b006d0300b40103e01701d04043d402240303031150a41d100291a0005e00c0405404003039544480a85107085500110090440c080371b03002c0101c0c3c551000f515909a100d05d003101d44641d0b03004c0440052680300b218100d9418081c07544602d450482800415809403401c140c1c04000c0301400070150b121a44031113803200300d80208881d18041032510558000741078102004640c4044812612240c01190440c0c01541044225440e81d5491508a181000d02c05a1042030f00603e65958646c94002c05040140d0f0711402c045040d114011010260b54641180d00e0f0000820008a1a0602250805445154400386452840e180ca1a030402c08079074055882182e690711006903111004a1812505810000c9002e01d0303074024000c402c9014010b1114010b042c40341d0045050003040c01940942d0100070300010301309002c5030750b848001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 722214802 1250 722213552 722213629
    0xc0319020301061e090806060d0f0c0603020712031404020105180406030303052a19140705150f10090b010306080105090a03030e1f110c0109050f011127 67
    0x10708402e0414921444e03980c0650700d5242030362141c8004003882d9130b64000708164000b2060042c2c410344503845241c0d01050102c41000b01070811920b0259441c5a645425080c102e21844900304062600709001e510142003401160050f40928103103031181c5440200078403482c058462264810b2400c90000105601034000b03520825056402c58011142801c1200384401c003940300e02c4c40180104003801528110210a084581c803074030307007680c001c5c4130030411880503803001a080d41c241e03008406610007140d0a0086070307031055208010038000e00b40484a03500420303403402645e26a58a030001c903d06030344a075104000820088009004900304219415200c0c00c0645054000030f0800c3c2580340e01040000300002d02d4450b002c2c1030140a1403540c003400c0280b1100701d1007007812104000c1d01500c40700c00d02950391242d0080d0050441500102040d0b403c4071804160044285810f10402017032901282c902001d03851500c149402d042010700c0051080e003001080c0780100450b441c2038081c00c0c1d039007400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 722216052 1250 722214802 722214827
    0x801090c06090f2913061823010c03020f0d110c09010e07080901200a08072a020f0d0f060c031103010302011b170a0201051308030c031902030106 64
    0x1500d04400e5269100c40d52040d00c5801100440c6010351400b61060189141e501c0c0303c500601203403400c0400c0860070000340740c186c2c2d10100002d8814030303820300a0051065600300500d85040d8080040003001d072650f0369004040c0b4042c1c14016040c01404c00e1600030b0040ea0015148002614840c074440d5602070640a039010318801944034904490b020b509245902c04c1c10784030140c4a5070255a01c1c1242200c5052b40104900c034555240c0d8403102c103d23201e1802d0071080c10f032883d0380d850300c46c911405e0003845140003d00060802415103444849448550702c4061400c111030700c945030304c200d1400825a0081d100e40300f80c3d00100c8600d0000d05024040180c900040c3c414541409100140f03030080b000c1d10101301c0050303581034041004000540c002d210007458214503c071442e016603d541c0f541e0250702c00060325031048000000d040c4000913420720074503a01c0b0040e00d4a80f8642d1840d52680151400014110040020000080b4070307645201d0002e12058221400250342c0c039a160304000306140c8010a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 722217302 1250 722216052 722216057
    0x70609090203060d02060d0f110d29060a020f060109020705070603140f060d02040e03090102190b07050a050f0c010903030c0527040e03040e010305061e06011202040801090c06 77
    0x6004504103146008590082d00d004149858106158080103c158040c2c200003004a60750100000c9161080c0200100e5100d102c0c600c83d180c2544c2078401c0155102c603015000d05460f891180c4804440b001c0a07200048401d07981144c07101c004102c1a86821180154070302140b007084000652600c40340c00405c2d00c1c80c03040043d1800265541c000345d058131005800071039000c02c1c1c94000760201040940207940708800502d41007040c8600d4000c47d0846454142102c815007001401491a580400c0030180406c113001d200e03a10400683c0310609d481c48081d1680c01040360002e0b81c90203161140c020340d0030000c400b41c0d07020342d14110043c460f03000b0101b121048010a00b084034081c0c0c3d05025100761480c50061141400040c1007001501251941700000c080d4413503598540c01035008000c10140c000b03031440c561072035140e504601b041850120002d11030703004c001c113014130034070044d40e14104c0d20740122007800c150303020b142c03c01480340207070003070390070900c040d610b020001014009512240320072107040d80c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 722218552 1250 722217302 722217317
    0x903122a0a020d0f2604110d03170a0e060928020f0d0201031806050109060e090304030b19020a0e040b0102010b06220b0c07060201110310170109140706 67
    0x4508500540103805280c005604280680a146805002c4038407040da40d900c0c0c0441280c00c4054019504060003c41c44001401031041000308401c4600740480e0301000c0350840400a40c642d03000b070541d18005900701d24901c0c43c0010900310b02f280d801000c40101c1031301c250340c0c0d580f606d101c91a43e00d405a408000c99803102c440c54141c18010000e40e0000b2940107402a4940110807003800000c3c405524120f04060b5240c0721b0f006948400c0340300210340e03841854003281d1545086200800d42d085e40e00103003680c03d0b641c41405240c80000085500701c80d0320421140c00d9a03114000800c4114aa440c402201400001c10610250b480729126907150001c8404000c0620007600480c200c51102c81c2460308004100041c03030030024401d24825102e407241c1c0b8032908498407025030066a401080c000a0f01e680159420b0000c940c0a004140901341a4007059048d40b0b400200078008002c41d210300d5035a0205464101010482034001700c001a400c01514414000d44148a030790300d224602c106c0002901c07a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 722219802 1250 722218552 722218621
    0x41506050927101e030b1902030a02130e010b1e0c01050411041d0714030c03010e030306012709020723070f0905150105090105130e04110f031005090312 67
    0x404c490010160048403c00981e0b034159541d8580c5120007410072229040403401c0080b0000d01400250300c20303a181d003005a03c0780409551028080c202d500300c08440c40c250f000600c0003031640ca0540d14500680103102c0d00e140100d8413042c14911645c4030100c115400c1c48104000c0c0424001102540402aa0f04004402c1d10b40340041108a84049032a03c98005140400c01034002c0716600c00b1307010008050b03909500f007840c0003d003141d080c03040020f2150004000c0008940c0c100311038400580340f1302600440300c3c0c485044150020007074042c0f404025804a40d000a0264030150107c54039800011741e040d10040300d0036103a68103454402c0140c64000e080010400403424000c0c103020742c05500d000d0350101d0040c40152029002200b00c28100a424001c071140c003503c03808000f006010140c0021030504042c00c01f9a5402c9070f1a00107070050901d0100c3d00b0098400003107135800000075903400280c0b03032501c165490451060041040c82e00e0003e209102c040d40c808815032820300b042c00a2981220107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 722221052 1250 722219802 722219819
    0x2a040b0a15030213140102060601030c02010e031303050f0703030c0609080909040606170c0306160e0312030a05061c240906020913060302090103030c02060f0309031804150605092710 80
    0x2c01707008041c0181c10000c0032030501e500035007100155a81d24000840d228101d499a5451504103003002601c401d0700860130014880188004a425480c0c5009001a1401c5d510050418140341c180100101e0703440d0a0300c010b0248a8084c4d85000c480104000810b092608111005d07190390301408440c2c42005054400490001580929140c1c0282c040d04080d552500b070040101001c0c0307183c1c41401002040d00b415a6400d220341b0510001881c1d071251203090543c055812900010009809402c52000d840b00e1240000105d080b020b50290040504032174030ba28801c42c840d030b0080406a00d0b41840d51320010410940c01031b000c000c03800d484035000448082c06840c15100c0c0c920010b03400419001c0103101091049801d080b680e0f00207000d442c0b03054401c4444032060360045a00000035000030510300b0032900c0301100024080c0003258107206404100501e00808625413040e030061002c0001c40d00300079111841114440c14540e4103240d040d0368005148150000704407000051414413040c081036286 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 722222302 1250 722221052 722221079
    0xf0405070e0f0301020702040e1507020c060304081c06060203271f02030705070608060f0916180308131e0b0a120f0e0c032a040b0a15030213 62
    0x5a603981c01841a414105001c2a1442c26008a4065400300981c0700035803a54040c1c0d040c490080c80c02001c0f241104441c0c144a144007619210464001e1401030165030b90f104190383c0c016401c8641d403643d030603d4030f042d40001d4002c0700003900841e0038100c00080301074000c400703000201c4950312045941c4140e0440010710364a00b14801c0d50000e000104940e0200c0782010041c9000090300450703242480707944a072071400c401c0d0f5008100080c2c0003402c000703c1c3d0038107800703040440c2415a20b800031803d21003103c520b1140c06000d803c0401803030300303003542c07116505500000c021900025025550f105800501c14050308600a46140003c00c0c0500041c5c0040d03440d04200700c07618811403508040501c803080311042c2c0d4103614000c040307894071b036420000010340c8030380c0040c07ca450000f4807504001c00c0c10726040c61a0340d04000340d100001a284c0c45541d201c03202d4180390f80c000f2640018055548000200d40341525003124509616184401c180e00760550b00911200f10390001c0c03d20f0103580c600390040d050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 722223552 1250 722222302 722222311
    0x301020c0709020c120408070501122a020a1a0a060501050a0f03020f09090f070f0c11061614070906120f030806040f0c05190c0b180c0d03030b0f0405 66
    0x10781c07024004201150140e03014080380542c0800342c0b000341104000c09281034000e40c00104080d00010400c1103a580c00c8a040000c960390b0075010b1000140301d00040f8004503108400440082680031403950241c424808951036a40c00701c100700c101d0207501d0142070b40e5441120b000c0f286c0c524100000c0340ca58058030943d00c002c201540e075202c0c440e0400504038007a4100022010045405004000c402e030b030780780403191090a5401c190b04207858000300c000c09104070405058144440001e280e00800c50011500b100c0b024241d510715078a0f483c0014a89004140c0103002d003d00b0382c041c81c90a8525404a1140704407203d912007480314070345844411a0b0804514001090680700199000000303006030b10459011400074400202c0e141202000703400da0306100d85600c0003c500184031441c1da001c0c0d40703500211112602d03141c01c01c00708903a5002c0021002800100e1a02e1703604c2000008100c00b00701180003008050801c0115484510700940601841079a45205810f003455910050a05100d2503104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 722224802 1250 722223552 722223577
    0x6060503010305030f09010504270f0501050a1a1201030c0311090c12040c030803161805010905060d09240e16091a090f1902030402090f0a0b0a03080a020705030102 72
    0x17045816003402e42a940503901c0c00f41804020320000900004000381c01c45183c14101090080b00484c28103a4211100b40d00c1281e000b0703284c04010303c21501d81e0424802611500100d2780c0450401c1441e58105000f0001d80d95448030b2108004070820008409800172a8420554022500d400e1410400120000c0300c0712003100c03000380b014600d8400745c008410741140c024141a11321584984036180b0551048400521040560025881c1241e0000d808403200740003030032040c6400c0c01c05000908014030340c42898411000842c0703070304440f4156440760300140d92054070000308084128841c0b440807264808059403c0c50911401c2222034040f403c0c0b040c402038440502219800d110441005040382042d42e00200043c818120180c4c8a03a81d1850107814900b000c41d40500d051a40350b500348a2810304090114014002c0c440144c0314a0401074100444901ca9082656a28030b4007001f00300741d201c66503115044c52400014480c03004003c0100021940c02e4600c036503150001d25090348107118a0114 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 722226052 1250 722224802 722224807
    0x20309030a0c140a030201061a07020604050f13020307030614060c070e1b03101415070f0f06051f09060807031b080a0501061509051c1707030302030a0606050301030503 74
    0x180c00b84079607549549140f0a403100700d01c22034031a4515150002520045001d80e6403075006204141c0d032110840d04140c50039171560300d0306016a022030000d010b81d00c55140110500744540700305559000d03c1d40c4000a400304110349920300b0602c000c0281811b03103d94182039070092400c10031401c0260444504a465000a00c03110780707441403401d01400000c1648021300500306411202d00c0e00840258003c0a18868602a0358281202040c1c5ca640c8840160304c201120f1204480740500740c2c058032107150708041c001d056480719042566464094010007400359280c5010080f8002d1907018001082130301580403010356072039500c11012030300c1ca40222034680c0c1c0003402c20000116000309070405d0b0b1002a0003004020358506405250811600048441da51a03090a01003c400101e01c1c02c0b81040500d46500d52a03d000042003001c10441c80300c44040c1c0046044805100301d00c55020b028548400400e40c5e2002141801070081d00244c0d901000c441c02c042e00020403901c15070640381600d4204000d1803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 722227302 1250 722226052 722226067
    0x2040e070e03010b04060602010b09060a18051b0319050108011e020903010b0415091401140103200a1107080a030f26070306080105060904081b0304120f050d020102030903 75
    0x1641c10100c074070100c0d450764a482d90380c0f0041d01e69000b403e008014580000c24510310007070030408041c01c003c0c103081c007079000301c2410482d40305004a03144a9154802001030070391a50f032a8910301d40200c0394803040b40c00340041131002c0804c40861120f100f2241d01b03820803180e40c03241210707426204a230600d801c1c2180d040c4442c000146c105d500400c19194010b000145070243c110201d010380e42d002c00c03442c40203410103408110308000d50041115500d0030004648041d81000101100c000064000b6410590b460f80210500c8130340e441c10401843c100940d039515014148001403010202e600700041c0780c000e01500240060002070060407031070b03154560010121401c00100c42000452520a4500e203080d02d003500460342c02c0356501d016a2196401140c0c0c46c0c1060b005509485000c3e00442c010201c0c1400c1201054081d001c2d00c0a940f030881c0210030403c0e2f401410352950003a0382082da10740001c1d01448080249807400348041a10620031b40c0c0c3c0403011500300340c0c01c0b401701300e80041860b00b0410048 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 722228552 1250 722227302 722227307
    0x12170c0a2c1009091109130b090115051c0501050102010e07031a0c0d050c090901050d0b070810050a08010b0a081209041d0f071410020703060e0307050316020406050402040e07 77
    0x640303100000e14103507441c3d0303540744214000e544070106042080f4200013200c0c021820400160010107450180c10300c00303010400c01051a40c001446904000c91034510415815032091040712024200001607800000421042c580102001e02c10540550f180800a05920b00c000c02c680c2c088a4202800f25844614911742c00d0160100820002044030304000030840440325124040c0103030b180c142d6064480380c42c01d040c04111030041c0c1240b0b1240007603116900009000c1d0b0212980802a0b20707054100341c032030091140644206400c000da000c0314403500407418500c150322840c14520120754400c0d640742d0703e0040ba5140d600c081980c0303600000410a82100d400c0a410412800c1d01c0d1300d040300b84603d08901f038903042c00f0310381e43c8004585d0007050080200c40346220038030160780c0b4110b404d003031000b0000401070b41c1c0b41d203a84001482661070b9420005046003c4c01134904481d0041d00742c0396104003503103048028001c803060480c8030f02d103885408107a50409100f0703a07080e00c1078030036020030903126507030305 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 722229802 1250 722228552 722228569
    0x1d091b300606182202150702012c010f2319080105090721091515050f120f3304020d03052b060905060d050a12170c0a2c 53
    0x3000366504c0303907481403005031502c550140003680e81d40012074803504a88001413120719410b001c42d52a69180412a5040440b0818414000403d0030502c0b1200025041646e03c501e0890700c1070280c0d104806041900858600204450504101d40304410410701c0c81c10b840482080c06941d400c00340749800560504d010740b0100101d02010344610048440b4403c00c1f0044d80e800c40c000301d802e031000120184022600c0d000d20440600d0100421423090304010101e040c00d100c0c25144d1348610310411285916043c18010040c101700040c0c252101580d070038604c520344d50403510f03c403102c01c0009803003100d40300e1404c03558074000c1358000d1001d00e080c0c070103860444103900b10303140c0715007d00c45107144642d220035465400c00c1c0d841c001e6140421000d00d0b00818104403200100654001d289920210b070000d00041181142d043c0c0c8a1444008490254400c5540307220444a02c400d004400d424450340742002c070041c00c840c040940e41c2c00f00d01e0a5040e5402c100d41754071140c44183c10350031000c0201c5031614405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 722231052 1250 722229802 722229841
    0xe160603111821060c04150207031509020d05100902010f020d02060a02030705090a090b0102190c030b070915030203061f0909051b04030b011d091b30060618 69
    0xb0740020f4034441c0e84400d41020015a628110588005420029195014501d44150400380041c1c007445107180c80c0c0030101d04d8841035545896540d0b9102801b10340d40e0410440225401100300d4a9144c0d49a424000420700d12000303a0200304a0050203040a100190b05550850554040c02540c0c03a0f40c0c5545000c2d41000e070540c014400300788401c101d15120440403c005082d81c21001c21030b240d011001a00300000c0c45200012040100244008240520f150608581c1c0c050f4904c040c0d503850410403103045540e41c00000c0100c2c6441e080c2d048480c0d0513000345019800490701c0703841c4a40360040c02070004080c6e054100100718035520801c0400310355800983c0c03003910045a035900032848810301c0f0003980700b5001141c0001e01100140110041c54a6a0040500c032550745192410300465440e40d42c071090410458412218a480d500b585840b054018201c100942c0351005a4604028207031006d9000c100340e03064413440c40002ca503882c040041c94403070700d468120024642c0b502e602e50759030708070b1012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 722232302 1250 722231052 722231089
    0x50312071205040c0609150e120a1e0506060105070203061302040b0d0b0a0608062703071406040302060f1306050912031f060e0109090b040e1606031118 67
    0x54410341c00500d540107040c429441040800c2c022070070202c01811140040e004980780241d000302003d072658010341c14180c410400c8440449100151103030901d0140721000081120103001500641c4915216407400d02c90b21440c180c5a05070b0740c2c4001101c40b1f00802c0300203907050b0f0041c404545d04083d010816001c640c009440851412800c038003040d90b03241c021604889441c0c1080400040780568402e0b40040c0296501402d07413410004600c4038181001c01495a8904c2661003081c0e194070100111400b85900422180c02c20f041030b4502c54650034101e400b90094041c50000030000d40180103902e100e840e2000c0c1d42c070310030003058540c0320091000070030742c1d0321078880d03103c100c040498503101551084002c031006240c1701e00a460030322800a51030744080188191031641a00c0b0faa00000c020b4240c03000307124001003403081d44001402910b6009070000441c00385400d51540840c810110a0a555284d2403d10400104000c081082d00c0b0b5081c95041e0b03800b8055004555103070000402d04c8924201 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 722233552 1250 722232302 722232317
    0x20c13050a1b0e03060105100c03050a03020c0118050c030a080409020f0d09050c10110618030921070f0803030c091306060207030201271412060109140c0705031207 72
    0x2d000040c0112036001c0c2010507aa08001c143c0c614003007002901504094a22250b642c0c034024001c2d1400c1401040181405004108910b007148030368191503500380394500078445012603824011698003910300988280c041c0080c20f001c141030008607440303a5903000614501e45403924490350025040040041a0b1400400000401c00c030742d802802080e50003803015001c6910600c0800911001c140c034400c003030001c000e80d1920309180126100f03070b0040f000f51040c0c020740c580811660071071140c030b03007403e42c00701c000000109620f030303c61a1103880f100078204030b072655034540070140740750f85d20381c407810320150f0003003000a9094069802a1a10842c0980030030094100e4038410001d0320311942061006030300400007001550780c004250304000c0506d07401103540d0710003103c85540c1c0181c20701130755084081c450317030b080d4068640300e904641081e00a81619460350316841141c018109412051040d4012180400d0104c10283c00316900b0325030100046140400040b07c942412500a01ca8030500954 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 722234802 1250 722233552 722233571
    0x150105010f172404061e0602120304020409020a05060a0216050d0f120e0a091e020a020d030b03030c0f0c150c190804030c030b090f0d0f08040204061e06020706020c13050a 75
    0x39406503070701a042051000e20310b1011b0601030681820740d603000700d04640c0511006001ea02c140421079030000c2e0140d402260301301590012500d10003059105541050300052241c80b000c3c3c3c0842c0e6546009081510062407a980b8420404000c411981c013420621603180c00d00e00040c12141c20a00d9501681482e0f2529071800e00010078181e02a4050032050751240a4800264011f400010b60000d90b02421828401c0340030300255121084039030003045c15914010030310b441d941001a180b0f403082403c00c40340a0385881f80c090f5160a003000d10301d4050748030b81079001311050386101a1060248804014000869001040343c0000c50906d0183c58051080002101040382d07101d64801843c062410449141400700c03042d4981440b111100c1140d41110466000040d4402e4000c3c103482c541d85450300440c0c4503400002e008150540c041210240207034508045200714060b01f50841d0441c6c0c003920740c416902d0710240e880c0e5008800c11a80503542643c42110140154081c50300203400300c000281107241c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 722236052 1250 722234802 722234809
    0x6021b0603180115030b012c060d0227010812191418010f0c0c14060c0a03021c0906090509040501020c01090302100b03120a05030711150105010f1724 66
    0xc41d00d09903180349130351181031080c0b000310382d1040c0c0140240302030f60141d244001c52041c070100c00003004080342d000040100e8103030740e5145c1d1003290094005010600440c101102d445289914240a800907801c200c00004d045d1408a8201c081d10903d004240c42c0c0b40021032110421460040700400380500701010985c1a1440e001400030620381c0034400310422442320016040ca030419500b032007003000b1584640000b981e80c0c1d40c48022a4080e980c1c46110f01c0301d4400040d039a000361083c00e00140304401108003171690003d03440a180c0c9983d881020340c00c0c00ca140490326070046000d07a0000c80c0c0c07920b1080002d410100d80d00d980c0580950001030070840310030225400d44004071001d80c01607001e4900c1e003028040510072011920342c00c900528a03401800c0160045028642460090080100010350704034010184035820003000000e8405414408140709401d100c00e0061a0014100681001e006402400001c402280c80c40602221345c1d980080307844c50ac5900003244120603804142d80d119a00e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 722237302 1250 722236052 722236061
    0x11040b07020d1a011e08031602060a020a02130b010e1c020f0a0305100c0206010602010606021507050702030a0c0e0604050103030c15110f041401020d0804170714011506021b06031801 80
    0x64017400b034401c0e0711800740070140c1101143c2100c003a9400812443c4d601e80c0200000140c1d40760b040c4c0b0f0040d120181503406038200702e205030740a90001d4092551800310b0440354014090f5071000d0b264003080840000c2885542c04000c001c142a83c94100145805440d019100e9501139000402c03101001e82c403a03a402d810150080c49401c145a11111040e60342e61301441840e003d0b0503d84020000729180035030096440011228113140d0458180103e01d1191041c070488800c1038010301103510b640c0e9903180442500705c42c0e105128015894101080341498540079407412660503543c1c148481543e9124a2000041010003922241c1e42d020000400c40504000d03042622a0001042d2240d11f4201441080748000d0356842c110f4005404d4540c00c207410440d1190403039040800d0460380042d40100850500c286000a480800c00d029464103101e01500510b20080c20070f03c0c1c03540d40036690702007070340e80b014803d00c1c02e0568112240c0c0d44070b10307080900207103a20200c142c040741d00710b1924814032400c69 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 722238552 1250 722237302 722237309
    0x6091f092306060a0f200d1e03050103020d0201030515040c02011a0405220620210105130c030b0a030c03051b030601050607050c1005090411040b07020d1a01 69
    0x1601e8010812100000d600c69050340154180e8680c1c0c94114400001400e4030211459038003400710590f588a14207500c082c002e01c80205500403a22040700e9a10041c003c00034030b075461038569880d1503c48140901c640030380740c12243e001d81036201c5c2d541d01d0b071300540103010300803d55070005515900881080c2d40c1ca01960749115840e4000240d26500c00706444013074944c80301c52600445c02d00c42030251400c0c0304406480c904008050610100341d0074a000c90280c0300c007500b0365200101143d0020f603149071302c400800e82e44125881c40c20140c42442542c003800c0c4000d02c070f004c0d0300040d040000601441075401c100d666034140d140001d00314100c01d00040b20b83c2d0f0650400c0e1240089a2400d008000c1c0820a1440343c807190b26a90142c1840500020b554020500501d4040c00000c209502044002c2107403140e1032500500744031400203802d500810301d4110070403881c412807c0c40340e5411a900440211410394501100280c030f0402140c092083c203100710310003200c525004000c01040c80c074425a0b081e018 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 722239802 1250 722238552 722238581
    0x30906090b0924040b04020604080d0e13330e100602061008070302010e0112051515070c030204111207030b01030b180a0911150705010e0606091f09 65
    0x2541003403014140742803420100d00d00030f030003412200a03014642400155105a010113140d150340d070786201040f8203006651044460744600050801c106402c460107003554141900c440c1d20040c0c18216820030b03114820702d6150540c811026800008540c0c40702070a15001010b0642041c550390070301a181d0082c00c50305540030050003201032105903410b000310764000120b801c0200c0c100b8104035600d52034001902c0001d040c000702c8042d4503610b03401100c840d1110700501d2010007007450605070b01400702d9420652507100f4a44010800c40b20107200381692551504a9250280d0600355400c1c003000303000070790b604402d45034107100015460b112b1030103075845407955640c04a000c1c1103240000d003c5d60001c4070a41d01c200d071a400c0b217841286420b0021680711400031400701d0300c0801400c254541c000d0740c04825412034011070040304078200480041c10401e214600800c10700842e803030170a031289020380b00250321184070004100c2141244280c0e20013800c0d003a40e07015200b80c0e039110343d104031048089200396 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 722241052 1250 722239802 722239823
    0x307122708030a181a1506031302010f050316030504050f0319180b0f13170a02090903032208090406090b1309031407060b0604030b010f0f080304140103090609 70
    0x844005006068007200c103001820403146044d40e0380c28140030390082d202c21000c0c5c0000010203030320020300e405086a1001d00050340c0e0382401e40d40868488103040c8280c0c003280143c03090b80c1e0b00ca071207101160b02c640d8205410800e000700504d0214060300c0c0203417046d100762003070f0030b52001c0652003440200421241001309044042c490580509841c8201c186032444540602c0c0030415817068030100c82c2149403d10410f561046000f5180e2040d580582041d01004500070710840d0040000038a1040940200c90218580e60b4000f4840c1d600d101c104e03002007004800718105070950003c05091b1401c0c0f4031034103426040c0500c0c0300110301140d200d030f4403d442294541f0a44030f032500b000c800910b06180300780d9080c40940084e480182c81381d102d940101818420001c3c0c21001d010581c3e00440140c1d02c010000c2e83d0712640c9017403190401303000703001d42c01c04030720384900000c0d004203d410310604aa42c0c86001c1c0d810f01e86004400e520b47d8480d03030602d505050701d50083d100010990302c0340b012a40d00c50384104c403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 722242302 1250 722241052 722241061
    0x408150a060515030a0e0715110601050f0f0604030b07020703060c0807020607140c060406090201020730140616080106030605010504090914061911030712270803 71
    0x1000180954011524141050107903449460000c08400c0a24151581e603032245c0781400f0045c0003124031140346004203500810080e0b40d11000f0303007190010303549260f13042001400300c82d1108c01c00c2c442c507503110108001d900c0c101c0c1022070382c0100f508401080b0500305540d0749c640040d8000115040c1e00103070491141171003040a00c2c0b064040b8000e207850403c0c168609034101954412020340140700740706a10040300390020b007900407501d1740039401701510414101440c042014010038941240580a403920104d0b5207210505e101103d10f403090740b18184d002c000c442c1c404220305c2038902a80e0041085908075216101001282d00801c00c81c407140503115a41c50380101000c0c0180c001d01d007010300340101000582c1e488400d880907078001c1000042d42c2702c80c0b881d1602807007440403000ca645008250403c0403880e6942076150611000319014406030712900700a11040c031084901d80003003841c0080f40107400d65140c1c0515090018074a22144d80d04030020811110700603820112104a800020017 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 722243552 1250 722242302 722242333
    0x1c0506090c0c060a05061f051308010b06030406052d060a1401050403062a080a0e071203050703022107150605060702090408130f50060408 61
    0x540c407a401407803241c24800295070864442c80058210204035403214007140007030356008100b2104851b04070910885a4242001600d240c1080010040c0c01c5c1c0100030000d00200103021340900c40c5030003080c02d4619500c540c0c400004007030141000340310400e0304510341c001c0201101135800b41301078001042c096140a0341004410003450300445000c0281941460f650b0b40c02c503041d03500b03a951082000c100034000042400356941204c02036081202e042020b600090b420140c2240140f11310401070003d0f50b000006566105801c4c810080a4114102c2c90f9000c01d101300050410141300b441035540141101010040d541c00d000c4c20424100e02c00100101044401d01e0b191480c102400c10900007507142400050349030099100103801901104005401c000c0e140381194000c2600d4050b02074800d132103090042071403806001d5503100c0d652070089118040301003407089291182c11810900800c520000c100900c01100300e01030369400c603500215850b0f40d20349010f4000303420054020030040c440040c0c00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 722244802 1250 722243552 722243569
    0x90801050907120f080f120a0b182703040608060a0b0a0e0609060d0c08220f170d020a02010902040609021e0c03040302060d02071e0b070305340f090b1e1c0506 70
    0x540f1801032b44921607888030340e12000c07035071000a00302c0503c1881c0900c01c042405402d035030940f800601000501040c031540000750b85014950070340300b01d0b44003038603060382075410301c54032920b00302207840114810314034a407503001000c603044045d0250342042030200c4400300fa0781603040e03c48042003400c4204002c41d1650b0081e608001011003525075201105d031140761514031400b0b07021b48510110b2444903010f030085800c440902032612001c664421101074000d009000c4a14120302c558100040041d1060450094030b121880d86140c042918040d0080f8800507848022410802d000a000000142c3e03580b40142c04920700801c400747e40c60300c40d46071075404803020002d0040728003415142c640110b500321041992016a5007000141500c2d48440620180003411849001a40d0000052220043c40c00040d269090036143c2140c442d40115090760800d02a015281c5040303424880706031015000c0340c05074646062140711528144a0000311036403d40200b08940d0010307111402d000c19418550071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 722246052 1250 722244802 722244821
    0x3030215190f05061f140304060603020901030506071e0e1201061206061503050c0a0e0102211c1a090a1116030908010b0603040b040201110706090801050907120f080f120a 75
    0x10082c00c5001c0c0d040d0144c0202406c4001070350743d20000c00090100f01c890f1f40404080c5400800140c0203695a00d030580da01e1004032440300004010903000f004000c489824244642c0c0d07152500da00105403202030000c50588142e145200d5900c4010000d1000b030303a039004103409030288401040c1941080203045166030040c07054004c2500e00707000c0100050f088000c0c4c031403030b254520b80501c611b03d000e80101e01c0d00300001d09440d40030a0500c074415801e102071004000c40994200f010b0355003503141c0ca694044550310036070300c80268005c0701e242d90140b522409080e03001000140006191540415045c001d8008500c107404050903034855105042d040401032005090f100d009000c0d044941e00030522502000d00010400020000454210382c0a03000050352071b1002c20440e010190b88010080602801344100915946880d000c5401603a0101d4038805840d0000942c40442ea83d03666062075080800c41c00307032060f44040c440d64800b6031101c2c00805815001134158401410650380010444140d03a1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 722247302 1250 722246052 722246089
    0xb0901030515090c0a09020d050a0615050c030408100903020610030c050f030c15030114150703180b121b03040b06010e01142205030703030215190f0506 67
    0x1001000000c500284103600030300940c800308020740b14810040d18006180504079800580548003040c00c080a5029042c2800780400a110310340303031b000700007088581c136004a10810084a40a2090900402c0144018003000b0b003100e11f8107a81e030028904000713180c030061039003603120b908080c2416410003519812100913085554a42e00e5540c5250002e030b890b00c2924010b000c1308021401c40d9400f40f011100d110000351068503020341c050381490352030340240940740507841c07504c0303158000342050f103405044503000030b0074107103030000c5510144c40c03400b48070110701001074004c0d8000c1a180d860101a02d290361240d10380c010b050901c200c01e01c1016070000d13500141da103014402c001c081091713491a0b9410060a00740086010200d400489102d6130804480b40181c000190340400b100c10301075448420302640624595990319001010b032a00580d00c000780060344603030244001c04654020403600200f4007a82d042d4907003501175a01c001c2e01c0d0703900403000c1302c80d55480410260341008110030f0750b00304594 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 722248552 1250 722247302 722247319
    0x30c0a121710140a050d0609060509010c05070f0c1503020c0d0f02030a03090203070f080a0b01171b0f10050901081f030f021201110703020c01031a06090a0f080706030b 74
    0x1e281d415400218407070b0000d030044901030710030f158848241040152401614190701000c50b4180080a05089102111003c5c84c1000042c0302c2141032042d00750794001c5a640b1882d091960b100c21190080f205e800b0307607001c5524280003443c02c0d43d0500e010700504103510301503141d400d51040c82d03080080c080306190501080e44542490b90b9404030442c0e4585403181000903082401d07001084c42c00710540c00c0b81054046080e00420990b50000e0110a180d00c58041c0ca07525a0300c654800894001c681c14070007c6900c1504500c08402d1512910204580044d21144504000100050b00b001407007078280081403001502210300c3d64080d81c000d901080c00004010741107602007600b18401580d00c4080c00010306680542c0c21035440801e00d11004401000901c441210300c4c1c401072050340850801c80140c8151011a40194028051511140010920b041a524a28051040d10740c043e50141d90f0005e0000000b0035840d142a130040041c105600c024001c60f41442e40c054122801414a2841841c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 722249802 1250 722248552 722248561
    0x5030a08040510201e070501090e07020a1a040302061302030d0f0210091109010f03080f07031e230c0705041808271c03030b03030c0a1217 61
    0x948110790840301c064500b41c00c1080f000e54200e44101c10b10761261580c460080d01c00c80c4000b0009103030307603140405080d42c96032030300310310961583c13283e042c4641d5001c59040242000b5011000803856400907250054030b50107056a551303040f1141e60014a40b00803c5110184000d2550401120354002c400c1e50303180000004c16000241d555038403800040c2008410b0026910141c400c1c400006001d40c0c40109004c4038500d8500140c20304460070003035006070440700000900c1d80c6455085001c0781e401246075442d00fa10004000581e502c940380507410701000d20544140a009a8090f6003029110303556001342c850350148484268241030300551080c41c007404080101e540114094007290421500029480b40001c1c40f444c1140d80700710050f00b051404103c1140e43e0141c03070803090782224094508070701120140c04022281d403200c0a0491685000e40d0448000b0340240d120020b4a00010100e07400c1c840103e02c200d14111900f5400c860381c10b481140c82d0302e46a0003d17a020100c0f0802a541e20403883c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 722251052 1250 722249802 722249813
    0x6010819020a0c0506010f0303030e030f1c02040b030f0604180503122d070f17060f01050d1a03010b1002250f14030d020303150d06150e07080105030a 66
    0x852520440c016a40090007003500c9004085080c8507913480720a880b035540e074030104031652010610041e8080390030210a03840c0c07901d0100480d01e03030341c03805e413816400d003509406905c0d65610010a00c4014507400c0202041d04480c000240d845020250868401858014140802e413480040100608406049100e00089010080e5240e55070007114584995581c2080744011050842c041c030302e20417a807050700641c07207041c8200e2441050b05440700e03401040e99800441d041c20008000c02c1c0d180b05030101140a03481e01900c00250400145811030402d03032400200c40403580081c1090011900840c8140140d040070702a448e01000701b100c1081801e511554065182c0d600c58044003030f84036040082c0c01002c8440c00c0b04101805126030140da41710380350b19000d1b90b95014130055030f100e8442d0078400a005407001040303130310a248000548200c1d04c00c000500a40004c9001c0440d0115103802181560000f45c81c00c02d402805580c5001c8030605041c44044c00c80001078010f58020b8010a00441c042007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 722252302 1250 722251052 722251081
    0x1505120120180d1e0f1a0610050a0201330515040e090a0606121a0103170903011e02210402010807080a090203070312120203010e151212070b060108 65
    0x205985064009241e403070144c81131600341d15403030030080700c0d92001820b1154180300d14402c9441002e21031403050f4104407120304d20000300d4100c0d6210079414251611144030344050044000c0d240004161401a81d191380d214030141c64100480c0d845900780400f0b22114071150a00500e003e03600c2061268455002206500c900c1c000c41301120342c41d00102e24600d000304100310280b0b070024420071440761204458442a00c488405444203090f18040503450610301403c1c6041303a81c080c038541803118503c03040e46480e0f0011402140e0555950300c41c42c012506500c038080ba060710054005950f003d42c903c003401d00070052006c3d0120104000b04100050742c105481e687c10659500b0320301025521510031401600341e050000f5010300445100000704105800e20382500c0502d0f40b038407000701f100d00034400c08030301023481040d01510030503000c500d04441d100e15400d86290040c0603050301041d02c1c2009440c240b4543c00f481111040041c0c20f509110101d255141c000e00246011a52070034a80c1500000b00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 722253552 1250 722252302 722252347
    0xb0906090d050c0703030f0c0f051b1002060a05061305010b0a0f021209040207110d030e090c070f0219081207021302040b03370504051005010605030a1505120120 71
    0x444032040d04440e01e400342039507088c0035a20410702c0c0841c0c245440e1250700c03120076a02401c14102d4200b03440c1103900d40801200a409900d13402001075995100412010f13000182c400c6400c0003800741d541b00c1039213071805554040c1110115080e0780e0b081d056001084083c0045c0542c04540003024003002b800d040f03e003200c0364014100d80150b215036441c249241c0c071544501c0315950185c02001c002c2c0815401003c0300841c2c0108444104155aa40300100101c0c882c0c000010150741c959010400149026001d20401c90f90380c4080205550729008001e02e82401c03c800a2549900410b01c4804c61429095482c1100784000042d4106460140c9000f03c43c00081e00c00000420501c48801d2a6000480000b0030714000343c1c03c24038903034600000e80d0010203050783d06658901403200c085480c200b0a0042c58100d960990315540b5560b074000d0740340014a1600010650340c2c9454800050759a5084030410040c0b0011000045201d00d90849035891001d2941010340d00c10180b080f0b142c0e0066000911210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 722254802 1250 722253552 722253557
    0xe0a0323031b03070203040f0603050f0f011202010c0819211104060e03010902041503020f040b150a090e15090f0601020d110f0304060327050a0609020d0b0906090d050c070303 77
    0x70f0342c49000c03041e41103009580001680c503030845000900341e0f40c10740105008038844054542c0320744807280901004102405413452400c404080380d001948542e5840b40654007555489082c080446c002c400c81c0360515041c440011a0210074155078100502005104210300d4004c00159002c0c1010f075046015910075030b0709020041410894685003900f0540718182e0042080000c60090703242400203c400f80000c0c1d0240144001c5841c0c0c03400c2a10a54880d110300821161441600000d030900315130001c9900004c108803d0b50000f402244e134086907010705100742e41c01020369044818001203010082040340014520300c14400c090340c001c24960036100491901c1111003882c1000c107171a1400c241100320303040c8400500060580c4d450780c400c02d0407000e124036070800b01d43c0310030803690300501460018089810168443c00004e40355800022850320240c61141b014400751643c1591010880384101c440d007000d010130058007014420024280700c41d0a002c0d0420071082c104503030fa2202070000405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 722256052 1250 722254802 722254807
    0x80c1003051e0907150e03100c051306050d0b0105090117060312160c0501081b031003021c0c09060f2c010303090306050601170f04060e0a0323031b 65
    0x702e402c080c14074088801c049072242c40103070414103411139603484184184c8102c001200780c19180548a03810f508002d100081c010010504840f600800802a040c0d2040034443d007040120162400c00d5403d1008102e140c4403d5140e5901010420a4584110150341040005c1042048c66030300840c981c0ba103c144a4414500d6a9030f8101007850080d041e03940d5817142c500401c2840c844044070300e1948015115500c24851181c0e90401910128001e80b0700f440e41030070521050400c1410b0300060340d40258500b50204650343d403034010581601086440303101441ea0b5190b100240030b00000040001c00d40544100400c928040728000035110b41e0180c49200030741d4803c100d00b6200c11100d100d01094108030f00c0c2c010355130340e46005030040030507100c11965541400d00040035903020b00315654113401d852480f919680c0c1d50b002420300e5150700400450f003041d41c0340c5803502c007280c007044000c9005110f40c8910075a0380c00703c2504040c607041500450320009041080141c40c2100c0c1c500c41d003206005020264 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 722257302 1250 722256052 722256061
    0xe04060b19080601080f060403052203060e0d0905030c0a090203040615260d08180f121809092d101a041116080d0203011e080c100305 59
    0x40038400d0142401010030300220010800d202c2c04140c03a1304844c0300b07900b244da07a81060300407161548011500a80070840900000d48502c4042e020202c1024500c81401e403160b0b22951600708450a05602c0000c0d6440180c05c01d00d5a50003020140c040c12046004003030503469040001c2000683d8050340c4081074000c0041000c00c52250004140030380a548001d0700c0580710700e2000152024203171700a1030201c02580000b807134040850004406c001c2550713240c00036554050b04400d400661190040c65110b800396890f01110240080c1014050118107207030756010828042109103001c0d41407510414554060101126000911503580110304400d15030042001070340a00880e50191206600e01036030700680c11080c0150301c031940c101d8a02d600340c0101c1800b40e05000c2220392180d13010030ba00d00d00b0800302083c04110300080c2441880303114a1440c0800030141d24060360001ea100c0d22160038a0a040c0d00740c012440c03031070005801c0c00b000030403c4128200004a40b0300c2071801003810315984c1c40c0801c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 722258552 1250 722257302 722257309
    0x150f0a0518120a12050903120c031014010513090b040f1a19030b1518130305180415080105070c0305040e06041b020f0d090f140f1207050907090e04060b 67
    0x41c00607890665017040203140c0b004503103480742d001808407241d219514002842070070003078054030300a21035074019060070760400c01854421840c0a44060601c8418400c820607980700002d080058000312a0200d030f0041d080e0184020b5413600b00c10005058142141186440d1030040d680c1e64103601220401e40d0102c10180801a807a00b580002d403a40c8660020410210202104142c5210060303e43c0c8d94511170b0459200e00f030740c0042d144c12198003100101540440d10074805086403c5030066505000c482800000e803c68100e002001c1d01512004410083c0c91403e21a840c1e000743c283c2002d0206a08990700100507103c0c0740120102c04903070901044640d00c1341e0744140d017242c5e445000c01c44c42000c500c0c400795031020741520104517480760510361882c141c4209011000c4940e0300090180c0e01d402c00503120301c80c0700c180d03100c913400c01c003410480a0103580715030b11900314480c444058422941480c0038040041c500510b241c00303114003014100200030171002c01580c0036400c08400102c070003404000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 722259802 1250 722258552 722258567
    0x80106031113142e050105031501030b10021e030c10020d060b030a1409070503101a0a060c0303050604020a0923060d060501020c190e09150f0a0518120a 67
    0x401d0f0140042c81080449850f8020710f11042c007540300a0346000c03040da0412101c8251a00515000070014000702d1b11040c13101940c00c2d1704840504010625043d003c021aa0f01c403103c4110f0fa006a00800c03c1b1109181c0c04034130004040105030203035113800c8254096a030b55110b0b541900041c0740d03001078021000402c540c45a4054591110101e0b03503401c06114100140240b43c0c450b110309560b00c070101e805c026001404034103e03040500a008010305596052008003e0400041c1503554882102041641c03107100c0c0034081c001d2605d5001401042e03080040403100010030b030b40e0140780704020408500e42c004102c90129148507070540d9114662282000c00520020450364015401042c44a840e4416410400c00c0d41d80a0342154407190b061000c1002e1303088580c0b0301c0c030111007080030309000d0301001d41d00c580c0e8091500700c01c0352a203004a1085c52420310045544137448000c4006000960040d030041c513401180f07c41e5646100807404101c01d07200d0342c000403482178640340000d0380703411907001d80c10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 722261052 1250 722259802 722259821
    0x30601050d06110a0801090c0c0210110f0124080105070504121a0a02180910052b03030c09051f05031503070305030403050d0503090318040906020c01060f080106031113 74
    0x3d85481d0801e2075009400c6180a00076440c8042c202150021814031a5043c1c140c0c00e40c00030071f6140c8507040044150341041282e00c4526190041c44900303407202209000380385424003c81a8824070b500d400300503651105154202c2181030b4186030900103160f030b10001f074406827544506080554041d44c90181c4011004607414400b420f52035042000e081c0155010305400550b0105448640f81881d04000190790300f110720104890344a02c00b0300c4541480280c04911005600c05076003070300115800850f860048074401c5000946a02040c0011036022100100501040e603001810510407171000b91181101d000071401c015002c4006484c6480058480c114000050180d840f0b41d604ca061040c0c40b80d02ca40000d039101d202d2002c114a0f0340c1e1240040364403810303208020318204540d01e0408807882d0141407450741d000d03856181c00d00c0460018801800310b090f01c1c000005079207180030b1040c8581440b9910900b07841c1d15025040001c00c4d905241d09075403803800c0343c440c1483e440034148c920013081c09030b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 722262302 1250 722261052 722261081
    0x1030e070821160c0504051f03082b0504020312030f0a0f2c060c0c0706030c0c0614090d0f170415051006020c040207080414040f0203091f0605030601050d06 69
    0x2520f074014403040c12101c0044d40d40c1502c09009903603e0181000031040b2a4000425105040303508102080242020700300c00d03e009008501c07503e42c80b80111310300d200b642a1548130b0f29561400e010861804000c4900c2400f424a415803c500e070a8116420108008002204641d11441d40c4265449036034003201c2e40c0b400e600100000405240110000c1c14450549002c1038483c40012400d20041a016240844050401040790504000d411405040c102c1481400d000c85c10741c00c1070000380316008200f00c0b809100483c2c000341c5409181c1d5460044003400441c28814002814600186e2003400304100501c1e0280700985074a0780c2c80d021851b402000038898103503140406015000030607118110468495901b01c41003620580e01304012480350150003024801304020411511603a2200a0000000100005404040501240180c0c5d00407181e940486e041400d40e4501031a410100820080c26004100200360034940803a83d1200103019552040040c4c0911070100106904006651714a81 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 722263552 1250 722262302 722262337
    0x6060c0c0a140a0806090304171f09062306040b010c02030a05010506091b03040303270c0501121b0c0f080c06010f2c060102070b071101030e070821 65
    0x440b0011900b03001d24142c03d2003120790b0180081c6264000544901950121002c2c510703103450035925501000040d40d054500f80510365840c2520401d9032011002d2480f001408541202649020022240e05690200c3c80458420b50342c407002e50745030762940d807080007501c2c0020755150707600040c2c4040a0318003000350703d88110607004040140640000c1d0055009885d25640c580390b80b01c03107401b48011103a01010080040c000100800d00c650054000741042c80100c1b01c0306524045000301038601c0d40400d032219203807014104121b5900c80c501f070322090f0302c2e090100080c4e0040c014aa4080302c0c40c5010700100b04c0404140428450703087c0749d800c0415403220315643d90f140280501901d41c0401d103d072140c040f080c044009211070112510f0016840d1008402120028404000780e4100010b014541140308040300403940c0007050000703010305400f80c00000c155940040006054030042249158a030304010010425020000f54000d0400380c9800020288407107a00c82d22118002d41c2d40d03038803800004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 722264802 1250 722263552 722263559
    0x30a14131e0302030d02120f0703090b0a0908061803070813051e090c18090414010e0c280b03070e060d050a0b0a140118030b19060602060c0306060c0c0a 67
    0x12182080c0442c0d02c250300756817078840800e074140d032180d018429910241c1010440855a01100c40040c040a40719042151003507440f8401c0304000c0d0402c3d44140046024484c05220a003802c020f540ea105c101c0b2110b0321004c08541c80110303141d026921004048030800b06400310b0365448842002c01a040160802c1c1a00540301141d441d0908801000c502410410b004502030000c400104c1c0d800ca200400c241070000440c4040c840c503c1c00c02442950300c5155100d9002c8050030038000c0c000302a8402c001804010001000c021501104c20a07840c03140070f180b842035000c1c1303030145601c10488103032032502c6441e9a908a02990290500f84c40c0c0d9130302c40000250800503c01540c8940c0c0074681880b070400800c130b030281c1406440348150140e40d24a0903e0001001558410901c2c0d105403102e0354100340c98560343e0f40d00c0c0f062505040c5d0300203006030043d0103034840f000078038850000185118801418642401040f62945100182c082d6004402c00104107800e11810411403807105000ba15104403160b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 722266052 1250 722264802 722264849
    0x5090f0f120c121611040504020a140a150f0912050d140d06030c06030f050c0306040b152b05010b090f012006011406130e04050a060608070e0702030a1413 68
    0x8071000444403030121210005c86400e042c42103a02c1564050103091207203040610a10302c81042032199603100a07401c401164140310b40c44071310f0150115172501c015107a00070102402d4801607803c100d042c0200a00310001080d80041c2d0314102020a0400440c02403c1d0188400707244901c095056510381844000810440414043d40460310140d5007080400a14078202040d00e0042d20224407960050011070310703510b0290b001c8003010a000b0964901b4071103501161046810280340341e00031650380e24950103001090024458090030b00c03c0300300440c0d818185409a1801340311440d50141146012081041c1d004007402004494000c0218540024079030300306030380e01000d0040000d45070100c094464135080a1056130f104080510412083c2810040c0b808090b6400030801d40e5240329420348280402c4644c4a0b080c06880c0c03c1000c0d01c8414100780c0c0900e03003000054007440c215403040100c1e00102e540560a00160300807e20459543c040c033000f003401030800c070b07000381c1e08124049860541c07424 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 722267302 1250 722266052 722266087
    0x6031216170a09080c130c1b050304090c0206161b0212100606030b090402040504020a05061908060f0d020108040203210403060605040c02030f0d020f040905090f0f120c12 75
    0xc4a0b81d544180c81c9481e0000603881702a074860715a000038100e505072118403825085042d40341ca5070320b81003c081900500e629000d003203002d41501c0c2600001402e11078001c0754080c0754402881400103007442e05200000890076800303502c1a00400144041e4200024007130042c440c8280c0d00100b0305840e548092a0f040d4540c6031030300b900c0000c58a08030740040c91600030300034070101c00030007454021156034075024131002d8100100200d91000c280b5802195546e646406090303604005005c400c0d008000c40e002900c1d592024200c24402c0c540c0030792150280d40da41181d000056420718016031183c9591000c01e203030030040d8010260f0a241402074410086003000500100e90041d83b0900c4900d6540c01844215a490000c0d0740068208010844001340c4100c010b0201840c0e18100501c1c0030f8085181c1e4100340c05c243c00251565031144203005604904000c170880a03e404c00c081c021031440f40030219903c030052034000d05404c801040520881000740032002e1400500090282c2c1ea110a0406408a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 722268552 1250 722267302 722267317
    0x115030c1a0f0d0506041d120c03280206010519150c0204050112021f140a0c0b01090b131116020102010f050708071707080606090d020a060306050a0b030603121617 72
    0x154505101091142d80c010080010301f2880009462040404480d8141a5104018541c540e1004010702a40c042d0242084407101381020b912034051300903020000d09102040e0700080c428010302c4040081e0210140d424003c07154146201c1c0349404256505980780116400f001c1c1d8850f02d080300004880d0203501002034030714421545014030142c00c0c1c650380a904408041800010041031041e0280d0300072034005c251001c1d107420004880d45481d691140d0400e401d8014a6020392140d907042d0710703410300a030b4080c4a83d40c668405e011107103000d0002c103680c0c001c003489000e151401c8131b103140035a4002c0d40205041400c1050902c201e1519010240005005a50010000304503851101508824802c000e00800c026520046240c4032001008195001400e40d140e1000540e40b800005030340c4c211001d00280303456100451254942410400c1140c425406112018403c1042011a603008140d42c1311300000d5a845a4840d000700440807100590910014409000082d24080610020010304203c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 722269802 1250 722268552 722268559
    0x5090d0215060d02010513090b010f05090d150e010e0f0616021c121409011107030c150b0612150117061e0d0609050115030c1a0f0d0506 60
    0x60140454126907540d0100541000414800080ba446240034000c80742d072103005151450400c00002c2d42e00c0c0c412440342e4044006260749080c51483da58000c0c3c1c2d000030502941c01c0c47c500342902d860225012103c9001700421128905281030f40707800300c6901400340c1d038101750020454100d96859a903503440e02c042c4608114801c40d0f00041c3d01a8254030202c02008585d4003030612184800c0b201401040000d1005040c400c032115003e40c00201841042d98003503110f04415a541841c0100c1821103d00f41c3c4c1c0c0140b007107010403008003c640c0020040b00e100f03034401e090718440d45129420074001c0814155985d800000040d204100d641412041030280070400c1c0303800c4841c40c0410066800703000701800d4000700c0c81b41c000028a28a8105400002c92404005d200f0381c41c2c00d41e074002204040501c01c00c4036019134404600c010310100348512070501804450342420706003103444d68030066100c1e10400c801a6500100c07001a0b84060068920714036070b11380c4007078481002e54202000340c441250810302 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 722271052 1250 722269802 722269813
    0x9043203040603090c0f05060409091109040b04120306290f030f0708090109030f050703030b1009030308010b03090a1415070309025401060c1b080d0507020f130509 72
    0x180c11134000c100c2c00451f1002000d4520700383c0360018510150000480654404100f9000c0119a440b6100d10ba0700c124421000c0456501d404e151858007200c105160008140c9044014481c8101001080c0542110108260031462503c4201241442800b540c1e4400000100500540c6484002c49501030086901d031725880d65101c03118a030880d4088000500000d009100080d50540174a000b8490710f80640f070080b50100035800403c0d000c0c2c0c03411004100051424004009040e80719502e107024151808146186003400313010b41d44d403403c1321540030342904030b5a09242000d4038204401013480078080b00d540601d1800b0305d0003800034000808142d0007190013550700d0103040080040143c20660861001d603005c0907000143e000c030b00700e40c0b0410308110080c0307480e040d81400c5240024005c00c01980c03840c031054040e181500700d813074074001115203122400b441405160008202005007a880d464078580b64001400010011403805009e0364010580b141c4030120144a604450300c5441c00204450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 722272302 1250 722271052 722271059
    0x50c130c080705160f020f0d0b011503140f180105010b0901260f0a02070501092d03050913020f071a07020d140d0e0f030a020c09043203040603090c 65
    0x22001c0c4100213940c0c20320f1000c0020100004d00e80b00201d02643c6c0042c21484021500d607001c6180c510301e04a0548616218000410a00441d01c20154454a040c0317802d10610307080c400c0994801c0005400300c040d404002000400018000c110003080000765402808156507401d26120550700c01d542c0c2c107002405003c00b020050783c080d04803000c0e043e0580300c8881281d42d40700800d500d80c4400340020070010340800a03800410802d024a4400360f015029420504070001c0081800c125004403020110b064007481501003070b0041d00b601d955240031348200c0346d001ea00340c0060f0002d21074020200c000f6100420030206000328294011403015001c081d04410381c035030f2102a640c0d00c141c961450005011607071114201194140078191180300b01c030300410044400d8603042c4c2040c00c10140301c50564400b2540f842c001e5410084900030b00001c0d034040b00c06003019141d07240003030000c03101110f140c90b00280e942994003020164000c0303021404280da44803510ba20b40100684a1049c098032204400304011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 722273552 1250 722272302 722272307
    0xe1b190c020a09050c0d050405070b1201090f0c08040605070c120519020708120c03041a13050a05011241060406050d0b13150902090a05160309050c130c0807 69
    0x5019680e61700c109403c120765240c030203015080003881112240188140003454140781c4024105007a08015a024650705040c0400304459196a88148443c140a100c3c083c030758000c5041f030313041600301602041c0356445100503a00000c4a2000811105080700c4118840d94041c2c090219a4071001040c800c003000084100e031340f400d5034043c500241d0003961402c0c0b0601c444070001c240307403081041542d00f059910607010304201c4904d59554100750000131f418400ca05410ba020340585021518004000d08140000300340326071031001c0800c2203075240f02030810b031400034420a02e00894210004074108200100c01c074680d800b01c518000c2c0d002c201c00410704915150040038144e58010b40380e010818840d1712070700a4a0000f400c5680d5200c5101580400704141c00405420520360300008655440c1c10700c10700030200e6001301240c85040c50324062140090a00c44110711041840c80c012859807280e0a00c04d04042a0030034465105185120b60441c44007a50454504484162121901540ca03140103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 722274802 1250 722273552 722273561
    0xc0510091d07022514120d030501032f01050c1e030a02010e1203070f050f16020901050105070c140402090603090a030e0d0506040b0703060312170705040e1b190c020a09 74
    0x1c040c00b40f1030102030005c044029604d1800c4030004041705049440340c1c1542d130038140202d5601e000240c54a0050040c1300c02c800d200310039094044500690f04022200e00840460f01340202070401c03c0c0010300010910040120010b191072507444c1601034868208026680d034400f420a102550070040c1100c1c103002c0205203901e031164512095861039607061411600c28400c1400d4009100d418880054940210030290100000d9113186488180490041000708a0164000313410004204840c00c002000072501c0c50072200e400c55408c00300030074030b80020007900410005580004010007042066140000c002c04ca090280d00c0d0f20b068900c0410510103400d2805001810561101c0003280c0001c0c419000d595100e240c0d860009000383d10381e6590300400f041172031000c0000d1f110b0b6254940500e0f210f5042500303c0400e0500d94646840d1000c0960700748002008080c4038a0110482101c80e0342c2041100c03111085d00080c42400301200c40c0103444503580c0c02050340520100e000c0840c0002d500c0c440c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 722276052 1250 722274802 722274853
    0x903070c09050405070305061801111804090501020904110712020a0b07052d070c050a06020d03020304170f070606050411070f050f01050a061a04030c0510091d0702 72
    0x10442840e4103100341800507140150007110b5501c901c580020100b041400241d00480340741136107212035140c0604903400d5402c030000640224008110508841d00d03451000680d59500790390210300e442072410030700d009006202804d43c1090502c01d555120252101c010401c036882065016414200d0200803070b1341d04541032004228a0f8107101285609001c3c2c40a804030f21800440130050340d40080300c49840000c82803c0602d442c0020a40c1004c005060110401402d0183e07000d02e045460301d8130081d59604141024000d240e8000017160910046103170824000615598051ba04e0859404146056014040c00d072600c40c034182001c220340c07030640650316508040071031042c184441500c90507040d02c2480300443e09071081c100194030508083c010b141c8640350b00d0100240c080c0c42d08902e11070415410b440d48240441c200028030000e600c11000c0d4040c0c4400340c84001c0c3c0034441a4007a101c040458001822014105030200042c0e591010454850b003a95405c3c0c0d140c0548880210032440c04404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 722277302 1250 722276052 722276063
    0x1305120304050304120c1a071103010b220b121c020606131d1b0a3201050d060905040303110c0d05091c0b070e030312010501030f060506160b090307 65
    0xc802c105945e450480c1d43c3c80c0a0250240d070504e19610310414800d03412080040006050100300001131051200d100c2004031425030003400715103d580f00017141000c154007017911041f0441104100304903994407803042881c0180c10381d409038402d401844d560302612040ca050806e201690610118400b00b8141c1c01128080c0070201020410b01051016004880441c0041c101441d180c0700c6202c001c00c00c01105040c0c090f45d4041c10b0030201c2c18010f20040d0313500440140303c2c0e06504920044900c0e2090310f00c00303a40c200116482c8400c01f0040342d062140c00e000c030070010b082080205040c201c035845240641d110b610100428040c0c51a0300c00c07180191b0300810050b0304198020040c40d4011001000701d2080207001015099400c0f400540403810b010007038030340004460801c5061500803032128600d80d001c400850400355204505402c45005001307540c1016140c0a1403211000180c05c518042c00c4020111916030600c44c1d0220307400d403d01d100035103101c4021004298002c1c000b0045404154010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 722278552 1250 722277302 722277307
    0x70f080606070f0b040308060301050601170c070201030612080301360f1107151808031605090d060f060b0a050a4d030a0c030c14010513051203040503 66
    0x1410041642c1110714151400002e8510390000038600d0040180710ba0b100361583c142c6030512405060031600000c1416045c0701b1102c91601c80400001d000b141e20000c1d1628180d5689100d10048000c0c00a55018090007610301300264100402540558140c6054942400007121000c081000440b43d1991116400000400c1a002d90105810203411400b01c0075000c03074552411403403600580d11800f01903075204c000c84e04a00010fa66400742d809600f0220600c1200281c0350340700c600c214800074207403041c0310301c481c0b641851050148085d10b10407000203007504494410383c102a800340070401074a0402600d44100810030005100c1502c0c0c01c021107980302414184031000944541a140007680c51002c3c0a0042d503c0ca101c0d141500440640410960091525803400d072010b01e100c92880038007141c00900071580b4951b44a40008005901450103003000388030b5050400405012049020495007420100450340440408800c01c04d84038038115a802c01e2a0004000316000907680140150002c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 722279802 1250 722278552 722278561
    0xd050d090c150c020102012016030c1b030b090f0304062307050307202b0f0606050f090c161a131106030f010611100e0c0405070f08 58
    0x1540644600c520848210041a03101c04038007101d0304081070b10500180d01d001c2c800085507420300909003050042e000e03d281c0c0544807981130b41a4081d07100c004089030300c140b422105051240181e084040c4d0080d03042504580700380c00c3d0051035031660100380c0d030203002c54010a0b407500300003a10132042d0740348401031400c0c1810440101d07220320201d200c913400304503c1c0c040440c01010280c018015188203100459456081c1d1800891b9a410a0112406480003400c0d54032a500c0307000c8034400c686250203986120030210310800e40ca001c4801400742050030100410340400070154400380c20b4620442d00324910b04904000c2102c428001c5450744040c450034002d1100c0199030800c0c042009105120502101004040c080e290381401c50380031003c0a8503c2000341849031012062000c0d00040d61401d00d07518080d4074920400c8010700c00c0400b00541110000b9502e88184488140303900c8000c001c0c0310829480704600e94510780c2140c880e1241d464100842c1c026400b03542500f054060356141c000640d0380c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 722281052 1250 722279802 722279827
    0x4090c17010b0c0c10030e0f0303070906090807140103020d05130203120a0507111809100b040921030609090c150206100308030403140a08041b0503100b030a0605040b15030d05 77
    0xc5e1403041e50034103486540d2170481c448244003048080402100554403490040c0d4010726529480d400030b402d0104641e8103100756107010420a0550704401d5101c0b070040d50840049000b8411414400241071508040c00011481c010032004024000c03422582c00c40013188411465100d40c2080308086101004203000240304040250846038004201c02e1030b8001c00002410500021903149000790464240010070300d20700e01ca182d181040666040001c40310b40e41e0b2321201d034a400102c1c150100c00d9910091201d6200742c10401c0545013200c0240000030640c0303884640c01c034071402006800b40c1d8080d13410003154400203d0310300c0750011021480c2d24502c2e40d2180526684081d01c16410842c0c5d201c1c0d04c9000d0701041d001468072511359610b45050340307050b00f0181700e0000740114034440315122020070002e59800003a802a00540c0c18030000f03a600740d29001910341030410300000c1c042800c0404010074031900041491141ca00008602c4110005000301a240d4904518010100c1ca05101c0400c0022 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 722282302 1250 722281052 722281069
    0x150509270c03030c1005090307171b0d020a060b040203040c030b0717040309060f0903030816050706060b03240108070e010c02040509031c0605090a0e0304090c17010b0c0c 75
    0x9403068508001600d03002c00d0a662051070845490792009544254000300e611402c0d03070007402d400140d418030130750b41e072504101c41102040354511600820104c41381501c00082c010108442d0040b80c002c40003418020b500d079824018252070342d5180c00000710060a06001b101e1003181c0c4607008072003250455841010303600e4081c017201c04008014100c0d08000807004000b9004500a8030b0b410500e034506a4010642c1e0704486c03c500c200000d51200f040002c1e003207042030b5009083c010701e0750700c0758074008400c917401c1c003a46030003405880c00d105000810102c5500211300070501e800c01503208510b904416145040d03002003d0f0300051443c1c00040d0b0052041c0a070141c48201450300c01808001da80004090f0381c8250b07600d40c02e80e000040d4203542080310200b000c40764505150f061102c1450040054482c3c58000c0c40d41d902c95407550300e8640c401c0018000c41e4041d00104c042003008000b0090018011850ba40c084507900003004004548500120f0036103103081e850200030038094084c0c809029240 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 722283552 1250 722282302 722282371
    0x5070203070606140f040b09060f0f03030414100f0512060d0203061612060f0302060705010212010602010c020709060b0703230d05040b060405190c090e010801150509 73
    0x10302080c0411000546a40a03d600030712055590289211085007040800105043d80304c0c0300d02d02d8080b40280c00d032a0390704c00c903a00100441c4e0302c031980040e001c0824441402c4a801d15458040001c1c0031591003110721000b048030109440041401c414a2001d41d0070051300309031000416001c0c00780408070000700101552003d4003810f0340b042c0381d5082d030110340340c0703a000e807811031504203032014202c0101d61080108012810105051103940d00e00141b0604056190101a0084800042c101c003848425011076080c059080d8500b42c1079a942c00c4024000c03d160001d01d001800b46000024006442c0e0140105951444145602d092031581d0181d584040c0d041d18100e0b201c1c6095130f101c1c12101550040c1c18200810000420a80340c1031900214100005159074401c0f440d000c10302540c098004c0c20000c05050001000401501300e20090701d003089075600001444010303100200b5801019080007403001218502107000c00e0320396080000c1c48000f16000381c80d0302c070604c1030042c04402c2540350a488 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 722284802 1250 722283552 722283557
    0xc051314040f021c0f060506040e0603120a170a1407030902010207051203040e060402032809231e06060d020402090406170723040c1803050105070f1d01030507 70
    0x10042c144003000d041e0713003064a444840700c2d9403900781030a00d03965000340024002c0d5540100b000d581400c001aa803405503014600c012011940011801d403810420300b0607090490407000c0d1540c0c2c0c10040148401148116075160170840c001080d807241e8a802045081d20b6010101841c03940e5084045005214401080c3d04500c02c03d540081d194503043d00c9103c01d10002c07005586d0b102d040001e101760005018004502481c030400822443d48054080e4061448103000c0340c840b01d5a00500aa0207003100d000050300c00c01012110714000921941c00996219008007078850f1044280380002001100140358071403500090006055803901c4ca4424a02502c018001400d0070036401c0400c0c100c485541060603080450140c4141d0303450304101c014014500d00b00b01250702c01e0b84201d2409410f04070540356004036220021040054011043c4815211040155036a4241d41e41000340c0a0700c0182c5580c0081260310281a0032280300b00c050100e4042110748001682900800440c01484010946800c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 722286052 1250 722284802 722284811
    0x20a032601080133060804020114030c2521030603080c0a020a15020a06090c0503030316030b190513140c040f0e070c06050c09180a0c05131404 63
    0x4240e03aa144003140a050180000201e034010710031030845450040000001041654980c001191862414041511800d00e03040d0916200ca1006a590401e05420010348000200400803c00f0070240a001e1030203002d544c40c5078804298440c9400d448044038087c00030000f0840500d0701d5064a80b00851001d9140b800090840d5680c8903000207400540c52404940c001110f2501517140012601000d00744d841d0507010030218006010355031740000b9400034009a1190840030602c888d0100ca038004010243c03e8907545d140c1540b6200e40004000001e0012074508810035800e4200003200c01c01e801e1801c049042070314105810081680c0403a003c40180a0701c070120308501e0490048118014600300c070046469900b042900074030b08945412408180400b18100078902d079000084540b150307002200052281c483c41d900000910401402a804c0301d050401e500406024540003803244d601c0340420440400011070440d07262180c40d240d140c401e400c010f001d10213039004032030080003044020270018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 722287302 1250 722286052 722286107
    0x19020f0a1203030e33060109060215150405090a0c080304060f0305090c1816021902061303021c05010f050105060f03150d0804140111120904020708031302100f020a03 73
    0x9001c40c81c045c440c1c0a075240c0d120194110715500d0340b080f40d0444401d007041d060f1541001002550341140d2200c1c810080c05040215070342015201441d12000d1001c1e00500c6603140007030000fa07130782d400144101c460b50b03048100091000b2011094401fa21041ea0312a1904803d41508801500024180356018002c61201c1d00c01c80d0707102c0700400a04204040d507032841d840c06501d88441950134001e00c03419500855900850f00d5044506040d403290704a0303600da00c8185030b0742d40d1200c041c01500300135005501d401c40203480c10343c60100490103a200c3d20090106503600d22210f800c1e62000c0c0300d80c60300510103001040031048550b01641d8011711550b8504182c488003800240c142401c0b0f01c003a5103981c4002005d20040811140f112001ca0003820001114a09034000c1075480c00d419403021008078003c2404419640c079501210412904040f410340c480c248100207441460124a040f84601070b44440c200031a4010060f00d000101650041d01480103035480035030b001007200b9000759480b1285200310 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 722288552 1250 722287302 722287333
    0x1103030108011d060103030e060a1215090e010e0304090506060d050a021b01091203050a0e0304030507080c01021204330e0a060c02060304080d090519020f0a1203030e 73
    0x25402070002000101d00e00c54242081891006021200d10342d5400442c01400407035000000303030001003015102035640d06800e00007103a400240b0310400c4411070402e09580c07000340c1111004019250030020422000c0ca20802c214201d805960740340c1d42c0c6410034841002075080701c1d403000c1d920030b601412051500d00008030880888404441c070308145513011803103007000c0780e01500d01d40c0758603082c0008003c1090283c5905054591941c0003030101178031180010300b00d84203600a20030554401c0220b07512145c032468000c0c1c84001c03d00030454544103000986003e9880024043c64510f03c180380c0e03a10b00f82c01c01d02e20a1440001c95080a0110059880c0d0701c521006441d2042d40c000041c0c2c0d03010b0f0198020b10030411000030310f80c00141041141c5110071f0141c0e8522085a4029130b10001c060f540380420107108015107040340300a0414020404081c50007660030114000340c510880b040f01d00c0200401c01c00202512038010481542c0072060401c00003402940b002c1e900c0007100c000c40703840800c00301c4c64 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 722289802 1250 722288552 722288557
    0x30e030406170f01030302211b03030a1103060d0f05010605092d010501051209010603140a0303050c040f1e091b03060504020a08070c0f051218011713031103 69
    0x1940015042d2018400c0769140907041500a41c1d16804408103500d1030310025a1407042c051140020498198851030311030b40c2c4011a03019016082130540c0d000ca4517451162240c20881c1d40545a604100201c62408004000ca03445075000400000201406840f02106006101002c64a940d43c54801103196034581186910580c44401079403001042d5030390b03019034945142c40d0340700b00c01c020710014800750fa04602130f918102a11210356002d80d40c1d00c0401030241c615a800500b0780c12408450f00750218012882403480c1d8041d8509200503241d84a100000d881540300f00e4595014000b010703c00000154032035541080d41103d030403026070300c03800c80600b05c0311008203064034000b41c625840d43d0107405004110050a00320b90450504050b548050105c0000030240401c114006d1110010088160002010031703070044100d402e80020007551a14079401030844010b841400c2d15420910740c07140307c0c40124050250000d08035500c444d0305080405040510072020700419241007100300900704003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 722291052 1250 722289802 722289809
    0x30804080c0616200309010315050607110a06081509040320031b060c0f090625060605030d021b010c02030a0c05040b010503090307110f060a021c030624030e0304 71
    0x4030101d0b8000d00c0200a004c414410003040d50b00c808001d600441c4400200c10398520715400c0c2008581600b06080e00002410303150805e590002021a07a80244001ca405514812405450a520040d1a20001d51300554100c56110300b2048119000300701c0d0903d028a983c000e48242807042100c0c00020154441020782e005841c900d50001c209814045000020082035003405009410b0318100301c03842110b60b03c0782400c02c0900410002e88a2003540701c01c0c04460b204484d0082d01a50000d041c028081c03548220001a07801500748000454103141c0400d594030501055002001048059056601200d88807a546070500c0303240c0820700c0141c0c5050214401c00c07481105003c4000c1d003440304100441e070342c5501c560b04010b802c1c800c000d0f0301c030700c0002243e0388039070810741d04080d003103a01d00011040140ca451694104202043c0004103030740000ccc00c2d089101e8189840c138202c013445e00086044441c10b1150504034160300600800402007601407901340750341c500d00860303040106580340e4a198055403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 722292302 1250 722291052 722291071
    0xa1b050a020a0b0f2502180105040c0e030a02010c0c1d0f010801020903030d050402030102041809022d19050901060918020a09140406081c0e0418030804080c06 70
    0x10080e021803070000c034050050846200c101e401c211440700f4503e61806000105c0b450302d5001c05405210410603990f014049500918001c0c0c900c03103001d030411401c0c1080c89423602a904115a40620328040c0044072415000900188850a000d0b001180c1075020800300343c41400706d150000c5121100c443c00c483c503202c0031521802e034a0400c82c860001a040c16800840c05900c18400030215030740c040220748003a1589140411a52200c3c00007130300900c150791080c503412941c11003440c01411140c01284a46000326054074165034080d41000440c0d55164a10710341031030100130340c03026242400c7c03c0600354045d10345056000c2c0d01d4201103540710400f80c00903c00710f500d0700350400007020401010381141d0800d0a0950030890a490080c000e581c0c180642c2c50041100d100c10041c54845a0010b0010100074045440d20f0101e08400000d00711080b007507a000500c6084e1100782070030203000d08407801d0706274080d403035000c40aa102118490409802203030210000c1003a4045950f04004203070094a412 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 722293552 1250 722292302 722292313
    0xa0f0c0b062815260c0c0f2a0904080d0903050403050d0908070f0308030c0a020c180601090b1204030c1e0b060a091e051e09030405040b03150109020a1b05 68
    0x10b05014250341090014145803c1c0d0301350000c00c001490101442c2c019403c91001da45480103030170f24034107003080e03c0f880c0401803052490628070030b4900326400c0c018103900c0c41c054030b01c00d00300f4051100381d113002c0707802520f5454200035520041415a0100301020b02030719059044c02d4580d0f946500749036120120000041e0514002d02c44446c0030711160008024400c0321084440c51607135801c0e41c1c1c0c000105002c1ca0040045000b110640c000c0c0b00c1d80c180a2801081050108101ca1030248001d10540b00b281c00034103507000219140c0c02d440101c40145d052280d2100302d680ea03c0d039045940c0d524589040700d40c81b66416200001e00845038100207400d20a24543c2c269142c14024017107142010b0f80100c0d2003d04055103500c1ca48080909151640c00040d00803c80c1c0d6a003440c050b0003002e0b1000c0201081d150030341049035061011014200b0303500101da0610403100c40c541059642e10508000c480101d01404c0100503e0650350300070030725103440d0300384440c58013035488041c0c120180c19141502c041d00413 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 722294802 1250 722293552 722293589
    0x50a20180a1403060c070512130510030606030e0f1b01031508010608191101080402011107060504081b10080a0b040606020a05010e030c0705150d060b0a0f0c0b0628 72
    0x18003655500980005401c0d041c2106c2d911003503601c2218030148400c0e44e0001844607070303100d10825054050304019000500828071007400900900a0344540c00010b0300e807445240000d6400320b401c3d0100305031000200340c3c0945803400e44400d500b4076036207035052558465003000100130b460b1070034008244c400c000003400d629001000c0c2c200342c283c140f0040c0440302002040000788c025405031600100030f18010000d5501c0c1d00c01600e80000c002c003501c0300340c403540d040000c03810f520400a1041c1c2e40d50205807808810320300e02d070102060f01090307450361082070300510ba598a0b1103100040d85c0100d100502095801400300071404841083d04a240184c103c81125030074000300f405100c1084d2400001545000000451142c4036086405203520540903503409a50f8015000107855100c070101c81c0030050700e90303140c441d40801c0c1d1001c1c1d554008140c01d00b8400c8a05401248040116500a031441000769200d40c1000144640c40a8025151004121110007051552040e41c090801c0d40600f5051206 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 722296052 1250 722294802 722294809
    0x1b01090507031403120f090f010524061905030709120818090114041805100c1704030f080901021608250f0204050c1b070306050a20180a14 61
    0x10500f8440d801c1e40c3c01000840b05070102445e959501c112600d10741c0401c0d03140c40c04441d04284148100522941c00c100034030103081c00d44013070040f0409603c581d007034104070b4403002d00c80d160040300011041d0300c0100580c120414080d038011a4072001c0342c9014200c081e1a49040f8524051028003030fa0307004c0c0e001c42c0b44c01642c04040b050003c8100119078000d074540c500442803040b8400585030b03034000c50f01c4041401d1410703d942203106ca469031040039a0344602c2c400c0000c1c0c00406264072a100003c4183d42100301c0503403d00305050059400d913848a060241d24481511041c001a0080030250b608102003088855000d00b4803070414800c100309030b66405901107280d1640d410b400780284a107028840a8009251880da4041480d030580300802c080d42c038400d902c40f0a01a070000301714a0b603880000580ca44201103000826244580420400e80c0c5481210740111081300d501d446100c418140c08484501045001d03100e0715060072140300541c8091000314081032196403001c2c1500000c510754815919 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 722297302 1250 722296052 722296073
    0x301060305181b030114010b2d040915090c02070608100e0a050604060b040303050405041103070f0c02150d0209031009020109141906050705060114010203040302061b0109050703 78
    0x7454000c0e04a40c50ba07440d8902d03840c0c0240d400b501026080c0d001400e41c00b03807029085501c0f0ba10400807850169a03640c000c0d000242e00905940c15580040904940080c0072108242d01d07800e40c0540980c24541810385050052285c841c51041d181202d14000400101a00403507103018020b501030b006841c035020010b082000d010b8440c0b02642d440d540b05001d8000010b0f60781d40d00501c20f0340d0106041c0c540702c0c0407800603c0c4540240102401c0010301000b4150801c0042c81201d4050b2020840b43c00006944075044c0004d448020015180800c45c00705c240c03050b038200020301e00051410826504240d41c1c010030398441c156810744150041010710b020301e010f102c2802d910284400501800e00c1d5640005d00d0500c4600400c14014485203801035a40c640700450450035110610f1007000e59141c4102520a8000c208121801d1080d5000419240400c600d8907200315010780045003807909603401c12100390000140320b601c40c000e039401490a0f0100f40130f41b00040c0e0080c0c0241c01a28110f0802d508440d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 722298552 1250 722297302 722297311
    0xe0a03020d0f14251a0703090c0b09120115081e0c061b03070b0402091006232503021204060e040b0d06060b18120c04090201110d02030301060305 64
    0x142d600003000b64150000f070410060000828501d507a030f034034205002c0d0002074044030b95507103d8a81603a1401c0012011086802107165100d0b0f141c00c1c0d0f1a190300304e0a94101c80c0d4006d22030004804100f00301c03005100500a004402041290504880394000d0f0840c0c030315030f048055683c0506c904000d252402d002d490040c0801e8a080c1c10066011503105541d20410740c50a4001c03e0006104004020505070b0405220b4400c2d00745c4e40d662001c0e0070700300b160400c1900d00340d2050950030f010403801351020041e001102d0b4951034200244480142003011200790400313082d00482d0402411200030200c10404840f400440c4d00c69090001909000b89000c00c5004c40801c81041003005216079a0040a0b008441740122408220300f0300d51004039414083c0024020105410000082000c01d000c4016000c0c401111490b40415501001080007001080d5181a101c0c0c1007401d001c541c508250304907491044c01810800400c00120482901c0d01102814450040e04040f0060022035410f0098a800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 722299802 1250 722298552 722298557
    0x901140f06101409210709020306010e040b0a0b160b0c030115050c0a0b040206370e0915190618090606020319021e0c180f1305100e0a03020d 62
    0x141c060a0214400c1449040c08107445001251030400001c014004031000c05c0300080f0503542d42540c2d031104c2e00065002a1481404038540c18004078450900707208500c90784400610125040c0d10f80105a02551300c44441c0c1403030021031100040c00704216001850140c43d04075911541e03985841144c8031848004c00d64241000010041d801c640400012182281500110911131503107861000620500c10580000c0c0c02d051805810783c410841030504408100e400c058010750801001c2089078210762050045601c9484080402d0b50041460001d01046c0c00c0984501000310842542c040380803881e5101a001a01c01442104070221692000d03000f4511108144105810810003079200d002c0c07031980da0105030083d841c041d901807017080401d80d82060035041c28058141d00d031940e521049500b40850060011003030521140f0b85c0f00803402d02c0350143c421030f031010f515400401203a014003480140d0307041c4101440e40d40c20351020301c40c4210002406000700100c10b41d524002e4104400b040c0d25006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 722301052 1250 722299802 722299817
    0x50705010c051002091f1d031c050903101107061104050d1e0c061107080706020d0c0501140a0506090f0603060c0a0c122006040c0303080901140f0610 66
    0x2580020b0743e00b1502c070071400243e19501644049441c4003001c3c102041400800c25000200940150072041105103052041c03502c0410b0700c00b4160703a2903070224201e81c00203001e02889022807040c0090101480010f040c3d84c5900000444141941c3d1403859000c2c00c0030000030018104a00c0b4030a91940114444880d03060a140c07200048410040c40c001410f0044240148608141900d440f1540c10358412407441c55036440b200001c058016150813010b2510440da40800c40200c0001e4541c11180c0d540d00400448901d03110442e506140c81e2011100713992580d80d1510921092140e6a11419103281c0c0000d641c0382000130030021400181c0524561014941400310790348020618560100e161140c0d03640e07a0300186401c8501c41c2550740c0203002d0760004d01d40084520341c464008024152103601c00c0981c1d49081140540b03c007410b480050000f090b040040000900800d0816480000d0b03000002d0055002c0e4400040b00c0d00c01c0f240d10868030b000b08208001880c110303145440341c030cc4510b088070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 722302158 1106 722301052 722301077
    0x18030302010615030e0d140f0c1b0f0d02041a0a0e100501021f09170a0c03020d1b02040b0f030a050708120a0c060509120c060405070501 60
    0x800c2400200101c0d03d2140c1300303010f9086801ca2540c003901c0001c842c94001d48510398054158150140f00340320030b107440019000a0304003c0c1003000038166803030800d084020714219850180e40f01d0031210b14100c4c0c840d141c42c6103602d03c4580c19100000d82084c007040c4c5407094601100d10b1136020050368408a6681c01008980340241a14290a0040f0b40c6600042e1f84409602043c00d55001c03203012511400f440d240c0040c00558005c2e150410394102901000d000d942c000a45000480c4074030307170385e03808040d0304000d110060413461510100031811010300c1c42c2c40c3c2c00d4809002c4c4c89181c5622a40c1001d0313580e926460000480101200c107408282d1901c07a84441d80c1c3d00c6034104074001d0301035400029045000300c0740c404e06196508200d101d002d5075407000425010b420f501c0140b140e81c2c0c8100001c03c2690060400c444600020704d8540b6082c54024503110480d003000d410000d1030030701d09 = true := by decide +kernel

theorem cover : BRFrame.Cov 722122302 722302158 := by
  have h0 := BRFrame.cov_init 722122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 722122302 ≤ n) (h2 : n < 722302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
