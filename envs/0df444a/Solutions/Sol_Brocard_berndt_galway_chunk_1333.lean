-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1333
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:25:42.963007+00:00
-- url     : https://prove2.me/submissions/1fce55dd-e546-4e9c-a97c-fe1149879c70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 239568345 ≤ n < 239748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 239569595 1250 239568345 239568367
    0x8040b0f074412010305011409070e070f031b02010606110102071a1510020a02041b020a11060f07060b1903020a03171201030605041109090309040f0b0301050108030706150308 77
    0x1110b50800c0903000c141c601440c3d41500030703200200340d1044030160744413000400c891501c0c00c2156003001c100c400401415082c4404400000001040902000707030f2540050402d6202c0c1d00010741c40000040d0406004104000c006c1c040c1850b0f01900020480d40204480850014800c650146800c00a0b0b895208504500307100c203030f440507045401220410322540f16a41d640303a641255020140c00812508a60f0b1041c0010342d80300c0c0e05080c5640d03260480c800342c05070700441c8155000d5400f11400e4109644603000480500403500360400c03102c000300342901005170341d60100e001854102c178014030226081ea041040500d15001c02034010002740b80030800108400004256208102003840c11700e00c408004e5103034000264001c1d80c4240e103c030300780b2060088a0222240703003101130745d01040d54502040c11990700e02c20301045c5405541e0302d02c410006034489502544a00a006000703001c90b59413000f0080d500e4101c52003d40b049850442c0881d40030084a49080460742e00400a0b0f081c80f1303480b80c1d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 239570845 1250 239569595 239569703
    0x50d090602060c2a07060512061c02012d18120c06050a0509040524090609070f05090306090115080a020907030b0402070204090309080f0604051908040b0f07 69
    0x20424410300c0c000c1310308052950382448420054803055866946910358044070320301421020f0803c1d406000c06095180038002c1552090341e8294080c201440c1c1344540080302e08070a40b10300d02400300d207e440400e001415601c10361410309281c0c2502c1954066480d0a01143c410320b40c19001084403a1403c030030000d59010350054044e440c03290410906110792103000c01c3c240e400031242c0f1000f59801100c00e162280d0300d41041d130b44c50716040e5034a01c42468810b0104403902c80c0580310305c06000e02c0704071189091b8840d0b001c807594108050103981d030905014a441c0e000c2d00d4040c114009200c01d0180200b0360510003e001181a81c000700300009603103c400703042d0001c00881c2d204580140c0c08101d00c00160302c55008194903070388641e0391300008030300d49140203041c0f41185c0c5038240507411901c14880400c44c00550340c0e4180e505030720701c4500b8601034540a90a4811980016804040070420f140581c0140c0c0207410700e00d005484007054902c17680344c40d5016a481d0540041510b69510a116a40151503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 239572095 1250 239570845 239570887
    0x10e0106081e04050c04050a051e1008011b2312070905040e061b13230306180d080c03070305070306121514070c060506130603050d090602060c 63
    0x500e80a0458600c0701c07002d002080c215020b0314070758008100d00800d803c0ca81b117103560104d00d24008009030704003603030b04d00580050012a1910310081e080032503200790707a5446c900c00a007072a10080201e61101400c1c10803181589244102188005c81c004e0140d805440450b00c0d440f810a02d0a03181c055039119400e00700e0342c00f5100c081040613100c2d020899490341e11500611041d4400142900d00e0813240301220380390100c0207002110001d11800c6000218500b40c0000e072040c040040ea04150160a2480c1042c1701c0c4004517458401c2e0414054154101908580a1081e02c0251001803202220981d50240281c480300c4640340100300140c80c00c0d10941c4065045a61444c001c101c01d55a025150303c0c408489900f0f6031003091040517015040b845210702d00c40c0c60310b03103030500c0294541400c010f0211001c40a0160080e500d0380700148003640d030065a090880d0140101b00407803901e80c10f01e0741d0343d61900440c0030080f85a2403804500e9500005403c4c0c81454500c54852500c58040107801801d4660 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 239573345 1250 239572095 239572111
    0x904030f030f0b060406170106180509060301180c061b12031805010606020d030e1920130b0301151a0904020403120f090f060206060108190f0c020d0305010e010608 72
    0x1d0021900c1540d1385100030030003000b190390713440ca900020300015400d038070b03040e4000f0060010700102200b400ba1104500e200f02e44044411100c507546100100e030240484210544202c0090300c440e20411503400810010740c1c40b150707103600d100c00d00501d510005550703042014207404041201e019440e03102e500f0081082c03028001c21404800e050707407aa407d40311590815405138118484d0400c109916100b8030500000500c0140140128840e60100c5075a5410317000c0d01f448800c642c0ba4100082d0402410f0031004090040d600103280313140c1d1240103b1b20302c03600314825428500c0c864901080c040158040e0340001910f42900140400c20142c0c1b50303c80159503401680074000000481c0c43e0044501c90000252946009189600c40082c0080040e40150201c0c7c0409030701480f00c242d0000d0030381e5010ad0203007230604a985542c8011410800d86010041065060064080c5240041d410440f140d00b501c0d02281c0c00701013202001d174281da00902400654034400c030f004020080c42014515008428 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 239574595 1250 239573345 239573351
    0x604020d06051504050a0b011103070c030809031c03050f060415091d0a0606050306071d04020901091707030c0b0f070b0a060807030f170c2e1a040501050904030f030f 73
    0x42d0102080c01d1303440881c3d000703e040f030341c92120000658000100030303401c00e4400c9c040c504c0c040c880d80e202c0a0581007804090300c222804503844141b0b8500b08a501481490f8000000440004820040240fd4120303100801c10b034001001ca0444d007483e014a8035048050b8000600047c10701250000400c1640c80b174460406400740000150202804001b001c90700820000c150107003094145494424042c00e04800c0003020b10b42030b0308c0004400207495416400b1140507950743d4500c00100d81000281d080700840c0c6200e0070189003c0f104c00114542100c1c41f402e48401003603604c0b0280303002d9000303031001d105010b00b0400c04100000e5005000c2c561041051500142c8542c13240003036407400c121500102c8181d41850400c4007072003d600c201182a0610158141c034200b01041f5517500e5002140079404002c0e18004500070301402154a01480c8038400d00c01c124130f03030585a40d44a00b585105829004a140070008a120704040c0a0b0500c9550103440d80c030f912151504044000301607541c440c07010703031782c1e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 239575845 1250 239574595 239574631
    0x3091002041d0a020d060906030519030207060809070302060409020d0605060f0f07080409050f09100612330c03061706040f1502070b060103150806061e0a03080c06090604020d0605 79
    0x5d0709100d404040c001180000a002c1d04602d890741c81c00300d0012002040303040100c03240300082d03400540407054404030b14100425480c0c03c2d17411480d082450f08001c0d40488042130210340c02d40c05902600180102e804103009441d981d0041c801c20388070310368010207082003c008502914503460000c0184910540c084c03403a1030381d2162002c080311825510342881003460000d01507000000c00c88980d07107403181c040400051f464241150b00300000844018440143c00040c40c240311954140c001c40031104070074112040102048e494010100c1303c0540707002c41e1803d0700106040c0d464610040641d035140000740415159500ca43e00d0030342c1c810700210b620008031004c00c030040c61240060712a440c4500d10598050512400240035a007401c0140c1e610252064403c02100000241207034106030291009011003074105245008070402503100f07070704902c0307049000080040c045c0040640116807811344145071034810182d03444030010b80380a03501c80da581d4220004950b17039500054004010b01000c4075921 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 239577095 1250 239575845 239575867
    0x250b0f070501021902070f0506071112070305061807030c0509090f070e220b0103020637031407050901030c0c060513060e150c03060a0e0405010203091002041d0a02 72
    0x20b4440b144c0b80850f07656490b101c1002d103404120007400380030745500d5017850504003804038001e80524040a8058910f48903080030a8a405c0c05060403501880306550340385803607003081030b5548001e607040c00d1400d010090011a051020607840142c07036001c036030003202d1381c680400c00013451030207031450300540580419000424000c0048070014884203000052620704408000040b000486044110741c4a1200500008a080c6462030640f82e046400903221680c2c2c2c480b68034a000d1705400060a11940301fa145015001d507540c3c1800307902903550500810004030701c00c40101806503070440c04901b0600c2080034940c005e0304040d80f042544c0ca00313540904003949448013903580c161074200f002c10300340082d041031184a0003003100c002100802858003505103405d0308681c400040141580c19004804100c0507542c011a04005144504150585090504205000358800d946100042c42040e5042c400040f580c001c0d28200c0d0b00e0140859020480080d440504400007046401c00903420000b0501350 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 239578345 1250 239577095 239577097
    0xc06030106020706031109010f0f030b03030f030a050705091e0103140112120806060403030c050f01021b19020a05090711010f0e10020313080c0c060a11250b0f07050102 74
    0x808466000f05803081c030740b44002d800c60f00450440c20350b081d0100b10001960740c1202e9981100c4c1d416281110b441044840220000d0610244981d4140000124081e0200d54540558014440840204800d440d410020745042c498968490340111015003004a05400c1d03c1d100d254900040c180411100f1520782c0d08150305009070080c0ca05484400780d40400d000c420031340410b01980307908003c0304600304240052000d009038130004080040e980580c0d400c20500b4042142e40c400d10000039074445608015002000c3d040c285407100611600d000c401c0c0e120709174000300c010140c01070206102c0c00c5c145000c0c000b42d00c1c0c004102c2024480c000340300c00910003092142c0c803c0c40e4111a0000303402402445003a0504905c0c9400d5030856005109225030004140d43c421105e40d0310a5143c0c2d03a40240c41215401d18000d95001ca40c0504045582c5030110742110503e41509441405d9030780135100040c46030107000280401e007240031500322050051100c2c5070300401c0c80c1803032481c50a04117825580c5060036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 239579595 1250 239578345 239578349
    0x120f090904030801060f02150c0c03120403081e06010807030f090210020f010f0b151b01020301030b160302070506040210090b190e0901030f060b010507020636210c060301 75
    0xf01030000400486600804280e621000d40c405000704603010456058150000b81500900d40c038000740c10850200108111600c0c0300c0c1d04410012685054103000c4e01d000b03800c80704540082642042051070b040e01d2000c00e445410140c448400316200c40b03d086004000030500c50011642d01c2110201503643c050307200000302c413242e00030480c02c0c83e6402402c3c00c1d034003620094000d4a05240c0854001e60720103106180024034204d43c26151428000710b140500504601001a548000004002d01c120b4000c124820132254841c0050004103101c00c4003288580784026001d504000081001458110f402882401191419040d2141c071984071804651104c181c00c02c2184503c042d8144a5400c44c01e5100100c0b01262918199071540d15054004900c00400614203580e620140c4a244c7c082e0041d610901e8015200940391500d00c030b9045071710100811004000054490105491807094900c40c83c040001342c0071146a48500301000f1910350522f40e100304074000c2c00042842a00c1d1a405140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 239580845 1250 239579595 239579597
    0x3030703180b0f01060e030a0c0b03070203041a1e04051e0415061107080601030b0a051e0a20030c041206240f0f0b040605090102070503010c02010b090f0108120f09090403 75
    0x3c441d4540500500140810310070103009401030208407011498112504080714405901560b507135071a90801c80c1148070701e4009580032201c28100c0513845039140007802c1006c0e1060540b0150000c1da0101c0c0540c6c2c0a40c0c80703015406111490030001340b00803500041d4a50724080d0001c92620305951102400103101e4111078002040e0b000074110301c07401084840002e02d058800f4060030f5040d0784900d007140e000241000c05154582c0081412402d213a00601c100c075038441941500f03400c0802204016015006900a09141c20001c407001c1c545907104032401030f20311240e541c1c0f41a103811014a036a804103502034802943d01c0460b03c0203185622112544c008044a040d81150305020003c043e8020715045128901001d220611202408808071019500d950178013a480b0a0107500403464640c1c3c907004982c05508180d103200700e15805420030623010a044441c122141e640c40003034034588000b4812540035603c0030003481160b58034200101496000481150b2800d650f11010640854041c0c404034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 239582095 1250 239580845 239580871
    0x3011523090f06070201080c070311060c0a023c010605031605120a050c0607050109021f0e090c1209190b06010905011805090c0714030a020d02030c03030703180b 71
    0x81c0b42c41d900940e500041264407504001540e0002081940c0c002e0190a000750002144014903000d03041d190035401c0a1800c0701c216240c42c0104d080c079500010490300c01742c401c40c400103019041c2403081d0300c540780d5404d0b0034824a901075070055000d4432594030076410035540c0712004a41924180980d202c100c0285500b0071000b46404240b001d00c40c0418020700c0385801040c252400194080340880c503407001243c0c0310780c80b080c5c0c0d828000d0043c0070280009500210803451082c1d01316500703145441301c00c120385844c623801e80b01c1c03028090702640841c2d403145240300401c10000e4242e80b00d0ba40c1508042c0071401ca032a0884020131500d0034a1440342c06480415000c0c080011641c0d0192120002d1300080c80c10b100c2440d0200b030040c50f6000079000b513510940c1d080300011070125040040e9018075401030401200051640096512940185000350041c000d01103080704075800003085a0060b449180218a199191902107005160b208061811032a2445a04003c2001e90403207074010f44032900c49d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 239583345 1250 239582095 239582107
    0x908070906030515070e220c020609061501050f031008030a1d0a050f130e010207150506060301080a06051317030703050f01231302191403040803011523 67
    0x25a00d4404d000d400489005100e904001c0f1007640000e500c0703140314043d1039502440d0040d0508600380c45030b0300c40e252480b51401d50302c090703000c0d40054401d00400031001950f0302d070b446d1744400103c4010b031428100d010600400882076241c00c2c510003164015903641b0510001e9496002250840c0e0040000c0c800044e5094441da41001e0714061070f01b91000110b0314280310600d4000440d001007401018288180700051280c2c070100140e030040300c503841740304008640d00c001d5481d03e0382d41e01302c2801010354011320f440009005400c20108817816100c1c01001030a91800c00d5640384080d040081c12011658810140c1a0014244488540e5800f82c00402d1784e44070b01e40050024121507000b00500e1001380c0000c01006001d601a03101d541c09180f01141c00c0d4600da500c03020611044000c0302c90b624007840000c0701880e201c0703441840c1502d0b281e540e5440f00e22450302c1d013005002c0e000644014101c400104010000f5400d07044c000201d40000f410405c05042030107401c0a10003680c0e8142c2da000303100c00658 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 239584595 1250 239583345 239583353
    0x7030b010b120f16030c020703080313060b030a1a1f0e07020105060904030509130b150702100503061e010e0a090e2a0607021207080a030f0206040314030601090807090603 75
    0x14141c0c080250380d0303110714600d400780602c5074444580d000707402030546e100c080000b41c2d8800d0041101942d0440300590f41c1303003000c24090440390319451040d14002d02e4100c1818052902084a254481c0c0024555250710002d5020015a05000d0023850342101050024011a100d9411600c000c0054070300907846071410f000042d00b0341302d00501c1c003485580b00408010000303030054207450041e14180e80172007010f4008107040000300903000d40d8503880040e071803802c903448600340014203c491080e40c00340ca100848480c142c41030f000944030180d004078241039180c5949466540d01492040c14540504401c02501c0864802c107200c1d00404582074484d06103481d00c050070071441130350409000e444182c00c200001c0c00084104c1e0700c0c41181c4a0000000d0a80955846250f0841c8000040c3c042d21101641c0744902580d51404850490125070402c855800c8940089000d920454158907180744102008503819000d40c0001c160a0502c40092400301d8901d208005000107410320290005102c3c0c11400c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 239585845 1250 239584595 239584627
    0x13061203030e0118061509020408010603020f0a03080301051302161a150d0602030c071505060109050904050d0c170a09080708280302100e01020702012706050c07030b010b 75
    0x2e90701c10360360304100c0910a5100300324071255030250026030019500b111403012035030010381544001c00c0a17001080100d60006c041d40725904503407003207400c608000d808105004c1403042c507200140031044c0a00042019051004a0480f081d840c070000514041307046400210b0340b18940d1080c0c444004d91481342d0721000301d064503540c100b02405180c2105101d110009120745540050040c6420340101c0410f5889210406403090294000c0d55032501c440d540c9aa403005000c220341003070010b41c54501c00202820309440150140e0341290181c07042000380c80d010380c0c680e0000442190101058075a10325001c0001c40584075900303a5903281c404091410524030b01e416616040015a03800c0040042415903880c074060f04800d0040000031036005c0141016410070701e4020300c0c07103441130610080c01c200c2c040c10340c01402001c0c0700744c90380300c80c800341c00c84402c2caa503100c0c0a01078000c4004c5503040c4030041c01200504861000750080b1150301d91a0342d0307400f4030ba420a0380a0401031074049003805043c00c0c1c182d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 239587095 1250 239585845 239585861
    0xa020a171c021606150807030503030a0506040902010e09090c150904060504150608071707171006050f09150d14130c03080702011707050301060f020f0a0b061306120303 74
    0x4040d420840329203968401d0f4088075030010401642c0b55001848000d50041c030b203000f004136506603403100e5641d0505540740e501c01c6468070761040c40c20002070054900b9115407039a054069549100c0d541c124030a00c80b0313410020703004080c24400d031703d050561642c1e0400711031314248c01c840d0b40d1921240807109101c2564000c0e0090f0384164144801030b07040208103003181c01200c80c0c529140945868a220503101a002c507800b00648511040400c050355030000c4024006460f00ca40000c129928005402000c5d041801183e0020f0400c000302d140b6130000070040c22940f50b00405107044d901e15030442000c913620100615044640f01c1143c61404a00224521303800020a0304007050346146a03103c001d0802c4a001c02090a9004600c160559204100702601c0f203c0c40300c100810740c01d00e4070008e42950400d10420001500c01024400414404a002d04200849500924001009135540031843c000109001d80042102038102048403132401040f0082c100308400b00016486030600401b541c02c84 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 239588345 1250 239587095 239587147
    0x10c0201060807080601030206030a2a09030b1e1f050316030b010b03090d080c16060b030c010f170703020f030a020703032304030c0201050d0c0206010906080105010506030c0a020a17 80
    0x417a0040000d40c503002c00f12640300344131000c000784a00301200428804480301d0042c89130112140c0075040c0132a085010501624000d440d608070b544c2c0d910502088006040402283c4146c01202164221002d03152403c1c203451442e018102d801d0311a00030078075000d0706031407022152010711000c009100c08100407502405034015a1441e5240500f0302c5903950b039120f248a42000800c000050240d290101603e80d0100200c00420343c01c076850909901900da00d6544030720038000c840088c691503026021501000040381c4580350010404450701000c18001450340050640030030860642d0031f00c04008521907103224800580301d0000d410000d00b12400b411484029000741e0f2000d0010440b08881242c1c0b103039251800441100c12880100d8443c0200c4040325151420048030766102500403030b0542c142d4140e80001c120f0584e96120f9a400e0719020710550750071507070400102e04190303a0b100050890700154012540c6d000c01c0c9664a0182d03014500113494122000700d80100784440220070100b2083d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 239589595 1250 239588345 239588353
    0xc0106180b030712051006090504020a06020613021513030b0124120f09060606020d0201050609010303080711120f071406190e0c090106080403080f010b030a0e010e010c020106080708 80
    0x1c01004259105510b029800300d5460103403203003040020410000c4040c1c403881c00140b103802e540d184d10f0700c0648400c2e20200e204840c11719011500c0c91000404d18461315840b1402500e0075003c0d000c5c006a400180055503102c8020005c003122a034888075400011849034402c1d00b040e61410b17450302800007804560f04155013a4241070b080b12648843d071041c1c403071584180041c4c00c0c1d40045080c0020711500c00003c240a08103000050655008240751416201b40d070000e0215982d0002042126202400000c0204240c0404505054801c0c4a900c6012900400721030230341c80e0010700403081d5040300a5400080c140042e00c0f00030400000201c0b604480005c000741440d080a40104880a105003000c00c00e5550f500b0000001102c06c108070041440c001e13250032403d50311444010050002110140c0c042860f40001c0b450b141d28019590341219400d464840c110380f41c4414040103090007100c01da0042d0f4850b40070030960402071080c0c404508440d000080c46620300640d81e4104001ca60100441c0d1708 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 239590845 1250 239589595 239589611
    0x2070b070b04060203060607060603080a02240c0705030c01141605120f090a020d05010b0a0b0a0806060d1d061602010e0a060c090803041d0a050103030e01081b0c010618 74
    0x50200c40ca80e0700a0f9111030050307125030b6020086405401b0b054400780440c6c1c01c2c1580002401103d00c020004485c0f01d81c25221009031903c0c01020280b0414075803085070404070f000031917080c00c01d40030300703405071107403064034541402940c01d02d09443c07041e4010301500c000d032020b100e90444900c0425809441504200e81442d10500d850103e002c0000d001f02c84000c01c100014081e20014862520019801080768200c0040780c04c003a0f00800424140c1806591010340110306000d111068a6681e82607a407241060703a2074109022103a0488203154158545602c103159a0522102408080ca1030200060280b4a8101210520360f8030240d6403a09592510401d0b6110700341c0070800601070ba800c46004034032480841b408540380044c65108441e20f010214010801d0045048020a04022441040381c5c0b6201c0403810000c454003844014080b46010500511650164a006500032200742c1e60303c1799a201c0144821003030380601c1705e0000503503480c5402c2c42508502200d4210083e09030300c080010307075 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 239592095 1250 239590845 239590853
    0xc120604120908011d010c111f090c032001030b0a0b07020d0c06020a030905061206010305061519092c040c080d0e030d17010b09181602070b07 63
    0x40584003074000040c01800580312401202a40c00030320300398000f0010410f030104000b00c001d2013540d241e400d550030854540512403080030340c2100f055040e0090080e20f070300f031100440302c00103a412548003141c480c4145404140c0300246d05c5c00450092940c0301c413030007601060944210041d144203040c0351802001000e951140c15080042d0b03400105a01c3d5141010300020b400c40c0d842050003060200c912001241d6240d0110310b0314072003131003601c0310344442da1101c04104881c0142100c10126981590000e4907941c0719800070b540145001e07280300f00d8060003003000c0c0880c2e8406202540e81c12903000c440702e1040e601411800090900c0000c0c04141510129072055200d280d00c0c800c050706011102190a004926610000501c01001111104050038001400f03242c3c20150691080c02181c080480040c0504044175124481900740e014503030801008034003581000c2a9103400c442580c0606c60a2480c240c0040d02944200450324417084004d0402460008690801c9071350341402d0102d18001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 239593345 1250 239592095 239592103
    0xc0117101d19141501020312040c18050411010507060b040f02130b030405030d051e071e181502010204030c0b030f0c071106070f02090a0c0e04060b07020d0303060f090204080c12 78
    0x10080f4850300144c02a00704004034030750300030700024500700141c0e1403e0100708082605410b085802d03107425031030380b4511081104121801103030054500e502040c0203080c10362040c0c4c0102003551103030710001502e24005000c01e0846480c001e400c90712036800107424107803900142e0703003900400c0002c514900d1880c00c0d030b44441e240d0007004a4486000d8413980840c22406a03108500032181030000700301001c0c9000c110041c02c000074081c0f4000111004820031000b28450342d41180640c1800080311b10482c54001c07894070007032101d0f0007682117560074040400010000c480c0d1200a200d03003503640343c8904044070440302a0501610f04c400f550707020070581000844501e603441001008036441078590b4040e08091803000c0440e800250320811b40810051000069031200c04001d025603100b0350455100801d000484080303000d100c180540500a460051030000499102d0174030074a4082921030b034030a83d40010320342e5904141071444e00802c052140100812024011400445445c01d400e2104090b0b0303515 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 239594595 1250 239593345 239593351
    0xf060d150f0b090a0903030506060403030807082a0403140a030c111c050a060509010b01021f020f0a0f020f07030803040b0615030c0c0705030c0117101d1914 69
    0x29141c03141035803010110380e80e00942600b107001d040b60a06207006400715004040d0120114007103441e0034040b8080d41080016034050303d030305449550b02da0302c03480701c1910121002803004083c11404135025241811f40c1c2000c14020503451021501c41f415450200c096080c80c100101d010780c820a0000e02090340404501c005ca900301d54485859003480300820414080c0369002403d1b0240380f9004004c01c0f00000b141ea82490048600300040d03100c80c1100341c00d80f07442c06c0c086401680411255185901c4010000762070000182c0e0061401002e82c02482745604050526408503810103040403140350103120600608101c0009000801e0139a5681c80b8980800350018181d20410301c00515140c960081e100f116003051442c441d02c901c0d0400c0c2c1c0d544a03500ca410f000d4528064840005501c1c2800a101e0401082c142c403a50b074400403241c3c02030504a00180406165200f001c0005072035901f106001c0b402c104036441c059901e2402481290920140a003500c800514001e14540e40c607004401d0290 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 239595845 1250 239594595 239594633
    0x1020307050a050c0a0b010f06120605060306040f0b09100e010e010e040f02060915041404020c0d050a02070e07020703030e01110c1201060915090608060c07020405040c1d0f060d 78
    0x5220002c25160501d401080385c8002c0009503013000200e03003401d1900080c4111039866440010390816100f07900242d0707c8600c0345c590050802d00128044d03290940000c810340607012400540525058006110642c054032075081410342610280a400d111500080c007503d9900c40b10001945403110640c0c0380e640003400a085550101c001000315035443d000c80b032110354014041c404021085040100550140c0300d208940a00b043c041500c42c00c05000361003102080f40e011704000e440d50102907442d68800c4200320b0441c0108240410b106441c0701c49075000703941c640d0051000504610b00139226040711880b0b103042c400b45110101020000040116403640e0039a804011400d07400d000601611480d0020f100e22814122458903c03107554103c1000c41d0302220b401c0c0449551ba50020351076a2003a100481c05c00400c2140b0b00c0903040581145030450700c940603400c00c1d240d80340c1c01c0c0c20b41e110721808901505181602885135905005100744d802010480d60b202610305540c1d548603c0490360a0070030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 239597095 1250 239595845 239595847
    0x90902010816020601120f120e0406090b09060d0501090b010308090405011205030334020a12030b06030c0f0904180201030b0a0501171009020703080703052203080a0b1e0a050301020307050a05 84
    0x140410007047c070032810032948000301101003240311344041e02a18520301c05034000c4d85800c80004080a07140510b10380088d000d401004d05445580030b200d4140080070060301c245d0340328082d603030000f4a50406140254000c40e80b090300c078801042080240c50069000303003440c0c81c518501c034000c2180442244d8003c010310b070000c521040c0804c1c0c82e0080c04a130100c0b8008820003c1c40c078022071500030034203010b41c40c40750303820b00e20640c1140300540803a18001c440035006030f024000100c0070040d210007080085a031044440c280800f100028094502c1601c0f088001c0f41400040800c6580500505594690032244124010300305000200060040381424403056a03280110380031010050950700174001c042e0056568102070306025200e0b5030103841030b000003403412000943d83c40d200b00c104008002440d102a404000380c0d02c0484071aa4080d140304005969502c1c01100307603840201110500c4010100080400201001c000c4c481c2242e42c00280241d004008003d40b45600004031115015142842c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 239598345 1250 239597095 239597129
    0x6120618021b010e03070204060807060c0206070813090605130b0f100318030809100c05090906031e011d120a032705100e0307022b05030301090902010816020601 71
    0x1600d02d801000700410a5180085014003610040010102a40242c60500c285651810186d9440966210782c00c001080b00001ca401803411100820445024a0150b414036000150544a001c6941d11100c0110381e241020441414020080d01c2d1850740d40100b042810b444a011981e9038400748410341c45003106680001c02c0e00e0085d4842c0c441a0044403c1750f05c4dc2d401403a025089800584550b45c1c01d101e10f07115030030b601000d4026410404d04503900d03242800340d400d09022860101908055260050115400d020000c0311740f41d80760070044038004144802420707a050703d440c0080800c041c00383c01c0048040b4160b01da80c3d00700e070721100e82d41c580001c2c218610314101d00d081c040703640136289a4a81600c10410b00100145c4c0c65030100b04040200464014802e5090303482c85118030094004407459506000c454003c01d0f075840600851f45800c8a40ca4656502c9085070b0090708107585044d900e49044081d568040140c0e0360209940d401606a00028040a50381340e40c14410100044410504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 239599595 1250 239598345 239598367
    0x70e0f04090c0305010c090512070315020d051303230301050d0317040302070608060603160806210a120311070b09010b0a140f010f0e06130e010b040612061802 70
    0x2007107090750040422251240c60349441800f0341341c00109600000c504c42008030307440c82c1c0401d005c0b8610b80310704000c5c4410703032559407141e00e006007190540d121580d0911801611136107501a062242d869a542c0c01001c0701c1500e00900b0825122120124a09100c03480768103061400c0c080703905403401210079562050b601d150131100f40c0c0c01003c0c0503910701040310905c4209600000e07048191005501c88503025560682400f05900003210b240100806000c00e60f224a8051703103030710350002c001610203a0505480360185510740d140103080f40095015001c02c9050100d1b801500719501441c0c0740a008444034110030140d075000d0350b40060b00c0b01d2404000308040040950080f042c000001d0008500b540d640e0381d1880500300e41c01d51181c0582c00004800c2c01942c40303108409141c00c0760351510741c2c0307046010050250a4001560403000c1c0c0803040008178205591660540c006c24290310712a60711800d01c840100080c4403d1583e045480c2042000d20948a10300010180d0102540e0016141c00c240a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 239600845 1250 239599595 239599601
    0x61401121127010f05070602031b2704150605030c07230d020105161b0c0e06120a03021207020414010e090114091c0c0506070905011106070e0f04 64
    0x406088403100c005074103440c4102d2110390a00504120a035818885102001550442d05400c1d90300c001480404c40000003581d103901a640001f401c680d03030740080305481c3e07961841d0b0340141c4580700c0c0302076802c2d800362030f61851174144550040113480a00003100060300440c017000310b070701800b410310001000241c8900b0402c81941c039410b0304211803101542e01c0c8258206940c00f8171014108a005104480c2d000900501460f4000c41559100c9800c04003a000304031030340c0f502017544034004200c030110540400c040c50050000707081407040203500c50820380b04010720301c02040f00740031158102e004400d0110350081500004400704074441c941d243c0030740c40010010b000e01c9481102106c1b02c0f400100d500e40c6850f0465209032180002044208400081c60882010446018042e40e100c00840d030301e48869851307201000151030411840220303080d60343e681014030484a02c000926041010881513030301c441110700300c41058002d4621420311040061244c41c4028410780603468100b01d0003050b0b01d440e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 239602095 1250 239600845 239600861
    0x5030f06042613030b0108010b0f040209060d020c0c09100807090506040e011805060c09090109020c0c030d0305061914300625170c2502100306140112 66
    0x1188035907a0700440c050689000300f20740419610544007400101f02c07080b05100f407580e100002407921603190708000801c0080c2d403044041c40c3c0c07c40001e022554451070980080c260031401d03827015104009100c02441401100141009844844c903c8200000200400d000042d9281c00c2d1001c110303955400c0204003d000c031102010724640c600000c81c0000b40e645001050f1441c860030541e28a921007403101e643c0f9014008040e40e0040703c0780010010301c24030b9401406203400701c1040d41c0c05543c1340c60009040c910880420804a0b4880c42001900d2034143d40c0346848645030b902644031036041101503014181481300039401010941c14807400c0458012506030901c1811001c04514420703405803903103425055902d07140404102480a04a0003010300c002c3c00d51080b40d030384940000494502007080c80b00078092a501030307400c00401d03e41c03102d25001f080d1154151443c0e101910340601c180034920080c0c054030400c051800d8000d11041c40c1d1107081a661960918092100c016600c1c0c000c40106008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 239603345 1250 239602095 239602163
    0xb12041703160e03010507020d0c02040b0402120106090902070308040f02010c17040f051507020d0c090f0501060f0e0901140a1509150e0607060e0f0d0201051005030f0604 75
    0x3204100b07040042c00741c100c05030030b41941c1d03c440c00300802c010305080c2c0381d041d02c0003400340e00105241c1020710b11425004505034001080070401e00301007004202240d00ca59244d0b001007900400520003550480700482c01070840356021842c00c08a030318010031043c00580014100707814490403100303680c4a030010480311904052900401000105400c110364068840c2603681d464440c80064140360200030508581c01c640c4d10280b82100917420017000040c2e0f00c0003110100c000d00340102e0004428403c001c0c0c1c081c1d40c000009440e50410402401d840602015001082400d0340003820343c2e11000c11040c112500d40b100c910300880b11600203a4405115044240745459030004040c00a6010316040b08071031494040d0140800d0804040f02c040c004c0048668200408000150000e105540500b0385411410b080c0d48000e00304030001803e1880d40003c09005070744070014040d0850300300030320400600b0304900401d8401e007120781c09500ca0760001c10240015804240042ca21440368111100180b41 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 239604595 1250 239603345 239603347
    0x150504110907052502030a080c12130303121b1101020f07050a0b07050304110609040f090c0915030c03020f010315060f0f080f04060b0f03010c0305090d08010b120417 73
    0x2251800400f5600310740c500a0700c0360081c03030a1150100d802840c0c5074100d034000c2c019001c095056203a40840f035018a2194182d4485c0344036445c00041c2c0710010b416621340e000b000210482c030b0360500034246a8407007101800b4a107044015203203441020003080ca50001c40c02e150b50302101d400d041e24024011030f04030156590000481d4000c1050100e02c1d5001c852058070f06500c00c0d200e0900840b02740c0403c40700185031440c2c5c4c8038512110315020f006000703d060000c102045c1c510801800c1c006035440c0c11812203094102d0501804a140c850044805000090000e0700d02c152071034991290305440e500c00640510030711000003103241d100c1e400c0700c81030078a807404042c841a501d83c8c0060a003a004a03400c800207003540400740590b03205280c41c50184800d420500b41c99156a00c0e400300030242500010340c003222040d05984503440a0280103c0890681c030005440d26040c9c6226041c0303207410f8031031000c101c10000144009000c4405a0f8a105c03910340c0c01818980e2245031610b03914130089500b11402c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 239605845 1250 239604595 239604601
    0x2030d200c0a02030d080702210d06090c110d02070b07110d030c030f020303060906210118140d0503071407061a030c191205031b01090210050301031505041109 70
    0x700154001595109404846209140400444418206650500c0181c0010400c200c07114594108212810340d00300e03200c0d19065507018882c0480300980d000100c0c0c1601d420840210b82c0c0c03c050354225168220014050480d1400402500c078009070266150550000ca40d100c140000325400a11100014001c00301c5003d0714100502601172440c022070010340809000d004903407020080e20300400300030701010301a03183c0f101000001d031820170841c142c481e143c0ea181101031800f400350403460102c08409070518121810014824811081c0310480d5a0007a1001802541d0160860758003000310710300b1741034013140c1e82000c000354030138800080c0c001414001701d01400061a182e4188002c0101e0855501c80745040a000c160352070150840c44111903414204a000c030341c1d600d034148030f41c45401034902e01402c40d01003000640c0e41c0c8001c954a0382d507891101c41142000002c480b500819800c00c581190303d1a0f031582d06881c1910030803d103440e12607010504006030242d4003072210100030070a000c186 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 239607095 1250 239605845 239605867
    0x20a03110703210e030301050402030c070507060810060201060305030d021b010e010f1802100f0908070f0e010e010b030a091e140c0a0b0714120310060807080702030d20 74
    0x941c4403804070400c0b01c2c42244100f21000340e4411001c2c00c8000070080c6056a103010304000094000500141540404000400000f04240044406010680c491b02414200b40700100b42c1410150088004e580c5048414404210000159040c1ca04d0030240941d4541c031800c06a02040303207078401d1001543c01d000e01416844010341140307003c110301c009c04010038041a040c000e81030315000c0d406500301e045100803480d940e100351f140c900e21210f2801c2291174280c0d100310b4640b901d04141d010010440b58090b0a01014140c80152401000078012031102541031000f02c4a45100c00385c2464005a61048504100042c0349000c860038a001240c907603902c0410f080440e0300051404281004e0701815800c10020324200d0742c840103888818042c542002c04035620362184142441000c4154482c4072100d0741c2030714081005502c10108000e2024045e841c01001802050f8007900407c1402002020001034950004c15078800200e02400031030005215118989a1017921202d04002c820003d0302d0303c191 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 239608345 1250 239607095 239607107
    0x70f060206010e10050f131b020f0c0105040f14010201141807080610050910050402041205062203120b0a062a08070b090712060902011719020a03110703 67
    0xf14541e4580e000f0070740d01e200c120700362003980d80100c984c00103680c0c580c078a090a02503400a040907543c40009100402c100e40070010350f0002c1807040060b1b02c42151124650014011040305040170700b8400c7c141410400c072828100003a01401e80640c9504002c241640c3c802d4000c0c070903011059411400e18208040e0114060b51040090030140c800c400c0c0016030000001410382c0305c2c88104400394810344c01c2000304a045040580450723004400c503140030030b0350303607a51004000a01102c40d030121900000c1c40c10b02c2c10301500400402030b0440449407480154400a500f104055040c5003031103c95030040a0300b0014240e41301d85a80020010a01058481c0c120508424808060304458a2100b200164400f800c1e41c104c401000c44400780113400000d40500001a049564170041d0340d165902c034414943c40c107541c407a0aa800c80c1d200c003058015543c000704c00284103440860103f22034a031100851088011f0034a200b44455030024403004071910039403103550b242d20041c4010742c1c1d4908a08008001e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 239609595 1250 239608345 239608349
    0x91003030f021c03090221010902011211192c01110c031e03040e240f090f0a0b091006090506031b03070903140607020106121a0603070f06020601 64
    0x201e1000300d51005041d000046800703000702040c0620400c446982011806041c1c1071a0072a0441c1c0b00020156290007a51030044001d98003400008400034580001802038880c007040049061400089410071041903041b0f0300000744400640c8004504100102e501c180401b404002d0185410a5032488680d40e8903540170046090381c80d10782c40c841070b2001c00d89a2440b0200180e01d50301000d02003444500080c1ea4648500c1400d0990b414260b0741c0038541e9800600301c510540355074104100010010850800800198081c0c80c1260804000d80210b200c09001900b810070f600414000079502c405240c02c0490000405010340340d0390700744800388000007151400b644c4049000b2001c0469141803000c20f40b03100d1401c03012040103004100300303140031642c0702501460800ca4054808408500c07804012a01c890283e001840189130150000342102d0058001d807044100104128010960b420100121410b02d10441c084e543c6400340064038107242580400e0403070700c150000003082c0340c0226500781 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 239610845 1250 239609595 239609597
    0x20d02181314010605030606090c0c0d0f0906050705100f0e070e0f0703050c03070507030504090515040506030601050d02040f1b020312070c02010906030506010905060d0902040f09170c0102070209100303 89
    0x1d14841c078100d400f401d0324100c1c080c040c3c043d804900025107900e0001691a0000c20681c980303450314401400c0395007080300100a0340041070b01c11400104141c0c0c03110a0b078000b002c0390301e810380c10061540d484540710741c034105890140d41e0321412050625412a80280c9081c0c1c2200c003101c46c110765807550030380c015100b10794050381e0011240c0001c01142c041e000c0c2034032510549460500d1a0b0382c10600390741d00d41001c8020382c108a0f09100109060704544120b9001c0c80f203034031010b03156610303000c03c00090710b44c010a66070080e0000d00042086d501d03640301c06080c0c542c1c1285c0100c0c141d0102000c0b038008002c0742481d80211412084503e283c40e80100040a00c4181c00c0705241d01a42e0341070069070980714182000340001d904000410204d84280d00c1107410060516102d81150358900020b80d080d0030460708210000c0d5a461210114a49845140145040c80300280203807002c9450711a0034100b281081584100c0002d9021080002941160610b503402490201542071032000403038100b80c1030100301c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 239612095 1250 239610845 239610863
    0x10b040e2401060e010503040c030605040c080f01060501230d060e06120307051c0201090c0603020c0705091003020402070c170604060b011b060b01020703150b01030c090e04020d021813 81
    0x64207034441403406416100c4544072200003480d136600454840c1e00060084c2c4031a2941040400099018012540210701590849070500d0910300e0903418080090740206540c0c1c5440c9041042d640c00c078888100c6103010030403800c040410154907100e0340c403458440c03207002c40c5400b00208498000c40101409440256120b0052040800c003450b078921a03120b01810944c031584802d440c13900b122800b80201d10f00f40c40081030241c015031f02d00031004950741128004c207801281c1e00034026001c021840c000e1400720341c0444142030aa40207001c0b0f038514000680035a030005085c1041c080407492a00c0100030b80d6180a4540d454103402c00d8807000281c908031000d40c140304081d40258032072489401ea80c1d07119140000000c5084c0c0e40c07080140240f4180c00d040d4040c031500000885d0404d1813401481454107000304441c00544001401c40f4080c003400700510040040910000f607100c56906c0c0e00503815107400f4440f54090001a0350500407285c1000744c010740781c040020141d4099000108148504640 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 239613345 1250 239612095 239612143
    0x50c03040c061d0904081204030c14150c0d020c16030606060309081b12160b0f040507032d06090201030c0503011508151008071707051b010b040e 64
    0x12902d501e030f2816090788400f001d0a1426040ca080364100382c02911030040d4615004d084c90341c0a251034000c5a0075000300d1030b041100c1d8144405605c4003500244c858000c2c007030040c80542146c2c0d000b2000b81c6100350b10345022510f040c203c0e60b298105c0700900c001c501160762070b03480c008ac6c3d0002495240012039256060000c0002d4460081c02144000343d4850b0f501800c0980c4041d01d90014075110415854074405d5000c403483c581e444600030841d24000e015440c20312506420b1071200710b44007918a01456030040100404100d000c94075a040d070b60b0050544000c2500c0418882414443c0d0042a440050024180b420803001c2d510802c03400d4400c3e2002e01080b0000340056541c1d020910902088400c04100c03458254864071a0300d60081141e01c03d00c0200c2c0b5440c01046400c580d040551011560f42401d11941c290046071180b00c1108141c000d24651900c3c0030014a140070702c00a403040000703011131017001d03008203400c900c1e400fa0019200b00321100703525140c10b0342e50140011503c1d030101c1018407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 239614595 1250 239613345 239613347
    0x31504060e0a0c020d0e240307030b0306090c010512040309080303010e01182c0102040902040e0907091a1e0409080a030f020f1603091e090b2707030e01050c03040c06 73
    0x200e01c405c840c90b0311811045200203045c8056025414201c04800c00442080302c4903125520240d40119020b940029102c04503d0030b240c0f4220000e0302115507540448804c409a030f9100b41181d400003201c2c1c4d00c5907010b0f00c440c601603a5100c2c4a0b000850140004000841d0b84c031111000d040c1207807845440b00341c0581000c0d1001040782c90024000d00d85071300303140741c0100c600180b0007100f0310411004001441d0583c0e070842c4a04030b800a0f004510000d2401d4144070006000b080180701522102108000481c600c2500318650003689441c140921030550020140c0030f03040d007400a14a030003600038004000340707250181e41940074207040030100307181c0451724aa8011502c2560444800d0002d19840d000c06ca41c9559148507803007038100c0800c030040300040741b13a40211900100302507141804071000303801c1180c050195203003502200e00411940d8202c001c0000321200d0701c9151815406c01d000305851310901100507042d5004441d00139030030401841070140e000001540b02c4c1d809503409a14203a10b502c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 239615845 1250 239614595 239614603
    0xa05190902010903080333090702070b0d0515220e030703210615030b01141207030b011b030918062402030d061d0609010b040b031504060e0a0c02 64
    0x2406800520150b8080c00010f40c9203009503008407545450380440034001c0c50f040480c2802e6048181f0b400f031240d02d25061800c0c5419240e40000d8140003a084580c1020b50320052400340070320750360001e501e81e40031402c0741c04805000308003000c0c090309000100c00343c1246100350103800081105014034082d11030441c0180441a10800342d459502c11021520114060f10206100084c04000550351400007401d6242c200c05010900210307240441c4903604140003402a10f429400d0656840f000c00203070800e0000e1510346580b000d5541000101440b13240c0040b516151205110345481030000c850205058100306407100700c50040d0788040500c0c5111280380240e400314071070452010b80c603c903010034071040b00c0c0f0002808481c6104403030400305406c407444260b81d000e90216040002c01020554060182003040e68407110544480311154500f250620f49442135205840e40f4060200100701070f45607144d00b91300100001001401096220341860460007000c1c0d41441c0310328a807031201c0c1c030218000f003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 239617095 1250 239615845 239615861
    0x20408031206120a0c030b06030c1f12020409060905011509030b0408070f0c051e100c15020f0a08091c0507061d010614030601080d0c1a0a0519 63
    0x280034500700110300541128410780540314503407007680c5021a071102e40c400c00c400c0000b24061004454094598101a03443c0e44001c2e100038001c0c0c2103603410b0b80d21511890340b1140361642189800500503101d48040303e00341d0b0302c0851140c04038000240060601030903049101560310340740301004166a00d11442d27000c00001c2c0b0321a804100010000c00104d000c6c2014190b1040c040c015240c034120556807075082503841c0340e0b011110315021400a2046040c1041d000224580200502da110008900080d0401110026210400c0020702290b01042800e00182c81c402000e0f0406545034505942d103000c0c23507004000c1140c001707203d001c00104144400030f183c1600082c000e10ba058500030040c0215170719400100203450564980f604285603200c4400d002400c20540000003646c50b0501880c4030f000541c10354094880c1e8400e00c01400212004158030040f04418103003239245014500c1c0c0b045d1598281c220070500700035410200040340e046508451302c61030103e032180002f41d04010322030f001c0310302c51 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 239618345 1250 239617095 239617109
    0x7090204030f11060c0d0801091404020102071502100e0102030624030105060a03090816020102070617010e0702070b1305130603150e0c031902091015050d0204030b0c0c060a0204 78
    0x400000003c540c1440703800d0280d5102400d40781ca05001c0714042c0b0325041004c0382c03110000b2401d100402c00314881c2c0c0310302200710200c980400307183e0400382c0000350f44010b1401071241c920399000f000842c845c020400d80d05500d1001c3c60a2010780c2140510328003e400071a5268001c4002c1000c11440100c200c0b4919252135414a0040c19070742004180710054002c800c3c041d0900d5900d00d08940482e0343e08024228480000f061500e41385840e2000a007801034661280090200c2c0e00034081503c810341c0460b0341907660407500e030400760352042003c9245c02140d60000c200c0b40e00005070341031801c02c0180c900065417015504032041110034103100341140d20702d100180100b9002a0050941481c54000c40441e40e40e400485144503842c2c0c0c000717410009084000d40c180d9080100d11000c604018101a0b0b0115103506142d006034544001c251507622241c0c0e100040140c00075101c084188568140d402550300002c1010861808200c6412590301050074401c0c107214031030015030104458021642a9066 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 239619595 1250 239618345 239618363
    0x405030703030e150705031e030c0403020114040521010b01021207060b010e10020c21120d0212010b0405011d130f020403120201050709060f0804030807051204060b030709020403 78
    0x59900c08031041507070b4070783d01c5034001c09000214800914000140c07550900600c0030319540c200251800040d941881008001d80750288200310891404805603022aa02800c0c0149440740c00050030140703108580003640d00c030070a00702190500342d080e200210b03038540c0c0000030403413500401c2c01039a541040f8828603120040420451000650b80e1b002040c0c051018141710107104e81c1100010075030541d585000005030f01110420b50b039490104107080707450440f13480d98034100130070b44101502e8041100c6450884a4002860001c1d00e941d94102c0d410800c506002c2165940c49040030f8035039512900c2424001414103008001c50700401c402200c1d0b139040201072042034640c94855401404130306881e6203c40d6800c0c400003002ca245a00d8080780100f10b94000146440c10607809400c40600c0c1d0058010000c4000741c004005400100c41c5410581600b04400399540b446400c94044c4180510b00d007440e880c2e0401d000030440541c2092040c0c0c4002c40c19510100d4071696035004901640c40080c01d1002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 239620845 1250 239619595 239619599
    0x70609080c061e0d240501031b0c05030c15070e01030e07180b0a090207140d080a05060f0d0c05030607050f0711190b0306090a0204030f030806040618060e0c04050307 73
    0x281c00e48843d0b0390340c20040704076400c01c08041010701c02c039034030382c0d030081d201265668000e1a264409406000680024241004040c0c5011590a074100714604002e003805480031803401840780810544601418a404032041e80510140f15151900c05480c0b18000ca00c180407011030960083c0a4188580e009000402c4120314118910710743e110b801080c8001c00796611445426500ca284014000d0406402c0c05a500e146625001d8040d00b0041108259070b00035240d00c10f5925071100029030448055140460180c44500c0015048003410080903880b2169a210300c0c2004100040341e422200e01324203880c0e06950b21417083e5100e1149100507580840c1c10000440001c0c0300407200c00d03814501611850000c52090812405c0c0c01c1c0d1900001c14841000c0100319107407400c110103542c032a00b050010342c146441c655901003010540003000b41400590300c0016a50384030780e4042c2c4020100011061800d400350801000140310500500b13000e107200e00c000030404080c01007200d0445801400806604e8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 239622095 1250 239620845 239620867
    0x906160507050916021c051303060539070204020f0403050c090a06060906110f0708030c01111e090d020a06180503070312120e0703030e030d03060e0a0207020f060c070609080c06 78
    0x14500d010310f0000e211041c002e01003445107088848c00598464100028030b41011804840700e0078a100024a80704205141c1a090b103000c501c02ea15000c4010355501d032229450b01c000783c0a80201c0c1316503414848040303400402e102001039800c42d0340c2026940c9000603183d00307041380191207082c021b000c003040c01039008218461007090120304142850065540e040104d4080d6810540d1541c002c198951011501c0e000b132078070a20030800c400d02e50503801840e02c11408109c113600c14540a4181c0d526801058041b01500c0b20141d244507158020554400c064580501a100e182c080054040c9800c1c661800704032401c00084940c2501c1d000200340c9410412004201d40031034210740700404103078603207104480300e0710b040141d00040d520070303290741040448090034140350000302c0340c402041504258041021080140c1645d4100c2244070025a0301c1050b030001c43ea16280f004015034020900141080110801040e000e00740c40e000c2d41c0f801c080c65941c40c00e440d9102c41c500f1000f42e0018080003410004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 239623345 1250 239622095 239622133
    0x10c110f060d020703080403110d080a0c030f150f0e060a0302060307020a0c18050901022d0c1005090c01020601060f0e2b0308062202090616050705091602 68
    0x401090640b900c40320140903802d03a0000342c02100880d03010421b0004050300a10100580b1804100134031700400390701001003026601604d105c00c1181e0b240c4642200605c00e0b000019040c040e0724007803100b5001c60406d0010306a4a110740940440c849002042581c50b90040368081e40303008044020690468080021580c4060852810743c0314242c28280002d0201482074002c20507500e4100b121b6030b4441c440019902e004004100903441004200100d4654032a461701005801e1480300007501f91001c601d50921a01c80151024401c403145403200305003d400252040682c0e4042d182500512001a40c2d0741400b80a41d40204106003101807203039210310961030b8095001080440c14801c004010510000003d42c14140c10702c0b002107403420702d500f21000d15081081561151010031030514142c0810701c1c02407494003040d800050407002c56071110151060850342d080740c1441d07a0101e2400d69650042440b4180c0180790000003d100011120f0032203500c0074854000c1d080540d1280e40c24242 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 239624595 1250 239623345 239623369
    0xa1a07050c0f03210f070f11070803040f0501091818020d0605060102010c020f070512010608010e07030605070905060f0a020a0b180f0c060a1407020d0605010311010c11 74
    0x8112091064040c4035030100082e0710712402050165a55040f110183d01c20240c1c8035240c00c607410b89003428400e00900342101e190b032006207841c00000462004008488112603014500000e1140322000b0500a20201c000c0040700e41a0242da85603682c0c0f50b006680d030783c0640c49a803000220002500c0d1080c0030a41200107100700591801d140101a9800141010b0b003005042c0d606070340d200304000ca956024440e24810700680d000074958181408030069440030b60307010307083c00b600c1174444038210078409402800180c17001d4402441080c00803131450781e807180540300564502c1e003400003080100b40980c0710703102a154068103d9107070003008160743c2442d50118411004612071007130f408012660b00e032040f50198118050140c1c4600760300e80740d00e1800400300000303600c035080020a04000c0d51a88112210070704141026003c2d11109040007559005482000e0f400a5040c4148400c006095008030b0690307109016041c005401d11004548044003054000d0108d500d0807800c2040f45040301d28518 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 239625845 1250 239624595 239624597
    0x1602030a080a020f04060906110624040902120a021e0a2102090403050c0f03031527090303040b0106030902030c0616020409050f120a1719140a0b01020a1a07 69
    0xb00d0324084400380d8004d540213500600024500721418494590b1051101d8250200c51004190606000300d50120700341d020710303142d0601d84c018040300813070340c8580e000705030716a40080034140004030b400c01058480c1e001e404105d1141c070740c0501510400c0c2201c202c0043d20a0f01514800e01c071400c2100b110340b082c4200741e8801d0305102c154008801a92079081c90b52041d44241d031902d0729600c082a45500d4000310005846407074009000b08410160303a141d1090000204030344086480d0650340803040b404a010b40e405202c0c4401108001c8a00f400000450240344a8840c07800183e1744c0e658120300322a10100025415000b03682011101d02c0d04101402c14640544102d40b102e900d80e500050481d19030041c1115039400c061440e503c0b009042c0140e4800040c3c08a44ca8030b0709240010040040794652030803444481031002250300503001003001c2d010300074101c40420401520155a252124080724003d0859081c160704000e194400b046101c989680010020405002210b510000e03c2004001070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 239627095 1250 239625845 239625847
    0x21507180e090c090f043309030e0d02010c0b1803031302030607080601170405010b0a031412090901030b0a0605041a10230c0a1e15141911130503061602030a080a02 72
    0xb081e0705850303d2a034140b03a4a880c000206230449180285c102d60000b1a940d10428002420340c0150342c00000305000c0543c80030102c089560703012417160124888a19400040c4400700030001d014129044840855008074203c464554411030200c0e400307101265041d001640804940d2614a9100d9103180c00611410000c134165900c90003241008000394801c0c2c0d200c0030805404107030080140040250030741401462441c1403002c034042a03d25106201c01417000e1000d00000e107800242c0d0b8061000b4050081060080a48200c121500c5082802c2c95034811003106c0c801d030081c60b004044a0343c0b454039820400d80f100c14014144040d642100580609030b0250007110000290111000c1c9010200c0c1640d00036440c000e410210f5040c00c9104110a04a180c9101001d102800c0c0383d071242e00c0218012038070000e43c038a1200b11302a01d0b20400c1446c03017003808a0700100842c0b4440111040d00c505400b00c0307045039595103032000c0c0401240c3c41000541c108000010f813092180303400342e6000d094040c3c05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 239628345 1250 239627095 239627153
    0x905070503120901080f060d020105070f081606051006020c061e0a051c0b030309120c210f0a02060405040e0a0b04030201020a0e01050a021507180e090c090f04 70
    0x710381040c0e0302c070094910300580014109100e6800c80c500316081102d80d4440e01d1a032a003000411703030030742e140580039048c082c0c040b0b040020480841103032420250301619140e02d480b0520f8292140c4448a0002c40c0d40905200004401341d107100405021914030364010440304510030f0600800382d100c00b110011207e655280c0c03406d5051f0001c014a10b0b51100c0e902c05a85400851020882c0919001c00180050901e0480d0311a0740e400010340304c05190440c0d404500f48900083c0c2c61400c3c440c1103010303400085003001e070070f503103984041040070041504081d00c4038480c10040c41901c40c450b40c0340086d03200300280000d0140f820641c0c0281001900001110410185503c403062000c108490880060390009006134003103a03c84051060004207080060901c2d00c1528040d450300d21015001e4206c4048400046409108241c915403c60440801c041281d48074034000c41080310403500c0700c0084c41001031543d651308015118510411340010144020745841e0350380c855206616620f40f4280f1050540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 239629595 1250 239628345 239628349
    0x516020913060501050312030601050f0d0504030f1e0c330203060312030103050d080603070f0b130b030f010312020a080c0604020a091a04090614090604060f020306060d09050705 78
    0xc0c240a1110340307085114940c1140b400d64152001604501d0003074201e03c140115150102c401c0e690000c2003400c020b81c84100503400042580201e052407244181498240024150004074440030000607039180f401c010b08841c0c0780c0c01081e2060780039400151900b03040401040281c50314445450604008001c46803603440c42c03817403003a460944404001e60010034003030341d46800c01c1480514204402618290340c03442d02c0e6aa113406000c486003061048107400254a03076001d00050010304140c04490081c680c9402c45042c036600209030087c0d06d108408004038030540d01d20241e034460031f01d200c0701a82c5a800d59903805440818101440d0940c0300700740d443c0000811140181400000501c003c211502c0d0034010414401440c1e800300c090140340a0684081d1421404c001e4201442558080344180962800354004d003900180c1080501c210801d002e04000c0215496000b50301510080c8003030013076403101d00100d20040ea10650320080030480c03000705840c1c682104080a0148041d52803e9580f200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 239630845 1250 239629595 239629609
    0x703060906180c0806010929010903050304060f0e0402090a0b07051f02030a05060d12030b010e030f06060a0f0e060112150305010e240402010806061903060306110c0607051602 77
    0x225410b5102d000180b02c130007401c1002c20300602e0001403c0c01038000e01079410200030550850b5040d000d02c0c869540c00c0340e9018050007002982d2000c100d81d078495032010001c5c181c2d03480c50030000000310070788002c0045107000e000751440400c000f0070404025141070100941d503400103034116154059414000080d403074207108100300030080b9101503528541210110100c0310010401b03845054840c1c1c124000c5084a521101d0b10201814006002d01507400140c640700d0000308a540d0602c0741c81d1803400c03400804244580203c000750b846640040c4c840314603502d6010640140a0141e00100002d00d20791304c00e0001c1c0510413112080000c404003400b4015201c404650007d0b50782c0e031745898500104070b0040040815504c04040720b00b13120180110000c04e90300e0064401ba041080c02401700d142555070f03c086840c0c03001c1c0d03031034018001d2088410182c080c040f9480150340140c0b41ca00000c0d848005401210784e100030000c058500c43e5038180050302e490300080b080e41000740000d20307107100603100c0751 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 239632095 1250 239630845 239630891
    0xc040c17100504060602160e100305030c0f0607020303010b120709081006260303180f03030f090613051009050c040c051b1207030e01020c041d1e0703060906 69
    0xd40c9441d00181440c080c0020b0f11500e1380001c0c115401080000c5070803070140d80c00400d07a0400d9a400b107854442c0c0220f9a40b030344054102600c640030008112044400006013682c0f0342e410301c030699045544110050781ca07400b09200d0000210001c001003940001c8a41c2c585900110b6810070050a0340c5945045107484181c641c88002c1c6699101e0901c25183c0d15180c1c0090b0b4131a121300d00903000d0802c80915200e0101800400301c0100801044039040301c00c0c092680511009011a42c485c0341540c180c0e00c030080141da00380d00c0c42c0501c0d800b20b6170101da07808a003407155802c40010000c140d841e0000400900c2c90348410784180c0181d5207400c1c82aa914000c090b0180f0071561a02d4071264815184000590703880c3d0710042503807040340111307592110f140542d101560907050605251100c900140c2c2004146079440d9403052600c0c900041d100c2d0724400d00e00c0b425030011b0442d0304044031410a4054160f6001d45221954442001040042d149401c42c4000c18810440441c03482041804054403e0f822 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 239633345 1250 239632095 239632111
    0x708060a15080702100b0105040e090c04150f050f0a030209060d060e030405012c0120010c170f060123070506090f0d0503060a0509040204090b09060a06080c030c040c17 74
    0xb003020300100d10350400102e00b030008036500401c00090113900103841d0344500d00c20030300d4507005030b00054222481400b51f80c41d107804c058014404119004c500318041c0d5064000d00c094403410403c007045900f4064625608200058030b0054440c0c21502000383c81e04000304859485400c42c1c144000003139450050341500115040255156800c0c81c0016148003902994080003002c001040e050200c010199450801000e00305900055072029460040550b4028648229803c02da039840845a20201001ea800c2042d0710120035034444c6000380440031010b0351054001103420341005021a00180030400240e20048d0035898414240d6a0340d041010859840c48075410280010b040c104040c080c6101c0340c0e001e444d100e491850700c0070000d1410342841c001d450040146400040464075950b021104583c0c1004e426292450300700003c60f5116000c6521580d180e090207000909010002040000b44400030701130402010300209200080070380341940340800040310621160b81c0705000a0034026891 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 239634595 1250 239633345 239633357
    0x207120f110616030203100b12070e010c020d11010e18010314031c110405060c010b1509090109090201051204050a0209010e0c0304110a08070e01030c06090e0708060a15 74
    0x1203401606512040c0700c1c00215800410030080301c901c10400c40160450755090040e142d40300e42d45180c4812113503401c1946110000104c608510603426a160b110310407035620346941203030440c01103c1d03c214514000350820b062802900020312025200340a60b107040c500030141884420008485a5001101c001550180c6005006210100f040d014800c40c01c200114500710350220f8000b13040c000045211102036540690b40d40c48034500c8205d80080c44000c1041d601c842c48555458001c0800310005485221400d40d18000c00d4013100c142d80315900003c21039205c076841c1000301e1000d05030700c8030128100502000700c40240405448014007890048000300700440f128414081994010303000102c007072503664204298041140c088a0b446907214a000d00f40340d84e00800300380e40703101b5504440214000c801d070100b43ca0800c594001d0407680220a00d040c81340e41c0306010b840b01215801401a07043c0300c0740c000b40b4070b10300445031a0b401002c09440081010382d60200920040b59184982f000118 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 239635845 1250 239634595 239634617
    0xb0a0b040f021201080303060a150c14061f0f0603050c0417060403020c030c100f02070e0901020d2403031b021f1d031905010e0102030702070501171b0d020712 70
    0x11043c8840c03805090010300540c03450808038006948080307203101c0e4105002000750f0100300c192241c01040c610395801765145c90640151003c0584540d01160324a00910b40c1402c904000c0448103443c9c411105540005032040703041040460140c40010242e030081d5504020005a50001e182d0341440010301a001d0481c0341418074009040403e85e494083c8668171009070040c0313956440856000100003820030701c011a8582000340d051201703d40c0302503065000705080144203034041d0000d210b0031242c000c04000060380c1c8295044c0e0782404107064040310071402c0c010b0001078040c0702046400c8402c810501021049030b80024106a401e024802ca644c140c0c1a03c0c100981e007042ea803d440c000c11003500c80401040b1000300741e841c0c40c4e4410440002d90305856104c103201081d407200d040042e100f8000d559030329000c1001382d66003c0758480d8500040c10105a40604040d003241580074444040c112003158a07501080311560b00412410000140d080110000082c04504500b030a6001c2c1e890f4045821 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 239637095 1250 239635845 239635867
    0x403050706030504121b02191511150615040f030b0108030a12020a03021e0c0706110a15060504050f010305011802010804060e1504060608010510060c0b0a0b040f02 72
    0x20040d03600010038541480140b10000362410b0018024100616260300b070111442c0500c6140d481c850000307034204a05010713440176003400311000802d450350020303488095582146e04407a42c0500c103c00b0400ca4004482e03066001c0c0390030703c8458010301e005204c003458003100d59a0f051503070b1082d0710203070408102c42c80800c00c014a03c00124010031013a40994241050684050400d00b4400f20008000342d0008042070b801d4080c0e419500f089001015140404000140f0007005601c50150f0301c07a1403084040001d4070600c201da40321401d0340c08101034440d10995540e21f01c602c004800302d917400030b611828086902c0d1075a00c140752207405100420001e0b5407440c00c0c4103085400d003010300d07001902c00900000160b41c100c1010b64000d80c2c4000c0001d130a00d280c51681d81846505c06440003940146002d00080c0116a00040b042d1025040200410340395032807461074a8129106e0000031860505254021500e2200341d194052103400c1b0100d078104054000500f26282d00c00380d02c1d095513020802e20051 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 239638345 1250 239637095 239637103
    0x70209100e010b070506040b060a09020a051b16060e0301060b0a031a040507050405060304150903111b010903030c03020c09012d141302090334050919020c070803040305 74
    0x404245282d60304d01403080c0c488584500340200060080409000829a15101e070140c001c002e00c040380c4110745408079188014020381c44041c0c00c19200030070a90000340e1071008200f0207409903000010b030260610700f42082d60b0080c208c011803603055580701000034030240e007840140400e49103a6000a004640d05030131100760600c1514003401280b800042002803a0013100f01c40646004407400c03500d940d5180340482109040d08004c80d24207007040c0b034048c10542c1190707010300c0c01000070703041d13803070030940400c03040c0c0e1581d0f17560196070006515810800c08640280305d04020b050203441030381c40380305a03840400c980240030781c041c0040c80245a45440421554441d000012042c00103900306280b8207800c104041e05601d11280c802e00d5019060008204160b0442e00010406800d0365486001d40414240314050010321811070300803504101d117941c1420001205540c4020590115070b180c0d880c800d403124021544190040307600b00503034009200200044402054031600440c1e84509515100d802c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 239639595 1250 239638345 239638349
    0x40617090a0507050607170f03041a1308070f05060429060312130801091b05090601080406150e0405030307110601030804090b150d0e0f03070209061203070209100e01 73
    0x1858004001c480c00080020480340c00320346044410342e841d09500d007030406e80c2c484140703151100d441d0006080000044480c0c040c5104031300a85c1c40e4402140511b98200c0202d0b0116200ea401c0300b080d0012400107403c0e480684641d500480741006c1c8062a580c500349040c0082d5001d444440c0d45c65844801c4101203d000b42110001d104030700c01070305114010035500c0142c20383c034201c031000c08503101c24400800710243e001008094001c0c400e215050619100e00c0400a0700030000400c261030110781401d100920f02c0c020b0344180e580c40110750340e03510703001c0081c0040903031010b44030b034001c0000960f504148095400b0798082c02c007441d620300344070710302600c41000c030850103000d500903500410211760721a0684003180d01500000c2010480300c400945015515442c0d136041c144040394082450136190f00070050451f845003100ca5203c1342c0103615075280250300c0002c1d07101d03842070001001e5050005527002c6000c076450440c0d060409560006610090846214039164020300e800c206100c030f09003600f80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 239640845 1250 239639595 239639611
    0x1612030603200a03020d060915020403020f0405040f02040e0705030d0e03010c030902030a0b0406020910050a112a0409140d09060c03080f1017070305070b030606040510050c03040617 80
    0x10003554010108103003d2003840040c1c8140d51207000320b4203100341c030f8010201d016842800b5080100c1021200740c000d41140c0000c0c2c0c0922840e49843c2d4050405210700e0b4003964220b5014101d491190782008040c0518480c09180350042c09000075140d1001c000b6980703001680e88401c0110a1008203040c00c550700740c03425500301801d140340304002d0303140800c440941503004415074100b9a16810003901a00c03a0340f01d140d81120740c85140c445c8507540007001d004204030070f82d101280c01d9003091740217540300c0b29800d01300c1b0030050a2a0011103075001c5048034607400800340011a00e2030464071a0000d0158030f03611101075070000312040c4c4142d42e0150f0b6141c080c0249017410070303130001c0644009000340780007003108074101e16480102d40c01240e0700314000c004001903420501091049034216803500b48611003110315108290740403440e540312030280e9108150150a00341841d10b40401c000444000042180c1444010090310266032014401400508600d880d0420865130b42d603440091030b04010140e030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 239642095 1250 239640845 239640893
    0x30304030504150324030201030509060c2a06010311030f15040b07030e062511030901050306190b09121f051905160801080f0a02061612030603 63
    0x1100007034001c0d05480c10b4502c10250424000301800064005003401000b80d40343c01d46403168403298440101800d002e8038800c0c0c1c4c0521150700c840030465600c200560360310302c241d40e082c0700303504041b00300d00b10f41c0c011008a031215034940c940343da070014144402a0802e503200036850910030b249040801c42500703c1041e80000703000400d10344104200c0200050801060100c5001c0400d01880c0b0982148100c0800d000036184181040300311285a0b14184030041c420f1090740c4041c580207405041c9010b800002d42e4003071841d01d60840f004403490380c0001c102540c048107001c00741078051040d40b455000390400341113881c1e5803400c4508000c0754089680c0c603101c0a40c820000d1100d0007903941e0b965042c10100305800b050030f84905075000c500308a6110071101d007074603000030004405000019a02ca0482e1034455221a989a40d11281c540c0b002c000510b41c50b03400340c0000001030401100400e003903204224881901060303650f808034400030901c00880026154101441400681e98007403c0c110440c00c815 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 239643345 1250 239642095 239642101
    0x515010903030801030303051e1f060e0109051003180312051012060b060c1504020f0d0c0b0d021308160504230402120319090501170c090a0b04060c060e0303 69
    0x3c1841805000040030151500081400c1c0340c45011079500c42c0c60a100b0041c0140b504e204003003c04181c01808003206000d4210020b0716174014031980d8201141130703485041c81403d2034103008c105c5400205200806a80d02c803100c00d4080d000f054010707420300c41d0351000c40039a10200940184c0d6005481d5411000c5003810411407502000407915501e5403040000c02d03130300e4503d0009182405402a007940c0782c0076101c0200701404071028164402c03442261400030145082c3c00b8444075207041031008002e4005034000b0310000895101400b0544401440580b0b816100b41100180020b154001c202c142d108490110322800289001005004146c1342042205811000c018500c10a90000000b01455501140654540c0004180c51001c81e1084903621071410b010090006540500d1500203107640c0300101c1c1543c8268584154480c03508a1400d541d01e1304011703180140d1113080c0880c1d10401b2904005256424a0007410040c4690b446818100c10701d401e0541c156000318010a440390420030070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 239644595 1250 239643345 239643347
    0x507180b030f06010309060b03060a06050405090a23120a0809060603120f070507030f05070501020f03070302030714150405030306030706090503030a080c070807050a1406130803060a030c09051501090303 89
    0x50b0507405038091901040361180c40c02c1020040c002031a103035400d4000c400070885082c030603030482c1046442c280c4007040140c0d2919010364403000000d100402150210703e010340ea4a00c03941088040c6806d010a403001900c0700350990240358422290100490105020081c03409420701c10150701090a402801414125054114031071080144d400b4030044040b070584207209040250308003469001d0366001186c030541c10301d40d41d07c0100c1c1c0300d0305005114102503045241e4010040c0c5240c42d5041e0001c41c2805d945070b81e00503000c1c1c2c3e10034118101d80320f886140ca084001c540c40c032074001c0c4c0c0a04080c503540d05200042c14100b90082d04030206010b00a40100225107000040701c949250701c1ca0b201d482070b242c0b11000c5055118000014000440120f0150706020b4003159a0b030071540f0134882c40da164210701d0035858417828101c0e03485080504407009100031490b502c00440d44003a004001c0005241c0325500c4400110b0703140c115001c015078950810440400b0175130a84844013007428151102440d40e60 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 239645845 1250 239644595 239644621
    0xa090b0105060f0d0f06150c03090e0411180601020c0607020303040e15030a050d03050132030f0d0206090601050d0818130c0509091609050405040203100507180b03 72
    0x315070390040078001991818032020b00180e6401c056150018000120f0315012500608207600400f0030b000c1c0d1900c010b2407624041e140443c16a9890344401840f54904142074040c80030042059403074051104698550b0790319091150b886440f5445441130505000000a161208841c41c1070b00805041103800f015179070002c151000c0b22118100414595144100342c2c0240007418196509442100710b11010440081040e49a103200d940d41008540c0e41c4a548441b00c060300b5102c410040110440d0050b82c903a8030f0b207510400350780541281c04110181100c3c2e8504807110700b050005030001024418104406d2041c140100000c50303259010281c0da4035441c01c9c502c10303280501e8900304080724010064541d00d016180030540c05c1c0d01000000348050015203558040005188511154400900317105503801d514403154003660b0741d001005040c401407100a1401070000d070b9146c0302e0440c0c060b281410501a191040701c00d40e1b50b660380000e035401600244401900140b804503014030400041c0d001c408 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 239647095 1250 239645845 239645849
    0x106081609050f0609030717100b040501050a05060723030406110a0317090c060f0306010e10020718090f08041703030405210c011a01020708030f03060103020c150901050703050a090b01 81
    0x80e0340680d10178070140020315020725684440803035102031290190001000c41ea030030f19880d13031072400c1c00480c44180801086540c00d010b01d0b640003001920038049420040c0203031804c6032040302c81000d025041c00c0b400c00c0c121483c000c2070300b43d607000041c180079480d48440d4400925080708020b140c42156650040c0c080344081c480b00500329112000645400003c2080e001142c1001d04090f0781d45150306a43c121a030f2080741d61a001c540d00c40c649180c241401042500400702650250034024241405071102020b000d00d141440c94955070303118041480001d03c41c000340d100300d8031290f03030360724240701011142c600e0010201e150f0020710810021410104031003030100c40c0580604071816860101c0700e8a800b8003550304c00030703610b40071401410890742c07d4000010b071401d03022994200c1d6210038040c0e403481002d4100d040035000f440414120f500a801400d080311021094540340f900e04440300680100464500f215a9124001d0089080d0503108803a044240440c0030700200409480d042d091000c18 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 239648345 1250 239647095 239647099
    0x306010b070b0910020a0305071e0818030d060b030a06050d080322060f091506230d1a041502040501080402010c020f10021606051905160602030106081609050f 70
    0x2100000c007241c5091007000c04c0a2454542151611480b0344010010002100c01d40081508801032401c0c01c00d903044c42c0c024102140d506c10410756984105244001c01500f281c41c114481480103104680c2f06003d03d102a00108401580320705d018080c91041c0d50407640a603014000d40800380c404100300034200c82e07109005405052220704450400980c001c41000d025001c0e52601d440401c80181d15044004d25030301600368511140b20700103c00d0101e4a8512422400800c21440008941240764451501301d600400804c28079229450f00d0307280080203070303690782d01c40b03905010001081203200301154502c0305400c046003024180350000e0040c9001400207410322000400100031951215a4a82c2c40100a071110043d00641c0c0c101030364514014000c022420300340764000c03030300354070030700c00d0710a08040318800c524268420b60080d03038107602000c41d00d68103286800041021a0980c0000c0d4020021952551481e180c41940c0b0081c583e100f01640d010400042e42c20055035455600c4005000c400b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 239649595 1250 239648345 239648363
    0x30327120304020f130906110f0904110c0105011e0b0403080715060512070e060d05250801020a0e010e040501060203270901080619110708030903220f050306010b07 72
    0xb10b000180881d0f103460202da074801c036004450408014990032403659a807140500b40030721102589024410301502920170300c007030780030311a4a0f210f1030584c00007048215510151464521a020b00ba425204260060500c2c580c07500266160400303c2c0300141c00074038084542d0f50809007917680b14100d511072100c02918010400ca0700c4180354015900100003801d000340b441c000f0755074100e00301d40c070303201c85118080d002000c420000c1d0f140c0c00c1130007190003880c0c0d00101801d190001d40c806001155a2005400c0724103068560129210002744020005900981c03a04011007106000051000720132080740340c0170302d080030010018582c0001c00c2d59081d240410340c1c0e00031542800b131559520450403500c203034405c4140000103000c480104040d40601140310640c10032400102001050f501d600f402502d0482c003c10001c804120000b001c0c40d00304580d141034900d480301d03180b02e0180c0079032003680c20401511480d404000c450b5040710b0000c010300b029006450a9803400701610010302440c3d00240ca20b0382 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 239650845 1250 239649595 239649601
    0x11412011505130312020c0a030b06060a0c0f050c0913030906030203070e0a0e0105011403041a060a26060108070f0b07110d0305090418020f1e120303271203 69
    0x700640564007250070041001d000b613540c0e400d240c606084420f64007400b50083c000b1116203418101c0088003541e4010035036040e56280c0308144a00d0313a02010100e42000324000b2a40c00041c910360024000d00d004000911500c3c6509040180002000c1d10490326281c800003c140040c2c4c020541e807048130b01e14100140c0b00c3c4d071079800c00c4d2510b0000328201e0ba03102d42c0240c40419150b4001003468140c407400c0e80ca0780003804001020744605d1109031405000d800e200d6892540701c0c2c10081c02c169200d0406170046106035921558034852030340d054512803890709840304058a21104001c43d81c0100909401003481c58074102204061030311034020244410030002d610720030322001d03032040030480c00068180750300c0b58054100100f03160401072101c4c0c800d6041400c125034040c10070b403101c60299002850340c03110200364410000e5191034825444480b80d49000c03d000181e0714012180414039400c1c0146030b4a20f00414092030703800041c403034210307804443da0401b00702480001d030724201d880101000316601d807 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 239652095 1250 239650845 239650847
    0x3050c0f040e0f01060f09120221030903010b0108011415120906010305010f020415030f0603051015080d020c062101090c030b0f010e0409060b061204020114120115 72
    0x2104a00404030320050000d400140082c000c00c10b14450941d40310300d0005139807914400c80305402c00300c4a510018186240911504160048032011607100a01d0443c403800c41d41c90900f450680d03d2280ca80f540c00c08030300b21415082c01e003e1180c0c0e1110910b0b1030390b036544c180f12140103170f601d517400310900031210b114400580400800483d007400c0021080c03040580b070004400c1366508024041102c09508008000f003803000f4500070340c1c0a0302c0c40c0420300c07401c84002c103070210020500340d441c0c1c41185840d05c80c00401300300180003001030554851404105040c500d00d2007000601580d001d00b00302da0200d90403200e1503501041c00800c40100726880d0759903800b83c540300c40d0aa100d2040e10000d4003161030000407203000c0c2d0303803207014000398030346050081080380400c1110762a10384405a0210f55501c1c0301c0440e61074154441c94066102c1c00b400a00302c148100441d000f0341280210310105001541031209542e000950509458103040c0c10790b2402ea40302c02c40c2c0e100c2c11018071031107030b07000c0d10303030399692001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 239653345 1250 239652095 239652097
    0x1c0b010603020c150f0402030d090311120a0b0906060a05090105030304060e0d12020307230d11010225060608062e0b07030201060906062627061501030e0c0103050c 72
    0x21018031030038901c0c9424103491741c0410f00c2c410b0720101e110b03205000b08030b42c41d0743c052008001120307081801401e128040100740000f000140710192050301988a621000a09024405015600c8940103140616041003801400c2500d03800c07080c400da01c101c0040003190350000803503040d103c05280282e45440000045501c41010000c000c001240700002c0c0034001d0b0f03002018103605402880e80740c0090040c0c07451a104c014500c0c00c1301d102500141401001980920365421030001854001850200842015414220302ca5007101c3c03a24a501902020301c001030081d440906a5403001e0207060510030342c1107942c0400711840000081544200ca1880c04444060340002c003050504150b0300e0403e4076000780202103900803e90418074000c1c0106002c0c0c452003034188402d948280f80350758195000e010100d8054000d001e8410754103821104003149020f08200f01d00561b14bc00200454102201344510b4186d8400b00e8a04040c034000b250141801d0010391100400c0080c2000116600d56001c400c5003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 239654595 1250 239653345 239653363
    0x60f090609100201020901030f061211130c0818060c030f0c07080d0207060501140d0303020c010f0207081c02030c090f13020307021015050102250302041404021c0b010603020c 77
    0x311003060b03640c06400ea40c064006180720342c02682c0410505035009894411110750f0300039610b641541c0d004c0034000620105226003000001800206800700180d0217009680702d81700354100186801d000c0c0304c1e0b90f8038a101c0c5c00c2c400c200c0c658064801441c08440e04949408014140d0350004640800b06034514600300032a1360701078024191580c1c4142c5150340703401943c002d410844000d840e050001400b9112034503e017000c80300081c10303028070613640c1c0c0b0104c001c0d401c400d0944140703560f1030100300b00d40300072407004291491041540c20744941c050348000492100303941941050f1401041008039200307a040454084600446020240c00c018402007440c0d20000500a007140d4800000c0c42235444d0001203d03844100600014010310090028010b800c000c64410305000d0b074042c10b6448407000c11001c049151900720581c10b40a141d880c1c001509075a03e804204100345504001c0c070055061404c05604c1032048401c00d0040ea0311150b54410601e041486101d040550104030075500c82414018000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 239655845 1250 239654595 239654599
    0x3060e010f2103110304031a0f070e1002010e07150f0509030309100e09071805060c0a020d031e0c03031407090b03060f060f030a14040312050c0c0a0b01081b060f090609 74
    0x1d210750300d0f40f030510b41c043c0408c040c140c1186050b00000703101c00980a50341b48502d10b10f40d5521211400071003800b0141110b02d0248055540311500d00b84182d2003007051400070003c20594041d544032066000d424464481d208c0c00400008222fa1809900c0010840c4d0002c4001d1301da54030b866240400c1214031b04070b64165658462603001c1880429a44010890640102e000c003c4010a540d40200482c0348a841c110b40d10135000340041101525140e150520154000e04120034081490756500040307465405004010034000c40031281810745c5403046d51308101e440c090704521030412240241500b0b05e80d2164120644001000503c2e41d1562040b000008034040c1110781c6805202328000e606030000c8620380045481c0800c05954440d5503200540503a0701902d41c1e01900c40303001000c4000d040b0052116454940401580042d4031040000e80001d500810f1403407665410518018200700c0300c80600c2241121100e0401c03010780d1030400b120021440086000d03a61480c82c1e0100b9041e0050390b002030307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 239657095 1250 239655845 239655847
    0x3f07050d0c0305010807080a0507051203040b03090a03090501030513150b0a0906180902091f15030e010c0207050a090b0d17030f0106140f0702010c02090703060e010f21031103 77
    0x24081c540c00d07410032410796803190113075170140f41c480300f0450750707481c20038400f501035072140804008bd030411490400c042055181643e161030b03201c0318030f443c0540c41036410f04210742c00744111310300b0316a00c0f104000284c00c0900c0d00b0300990820f9030b060a141c2d1301601000d000c0010100f80d09041c0000d982c0300d020b11038006007902c0074140c3e60f155010002d2682c0e22482c44503000700032602444055905c9001c0c549035005001c10030343c0d203030a00d4112824100808015a9001822000c0750f14244400d240050b8400c03540c01042c015000c485171030079a4410603000065600484050045541c2c40002d1015100700075030000e02c4c8110340f0002141c0200d022405000e180c2112820a50780e42180c009601c54000414010100d90340d800003111003116800308440021002c0c00740d0002070003040014484640145005409203105800207980c0764030a5500502195440c501000801c030003440460040098440c14002075103040c0c0c400b4a0a045c0200d9124080c6041d000c4508150140042c803803060440c1c0104c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 239658345 1250 239657095 239657111
    0x801091503050714031209010221160b250e040e070b04030f0b01140d060903031508031c0203061f0c06050405010c08090d140a0903020d06023f07050d 66
    0x4c40c9003052909402801003000303000340b81091004a501462060b8004c152004001001c0c484000b00fa44013500c90510400040310b140c019040740c2400070307005a1051034a8101303030003140e10b503801501d0b510f50b10028008480f14a560801900c0c9135151040c1c0d000315986928000080c100851030b00866494a404a000b0040c03150041c1e040f4002d91246030701d076400740d0300c901c0010402d03d21114040e40c050030710140c0b00001440c6030400c2c84d000d071003800c01203210340e048040805002d0080d008003c1603400491080704042402c4500f0070101d201c06021840e40c00e005c001702d0b60001000d1008290502c494041d82c601c54400d00064a4190700900b04020500303007890494060040101450001840f52020030704240012074030250560151f10786903079481c2c1024220403183c11450014060005136174000001d41c40e0850042c005901c10440140d8800d0340c2c103090300c60851583d800c00d01d8001060200303001400c40c20300d074421080b41102d0741043d075540c0c200100c0703039440307900101401c80e400c0501d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 239659595 1250 239658345 239658359
    0x1b0605060a080105130203011413080a301808090405070903080a030b10052107120c020705030d0c0507030809040f020c15091f0506042301091b08010915030507 70
    0xb070a1411b4400c90003402040c2c0014540500c0c86010380382240740d83e00e400640b80000784000002c001001c01400d065508981a0002024110480450702180e80404004906940c054403030707000222902014000c07448140d0b190140b9034011041c2e80d0380142c0e0342d03c01240603940605050002158080d09040c0d07242d00506004011304001d09140f80903140507885540c4150141e401d68514030a200101c01e00800351101c6068000c0700a4080d0044c810705408000030031702d0038000c605420b142d6400401b0190f141034241841c000c9900c1e44c41041041e4080c0d5180003c0300070a850080380d0300030b1810380d01c0300000000507008105414040c2030a07480001c8515420001254001c810341040b10841c0300c40d44d85040749500c0c0c400c16400104000c15100002510824130741c0400d4000c0000340c00000c0505550210700001d2072180c405a6040c01c000004001210081c0034040e9406500200d011051000c1c07480a400c0c0759044c054106143d03199004a040e881104200701c0c02580c00004548079542d80b001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 239660845 1250 239659595 239659621
    0x20c1902120a081e0a050306090403031409010c0908070f0b0d06050a12050c040905030a18090203010803090a270f0209041b0e0102010203040506070807050408030a02010f0c1b0605060a080105 84
    0x584084039400c58101144000c503042d141720400540360740b851607403582c2c20485010f000030000c42c00e05680f800040caa95402d10307206840b9016040001520402c0080060044492544016541d0340040414030449020624800489045203045612542980c01c07070005003034240c0216801c0b05603100300141c4646040802c26106008205032905006020f0520080d100c11a030040c01c00c1c1d00800c0341201c1544111518005990441000d2404640b161004404c7e82c1c820b92103102d183e0b0010400b1411032600d041400c0007040482e4500b510210303c0092803044500c0d940303001440e5680c43c0901400e80c81550102c500c22031f4010403c104003205600c07462101c80d203040c0f0540002e04d03551108019540140700300c902994000c001010b40340c1d126101100d4140c4001c1c044410040b00f0f110004441400f000a000e0290040d00046445071a014126088415404c040800c0022603048510840720403012640f401d0b8000c007000c203140d80d80340c011502a841662002c2c40700d40ca810f00308041c100c4400c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 239662095 1250 239660845 239660857
    0x60c1e0c020f09040c0311030c030109060203061002060906071209061515030204030f062403050a0302160b031501090f06080a05010510050a08070e090c091201020c1902120a08 77
    0x29410303010000c4500074071801d480110703801084540034070740c14008500d00300c121017047c200040071503c15003205000320b800e5400616040760002d4000c001d00c1308900d080c1248081c602c41501c02400c841c0b038031409161b80c440c000f0380030009002044128402c5108280c10202640740c0245062151071140007a00141c3d465078840c010340603041c0c0d802005124403900880301225000b1000340003c0415881c1c1c1401071045241c4420030700301c05003002100384100e0300c00000450040000d40003159040c18081d0401000c804440b044808080090019000e400c080e00e13042a662000f03184007441c0b150050340d540c80307140c00010004030b40e400001003840d40100d80a00c254204c5070140000c2c2d0380c0c1c40902c007018808403a984041001403041400c0944141c1c102540312401b483c4c041c3c1401010300114011a400341c07224110303e500060321600c2420f2071001e20725030601001c002c500e80004c0f10b00b401e80b00e1030480c890b1001c490900020134290754031403940140030b00c6660195000d03909503262010065001c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 239663345 1250 239662095 239662099
    0xc070302060609130303020c03040f180b03031312020a030506150109050f0a15050706090f060507080103020114070501110a09080d0206040b01030201120e0111030603010b1c060c1e0c02 81
    0x40000800320b04006030010f02804c0c00001071101007032556002d078080d400c55032140703980e403000380000600c0140032031458004040b44d0254030510642c15960200740c3e03803500c0380e079130180c0d0040001c1c0200c6a07003282141c0407201c0701201c03500c0d42038079480010b040c04460b91000d0501c0c85170805110307010b600121000c2400500362141840b00e9500c106001100300300540140d4070210808080101c840045400409410246405803400100755686400c94082c05001d13a80088216038841c10041e4a205480c1c2100072820708000702c1d0b1450f0300080c80a04030383c40c2c80b5070220002c0b076410100a0f003500f24003c261001d00c00f56854400700040244001c00c544a0f00b10581b05030050040280e00124007140600c1c2c1010081d04660300b180c0054440104a000f0801ca895a0b421035003a5000207201d001030210100f440760b5941c9c18510109801d40b60400b6805109003001641c80395480340001c0840c080321385c003200109114515440540d0750140480c2210b068401d0500305510b8190310038184880d142c42 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 239664595 1250 239663345 239663353
    0x230f0909010f1a15130b0403030f080138090a1202010905010c0809061c09110108010b0c0a0b060f0d05060a0f0b031e01110a030e0c0303070302030a030f0b090c070302 73
    0x100900d055a80c550709410580001d090030540d1089913681c401880d0b04001c2c91440041e846d51458200c0c200c0d4040d5009400064103003a40d0001c0d80e522680180c01024058950f000066000305514542c000c4030841400640050080c078500e544290103403044a80c004010100d4540c1d90142807020490000040b80014601342e0045825030094003405190b41d04125038605281d100d0301880419404510030318446160700c81105420303012805440340451244c0c0014004200f9000050110541a0840d115800042c0a80c9006240c00500d85500d40e4001c0c0708180d403a110716020400d4141e040c0740858000c49510054003e01c6400546180281d448a1041141c031081140d0381080301c84845040c2c4d4140c0100215140188501f0422a0484c008500004006011000b4404142d20903c580004030303484040c601ca10150910030810481410b40c040e501e000c429540080d200d00c500c00c0c80c10249503a9803003000b912070039a4800050004041c024100764100900d03a0000c80e0400c200807801481 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 239665845 1250 239664595 239664611
    0xc1e0e0d022b0605090307030504030609080d06090c0305240910081e0f0115120204060f090911040605150d02072f031f0f1404030504030b10230f0909010f 68
    0x17000108580c200c2e9010b50b0b90350b0425045075a4175002d0155840e0980f9404010b1152140c2901d031849884010b0002d05000104115242006030699100822203a922454001c00282e00a80c55051110348074080b03c40b017003e5501c404604601c00c2940e007142c00c161141e5030020340d00305000c4940c6850350021004482c0417262442c052420303500d0020324500c0035000341c0d108024040c0c20300102200e043c401000440c0c95074035101040c2d400f14080c2d1040c1c13422529091054140312102c0d803d029501001d503001d0080340d00308001710b443c0010701d080c1130910900005203200e152105a05468065500441010074402d40134081c08900c0201c0f00c0c4142d0894015007040031038680040e41e5103070b20020221104880c0107500d0310700300418511921030000c94690702904040144079000e64895442900c5441d265030550078240300e2210f000708080c02d2401025401e2010305609481c90312900503142c0c00000b43d0030a400810b0915060108086d0458540414895212419000a2a00443d541e01040801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 239667095 1250 239665845 239665861
    0x20c030304230316150e07150305160e01090b0f04060306090c08010b090a24020609030a080402060904060b030a0506102a1707060c1e0e0d022b0605 65
    0x440c80c0d54aa8040f0f80c0100306503141030200c800d0841000e07010f210002c5500c03000303407418415038041202d8100260041a020b000c8140100308030041c4e100360745070400403490f1640e50b1100ca8100c4d00000024131034520481145a0301c280d10031400b900400d13034040c1d1100140c001100301034015000d41000700303080ca000450003104034411a031a01c10156034440c400e074a84550f00d015039220301000380d044174445401140d028040c064204802d41c04500f100d010181c000d5000381017040c0500101403542082008406559111290540141e011511540d03103040d20740000c0d00601003640241c04402020081026400c0c1e594802e1748948001e59510201e8a40e40761308890706106607503990043c20140007c044126038040141c2c201a00c00c50010301e030a0030300465141070f50840d1908942c8940c03140c09070003190740d12000d0050000e4a0b40c1189418484882003e0005080d646009019000700c00c2c1d0765080d9603850544022406d0410400400d001452054403900c00c4061400d65015041401080146c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 239668345 1250 239667095 239667143
    0x6090902030607200d09080607020a03170603100606021c020106122004061211010201051605031510020c01140a05090603040c0504050c03010905070e01020706050a090306020c030304 80
    0x440e8028003400d01d5548070f1600391410741a01801031416055002e0000d204101040041808410350f20340007546413411500c2d504e00800207108200f1074000b10850000a80c000c5103140c644c80c60044481d089aa070900820320300280001e2610100e0700b0541e00196031034000c1004c802c0940e5545640c40358410011051b400c1c0c039201d00c524440b10491078400c40c081200c10200b40ba08210700f4080b48a2040000300080a40c0c2c41a000083c500c0f03003d142020400400c1c206110b1910310030300003401079242841000c54111006403405060003800800070300418025804a94440d038020407500342c842c40c21000070b542d1500c2c0c4041c035010032442c90b01e4a4000c101402581d8031084103589551030418080b003803029540000d08211a01c054200000c00c41351360341d00609100f408524803107901c83d03140c414458196407000d000542880440c0c5032108840e6404551007003900d4050410b165290700303110086400f02c80e00e0f44050000e074804140c10081140c04001980100d0040c1220302d0425460b01e084900e03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 239669595 1250 239668345 239668361
    0xc1d07020c0609040e0a080417070b0a0c020310240605040e0a090c030b011d06040917090a050607060e010c0906051207120e0601060801090b03071e050a180609 70
    0x1507400301081110500e0640000d0148000140001c80c50804007031516180c0384414104540d103e80100381030216024183d400921650300000a110382c42c50551a00080c0c401d00c180c007010003c16181c60030a549081214000c0e4034441e240810514007500c40d00322551481c0c009103d20b40d2200240065080d1054040d00d0540c0c1c4415007094458075079040c240c004110552088459005031540000441d1a50075030070700802e00f202c05980704600000180da441d4200400c0070f842903190000e15004203810400c8245000242451b155076180808000352109880e50b2005a00100c0003a0120411049403c01c003954482d0000030300890f07202e0542070f0f8044c13003d80a100c001401c148101410401080d4401d41c01c08410b00305070160038601000c98054035040001d514030350f4003110040202c140c2c0011064014000d11208200d8201e803000001d85550042c840c1800407192460616410982c0081d000c00907c8005c2c0300b080300759a9501107071001d614045006010034074002000519100501070200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 239670845 1250 239669595 239669597
    0x31b0c060708160801051c050303010b0d0f020f070b04020402040503030a030b030105130b070c1506060302090306070302090d0f050319020f0f0d08042019080106050d020d0f08160c1d07 81
    0x1980c0c209418040b1f0a4922640e00e1180c900d052411404217034103000460103419805a11941c50090000e500203840550030012100341c810012680c40c02c103c0816503034003550040b10130f160340d00c80740000340c040d00030f603048a81d15000018500d40e955070164445120700d11305074004e1101ea51400821180c050501802030910a9441d0000301c006104400382400706101e10301216a60b40841106800c40b003461300080042a40004d1641d00c038901040100e6000443e071900390310b4411040e000c104d034814000d0005016901c5106e01c00d0401000340107071030b144100003843e4a540828004001d603a0218000740f22424082c403c0448a00080895480b0b00b4110300d854620b8151110f60740c0c2c1844890012050f40340349981900c2d0702c9555100c1c1410f42c440d0018884010007541004021800c50340c00d944000d210702405d4400c100181c03990408410301a810444410800b40310341041c050500c03e0302040c0010154580c03096040042d0504500c0a0340c404601f20011048441c4500380300c03040a5404034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 239672095 1250 239670845 239670857
    0xa0e0a020603070c060504030e031c050a0c06020d05040309180204140105031305070e220c120201090b07081305010503090c09270304080d02120f031b0c06070816 71
    0x2405400c14000840d04804249480190324003d600c801d01150b809540442c00500350002d200e1051400700104403400c0c690410004d1b01c00c1140001502074800c0c50f40000522800d041003c051009650603149503000e046010b00440c9094a00101000840d000d4403484981500c0d2101e1000c034144251070550b00080c2d00c04251104a00040d01c1c0394200401d0744801041c0d40c3c1c0c003000080e105010050003021f030844502064104000c410107000f580c02408c0400d180c41303942907404030709994801d00843e01ea045582d400941180012a244881c5800c2b510007203e001480e0420880c2a400a0086582c16030381040c420f80c03104011500e17440700b66034200c500d51142c0c9201c1080d240000a0b15009045461585a00c915070300411901c4c0d100041340030110303000460304202001d070611000329210618800381c82c071100e146000304135a01410036113403a9400040005805c104418000c00003d041c42e000c100c1c1c541031504890340e0b440204550000001d1f04d2000403480100303420300500c0c41c41700c041c2c480c3c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 239673345 1250 239672095 239672113
    0x9031506092f0a0f030209040608150a05060f0a09020a0509030d05041a070803040b0901061a13060504060507141e1c030b0d150b0603040f03082404020307090306020a0f080a0e 77
    0x1710047c5d007081d80031070307841551040c0005a06008010082002d9180a0041e0f140d140c0003125004681c1c000f07140a003d40302c4260503820300d584040c04041511040301e401a101d000b0310320215020702550300341c0da0b0144120340d01100c801c0c2c1c1010181c401c031004150b1464a4a04c180e1000c0d51501918000608112003403020600041251240e20380c040102000007583e90360f00c0c2c20001d1810310080c0c035480001000560418003c159a841001601d600c6c03d00615013460044010203610034200041c1036400200280c0c1c2e050601032205041c811009503540340560011089507840e0241400386120060302903801506a500074090b86203a944001c05c000c81041e49502c914161092030040a900250354409511180d5600806507005602a04109448012524002d46500ca02070010307291031885058416900ba41e014414201c0c2400352005600c0e9200c0c000c00b40c4002c1c1c4035802c01800e540c00032600783c821a1b44151000b03810721180d503800c8000d44658801c01c1c00c03640b260040056680100c40e0b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 239674595 1250 239673345 239673347
    0x81609020f0316141305041401030b0610020f10060608070804120c03050405060c0303041a04080a03110d1a010207050f030601030803040f15090201170709031506092f0a0f 75
    0x40801c411003600f044d601c00046040e80a0b140da00c04c40c0c442e60700004030041800036042902c42c00310507106405040003e07504513140c0c80103080d00106a80d105141011798214040c0c800d211056043c05000100e50402010340300302006094180680c40c0045c0301a00022040b0b445007903000e0196070041c51001c0c1ca270801a804032407165040000364180036080000090a131078500041000324a441c0c0650b4490500b03240c00c1d0b101882c0300e00c00b009104000700a0102190300c00b000c0790b021080500300020b1b5004288030565460080d0200d00c581c1d646003158040c6003103041940341710700400c264261400c0750307201c904008408181c0321100d80c066101d64014000260f40c50000c41c6c120f400307038111110408580c1e8844002d001003c0310b5001b00f40e224030f400b00071541c01c1f035008090900345030f000301c440c1e140a0304002c007426407034400a0003107044440558000c001d551300179000703000070006c1886011649820048060500d0100c001010b106550f024850303c081c000b5100442e00741d03a5180800c5c000404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 239675845 1250 239674595 239674621
    0x90c0501050a03061208070506060d030e0f1302070302060f060d05031e19050d05150906010c02040e0109050c030c0907050324130b01120c0909050c040807081609020f03 74
    0x4100083c19558140810f504024401d40c03260240b00d910516511040c0c0d02d40281000800f400140c0240003031101c0100180d00214401e0000c00140c54080c0c0d0985900c000440d05109403aa00c040d0a2000031200141507002c1043c48c401c003400d40d50020030b600c032001448440c2640182c00350041d00207210f84072010000300d00384800150181c1c21903040007008441c80403440f110392005400b064000a050340c0d42650360043c50340c0554161001041001c081e4080754594400411450400602d4013a090465865030302603850051614000c00518501d40b40513076450b100001e41c80d101b40305118010290f45044000148124255500d143c210388500c008414254981498807241002c024007007803682c0c07500101261101c0b0003020100c2e2000e003d100240401c109415156403443c100b42140e540250000d4008044540c00280080c0300e50f03540d41c1403001c40c0115044002c9034003a030400001c0c4484001134551880c14040e4074400c00a03500d40c0640c00702c0c420980d003e1150032050000580c3c1c0040c141d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 239677095 1250 239675845 239675857
    0xd02040b030114101707030804051311040b310608090f060f06040e0109080306130b0d05060115110a02010c053c150a09150c0507021003090c050105 65
    0x640049892100900c000300111011184c01c01d40741c120007410082445660000c985084102010700680d90641d15854018811801400d000d200c5080d1940d00c1640d03182d00801034084940112501e458542d2983e045c542c0c096400e00e8540d600a0350215900d00c01c41c46030265440e52840404e041c6031414600341d51851700241a50040e004048001709520320501c5220700c600c00c140088012450300d4400c2108032045c0a070701c400c4687c50a51400002501002101d4000714100c401d0b111a05840180c2c2001d021900348054200d0365071007032001003141c001425816205a810340e4180d01805030402c030345019681c0d901043d02d038410301146026500803c281c03040c5c42c1c0074100782d800c2c801c9500410401b12902443e5005052408000d031004101c11941e11481051000003902c0120260300b03040c0850080500400134a941d50101d400400604510600c00c035103200034148070540310b10101401940004205a008203032111600c0d00d5180f0912594a40070b038001c003e02031881c01c01c001140d2980240d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 239678345 1250 239677095 239677099
    0x507050c030f03010302150309060a05060d0606120c0b1216110f0f0d111513020d03030b090c09060706050606041a0d1a0102100c02011401140405150d02040b 69
    0x410000300a114103100a2490300e45403941e981d901d524510520030010440146c084004406106100b02c100d03020440d1703034010408280104064440f403000034840304400300014507041c50071030700080300c42d152142c800c5203d004841c02c03594555140b8079801c0d10301c90070455003142101e2400141c096444500b1082e805045803804641040f40020114500440414641c001307511100030035000110410403041018841e00c4c01c800c0780c08a054900343c2c0c54040d0701d510440024035800150352400d150002860040c1c000740b413000782980904000d8010418840e015000f400300f080000d074100740c003c0442d0a41c1c00090000d40c6048039030f40b620700040078003601d0385600c060f00f00300000e20100801300c61060a00051005580c0b181d08880810840d81c98152100310070000e1030f040c0c030700750380c02140109003001d5031072001c903080458800072401007440303031107800360515140000726026420b991918030100003030720204196141c1546515103081c410b0412a4000c54680c090001420142c008001220300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 239679595 1250 239678345 239678347
    0xc121b0103020406350a090501050a020a0927060609171203010e0a110a020f16050a03020d140d030522111c080703020d120506011704150e010c090504021c050705 71
    0x504010045c00d0406a445800c81a110311006052180078411240c110000d605c08515008494801034664246440391032044000c0d00c0092246000b4600e03a004021903280080022035240c183c0541106098000d0126082d664541c0266101001034025200c03030703c2030300640c2140c0c40d00c081c20745440b030300420b124034454031a85082c3c11080c9920240039100001d802510140ca1086c0c01031b49820600124002da00c40b1130300c2c0402c25a200c2ca0310700402d40e1303010740e0041043da05508004a00d00103450300c00c106486050030400d003450f8958045170040f4442c80741c0700c10440440d0450f4000d035900b814080c0840303290b22100ca0b000c1c90050a09201c240682d128158625126210032081c4d8018003015000740c0c000ca04004241d50303100c03403408000e2180750300401060402e18002440d0b2064030b480740801e415081d000ca014081494030504c48155021828046080c01c107804901800d1480b007408041a010785c000300e1207151500a45080c1da80018010342e003001000301007406888094541424450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 239680845 1250 239679595 239679677
    0x1080f06030c0d0302010614040b100c0503070515070908030304030e04020a0e03120a2604062c070e0109060b0906090105190804020a0e01150e030c121b0103020406 72
    0x15050f20480303500d80a034000007803440c50300429680c2101d511041d5403280b45400c40c94010b6a481c10621600c020b8245042c104014551404a10314443c05c00701a09038881c44090410180004d0103041c0700d10007a80c1c41902403076686008550380c2c082030301c0003404907d15040030602c5d821305a0181101b0b4150345801c070f003104001d40c0400e04103441c1d41c0003124260000200322141c5500f0001001c80069a00e2a372620400028031500c0100c0e07014000600c0aa03c51081c1603c0c0c904000e080000c540044220800c0081c0b213029481d618603a5203d0725601048650001420500034402c4408607000c0944040c6000b000f8401c100f1242c0c403820089060007414066000b02d110b400804150354001d5481d141c1003401d246c010458281d00603842204148a050b00504c004a5040c1d100302c00400e46d42081c02c140503142000a0134422800b44081d04078034180301403256036000041380c81000313410442ca43c2101050100450a070300c42d50286e900480c0041000403416607a14060064068050041c40c0c4020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 239682095 1250 239680845 239680849
    0x109050906010210091e0308101703040b07060204090203010b0703020105070219030e0d060e030310080c011d031e15180c1003270212011509020a0c05010203041208100501080f06030c 80
    0x1045203000d80008e109501007201801072052007102030060058480c420800e502c001c80d540e031040340505a40101e02007200410412182c06860242040c0380066460b0761715456a138040380c0040000307500542c00c20000c070b00b5540c000720380400302c0f046440201d00201800d840949400c010889002d81111709030200501048613480350890803012480590f6590403c0500986614450f4100044541040d8130508003681c001c10320303001d050210352151044410b414006404c0c000100d209000060001140c1e01303020f000030036200d1828489200b008890b8484e4000341007200c0342c0f50030340751142d4001c600c40704140c5030002807891420000e1030042155000c081e074801d40524001072043c002c44000d4108002c500c3c100c08a2002c5e151848004c000c12802c0000c00a4200014801c0076a00c7da40080c00b43c1890780300c2c154500e0000e8210000395613900b0310f4602203c2e064440741c030702d00001e03400101141c202c610a802900c11110305a441070320b151105002038250726000f400c803590502c03074105414200d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 239683345 1250 239682095 239682143
    0x80601060f110715020f1618180b181605120a0f0b0106090603140604022d030a0b090103170a090302120f1b1c020102010b06040311010905090601021009 67
    0x44c1046950400f003008000310040c0c5803808002656400390014002035002031001030006c01202c2110303211114010b089800301c0c2c01403009040440301c100300f07100c40d24140040310b041580214448402c420040340403500d000d07104c030b40d0f07412040110106a101048a464105480c450510444041d1000b032a2150740310000e140c440c0b907049800d00010001041025044032140000703040c5400e0501c00b100c10b00c02400003004d001003038240f041c1e41c041610f1900b48542942004080308002108d0038040d0720843e4030381c4503001190302061050600410068038105010124104eaa1055140c042605450760120311a0060b00001d0704010101e840000540d480c2c0c008107200302104405090400c00c2074503171504001d01500e0324400c002a0142040d010340700c1804c02a03110450408040d09641c00d880101d025040007400c02d540050003180c0402402031460107001e00c0c0109032241811203507950240085c05404441150140e041a01c0501c945400c94000c0070300944944144500811030142450031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 239684595 1250 239683345 239683349
    0x1170103020d1a090a030e0f1f032405030d02280f200901060f020a02010503090c0909030406030501122f09130204050c04030f12020a080706090b06010306080601060f1107 75
    0x444d40c08100e2410038075070000a00180544262500407410540c00c01242700c00c1030349045211310514007900303481c0d69032190703201e203019181440000c520030112090800400200740030760386c403e001e081d140404013800082c190700040e4040780301c3c0c5000e200107080400c00320b0048000760340070b2071a05041c1001901da0440b140380708601c0140c2558090030b80090091704041600407000740028600703103101d03181d0005035402d1540e07424a004e6039039580306084a4200400c407564540c1000d069030a124030594084090800d490540c3d03801c002031ba9031180e01a0010350120030190030b80e81058170030040101300c00d11908842c4a840e0001f09200604404288616070407582c41403810007900700b1a00314500350003070580102407112044e051500395140c00510000885000700700000106580390524024004010500d03008682c0a449180724140480540f10503101101c8078615100001d0707040d0b0003446034006032060200201100e81c00d007441a02d103c2c22407007140c5d040c081d0701135a00032410030801000c40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 239685845 1250 239684595 239684611
    0x106080f0f0c2b200907080a2c0c010f18060c0822080111041d090f060c0d1410060f0e040222060531080604050f060601170103020d1a 59
    0x81350440021141030f035001410b01140c81078042500b404649a4803002450300a54440070000301e06441c21800c02c010001918003c4180c4013010407201b1040c400714806c5c40c0841c2c00c0c1c031011015800d01c00c007101d024184144507200da8034445c1b003d0084a102c1c01c84d603503885200d42100c0d4a4034203d07042031340241e0310800c4604070030500c0b00d800707001900703003805188150071121082d0380c02c103410301c010307144c0002402040381c00c000340030000a0140c110402c1000581000c4a0690340740d800c0c800b848405642c003550b0314280c402d08100c5650307a107200c0c1c42d03c03003403090f4502c040441d1880e00303000301110703d0341c43d445158040052030340100000e80d840b440140380464a410305001a81425103110902d4041d55102c04140003041c0199807002081c1c2c544140b0320780001ca01000004500d01c590702051455420040240c0320302c8080004024001414210300700028080798034030340e01c0e503004440259071040982940d82c58600100f0060800a200d01202032140622a00e1040304403070392000c0030800c4070144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 239687095 1250 239685845 239685863
    0xc0604020301060b0c030706020c1513030e1005090103050c04170f0105090102040b03010e0702240f0108060106020d030506130c050d0b0a120f0f050607020106080f0f0c2b 75
    0x2003107103000d11500000f0a0b00f0070a05041c2640020f9803600e0340030b60705000e80304980014607155103000c01d000d90641e40c100c1c1c1d500070005040c074240c4400300d1100c2c014202d0101c1e1140804600c10f290989100040c544656940ca103030400f400c0044000c0d18000d426015200020b00001c1540700c141000180c1c03104c0030340001d0100f9054601c400c0c3c02c1d16406401018203910400040c04562400012a0b05607511b0401d5284d007502da5075000c900e0440103208000c01300d44140314084030408100c179010b004038a01c00c044101a40c0703078604151941001e209020243e44152074030180302e4001d401c2240e2041c8006c1034540310140d1001d03201c007235445581c6c28000081001400301c0352859680700e1065440c100b0b84042941038103004400b048105488000303440e603441e02003480100104c400d0030a158903441801e48140381440c14010b806002c81380610352440c09184c000b100c800200151854050540400600c0403c6d44081801103e140340c1900d090901d80701554141c0401d2880f15001000f03208000e14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 239688345 1250 239687095 239687101
    0x61c052a0301060b0309060103020d030905090106050702041a030d030b010c0c0303020f0706021207030e06091503011d04080a0809070b04060207060806030a0201080402100c150608061f03080304030302040306020c06 94
    0x50840303681341c20048282c0ba041c801d010f0891400111141502d13416a0342c0f0407400c02c07a08090f10f001c0a40c0e4050f5920000010010440650040c060011144265401d205a9108002102c1e940c01f10403212394260740724a4041540c98481d40120030944010b04015844440755140c1d0070007804980c0087e40581e001c4c031514207281c14100038000007802ca82c4040d14200f00301881035200342c8504030015041001d15048039407035998010440c0c81016004124581a06103802d04900e141c2091250529003007400209199580b19a501503110310390010115180610301d0344140c4480ca405010b4195510840c400031444205100c01000608156000dc2c110603240070001090044024107081c041c3c0c02080e20840141d0f0032100c41600b060781113403c0c1c1381190300c161044070805c605a1014095480032104e8524420481e030200c4266412803064441540c0d400c200c06c0c200178002500080000d42600b07041022454150140d504203210b031801624080d80c9031540c8041c2d03008048240420b801490134 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 239689595 1250 239688345 239688349
    0xb01020607020706170403030f0f0f0e03040501051204030c02120c03070f05010818010b060a080613020c03030403050d020f07110a0e1005040e03070501060b03040303060509061c052a 80
    0x1080e58000120b10091005904100000b400d6010303645c54001e002d03060342c01007810140079400201c500c0e070660300b08000c5136040c04200e1740500720a020303552400e440c110f030f040302000c0c000c01254181d07103040e1589403410f646e8920702d84003264014015410010b030010410011307503c028510344008061401403001410031010075040400c150701c8030ba0340d000305d09820461a40c20280f0745922016460840c09142c055903005405041c8581c04250701110002e100c6890ba82c020440c507028420580b04a0700124070040c0140880c4a10501e4502c90f0b4420310010380000c5c8220000c1c0080754004101500301841c1e8521002c0d10341099000b00e6420140440c8003003e41001070a441c000c121094400b800ca091940b12050a8004e0307004107070159440c1c1030300195a400c1041120030040c0d01000801c00f003640e548042074150000d58040340001e040203400540303490159091802020b00a201c41c1a00721880c1c5000e5400400c88000c0b00d85d40903448480d1100501d0910170428a490f00340c81c0012402d000c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 239690845 1250 239689595 239689603
    0x3041505012306030601021c0207030302010605090c1e0d14070807020a020901120512030f180a02090c2802011e061401050a050c0d0306140402070213021c020705010b0102 75
    0xc0710351200740703006002d4900c20150741c101000105840c041d66a4032030100407410603981c5503c041084a0aa05070301c46994005030a0003240d00a41c020411151038100b0003ca030030b02900c6020300150180b042c0c1079001e50300100c01864052280e07100c2d250010b80010040ad4412160150a0440351030080020351a080443c40d40c5c00121480174005070205030b8002550044103009040d40c5440821403a010400b0802c40356003401d0125500036100e2030803200c0d50980303030070440c0e011641001480690080c400005201c018041c5e00030031781120340d0f50343c880110b4260000c0c198034010b000c0400c0040c01c00d40c0011295140130300c86031700100c0c3d10109569065806003004503e0841140790003020826000403103540303014070304246402603071190400c40880d0940540ca580380b00c64040c0111018802d40c242e0f00c9a41102d040a1101148103428400c00c4200d015801f006500984015231041840762542d000740f17810f00540641c005034048143e09a0101c0e0040541240c640e0b6480c42d07038014540e0104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 239692095 1250 239690845 239690849
    0x130504060b0a141315033b10020d020426060103080d0204051c0209060f1516080301140906060703020d0806130f060e010b09031002090406090e030a090e10290304150501 74
    0x1900500c6800b021a0343c1c071f5480781c292119a150300702c6610700d0554008052000355120341d44900c05546689101038200000d611520904043c8156554680f15481320074a52400420b0004003070010740c2e01c2e54440701d0241d4003211b08507001c0c5600b0071010620303030b43d90060201d014003c1c1400c1710400045106200140c4800b5020314420041c445605940f5602c4548103058003070308901e4070b81c81d8803220032a551015211207000700500408000820100c4801c22481c0c1d0500003281d1414013a203c3c1c02c28800d00d4407910b20b0140040c2c000b03208050030640114041900224080c141c12945030078482100110b80100b907045078000d45800c81084190121140c0c00e0241400303800d0245454582000240d94558810700b2004445d0082043c01c40b0755035a0703211000030000c4030b0080c42041140809142c03251300151390300011612518000c04c1e401e541ea8402849540c10f05540a0700c0c5080040324640c0262240d6180c140b6451040d0743c840c0d110452010303602840c440c10007044c144203000c030a84142c850513 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 239693345 1250 239692095 239692121
    0x6090c14060901030f09020d080a021506060a0c02150d141509041b05040c0e010f1119060e16060f0206060102100509010e12130504060b0a14131503 65
    0x20394448440d901c290850749050000d090004250782c171000500c0c05002821006540000c0402c400c0040c003010400805a41c1e016900359004001945800c00d0b03012401e81d00719801c0710040c00054059401a07013518005800100310fa00f402d144540349204607441002d0a41d10551566420000c10320000100d98002481000c852003c990a801044502c00002c00140050201401000003411035030a100c0c0503010152040c08140c04028011302410400e8140794005560950306000070f9114a254040000c1d064014000c1030314038801d07140f040c124109003070342c1c00ea0b518103e02110800030002403600b42c0c5141041000b86e450140080e12000c40869005d007550460420012140c1e40824590013108880f6400100c43c4c0340c0d0180c0f2801000c62038000c40d080c0c481c40c51f11100320340c00708002d0326031603100342003030280151108103001c03d0310032612a10302c05050038800792440354018001901c0032058120514100310440c42c180302c4c60009c961141190300c9080e0611b900c85a854050044ca01d160 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 239694595 1250 239693345 239693369
    0xd1206050f09041205130605120a090b0106050901050d061d0708040503040b13050306040f110303090609040e0c0a180606111b01050d09110307080d02060a0506010e090406090c 77
    0x98078021448116000308020001400c2d03c02103030449001d501a103070603410305196045c00c2901d5a002800c140d0200c1d858050084440d0006a2011402c1c0544502e965108184075016460454152001e400020850341031110911401c51040c0061041c28010f03c00301c401c07038003c920001070801c0058000b138a05403c0185850800c00441c000004175130450703540300d0055a5036109642c2d0398540490740c0c0c0200c1c1c2c3c0360080d0300c10312080c030144160f9025154003801c0203154800903401050390741d03c90780d012030350059018041c080035464654044562209050b0980304003201d50300000d22985019041070041810000c580000c1c25028491500548064100301d00c0310602e20080035074a01034080b022004080c0e0410004032644144195030350001d60f40b0003403210381040c0c5403140719012103100c824064481e040c00007c0b03088000444080031400c1c4c3d0003504403900d65803403c4000d0000209803606010308000319241c152103031000320344140d005803000607544800b80313010f00400846500c40710110030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 239695845 1250 239694595 239694619
    0x1b03020c19080403080a08090106060239030105072a0f020609030703061104030302011407140304080f04030b15040b060a12060801050709030b0f2202040e0d120605 72
    0x981e1091224140c90401805556107808503032407046400080c030703e80c00890b030082e802d0b42180b0310b903001c2c0041b03a009000301e549504040381c4d06c101c030b480314008032071640342c6c900700d0100c1ca200c40b804020001e2010442c0301c241d040219007503800039a407010025a5107014146d020802100b5950b4036070000000c01c2648116498080310002203400281c071030100041c03006100c0d03508008000c010755200d04240aa00128503959003160071a200a602550030240070b01d07244c0310b0886089210b08078a888002c0703506181180340d1a29040140100c4001d80c080040703442d180411b034054401184140e510796681e00d072906580420302c1442c1c40b0540900e0502540c11400c0c2d6804090f181300c003005142c5900c48000c014544400703072600346e1052816503e01401d1001d87e69006a400341543e0041290b6030050320307440c045190580301119016080804480181340f00c1d805881866100740c001031010074020080c902c004d0405a410f1301c2e03880803c010b410380310b0030350000e4010b0000809044a01c00d280c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 239697095 1250 239695845 239695867
    0x4030912080301060509010203091801050a06324503150a0b0406080c210303010909030302040b0a030b040b0a031a0a140c180406050303090d03050405040f1b0302 71
    0x2c001800f03940c2c18004081100050303a4420402d884007078800074142d000c17498010320120080002801580c0c010525441c004ca4414040e00d01301c0711001e040340d100c0900308000c81e0000c24200000c845001000b104011052103a2011075040c440c031520480210a02000300b05080d601d1903041c461695002151941d040c5580d5022030030f50310311005005c1641c1035542d1041903200805284541e50340c03240c5000804220140300041e0040814819180e24040d25a00c680002441c246510402607a900410061001410720342103080344a102e0300780581425194100d0f00c0320340e0810421940001e640c0c001140c5140381074042c4003a81107040c2e904042050468458807140100c0e10009802881100301180101c2e05503481452003c0000d2040c041d1410991413044065100820300c20071088400a04a080e2038203218203800c03a8401401145045601028008803a4041000b0303001e0000070b100010340e5403514000c03249000d460943c00244040c6518004400c120205150806c251050100490f54 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 239698345 1250 239697095 239697097
    0x5010309150c0905060d06080c010e09010b071b0603020a02010f02090d02040e1006030503130905100e0403180f0303110304030305070b0406060b0d020c0105070e1011030d0c05030403091208 83
    0x15140703440e0049400c800c410000d03541c4203400e51109400480008002032592515400309065602e42019100024801401103540c45200038005030b02825070710041080305040c00003042803a12035640e08100081c0c07486280c0194480d5406500440d0700012915143ca9080c4292080815118001c50802e0481030102d51007511907d402400703503586585019041c4010040c028220031141c2081c050946c07030349001912074000b00442d11a003540e124002c04c0494050094a00c510101008500d100f850130124500c0300c0e9010744103505004240150b001784651062401c40038100240550a0036455850024000b422540d5540c441340c0081c803003400000ea00c0300490707041e1600081605066251414484000d020300e07481440700f40b100140c1780c1c00601540d00a0b140d96401c02c0f00030010384c0d4811030155121400c0d21103442d0f1210b03040d1000b016041c060700c6aa108501e000040340c1c14055544c4444007203404441d2048040341e4040304002c01c055000d10400c018041140c00700d800c1c006183c0c1c942045d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 239699595 1250 239698345 239698373
    0xa0204090b041b062c09280c0f031e05180706080c0306040c020304090504030306090606020114041421071209080307030503130f0f0605060d02060412020a0810050a0605010309 77
    0x240400c01201c01720750040c845030b0f1401c0420002d010036944d0601158280310101c0c044090500201302280640421100b44202c000d0003980761a5081e1107840e8040c110300400e10b46586480461190042c00c010480d070340f051510070348801101c0c108610044110b00d04e420302941c000002c002c1200304019540240d074058a81054003900e001c00d07614000c2c24181d0641c0910f402001d042d5160400300030506900d80c011b0400c440b82480d003080083d40303c0314128280c500181201d41c4a00011020070001040780002020150303103401600c1c0344100303000a087c074044c00d0f880360701d0240001003540e038140305e56100c0001d1a00014108002c4840c03500e04d00c0390710f0340a030306270180c107102c000b000140d03000c940d080d0000582503111810096242d01e03441c1207a80d200b8030560580e0010303e070600185240c1448142890312580051416040c02d18184ca2a550366554500898111031041400030b5050350800c203094110700b440c0742c0071520703140c9202220212038156001904040c1450b20b480041481e202d64040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 239700845 1250 239699595 239699627
    0x10506011e0e1c05100605011706062703030705030d0b0108060d200607030f17060a0b07020a08030a02100e0a08190e12010207050c04050c030c0a020a0204090b041b06 73
    0xa84002c6034901d660f007500702d00d00007600d03500507036507580b950b0211644030400b0386e0300988410b00200760305000032942c0d6104545090b0810030401c41e00f5502c0305403181800103ca07185200ca0f0728500400082429038109200813038550b400401e0720004000c260064101c110401c3c601504c6600d03001002a1880d0f25800000c0c10500c48120166015105100c2014044d80301034a0f0555580940c6801080322400030b0881c0006245c144950031840b200c0c0c1c1c04071713010768402008000b905d420309510841c0c591041204030f91003030b26400c0004003003c2c21b101500a91903207802030720340c0c1d014514058050792a95103050750031360800741c880c1d000611284246e03030080caa5011490501a400401035810803003006c0c0c01030b80702c80104507410900e041500104400e170b106000703032030f4a4004d003414041561000c4d14800c0c4c1c0c005c000d1002848810f6401c014042c4041c041c411500008400c2d0045030490700d0410b401e64114140700200700c1030081d4281e41c1c0f40c01301c0c141484100c03880e2500320b0050008580e085200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 239702095 1250 239700845 239700859
    0x90617010903080c0a09050a06050306041b02070b0a1e080603060f060310020a0309050f03030a140112020103180611090a0519170703050601090c0f090605160204020d02030405010506011e0e 83
    0x154824030601b100340180c000a040680100c2d25500043c1041c0c2040b6403041c86542049011000458448241070f0410b0490f00144080742c20110050002d42265000b00101f2803019110800b446074449a80c0340d0b9095500e0784041c50410034141414510010200350111b0780400510101d03440000e40c00122030032008006840d540c0c011400c038060f2041c542c02405511604013501120807011005500038500c0e5101081059410000300300708080034403441c0d050030300700c1e5001c90155001e0f070084a000328170701c0c1c04080c0810312695800700300d4501140c1c0510303a00c4003181003011030030070700382410140004803200000d841000c0752110302d030a481d0181c0420101c83c290100d11150b000c020b00c4019641c02010b444071517840748642d82c0144140380c0000000349c107404e0081c0015004440002c107850b229a500c0e0700c1e2a1190740c1d0b0403000c4004d8681203030029403c000d0b40341c0300c02c1d581c406140102d104034000308103410200300052000710307001d00141040c00d040030f81040498020781d0b4805080d00c143e5001c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 239703345 1250 239702095 239702107
    0x18190b012102181f030b061905130b040f050649060b0d0c0e07140a020303061905030304090504050f012d06062001060f090617010903080c 61
    0x441c00c814660038002e4201ca4204880b00d0200c400c0a5030500c100b0b0001d8068001d401644202c501000c1184030143c0682c03000408201c0c0d50410708800742008250800d404096030b0740e41c001c45d10748c440a039201c850050341e51a058010f46414003914a0904d07000c08240210300b4002c0c001203402249206c03841d4407101c011300701030311100090600021401100f10702c0320364503440a5000080a010314040301e00300d10f01000d00c00b0030329107125105801074220050b403400c00e0402058040728440600600c041c420315001041091403060020078409007a5809903880e4100b403428032003010101c07001c61291a01c1c2110a00c480e40b03002050b101125004072005c900d80e140d42c18101d080c034131842980c0c175543d4203110010182e190b482000311005c8400c48204111030340c171040c02004a03140ca00a100007c0e002513591407000c1c18200109004480300b6000044003660f5110100e00100b150340088c8003980c84641c2001091101010081d440d03a80e50002d10616186079402400080700030564040458007040e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 239704595 1250 239703345 239703389
    0x9091127040b04050a0b12070621110331080d23010b09100c0b060d1b030521040f0308070f06020c03031923060d0501020318190b01 58
    0x2c10322203040074000300058140113440302c029202c0041c0c210301400301079005030645c0c4000900e0a00302c400d00d0340c6000c01e4410581001d03400d21190a0711814140e128070303900303540741448001580600070303d15020801c00710740702c488041c40d0600581c1896014003640d881021905040444000101200340080c1d41d1410b8420398510204031256400002507510003c110821000700804210908a4400580c010020422500c81c1e400d413900030403c0381040045419400c088038aa1a180e2244184400b075960b480119841c0b280a036000740e603664046804000c0011101001c030f04110040011649824200048240640c26901c002001000700042040130b120858164807a02613000c68190759444250401e1a0307203402c150741c1075645e80143e84603901511510b10810719043c0d00220b02e4440c0180008440c3c4000e0b400510080d04400d111108600040c001e00c010761045001038000c0c0d00c2c0d601d10380001031030b04c2e08a510b03808101a42040d2070700404c807910416411a180781040f900e051141e0f202e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 239705845 1250 239704595 239704601
    0xc120c010c1416030c060816051804090b0403090609060905150306010e03030c0105040302060c04030b06010c020303130e0f0a0606080c070c120605040b0f010b12090c0307060909112704 81
    0x450140790303d41d201d002004000c44244040200c8640303a50701c2c503c64071042c110b400d49066540d40c41010500803c200381c548100040c81c07a98288008000185280d4031751540d40c130f031340003c50301240003800000e01401540c2c0c004034174001a00140c40c5c070490580c184008a60400142c51180054810100c00540181e2080340c070b1030a50880030f025203031180741d10710300300d0302030300e01518120054018040020a070f0407810050300c00301d0750469410110350716203d0040d6800412440c0c180d8250104002e506010f03123101070001d00070500c0c01480220382c039100076480060032002e4020701c9041e08104e401c0104d10382c041c95154100f203900c5041ea68849103490906c0028115501000000a0052075001441001d034407881c8070740c6c001c4407000c086030b0314040115a008070900481e01c0412042c41113140c3d200001ea080c80d440684d4034121940c828a00300024036002c9503070702080015161960510264540d40603074a001e08120398080e00300700208050454140007118100380c52040e140344004160b540360 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 239707095 1250 239705845 239705863
    0x60905011b110d030503040606090203070e040c090506030c040302030712050d140c0a230a20061e0309150105010e0913170307110f07061115090c120c010c14 69
    0xc2c8080020f54440ca00a0040c2d0000c4400742c9585241c04400a500844d90080703910860f0143d139060505500c00302008000d01923110407008002d08010003085680b14400118010b05c81c482c10661902c4ca1031040614228603608094520a041c081000001d440054020340c0c0c1b100354284040403011103401c8400f0380c001d115001b0b92170f116400201050001d05141d61510103000c002c03900d1902d814035240ea544079038100000300400c0000340c0c00c0305101e0f181c441400744284e00510b21441e2050100600c803480411400070109400000f0502003204820040008101c54604a010300d43d8075240c0081c2c8062000c0036114083c3d4403c0b00010b1109151040f0050055400350230391704004591400e2081079001240c41d00e0100307a100c0d00c00d01a0300400500202d0b00704240c0001c0c45098200041294520499682c520140c031075103502c084140c0348100c00e1403003502c02c0b42c000d082c0c03ca000d004020000d410380e80743c04029000082c5040169078044001024035401c1000c0303069450740501100e142c54104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 239708345 1250 239707095 239707099
    0xe0405031204150c0513090209240a0905010c050a0602090103022701021e03040b09060403050a050c1305090309011107090c11010c0f0503070c0c1503050f01060905011b11 75
    0x40c0c402c0204121031040140c00145902074100151400e04105450300e2040d0910001d6107004207508005e46e001d90380080c511044050040c01d8510498200c545080d00c3d040d15103100c07040089980c013040c3d90b0003030f6001e00400003482d0030141803520f600c0d100d407a2400100d02800c265000a52181c00d64002e404480340c0480303140c102e4141c206805e41e0a074194000c00481e60040c0034100d000655660041900c2000d60b00c2c0d003020314907003850020106c41690121924641142d070500001010a034140241c9001034042d202403c03a03a4080010031904680903181020002d10740390510100300c40000079111000000c0c01c20300a101030840c00580b4000c2e080d400000300509005c070f50018030368000e5100002d9030841c402881940540074007504c459104a07501c1d4000f40c1d05100042200788034440079855103028403440035071107858440e80d031401610002c100001c01d40710130030b0001d5000424201030040420b481c100403050700b8080002d2141001c1005840b0a50407034850005101604801e8000c0c4880 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 239709595 1250 239708345 239708377
    0x305070c2012010203070923120f0f0d21060f090c140918040c0911040305150103051207050c1309020915010c0b0403051621180e040503 60
    0x1c20800c800d1030048120300d6025a00d264a5294034060500981c0e01a54194a0f4004030fa4202840c400c0060b200c006a170f0306030070b00401c401901d03031a88110000c102c5444805000300b1552800c10a282a800c1c2074200c40660044022450569000302051000e01070311805030446c0226490031005800303203401c143d83c0f403041c0002c0002c2d10406980222070007049911919405144019200355a0080d1441c65400c13125901555036101c2d18916001d5000707115812840c5110341300c600c0541102c40c40d250702d000b540e50004043c000c0c4041040b0519061111500b0305513158110354402d510360888004004400d02c0c00300301801042810300503180c224102030500380040040c044100d024000070101640101140c00106562085542550740901412303140c206c4000010354600d01039003001001901005424024030440901c801e5074110100d0080700c0890410401c0710710b100000003549030200c01e000c1421a0041d40d800080c00c2c5204503801d503074032203c1c00d684a00b882411807041007017014103106 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 239710845 1250 239709595 239709623
    0x50d02030c010c08010e0a05062d0a17070e07020708032106090103120806010509041b11030a0903060e03040806070302120a06030506060d0c050d1a13020607030305070c 74
    0x54000040e0615003081d400a0000603030303803402950045402c0c0201702201030b82d0340c0040d01c5107640d504110341001014081c0c2994201b6418074104400b00c640c158095641a0910b405031481d01088480140041000303602c90030413500c0b103055940200c3e1140030001c8a82c83d0000318414000d0140c0c200921800c000d4980d211a6000c0c44040640d42d410103541020002002c142c15007414185035050b664000c0e0340002108800b4002d0313888603c008c02440c10818204142ca07116122401002c0f02c1c00b060410700242c00744580405410240307a4081d200850b801444214800c603403001c1d0382401c403070700940f0020741021503410303250961055820008a0780b1070003051141c3c00703078194028081c8485101c4a0040703611140141c00c00d554227884050815840300021607003a20b0200b03490365070300344a0a06440c540390754001085107400400300980d45101e6543c0c5003441038650888055202c14a07400080312789445500080a50043c1e28001e410959240002075240b405412290070054210a800c03910f58 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 239712095 1250 239710845 239710847
    0xc10050108070801060b031302060409090803040b0f090a0f0503070c0605071106070206070809040609061203120b09130501061802210705031506070f050708120a020a031b050d 77
    0x101003071040d00024460341e4800a100c0c0c07810b120312020b59001040f5113182d0f840d402014502c0c01d01d4500d0503648030108001c0045c0e9442e1500c207001b90940308000300c0b9281e00d0542001192138400900c0802c007a10000c0402241000c041030f21041c40d50300c51804040e40000e42050352850041c200020001c50b034546003c904603030001c0140101a10410354085003298900a1102e14013541a009402c0081406110f0018219101600b050500540001441c1e40e4554440c0e0a07544c00340e00c1804100302046081c01819400000d0001c0e58075810404d0107074040c40e20110705041c40c0208040c80340340b80c1ca0450070401c43d0a402a200822603034018283c1002c5a00c589002036004c002d440c0e070100745454191080052174090203205204030f85030107003076503031310400041900b0400d4002540b0903005c01000e40080c103441c1c091092103000d10000c012440c18130707c11074a461000101e40d8015034003800010501640001d215011507414038001d48161b0701d811100d100d10050b460300070a0781c020313491100012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 239713345 1250 239712095 239712101
    0x3052a101403040606052d460506040e0c0304020105040f08060f07020607080604020c030d020706060305010b2209061d0a0c050f0a033207032d12050c10 67
    0x250f01c080b10b90140f03805607c8a0940c0680f15080003146081c900da00d44407036860719200d007900140200d0111804443d15210003000c0c56000d11241c04c1e082074150300070001c51400d0401e9030191034282d131820b05e01828101d03a0000074400504041c00b6002c0000080e0071079204005440050a00322004030380245c580b9902500d0704411214030418441c02c0000a904c10b10005005009082d25203a004c21500c0f030905000103075002081da03003c2480200200c0411101c01e200500040d80607200000301c860039031802c6800e44029001d03041c812443c1c216143d190740300760301e01085594042d04000a071480c16242440c09001138501c130f02c004000212101620304004613051210f18440c1a007203d2880d110b400b00f020f282448151290031105034042440080c50008200c2600d00d04c0ca40004c0c084803042614000c0401030241084558110f80020810803c049807180003e490010041c40007040d40307840b00c00f01c0c2000000180400300c00500701200f0502071411104912046016903a400f4486040034000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 239714595 1250 239713345 239713349
    0x9030b0f090111090d110a080d080a0e073b01120c080d0909022d070303050604021602040b010e030105102301051c0f02120103052a101403040606 64
    0x259400d11003c1c4168641003004c490120f080203062a00c15074142c0c0707500e00d0540612441ca42c200c1010703c80400c420504100c0f2000c100390550740c4201c0b07071030301c50005c070240d860200407401907034046601403141030500d1040071046840fa8490660004040d07041200c07a9180c07903c0390100e1007020001082090710400880c2143d03001c0c880c040d00059581c03c06990b240c40000b41c03480001d60015042c80210031a4004000c03035041c9070030a411840602e00c8510340050303040500400e168000900804254040c09400d9000d03038200c03011410200600d00d11551220a000000c1c0718039958003807211581e0242c0c00c1400c0d001c030043c1c0200320301e1402d207007412260002c40c001c0d200200c800001070781e4405402e100c1c1121049040c0c0d125801c0c000c40c030068000d24805c0008550403207803035189559150071584040c20b0305034400c00c10a40365514504089041500c500001001c400d81a00c050703803040d01440001045450941c1d4071030114580b2501103e40711200010320882ca4030001c00d0100b400f20640100e82 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 239715845 1250 239714595 239714611
    0x904020d021b060f0c09030309040c0207050a150509040c050c01090b061206010803073002011401120f08030702031201080102030601111609051008010504030801091113050d0309030b0f 81
    0x95000742a0008560740d000c100d03850700143e5480c4c1c3c0005c0c1d43e500107001034000b00501404980c20010340c1b60014051359131500e18000185c1c00044108080d1070410000300c0240140c642c00001da0b1901c5c4c2000f020392140d00025401591105841500d0f14840c2c011940043d030110000c10119140c4c1c5821b00764400140d5126100f00c00303001e00803900342004500306040360900340085150075556036451403059000000c60305428000c0020204da00440c4441d611404030641c0002140120f18401100000f8180c1041c590041c1d140d00074000144054512007125803c580e14030b84903070340d94408a1440c4600340c1d40b088402c0f54280000b46002054014601809098a801d881e0501206550780d032209158107405180026003000c0200140c203510150300140c036103404480080d120000c81b429034000b80e5086001500351130042040c0b140d035104482d0340300d42c44030002d440d00703422400c0b900c0402c0082c002c05200d0355642902d0410107016070341640c02150f211000a104d45010440102010421509a4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 239717095 1250 239715845 239715877
    0x702010915020a060f0c1d040e1506010206070c02060a030f020d0c05120105061c0f020f210702030903031c0902030d090f0603110d050403171003020f090f07050a050904020d02 77
    0x5c1002e81c00d80905108400b00381e8452403036800300426144065038143c18980c00a5480703a03052003445080c4550010420b016850b4030b002d0802a00080ca0400d0040c041000c0200340381718200140c4c6c42c4000c8070229261482c0104120204180590080c821810982c03289481c0c000074401c500d4000e030207844107861810603403503103a80e5007092000600c07422000c620300c02144402d0149081e2164041040c000c000140181842c994410480c84e81e80208180e0041e4071b5a4124125482c40d03648410346c3c0100c640c40a1401c0054450100c0d58a00803440e4441255482a1980d00e80c1c1c034440e03102d41e65241d001822220494a41e280241117401c0314020b900000909150120722180030303001d6120390140c603c00d0f0601d071072244900b400c0200009401181040310041d14007900500003210540030385001055201400c3ca9071042014078440b0b801384900502000042000e200600000a0350050765414015564180d80f01c0840303c82c41600d4001d50700901c049240e8010420980c040c255881c0d440c1c42c14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 239718345 1250 239717095 239717111
    0x31b02100510060f050d02070204060603050f150105030c160203030409050405100204050f0d110a15090806060901120c0902040e01050a090209090a0f020c010f020d11040312050702010915020a06 85
    0x1e5410a000e801100c020800c4e0340c20280c0000d10900003030441140c1c40100509150b5031780d00040079503490b0fa01c41000241c59030140203c0803141d40c4160340180384d8255081504c0703035080000c0c2c6503020050503d1a5600d010400543ca030322495440c18030180e00409a0f9566520f500798000104001d036401d8465110301034590710380c084144200c40507034030002e006644008507030342000403402c0b117140115001140034082c0442501d17040b007420007410750402d00a81e00202d0b40d00041414440e07038804c00450340f15800344040e54407000c40e080e0540f45413890b200c11180c0c081c10305400c07070403c9500000489100140c00110301040381d814078162001214208815590b40251509a000b000c08080d4007214000104045d048640e02484500107102c2c40981403082082c03c0c1821516203400d90b524080e00040d803411010640d1090140300c1010f414400d04040c21034aa84460065184103a004d005000641c0000c1da80074020310f85c0240340715001d281c2401030841c4001c0d125180030408541c00c60030000b02e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 239719595 1250 239718345 239718361
    0x60a0e04230718050c120406060302190b030103020607020604080d03150e04050618160803091810090209030a0f05010c1404060e04110c060903031e0c0301090c031b021005 75
    0x7002c0840d500ca1030f190100100c3c0102510007400042c05540240108026415002d8801d0b081d992156024460002c0c0c01403450040c03010039100100b44110300c07107666074280038151281040c0c905590301039a5440d00d82c0e90920105085220b96049240343d840741d400c0356245242d15400104100341c455000703400041e030f600d1900801500540700181349811a00002d01912590308030700c0c501a01d40c100715554030090003000200320344182c10480841d0070015038940507007008005510911402220b110710f80c034114040c441c0c1c0d54814082d41804940004440096907000c00808000b40c0d0802001001e50b40c0c80c0c94420300030100700840f1400314000e4042c220241c41944180c41c11a160741c0c59244000c40000100700080c401c0d441500c400740c1040c4941d0700440b0041003075a2203a0402c50007180d80e81860705106494400341c1c4a6031400507281e008009145032100e003a0782c11101c544c08003040510100f8000d40141500c0c00d00c04012406048000c0c0c0e810368005507880c41051409003c10a80e194028 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 239720845 1250 239719595 239719603
    0x2280807050a0c1a01081e03040807031707170714150601030c180605040f140303070b13150b040c080609070e010212040605040518090d0503060a0e0423 67
    0x1940c10110303406006a04540740a620810101c9105005008408100d01000500e02c0c2c402e802c078490a82c0000b840f9002c8a01e81081e0700e0b0080300180080d4145403900300c450b90b4810103404002c04040303400d01c040d0030350003d500641c1c0046a02c9150240410041c00e042c010903001840305450441d0300340d44400c2d4180000c50910614080b40342000d0340c6940c0e034070040d400b40c1050500102000f01d1140310010704001205540040d081c1c80c1d41b901e035198a02180981c50325103070307000102e080740034000400c03440d0b03400021514815404650040d050703803442c0080700e00ac81000c02c0540380b5a03010750790169840f450361082062001c00c0b503040000150f803074000c80300ba0320700f04c5032660010000702c0481c4481c1d005e41e1481c1c4a100c81481203d202699402c000c81181c8c21640c07280020810100e0240510304d40f03c07003c00c80d80c0c0004614243c461a007190380541d502c9041600c0c809000d000004a10180c5170500e050000d0801860300c2000c41c02d0520300601c401040d50515001c5040081c5502d10303549000c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 239722095 1250 239720845 239720851
    0x80a1a0f0f04170c0307050105010e0c0301080703060b27010603110c121e070f170a050913020c0106081b030f07180605090c031008060115110a06022808 67
    0x1030440ea0940c1c46949019062401c150f600f905500b06000b03480710340f4020001404507030701c18400418039514003066050380803c05842c0c9642908148018400c8a000240c500212a001030380420860307455004524031040c03a81c5e0200d1400300c0461a0503520000a01003412666103a80810240d41d1105041689010b400b03007030303045500b2600c00c0245000d4103002402c51064070301c081c81030507012080312000f0780d400341000b11402ca00300c60011092012a501c43c40140d548641c81519001440300000c0240c441d07058200d1295008081c080025884c560685890307034643c40003000350725214050b440d038405d1944c0c0b10340190100e01070600040d0070003003035100b11100103d000709042800c00d40c0c0850f2240302c2005c0c60308420307034880c00000c641d42d490781c0140c000c010305c41e04030f650307424001920000c100040e0032001c3c82c2d40c024030041003103e4000c11506450001d030700e420f00b1107400e08140740d07003480701480014003050b0010880d4181c0911030810529405030303403940ca4a820034400c500703540ca84412 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 239723345 1250 239722095 239722111
    0x1912020c030d09061812031a09010e07020a0503040609050415050d080a0309080a03050609070306151b0b091e0111070206030a0902040c030e10090c06050a09080a1a0f 73
    0x303002d12440c4034595044450418440d1002080d80c00c98840c41c22291203261000b9075440c42101c5680c1d801ea82c062081080d6500c100701402c0800790b00c5000f00c0c03601d03041031140d41c5d0082c030594000b9500038424001004596484001d136992295035550007840c180260250510451800c00b090304400d4520717040d41c041301e801502040c0044455190501c0c01c0c4c100c03550030820701d6202c010110001c1d06800c002d10880016440c0001c6030f0414038103201c04104010301d000141450200148014001c801400360720b03034950715200f1180030141c0b01916140e2184070000306058907070400d00c400075602007240b040701e00716a000519001103424000d0b0984e0031720200604403000c200003c10160030a58003c3da4010f460b9503003c5032a2031241d010a00700e8080c102010006544d5030303802566102c0510124110300e449900c18080011181c540741d05040481c403446061010000360250118041c4044000400c024420360b982640d0604081e100b90021302c1c04203406035502d80c006581c80150541c1c00d8014050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 239724595 1250 239723345 239723347
    0xa1b0f1b0b070e03030d0f06060806040504050703021003020705101d15070c030309021008010302010306080c03060f07031506021609050c0a0c0c0b1308010608120703030b01141912020c03 82
    0x101c2c102a500d0b01840c15002c1c2c0c141c0401c10941c00ea595160044c0701e007400820100280031850300f44010320040c0040c0039144514200340c00d000100d40001449800e0300d4048450240100d0080c0c42a4024414444010201c1c020b0307400f8040c220000d98170081e0a200c00130401c4164400c10f4410710b40f142120b08603083c01c108250003151a20b8400c4441d0281c00d0b100c0d0900140d070003910b0300045c1e00450b0850386600002d038900014021944d150044074000c2003400018220810705030006500d642c80204404030f81d00c3c5440000b07010380d10a4001d0707144c1141c6403030fa510010b521070200075200c003000c0d100402401d01074a0006003c00381e9201c6d030380c4580d95031240d40d41050054803048034851003011058600600600e408503e070450f060081c8601400d00d08070409075480c00406e83d00b5104164064880c0c0d810014a82000303248080c00c55155940c585000500003c1e07080040e980449202c1082e50080300104190a110101500180f41400c1540301c050303008162550342821307441617803403012040d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 239725845 1250 239724595 239724601
    0x304050a03080d2403060e100603080307020c1c0213090b092506080402060d09051b19060207050625030f0806040c0e040207080c0a05011d0105010e0f0a1b0f1b0b 71
    0x81c5600564442c500c21302034030344101400c1148c4d800c3d1040e581003a5461080003041c0440140c04110100680d202960000520318100714000c918106a6401034080d02d40140000b820f03013080d81c80f4519603540a0081041401c1800409940f003501b02611501c0c0821905281305d09000c00006a017142e1a581e10440c95665650900819802450b951651aa100e920050001d042413104114a11a04081d038000d6281036007044030000f6401d50306111f1000d0b885061106030382c00310729603080d01c030140d40f940c1e0b645016501070402c03107010425014418008082350340401d613210784120410002603940203120345400701040102c0300c1490916021a490003407070002e03814280c0142594034044e07130840e130404687c08001421325074220800c64141c1d41d1680d03244540c40d140e60185410010a03c02000b0540c141009031411a41c05000304260a005000003468115a0740100c01031201410040f003908102d107001400520007803114001140041030250b03d03901c403c418220341503400c00300c000440d403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 239727095 1250 239725845 239725853
    0x15031b0418030315061b120e0a1403101a04050402031509010c0e0f0a03060e03070501060b0306030609190609080c010914071d0f06120d0c0302010b060301080a0b090304050a03080d2403 81
    0x36000703452140072300c08250000340140da50943c2005c002e102d4442315580c0151300a0425050003542e202d0010071303610702146052070715a088405000304405507000610fa4035140002807506d505500005400075550040180d0710506403c414030002050700c0702d1040381181c40c100540d040034807070465081149000d0420100e90160401102240c00800303032403a00901d91103d0703007580e85580188131142ea00006010349402c1c20088164080c0d6280054040007101d4400118900030710100503200b640c4400c9420144003444003124a4126000020858002145081201c090650149015500a55800140505c0110019034410042000d150003656500f80701408491014011640001c51780e80d900118000030011070030103407260341790440c6102c4549002400c0d6001902481e001780340500c010410120300050b504109a0710807588821f40ea01d8130902451400789510640d0302c900c001a0001c1401030301d0b0003c2c034400c0303031844c8203000e1619407842d4030800464082000d10380500100c0104081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 239728345 1250 239727095 239727113
    0x50c0103050a020c0708030702120601030519020112020315130b010c030c0503070804170f0d05120406110f040f0e0624040b0a1715031b0418030315061b 67
    0x2c2c10240005040464644c0e401e4076113070254109010702c1c1d000180180c150300d0990411007019281d100141364030740c15540ca9035124201c1400d03003e516842a00150210b80c040d217405d003240320508008540f03d18004c1c0b81d190450180c82c65050117100d40140c00f041d00010f41c0107040c010b16060312030b0f1076030a003a0f5404598800e40c11038213445601050104200050581d0300502c000c001e8404480d0b205008488014103203039601c1c4040e0203d91001444441c0d80707804c442952040c0032200208000c95844c0c3c1481d0018000d031800e50381c0302d407100180c4069500c2d000405482a0340e4a81c0c0300c00750603915801c640313002d42001e0721019840741044a54025216142c80329039003540080010b40e05040c0d5814418040786c00255203503000c43e0320103084d038000910071025079a101c042807005010460101c070200c0d894129404041c2855400d889010445440355000214100380c00740c00d0000d04071542c03d00800404d0800341e01c4990422884002030300c1c600c200170b0810a0f0320104581201d84081c0d50302d454203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 239729595 1250 239728345 239728351
    0x605042f061c020c0105010608090d02060a0f0f060308031006020f0303060d03120c031a010c0308040305030a09050f2d0705010518040f0e07060314040209070e1504050f01050403050c010305 83
    0x30b01c540c2e1008516000005001815032902c01d24000311301c81d41448005084210f0051103a00543e03c01c0b412212a144d0005006401001880c40042d03800800840b482c040c1c0a04e0880b0100300e800c0c40400802c01c444000258812042005e8007403c480d146c10040740c1f980508213a0442c640d00600105c0c0c801d2404079415041d080c46828246400d095034400131302510b14440101c0f02099540d405203602104d03c51180391140000d01e4006131030503450303a01030807410005d000501003141c04800910600300580c40800c05680250403141e80800003441d181c0d54190302118940840d29880c00304103044e001c4602c04412806120107880f2150a28004540c5a040712075615041ea80161388044607441d80d1007640d2050f002c00c3c8001c6120700007100c00034a05501c0358010b00804d032402c00660303c2079100000854120740d0413038405141e0b45505804451b90885170400652005002040100442c404c00c0200100d92055424140706850500190790360300481c4070282480e00b1584480c00658820784c4610740c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 239730845 1250 239729595 239729617
    0xe0c030a0b060a0e1303020d140a1202160b04060606020106050105040314191407080619090809042301050613031b09020a0e03070e130821040605042f06 67
    0x51a41d81c0d80f200410104c2540c0760343d0341009074601e04052560501010502070349038244a050703540030340b1002000707100300144501004100e03c848548940c1940440d142c40c154070741c03070340140e96a9040543c000c04040d581103a856181c5503000880700e0041c0034560440d50141c41d0541018070715250400c1404009011400c180200040c5044206403c039090000354010351070050603c51000b095450000765421105565101904016446241012003045d1985011012416082a180c02d802d00d00607010460750060034000c81c1c00340c401e0002d028440036000100c941c4803d9a03202c0c00e0101d503216640c800c01c451000c800c82030001c20307040070080f40e80d00d5112083ca0000350b500c80c0c0e030303030102d801c07400000c0000341c240000d4000514081040001a201003001c0c80e0072400d0413489100b6041e04500011b00c0380c7c1e40861400c540e000c55450003035510f00c201000d44500e01d13051400d840240b2044804680e104503091150f0980b6000155003c043e28140189002e220440020000550011303041a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 239732095 1250 239730845 239730859
    0x20904060b090c0405180c0a11011104170601150507030e030f060421090f17030f19030509010509100b031f0c0f0507050606010e060f070c05040e0c030a0b06 69
    0x100168440c0002c1a101d0320345126000e440d103040900f009000d90f05c00c00355844560000e0140700c0214075600c120381c000780b120304082c10200c2d10403c1c01c034050303c26403d05603144172002c100016051803020051048086003410f807452071b80c88400c0408011404410b07000014410702c0b00d440001c1c0905e01072036078203400400f245c2e0240d01401c4524603001c02114225008c100000b04900505580c800c9150840140d00b4403500c0c071410445889503401091142c03194540540f200c02410150500440e00014116002207540e0011010355940e0b44235010050070000340740c03100150f04a031040c031910740142d1000000d010400401c100400c05044004046945405008070381e038000c0541703030301c007a180c140940c1c030100781202c2e1441d0181c003900900c0c040200303021082103250005500800c080341d01c5182400d0200050445034045012400340c8020303010094000a92041480881400441121003c480910a60342c01d641c0107a20b40345082d422a0301540f04403464030010300c1c00c40e1000c1d8061009054a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 239733345 1250 239732095 239732111
    0xe0103030c11040e0c010809071d0408120103110a060f05070b06011202070303090b060a030305030f09010204090e010b040605010905060711060708030f010e0c1e0d0e100b09100506030402090406 85
    0x70101c502c0d14042213001d40c8a030150398440c0d40c01648907075028035813401420302d03946014080c0c801c0010002d5580800041880010104034528003035440ba9140e6900103119580c59241c5080502c6540c4283d900c01e50f090031000131028441c29607010414a2555800c0c2410744603621100012000351005050001613040c07540d5010080c4003500d0f5030350081c0c1d40450401c40318101800241d9026007180d014580d115401c0c00442c3e00701c001c0b2900100c0d400d00700005030340d54044150080c019a0001540c103800d00d06041c2c902030054005040031300c800c81702007210a0b078810041d0380223000b03403090300e4003c4070610020f00803031100604008001300c094070007440c002e0180d544042d0b03584103c0d5400c50382c500601c0188442d4608600c0b2035840588515502c1c5029a03110b10072178028240d8940c28180c91001480014042e45908103954501e00d9104403803400c186116950302038501d60b0412406144803000042d82400700a81080443c2c40241585255454540a20506100c0284142c54040d260030780 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 239734595 1250 239733345 239733349
    0x621080d0e01020f0405040509070605121305070306140901090201091406040b031f091e0b01020c0907030b040e0316020d24060303110105040201091503090816031403010e0103030c11 80
    0x1403404c002558980c50b40d40d41010308000480304081c0074032140c6e60110006005039034000003220809800500c41c0c510550707840d041000103000da034030014524041c1e4400001000481e411081844911055018080d40c41591241c01c903068100c0180c005003403200104117540300700c0ca40285216018143c0341c901902c8180d5040c8541c820750701c80043c01c80c096122405d40311880700840103440c92a40c107000b0f005072032421002010841da040000140e849051030f406078020045040403210103000b070901031401c068091b008280d0700c1c0c0381c18001d40c2084a0900c03044004011181c0c54010559410300e8000641c0a10050010080e000c498100410311110a05850100c070443e80035030490001c00e0460961130300030700c404401112145280c1c104003d11006130307000810003040e12079480c501e2040b41c510281c00ca01804005001070044c100010f190341a108101000044d06406078031010b0848103203141e5075020b403000748035403034084095100500020b4440c000e1100304500032180c91200d130b60f4082c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 239735845 1250 239734595 239734597
    0x4020f121e030703110a08030621150105040e07050105120a090f050a1209050d0f060b2706060304150e07210606090c050403060e010e150108010621080d0e0102 70
    0x500302a0b0341c0041180d100301580401010204030030040903002d6403060b0f035101e0340d860101400342e43c4650300c1c6221a0b8031000c5810a81d140021000041307648810b18030444003488902802518015410103926001851340007404000f1950181e69051800f0b00195101c80303440c4c000b4001c40c0d00180c48030b0320400401c413036800c9500e08034001e40107000302c0e851034641440221100c4400384140052404100300c41c2ea1210f41c080c10094000c119040030700a5441c0440091550000a60f03020300c540e0855021031a4010342c07038071016015481404282c40700802c02090780012600148089800c10342d084c0341200d55000302c145480c0803001c40b00c00075180c0491110281c20000d640f00902c402c1d64000c024068117000303c90050030000001c10172401052402403581c4614000039101c145c6481d0a1900da100035802241680000c4042d2100fa2440b11040c0049100a101d604601e6007402404146c0240c58408012410300070929808503030301c00d544e082c01c0c5421078650400320680c1c6a0300b98aa400c0280 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 239737095 1250 239735845 239735893
    0xf011d040612080c06010807060e0423010f030b0a0e06071d150d0507030912031d03040803030103021e010c030f02160e0a0c081005040b0a080d0203120f04020f12 71
    0x344184c8031054100401d05d890816444040741d540041c01c10000d1942003c5040d220781c400782c5021400866120801d41c0100e25162844401e504001c00010341412501042007900c1c422078100b00591252400001a605900d2103407142e5040f0740c0208144600a9540319a298070310001500244030b4400010451345441400744d41640000a000c030100d03600b4401c0d0740e4001c64600702000990280d8130b408180c286d40700fa05005140d030750013980344003490400444110300c20660440b035980d503c408445890760401c1c4404c0307010f90300b40012400b07280c1481c80c0784a60403d060350759491194090300c0403607807206d84181420075400346110b9a079130701051245e5540034000c401041078141c01c0074a5844201ca10132071401c0c007000060002d01041080b920490421160100d5004c56440100e00008115000690002005100301c418089407660084007400c0180e01e4111078800392b0fa1180d0051100c00c40031240203522901d40034a96850b460480c6050050200d04001c94140110100354012456691 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 239738345 1250 239737095 239737103
    0x180905190b061011072303010f020403230a0803070e03030307030b090105030d08011a191d0607020105160606050a0e01030605250f031404061a0f011d040612 69
    0x240041003600d00380708030704440b0710010f0315101c0070205681c24401e40300e205c28000c04135010641c40803410403045650b011140100d0050081020300f00106200c0025401848101c2c0c072000700100c1d030101c1541204d061440b0240e2180644074030b141d55564489942d10081682c4280001e20203030b03c0345070710f00300050743c403c0304580c0340000ca85151404000d6207510591146120340e10803101d00350341c5940448140e04440355800480064141c1d03038540b40107802a800002e00001507045400303805940005d86c1d050302500b8801a416211003c2d0600c0759520402902038041181002510310003030705003613049840c41c0141e84c0003031265103400c001400024164454211116004014020301050303100d45904104060750031b1606c096850030001f008c4c0341010358031083c031180c000800c407414000c0d080600d04c0301e08080124440d2900d458404010310741e0300d00503810000008889035140c149422144400302058560040e08105410031808284003020707456001626030710001031501a00405840c1248a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 239739595 1250 239738345 239738363
    0xb0a02031e1c0f060b030c0a0809070504023c1207030b03010606052203030806060a03020706111c0c02030d0218040e0d080a0614060a17070f09090618090519 69
    0x40b0f11954107554082c1c0142030900d0081050041048a06046925011103410184840c0e41d42c0009142050700070340c4603d03082400018411846412403065110201c0e00c6912220a02080b2411007040c080c0900c03044801d210403c061140300c400d000d4140da00590f185004a02101001d0110f42075640551002d0041140414051440c1d002101f500407103d0300c21041d03004d80e2f4a507460050268601400d8640038100024000524034031a030115403031541c200b001807040d540c402d841d010213980048841e007825a4150800700412506008000c080c5a0a500441c1807508600d00c52000b58072000901d00c004000c1030071034100e600c1d24001d117628040450302904682c002001c02514442005000d2101185082d805001d0b5014000b00702c20301c82e000f91241600e0b045504400e5580211207081142140343d0002000780040d44442d00c02011240c59451b440780304c0d43c07034011030269811800340d00481101d80e4450b0002c0c121542c0007251482c003540c115102040c0301280c4400851188100703581c0088 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 239740845 1250 239739595 239739611
    0x1c0e0402091801050f041a0405061207082107050c0906180a0501030b0603061902161e0302071706012d06081609060e0d030e060f0706060b0a02031e1c 66
    0x5c0c2415089502d20004da07001c1c4502905a240380c2000d442508403244566035130008a61240c9034032410404a204031422120034544a0303003c0b6580303241d0301401e40e49650840f0001010415514180c50340b071035000700142040e08001082001020000b858590010f1464648101e0303d001320101c01d01a60781d480340010194192704001d0a00b40b802054540254031401c280041000c1e002d8210940702e000940058950369844101c0040003806a0301500031540b0100081110380c0300d410b030240c1980b084e0200c920742c6a80b90420b507200803054402c0100307908190010084544210401188044a400d000488100d40020b48075181403a402100010b40d20100700301c921183c8070410400440a07003130503c40a881d00700c0003401440e08000d128068545682c0840030180175004950500c03c0051140741c03104580400d4580607001f42d00b043c1c0f40c103820210001440000c0034101d50080046902a41c9441c2c0300e800300c03440461303040c00c04001ca50030401800300030101d44401048181209280030800d84 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 239742095 1250 239740845 239740849
    0x5100f0e2808070605070c030f020f060705061906270f050c0a0f1e180302031b13050f070f02210c0606031605100504080d02010b10021c0e040209180105 67
    0xf00c030f140c12400c1400b2003042940086030082c0e80d443c04a83c0d015486065040b082c1c4041814034400b03004054021344049421010800040342d41c0d403007040d85101d0131001200c40d6503070f10261950b034442e0340300d405c10b00d07000c1d070080006840c0c4400d0101441e5501103101076210020038201c03030302140c07010810200880e10240c62a84200c000d8a4581c40d4600b604414280004222442c00c0c113000c0710084c881201d14110481000c0130120004540040070ba070802c40e0714000d5290004417010442d486121280c071521a01d034160b1050074064104250455801e40d201542074170327840b1224082c4420f6200310200b20b5080c40342d40c18201d4a0700c180b400c00d40d07107a82000582601d1310b100500454401c1d0046594a83d08610115885007100d20444e2140b40c11080038005803518800ca4000e01d078603000e10801100c046805402003011010240e401301114020500200e0b00c80030f8102039020807500340d0210558245c400c040b0003c01c000010401450301c90800001a0b59000d400301d905440426903004002c94 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 239743345 1250 239742095 239742103
    0x60f220f1d090c040c030e0601180e061015110607020a0c06050c1b04090515040507050a0b030621030c0a050d020a0201020a0609030212121005100f0e2808 68
    0x4219a410454440c100320200c25181c3d03400155003400740d59208070751003403e4030039040700c5030b070700e5940c02070f5562540c4896600404042d04044e013103005092004e1194030b414000b0b051032144441042c400900b6040c14580c2d04001c500207041d108201d4410068001d005042c841d540c0200e00903002000303907a059241440401519078400c0341881810b004001e004180403820002884180020900703200d581c0000030020710009601509a12881146416010781c404060303000e503000740c04a0341080e42c2c80341000b1a420050203841442d0030188040b800328140202c021141083c2e12003800c60940e20480d8036451908030160b03e41c845c5c0e0021070710200344042030044c1071081d40144094241c8a51a400203542d803060510001c1c14503940c1d424107000d0510a2260004105404051581c0c80d2004100c2c144110000d645912103034280c050001424030340440c140308109d00d180c94034403104800c15004c0d40c0a40d0303c210230a800104025076105190281004910700c0484900da80003291306005e000f5141c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 239744595 1250 239743345 239743379
    0x7081e0c1603210c150e030d0203010504060e0c070b0c0702131b080c0906031e100608070305040312050a0603080c0304030b0c131a0f0d0204140906060f220f 69
    0xd0f85500d5003281c1c0060f0f40b000c0c03400d414035080701c0c00d1811309641d882c0c12801030070a0482c00c543c0303010200348074606e0380c050b4000b9812035400316418000c2e41d07110b120381d80800e0415618014940c10070001e610010304440506d90b030000d414101603048c0340307141c1c02007400565244c40250919556850032420300c17404820300c8510301024138003a401840c14142d41d11240c800c0720f22143c400e9102100003004000c2c4040460b900003510304458469050808108503101c40c41e008400204103c000021280da10910034544907541503600d9071b075a029403585400050401400c03681d54903490342d00100219040000034503e285212008648d48d80c55810400840c0781d01401150014008011030115111031001d490140c910481c40581d1080c442803043c8030512844480541d0b6070300100310881c100e111540a40304403068084244100c180300130401c08000d4085441070303403080007882140050744110020301080842020720038188801140f443c65603009031f41c0b0101101e8240c0f0b40501ca40300507035141030740c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 239745845 1250 239744595 239744633
    0x30c0702120a0c17160f080f150403120b0d0b0a11030112060c020a1401200c1509070e04060c0e010507030e040902010e040f0506100507081e0c1603 65
    0x1040b10229a070b140a01c00030b5100f903008504903640700c000710b1401800030349543c4c00c8104001c504565a1400c403084880b061003009114000d07400c0c440d10030280460f404803600c111042d031551999072035900b560750500307070030000c03110650340e2181c50340e1502c1e40301c078450441c1d00070040e1918514003100c6010030b0328451011203a0800042c001017000b1030004080c200351961140300400c41c0c03030800c00228604140d0b401d0290568031120050408185e040d4014030f040902c212040400d00301821041f031140c0320b0318070034220f40e502c044414640d02000da40103a401c8420f01040d070300110342d140b00400d0003c0c0180c42c2900e0042c1e841040194880e04809a0720f50381d4800c1c03d00500344982510041e1440c0300809007240915207800060045a10500c560210b00c840184100172000c0c660000d14018801180c09501490304501100d2605024a06a0310b03007503400703280e00707141007091300c50000442005c2e11500c0c1ca0210034000520405400d203c2d10301c90322400e919010040785142046015100710035999a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 239747095 1250 239745845 239745853
    0x20a0207031407121e020310150e06030307030c0510240f0501080f060307030b1e010506090d080d090501060803030717010302100302070f061a01020c0301020a1709030708030c070212 80
    0x4908607500040f110680c106600c04500740e0b104044560007801d001001f907150107001d084410303c10700c5520845d00c445000a060b0712482e1516228260300e0010754007154103500a05c0742000081c414088840f50324854403e44040548400550080d24050f42040c003000044400d0b0f054003044261004005091302c190b82e107007242c50880081c0491001801010b08140148001001620304102c00c000440d4003c2080c1d80d50304e851182d500b10b8172200000c640c2c3c02c401c0385000080d07030701e80038040c1c81e03400c00024140001c0c0c48003035545035941e0740000300c600d00e03441d1200071020100b5000c1c4030705802452013402640e9689080d040003041c102e41015044450442100184050313140c2c0c003004000610705080040e07880c1414100000e03081c08861006000d5810821300c100000c46141c51007145e580d003a0212000f0401c1c00040500b80d00445511100003940c03da884903401560700992078200c0790381e42c156032520b542034503004200d50049991687c1c00c480051540210f003401480b940141004802030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 239748201 1106 239747095 239747099
    0x1020f030406140601020604020f010c03170f011d0114040c1b05030a02010b031506010c081e0909090a120323040c051f0215100801020a0207031407 65
    0x8101607040d43c41c0454101d500001c0d0407030103654020417520a80300190011a080d1800203019010000742e2a01d41705001622850940130b07040520461f51a0342c1005040401402602e1641302c0241e00d010041100e0038043c01036141d009011207000c00d102d038111104852040c01420a1144030480104000400c88000020b018100701c9800070b01c840002241059210300d21848000d01c00814440058071540c8035140016005201d121000e04102180c07240c07170105000600c89250761070000070b18040920b01803200c44c1d400b58011000b000c040802e40c3d2035800d20b0010880d01401c1c182c5030810001c0d50071040030318680e0004a000c1600c8035107014180910844001c0c410b45028800742040c40c80019807581c00d03140310f00302ca50010602c000b072118034034600d00d4001f0012141c400e0080300c0880e82c2e240a000400b0705403001d50003814003170306500345210920180c0c0035210041e4800c042c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 239568345 239748201 := by
  have h0 := BRFrame.cov_init 239568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 239568345 ≤ n) (h2 : n < 239748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
