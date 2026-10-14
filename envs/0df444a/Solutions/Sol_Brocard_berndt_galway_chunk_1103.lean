-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1103
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:15:20.998575+00:00
-- url     : https://prove2.me/submissions/51fef79e-0ee8-4cf8-a201-5f0e8a5ca050

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 198201438 ≤ n < 198381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 198202688 1250 198201438 198201449
    0x40b150f10030609060807061202091807020c030f16060905180705070b0112140607080f1905010b0904060f030308040201030f110c10050603010b0303030103060c03200a03050c040501170907 83
    0x810040d0348a1b500b8954401140c4141030002d11a540683e1700e03160706000b501d0400310040c00d181201c03904182c03200c0c85284024a440b0440c440e0008030302007650100841001c80c280200502a44941d1405100c008070729500460140940144204003c4d20341801c1e852100f02512402611502ea100c01142c4500c181200680303202c0c40c0030f00100700300302c1000356920f0380f0b44a42600321182400260150310b8840841e0500b021a4181001600c403030380c0d4201301d42e0301c02d42d056400d9130344070b81c811014801c0743c0782a0091801d9000204140d0b000313040c140f050b240905840440181c5040c5550340092540400400080c109601c070050b5900d141d14580201416841d0468040c2c2c035580440c110a0795080c2c03209040346210b051102142a40c2411b1285c410480d80c06005141765a0039511040c0184c200041c02c1c50815660302c074101c4100b00c00f1700202090790b5003841c0b0159140d035001001415240040c0c20360640080c100810001603070442c5a104e51000d914034610101e80d00d80546904100c03095010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 198203938 1250 198202688 198202691
    0x309010213080706090f030b15060c032b060b0d0c0203040e01080d170c0409020702060702040905030301080105160f030c030e061320030d0c29040b150f10030609 71
    0x8500c110300800c0c00740a46500b60350f940481562401d1101c00011b10f88000744c96003400a01194071841202c2c00e42800c880041d080c10714201d4880c007094a140d03c0070104121410103407403448440202c1c0c04058145507031801007444464200145074265104440da480340540c2e41d81c03819a10300d030080c802e407801080070a12001d281d60b510500c59448075910880c502c0050502098414400280501c56001390100070b000c07420503090103640002540040c0d02030360f0009c01800110010f035298003607480100d100c1e80c003a584a51410990a0039036401800d2044010301d050080080c076907101d0611200e0b010340345000300310461100c10071303402404101c0e00c840040c0150020402240c19260b40d9445051045070000c4005400c03400200c40151401820b507419000b626040c04940d02c107240040e07115000b0144451000804485103640721080501031850002882c10002800030764545142d002c4408915401d80c12070450001d0300ea2010300a4852056070480700e2070014500c40c2c0e10200190075a41c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 198205188 1250 198203938 198203977
    0x30f03060d0f0c0b0c010e1209010e010e03030304290f0c0306061e1905090904060914060115080708060f040e0316080c0c061c051503060709081608060c03090102 71
    0x144440070303408000506171540c00c04048a0300004001810000786282180f91418501080011102189010703036060401140070041c48082c1e8040c001903004a2044554980b0320b41311907542028826001c1501c016007040300704000000304012640c40e40901103407241c995940d200300000d412070060203810503112030516603000d2016000c400a005941c04240e03030703080090066004032002c3c07052216140c0c10402c51004100000c860f5001400f20901c90761482500e402c12500e080c0ca403010982c000010f02004400340c003416508429000c2e003004561400020074981100403ca51505900e1042c2c025651001c00061100c0144242c51302c01d01c4e080100c000000c210304048001d03402c40c1600c4500c60244002a0180b481e1040465042d02303240030310628581d0602205200901009043e83e440014a0240003080c3e41c0c280b010600c07a500507120f600b0080d0900e038465103803004078409588182c0818400b84141c6a0015003254000d81d2018619900c2c0e942d01c140901902a144600c0c1c941c1c4403000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 198206438 1250 198205188 198205199
    0x40302060d180b0f01090c14070305090907260105010f0e010e36010e13150501120507080607050906070f0f0807060509070302060703030c030b190314030f03060d0f0c 73
    0x1010b1402002c04c1207444190b0390b240d000703410071582100220400b14a0b40d001d0102649070b003074043e1556034000c0c10320360b0401041602040c410002115844001840314070084010b4040e0f404003598800b0b500c480e40076a43c1040f00107004603c4640c0e42c40144003842004150580c07040c08401004100a00b00140c216440f101e0021601c410100003040c516515a07240e8403000e00310a0345048800310a0703062860744951160342c0486030080c03c1510b01101e0720b1b95410250300350707000d02d50003040d0f0441a14080d0356070b402c00c242440c2141c0c000c940140c001809000c801c907413100941d0050700c011581a99210441e2504189a00b0303c004011318001c400c424020500072074034050a052401213100340595500c3c603049640f1000c603070000035070015081c003c2901181c0301c0d901c41d440044190500281c85035446001900328221201521182d41e0394100600400a02d0b0b401c00100102c100001e60070b101f100382c1c0380101400001d1080b40034003d0714907110144505042071610240d041420b049040d030f10358 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 198207688 1250 198206438 198206453
    0x3010f0605030606030307020d080c0a050304120501150e0105061b0703080304140a050703080304110a0b0c010e01060506090904021f022d1506060424020d090803040302060d18 77
    0x20721035280310380140303000141c1c0d600f400700455041950050050040d40707425502c0c1405034010b41d0455031188140c08640000038810801400644010b48005044840605c1c00f242956841d1100c9030004000702c90400ca002c00304070185040d11000c5a40d01c0c0c5405a5070950401005540c14414507032042c40d000200307200400000f10300442c0142e124910035580c01e040c80d5520040754400502c1a444a0300c2040822204000f840d045031241e404089400e0062002502c550501d07001825628000201e024032007009124204100003088007d004261600002030b80901510445d01d0140714004005800c56803030401c035100205000e07140d41190072051100a54488403205048034007459510505100d01c1d803484080c000d0f0341e5400040c40401c8551400d0082c1802c040c10007a0094000d101c0491480c401e035a4104858031841c4070310702100d64000b0001d24044011100d0824062802028030580e50f02008032001c1d00d40550302d503940c841da141810001410651060390302d003110007000b4000c00c09c42 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 198208938 1250 198207688 198207701
    0x70519141c061719060b040204170706030f0e03070204112203230a0f0309320402090a06030e07231e010c0b060f062101120c060c0c0503010f 62
    0x200000801044620030200d030b503503944c0d000603188204044c2d903050004050340c210a01a030380c05000541003036614003810307510071385482102c0000c0d000b0040911040358184110410f22200741400d2000d0708800030516100e01c2029400b0340900c0d150b102094003905140c0441d07042d0540311008100346410620b00e45240d440602040311112402ca02c9030f00040076a0400780c5121411304094000c0002d2581d604210740c0f4180d804409200d400d0600064641c1c04503000c94904c010540000c1c9076401c081e02582144600706081442144180000340c1030740c035031350344d50003e40d1142d0070005506d0701c4030000d50785070a4441d48032188100480046d034142250103858171608805c203482010f100194425400170f00f0070464080b40c001104810481d0200d080044142e03040200503120600c1c4000010124469901158040d82448001304607042041e000c4191180140a200303606407011400d17546155042c011403103041c04002c0e903074200c0414017030032078100401440000c00802c201e04a480050001d03208 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 198210188 1250 198208938 198208949
    0x106080601060f110604030516170a0309061b080105060705010b0603070e1305060616140303040602030603060106020a03020604060b130911030c0d11010c0302030d061409070519141c06 81
    0x80e43c24104c921800002030b03d5020b2035060311164140f901c465403012618141c00425202c0002c050380503a01c1c441070710300604034121942d0300402d804100303041c14001d0761507250001441d203054a204020f130a51100380c20b815210222415542c0e021a418868003414281d42e1181d44050300001f0300592613008026681000d80595116011007174020040e4105d95088420a4010408004d140240700000701450b05103442488049006200101c042e481c5030400c8904803444c035070004c00c1c01181d2408103d200e00504551008141c400701030b07640203480b007001400050005403030b058070b0799560307540003041c100b80c04a8000070884c8030304504020405d110010181c90003805488500001c504040220441242d08503511041641203d03004407020103150710b081d004c502090000004d40c0c0140d000b140d006000c41c0201c02c030391480300c0f000c003c800040a06100b05220080000240c52001c50501c52640c82d202c0c2804070860854500c200c409200300c010321403601140315040d500d0305e515540716a041e0354 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 198211438 1250 198210188 198210197
    0x1a070308070507061b030f02090d02010f02161e0f120605061f0810090204050f0d030c080712080105180a09020a150203031803040b03011202040902130b10030c0905060c0106080601060f 81
    0x3119005407c00300c0c81200345c5903400c510441c0b241c002650150616220307039292441200c4d50000072080201e0740301155080300b05001041d46992841c01c0d40300899001901d15560b107000709070300e0a06001e243d9524201c004041c0c64444000a195507200942c280d80e0742d0544010038089910f41400800e480400c88240d0555007a50002140401300b03482520705550006c2c0c18860a502000b0820801c030b502d01c20120200820301142c0300014032541c1c0a0700040d442200400c0500b000300902400c251016003080d400748000100341020600110720042e0440240540018904603e0000c0b030300b501d040d50800c14802010713001007480d50358000011480b6680301510000e030a1088401140c491040d44a103c645000620043c0509187e103115070304503c0c401080004c0c038040c3c0768007144e694510310001200c1180d6405045c6900c0c24114264000c3d482c40c1e280800c24480700f1440500030f840b5a0241501800002c28136064140c825407242c000b1300000000c55010390703514900200a00d0b0b04000490014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 198212688 1250 198211438 198211451
    0x9090a02030106090e0c04050a0209120a0311060c03040609110306090706030e06040f1e02100305011d040519030201150306060302010207151d010309021201151a070308070507061b03 80
    0x4c81c070b10504881015035070140c810700701d41104100223000082e2003080c94942c200f000f0700050340d41c228511f0110300000c019044840035410080e04003d50b090b40c001c241e410240400080c05015802c40c1d41c025400900001d0139031039410039100b52946407507026018826541813000302c510018100045030781e5594288480300a00e44041e403030390410740b00240141e280d0140300d000146d0740c500300115505c00500d03081089a440d00020030001c000c040c91804291b441c0f0060118400c0c0ca04044015005204504058102551000c0d03551209042c14801c2c88560002c2d0400c0610070b40114403600018069102020f80300d082400c003c0005100c102e01600c600c000004107004080c0030a000c0d43c0d401d03110364100c42440c1d148012040242210141095179030305280300182d5980c4d224049082d0304c0c1000244407002030140300c800c4141c90304005c1c26200103250520051202c40200da10950741881c0c203810342e0319000016100c0340034540c40100b8440c1803200d02208565400828000f400d4295000e2028 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 198213938 1250 198212688 198212699
    0x4080708010b102709020a090503010902010e0105030601030b090f0610080907060e0109171c0207080303060d03030b0a0b0307031503021c03050d15030c0602300909090a02030106 78
    0x201c0d44404041c90308052031464885859010300c00300c2c1d442e40c070010b80c00c40701034204ca10603007881140743c4c0040f141c055022032580c0c0e038554806400406070005134020405100b032030300064081035500b150300e410410700000007101c80e48242c0150090520103021100f071400d0200c0c403e43c003c1811280607002d41544420040424440d91200380282240000703488031605149044880051414007079041c01041100091404a1102d507804c49800030400752510348245100740903e11030554840045500070001070001c89408001c0341e400080c211130bd0305018117a03107029405803071a61800c90b848803990380b000449155020086101d41410b5a0401c801036010584500390070085c00040d4100f0001d4a01c0403c0c180e01c04006c11145021b0f0403e141400e46840c0250306558115120341000d408103c0c04004021114500f08041c2c402400a00702a00404510440c0e142e040c01e41011203410000d03090030800704040440f03800b000d016149003003926261822565a5400d500120301942ca400b100044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 198215188 1250 198213938 198213941
    0x3020f01200d05060a0302060a08160503060307060e03010b0d120e060304170915131403121912090c051804120507081314010807030203060d031103120109020408070801 74
    0x80c59140070494101010b4080c80c60080000600c032603005100e005001c8096503848010b8818162250303200e242c00c1c6003101075000000c4681140d0400c0c0320041c03041c0405a03030085036204c15a0b1151400000605a0000180c05050440b16182d0082140d080290502520340101c61290703200340c83c0c2541c090112302c144401488115400381c0743c540c642c034820800c00384c2d40300200b0111030001c00414201000c1038607202680d0005030001034070350f20003c0c1049a4035510303032880200340c03046003d0055040c50464241e5244103810340ca48100703250810b0020150701881c0c025460010260040014511610b4540040001406200c0c4a8442400d4010f4011076000300e19102d030754040c00f104203203c42258141c6440d00200d40499030104d0a00414000103030800ea0300006100a844c800c00200c80003001420f0040701608910030580104200240d50b140d0303c074442815540740c80c01c2c01e044490f40541c5400c5004101840744142e030b81c0400083c1c00402900a8030580707441c00c055400261792048400d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 198216438 1250 198215188 198215231
    0x21003020703270504021809010e0a0c020118110a0b0408010501050406080c1e061e031e16180305011e0c03020c071701022b0b0130110703020f01 64
    0x40204843c94410310003424a44c01030030080c0c6603100044030000e41480021040c0b00709800c4040b24440500c1003006215541c000c10050342c5d0f2a0000f000b4400c004050b0b60007030424008017611209240c0000503143c0c0b03c88054100601c1d01c20011610b03243c84030001c5000c1d10080c4645481142401e0001c5101040440c0780d8403d404c0080c201020320a4446500c40c419850a90942d84020700b800501481810808030340311003000c1811043e0350f40b07002c10305044040f41d09400078070500340c83c80c200000342c40101c03000449a0502d090039000807840e000098151859600020525400e00480f0364150031140c4869480100602007400b20241c84c140403003c0303008000061082e41e11004003044805201d4005c401401d06040c0050b02d0300f00c10001030a003045c1002085c1401c012200f48a582400032031242030f08000342440c000107a100d4091158501d890707011403040c0d90a44005e80c21442d0381c0313103a015080405584031030360340780c1c0760600700a5194840e55070010142d50808071300b042e59070311019000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 198217688 1250 198216438 198216497
    0x907110d030f0f02070803011e05030709021c0911010e040e1509030409050903120c04030f030e1f09061707020703080c0106080a080c010c0e1e010c021003020703 71
    0x3404140080e240480142030030038142d5030100d944621a06600c8094002404624015200c0343e40d65454160200c2100c080c03052002c3e030501d1030314802d1265035000b0444a0403034007120000344c0ca0381c030030040c041d00c150086215201100d1500000750100080c00c1006036032030000341c031041c1048400a0501043e1092012141e869821000c070320310060410340d8006801240d4041243d091948414481c42100d6081d00c07001a80d07440444e05080c2d41b03010805582d4003416060000e42042d2842d9141074101c91030450003014003039a039542c90325680f161500921068079034030b0711001c00c5454580103030445550340100c0e1300040020512124070f480d40082e40f4001c0e80c41c1c2d4002c2c4115441c0d6110303202d941e008520003000715500d90800050503030b01080030351526409802050341c1d8424070700000e800c548030160103000340481d1203030f0b416451341c40050802c5d0240b1410100d0058a014600480302d54114090007035000568003154142c80e540b660191501e10f100340c0f2001d10300d02030410b40441044100511 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 198218938 1250 198217688 198217693
    0xe0f0606010801060c0f020d240209060a0e131e0e0601031a0903130e01091a090a0e150a0207300c03050903010c0c0312090305040302151e0306090711 66
    0x42144c0e0f80700b0031251585a00030358810266a2141d80011840c290200043e907520340c4050b45565804e6a4140300020280f403880211300e00523030340000c40c1c6d85000e900310420620120302c0c0e042c07030344c0d4a03100e089400d6000c03818000c00c44c200403400c81c40c4101c0b01e00b0748040041450724980d0702401d00d0009099050380d42140c581542c0d04035444288a81c0e05008102c1101030100340102042140703202c0d4041c1c05801e442000039160b6052a44e9501290010300c90500164160f495111071911840c1072560820b280078000b00d9400300184200c0d1a141919800c403039481600f100300241d141042d8058031500c0d201d07008811012213440340003403500081c0000c90075548070240d551481640118810390300648a42401070400345280000782c21900c041255002040355080f85408244d44200d0140080282c5a010003043d9041c0d14014680d00071800300034020640044000080342c0d02d20207550411400c184d00c20003a0320407031401001c5420584101d401540300e14007183e10079005415038a51010340800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 198220188 1250 198218938 198218941
    0x50a060f062103030b090a0504021003111e1b070f050303070503030c090307270e07080a0201050f04030204390e042c0f06060a05060f0a021f0e0f06060108 68
    0x8907042d070441400d804078145075503507a40b80680d46031151101d100c0c100701c01d000501d40c80c01e40107218640000007003220815161080d0390356070031b5460043d24403141d00607001e40c08840224103c4141445040c02d0750000d140024080780d034040700080c0f0101601c55038465000e985a4501c1030555a0040c040c008016400030f0000036620600407000e4199104018202c0303071480e40d520102070400b0030b907418030b1541c00642140c8000080d500e0080005480c201c40040c42010720b005041e0740c6400e000d08000b07040000c002502c40c5c0b001320038400c1d50051a0002c0082140c0320382a40c0100780c01c4801006158665a84c03298042820f03c200402a00103d01d43c40c0e61920b82c0680003000300030512a1441700d842c50451400185140007865040409541440101038004480d0100c41c5401e40061100e48600f01d882424000c40e240c11003503803c04802c461a00d625000400f1040e41458220340781a034040d2108914420383e95041d8000091005010302911030002c04400c40f40d1302d03a5811103900c0e01090080c130 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 198221438 1250 198220188 198220229
    0x2180427080a0903020901030c0302270c0d151212020109020105040605030604020d0e0105180714120f03030a090c0b030f01031203090506040c0617010f0605030a06080a050a060f06 79
    0x24000c1c407490215260803e155a120360006c4c10400c020382040d6203500040c0824402c43c00c0041b000d804000c403465541750a150344e20741e1f103405058000c2c680c4004680100e001303a420300301600304141c44492044d010281c1c6480b0240040301c2d1501c9a03003580d02c3c00c0b0443c1080716582c018412580002e07010f03501e0780e14048c204001602c40750704c06000c258125070b003007026a50012041c421a20b00244120006c144c0b410000206981c82880d00c1038660540c01220b800c02600e001040000628030f0f017a185c8004c61070300e480083d800d10a401c1d1000d04180000002c01c00c4007980c550140c411a48652039460300c0c55101c12840342180411103042140040040052010600c1605000103c80062401003a03452055441c942029000d46044800c0300341d00c6400c5c000310f034220010160100005203107440da5032400000044156080c07142106002000001c165003003d5a0011005000c02400301d0301c159005281c130f40d6651550020545100346800b01300390040b0281d008041c111586012040802010700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 198222688 1250 198221438 198221453
    0x315100c0614070e01090f06360302090604111801030207020307080f0105160c0f050106080a06060e0f0702030d090512040308030406050609010513020c0c0a08060702011802010801120309050402180427 88
    0x6450b60500310b8030002001c0d1000120100d641e170302703003100080622000e1070743c814000c8140d005030400d0312980c10502120002c1540c0310a560840c0505454142032003a0031006800921840901940500500c1004203815800040a403555910b0b00020800d5039102e010051144100545440000f2030700202070020030500301b0030031800c0e4040c2000054160765540b625140150702502182c5480c1c0310b520030040030601c00c02d0b0503440601140005918602014002d403039210324500354404954401e0f511060080400c07c5180c00135450b0b08555071a610380c18a50500e4008076402c859180c100f100255060510100150403135001030246071009a8a0038440069000201382c941984145c54030844640e0301c4051140080041740098451418800c0c4000c1c00e5410743c2880115a00512a003400141d910001540c1128400140e42160015500d82280c1020096100039401800424112810190010218081401213404225100c00d00444010b5048130443d040c0030211882820404107414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 198223938 1250 198222688 198222707
    0x1515010f0e130f090303140c031315020a030b03011b0e130e06070f02060a060317030c1204060f0b0a1a1303080409020d110315100c0614070e01090f06 66
    0x30030414010030b001c0d0381c0364101d4a500c14a07000b440d446000020030b0641502c122140c0009862214440c2c4c40c11400e44069444050071801402c2052880e008c1403047c03400842c4036503000d0600c00e41d0f9800110702d006018007610440b49109518100b84041d0252030005080d21600d0180c480d07a1a40d04128200038000312352240180f459521941c285080c514248502486131240703482c3c1444048a90304001e20b4004010071010119240003001d00200e000341c1a00c031881450074001c42e55980c0c1e10b8140c0c035628000c03050a261546400d409000c10070801f03400800d104c42803080100b10383d655000401070303c12114030550002003421200d160b04c00c000c98005146118840d407078825155500c0d6180401341e48035038030480c102c560208000160341110b001e1542c800751110071540c00c509041490941c07480001c2d11084c4540003081941c1f9001d4054001e40c4040e40d086181044102c0c0301c0c4281041c00c140449040000070400c50808129600800341281601d030305a07030342e501d95828801300b0344170b0740030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 198225188 1250 198223938 198223967
    0x4090b010509270f010c170606160f0605011502070b070213060308030408220503100f0f0222080d020a0308150d0305090a2106020702211515010f 64
    0x40303c0f0001c110072102d8620a14000b40d15002003484100c149030b8a0f08451480c030094040082c9030b40c5400920030400080d9401070b00850785c41d640d4030800c9210580c1100303044c00c0106012590900c9400340f040c658804c034102c9507810348107490814141780482c2c442c46140a642c010304020b121607409400e00007508101a0a00c04001801603200c0c0c4510b01150000c44045034074030300c000b0f9144203804543c0c0500e0108140c0d0301d41e102d203180c10100066155044261544051652051401d1122034581c001c42050003041c4000c42da41c04c4998044032554841036021880702c01c5808000410100010310b81004050582c042c041040301e5590880e924807000c2e00d0383c420951182d0038620242c0e94117541860003440303030700c802e592000080140304030000140d200110300e1102034240302020b20340348a0f018180358003d00050380c1c3c0c55148000382c4a40101c01e4911080c40d003d05004902c2d45c4002400542101c5d2100101820f80d21081c014428080d46031407240042d51450300481c3e101e005d40c01e0359030f9004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 198226438 1250 198225188 198225211
    0x18030102090d12021501050901031412040909030305010b090a030f0c03021801050102150403050f0d0e03040e0709120804030303020325351303020f0106080c0f04090b010509 76
    0x407803001c0000c01002804a050303405625141e107240715aa010043c40302014142e4504c2006585401c0c00170f41540740510002c3c1c01c0424020100000b407600784100380301c5c3d51001500a45441d100c000000c000c04250400300d0200745041c00114005914405075012108010490180759003581c1c1d5040602e4500344044400010710307200880107969074224804010810708a5500541c5008002417800c0d0741540e0038408401c6050501021950041c1201d0782034503070005140d500d40d4200c030f0000007400003240d000302c1c50101280118818021075607180c054842c650390001655100d001001c0507404044006100840411081001a0090700a913502c550083c4c8551100350140c131190074041c030103000402c0007405d00301e08840310080a00807400924801d0408164041200c1e22118001e0009000102d03850800c01c180c00805208014151441d42103d00900845640d11413040d6141204107065100d038024482c4040c8904140c0705e03215482d50806244000c591925084c08046000074000d0360500c0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 198227688 1250 198226438 198226447
    0x1050903030c030a1e1b021e061902060f15041808120709140109090e0313061107170604020904031b0b0103020405160f1101020706050f0403020d02030f18030102 71
    0x818180060800d005075a19040041c2c0c014400000d650044141c00c041401601400b2011306c4c0000c80900300800c0d07042c1e540c1c40d4110241030700c41e0002281c4455490380a500050600e0100a10f0b51907d40c100000340c0895404cd00c51144892071003400704d50681000314284204482441c06c0c1d0000b45029210740051220482561180c120651000011800c20240388040c040001c0e40044540700405400041c503003600d5003000001c0000d001407007205a40c03501c4422100810405004035501d2200b0310b01d0b684030b80c030754421000d0141c44101e000f0003914061300e2130009420810360b00e404900080c0b9000b50000b6507442c0d00300650740c03401810a908011901c495590b455806610701001c480c020003034011258503610402c0240c5800500000240120401c1d0300400d50300000002c500c401c50f820045105004021100c4c0203005191b4040e0056003060240034048000c484414022802a801e80da05408480410399983c4a61050300105540c200702d86500c600003210000c6c000c000003400503241 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 198228938 1250 198227688 198227707
    0xf05090a05071803030203090102150601230c1903080c03010b070b25020304031e0b0103140313030c060f1106010b0d020714030a0801290703050d090309051318020105090303 76
    0x400c1080d130001c80259000048101256804100d400440441c00d101c0f030726186807080c00200b07602010b603034198100e01500480c3e95413114542c00e4038900500e650403201c011600d615200400715000e42c0c02e8020400d00408969000c03d48011a8143c130f11901c0038030728148c0b0507502c01d4107400c0c00520340c2c0e44102c0031130f03ca043c18020203442404d284140f6402903450303d0950a041100d51080302c02484940d03061580c2c9400107200c4611281100e400c200240904842403007900c2c1144207100890081d11540e004c081b081025541d40030342a189542c0c0c4000c900d50b004103003541d07000110402072a80707600c840010840702000342e00821b040004100c006d82842515a64440910389042c0c6a0f2900c3e04040b54400038164005a41070042c07403803044e6142e007140940c0d284490301207a01c00d00310780c58100255417001d15000f8021200d004101403410098540307107050080045000740111031103240030750484400b24510740110403000c0119203504800300c03119401940e003a070101400a82501003440a03090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 198230188 1250 198228938 198228977
    0xd020414100801180f0b04051005090706080105040905070302150f040305030405011e140a0c0506090d032f0a030608030315010905011e0804022202130f05090a0507 72
    0xd00e2428104481d05041c0045a03080d50820306045081884451640021800d8015000c520f281c102c02c54041607115810501c0c1011412401141958101410312842e444000b40200031079030680c2d62034806907200c10400041d91070411000d80903500809040c005807a200402d03240412501d2842442c000541104000d20f4019030b00c1076800d80c00214040260b0b503045000284c3c40100c40d4401895404034010141c6140f03408003404a40d8080030665282a501a681e0806c500c0d4001044991518003c21259501c18150000304002030500308242c40d0300c1c5903426580d2604076103d072001d040c8c4007100d4451603a41c03c11001e4108040e11840002030003101400114010420050300c0d07104040040b0000d84201c1042c0d00c500e041118001651035540c5c54004c440041c0c008500d4001c1141c0c80d0b44c00011034100001510103c1100c000c40d02c48101c3e16a60f000300f0b00000c601340314910299807540d62030720540851140316001762a8400140019005901080e41715180c0e091600400107140c101c0720703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 198231438 1250 198230188 198230191
    0x40503150402030d050702010c030809030d0906020c070b04080706120b181005060a0909020d0f0e07140a0305030421050d050a2c210102120615040e060d020414 70
    0x3210380340d824180300960400344040010084903040c083d192885030b5000070040441040054104004000032401d00c1c00f080c070898a0f000060b05084c007a680d01c030b0500e540207511101c0131460a115594000a40459540c00d4034100c0700380c640038044c0700d072400c002503901030003a1084108040d540c03100c08505654800d803500f01c0c4491aa0b0290862400102d03000440c551500300a118007401d20021902c1d0794002d4102066920301303440562181454204d09000c1c2001d448070b40e8501d410400041021540020030a08580c3c07110b034080c40c42c1c90031a060028810850001410341d400070442070040070009420703080c0035a03030504040c401c0306854a44605001940003c00001031002442c1c4100700d9002140c4a2810301045498440c40c2ca0280c0e090b0b20300050020250145c2100440c84800441d903c03d00036854075641c00035503450140700c07000348260f84100c40142c861080e442d0a1407040714044295400d4403100802055107807903000030030400e40c00c041c0040342e0040d00d54203809030301a048402a03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 198232688 1250 198231438 198231463
    0xf07060e0a0911070b090c090402040c020c090903250809040504030504120305180103051017030409060b07020319080d09061b030c020708150c0c1c090e01060f050909060402040503 79
    0x2d5102c4000d843c20ba845001d01401340c3c6070700d03481f01e0f040884030f580307005100380c0060b070498000035602007508042c1c0c00c1c0710b0203940c8941d0041745413080022014011009000c2280b07001c100c04080030720114402d4181c000c00384003800c018001d0220304074034201503000c19003060103420b105061980c0d400c980b2817541c1145804800013840464090050365803400d1441c410482424144643d01e0a81e440d881c25404034481c0f43c2074142880c1008002010a00803103000c1d0102900500240c1e480e512001030b03903404400100e0092140d000d002d021300c800010202302c440e0b8054103403482c0c60040041580034002800e800d656090342c5030340c101000c9007015500c414000d0940c80108914090309000303805c10301241e1241d2426004032801048840808000c4d41c0c0c400307070700d600b09512004100d402c0d6140101001d644120007003801201c1c0f45603a0041c000700100c5d804800d9a081582e2901e0046413017400000340440403031420302122020746043c00700a5484a0050001400c0caa50b64001030300d0000c481010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 198233938 1250 198232688 198232721
    0x1305030d0212060603040b1611032209020c06130305040b0307020604031404050a03020d110301060b1905040e0a18020a060c0606051503180f030406030606110f07060e0a09 75
    0x540b10380d99440869806a01126440e05500e03041d1202c5420307840040124012103a401c00300960b0074020080728030303800600e0089035244d010000c1100e20341040005020490306443c40c000440401074021034042d0008040030300919102e00300b040c01e403e000d443c0100d09202d81408045950301106028622601a47e4001c2140341000e080240c540d080708001341408020801090007103455a02d646011a507041c0c0c1d41c0e81001c0c1c0a820100c00100c0705c1c040302c5505500302200014109610305c007500d078420b0780410100603810348040540c1c0920441c421100c901c044400007c14511640d4806070790403450b0000d4041e5620281c1c00a001d00d20303546c01c81c002260480700d0300e0341403046503c03c13040030344410303581700400e040c080000c22050700004140c4d519410b485030b50103c00382814041c0201c084104421a601c07203803208400342c003410440c01003c0c00201071980007107401400007150058550000c000e4640142040c5044801110f0503141980141424000040c0c10009210b00120034110010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 198235188 1250 198233938 198233947
    0x15090e100e07021b0d06020c060c091905090f09010e0d0816031a0d02030a05010207230d0c230304080106050f01020604031403040c090c0c0b07090602030f031305030d02 74
    0x200000c1c1d1401c060200d4003198010b18071540c0b080e5158913490840e920480c0e04800e07140403490000003a1180f00310514413800f42d070b0f09204101120303002409410030212224140c99a0350340c00c107003d0310010310401e035020754807502242a4080040006401104140000c15502c400e10245880d00d50078181450005401c00200707c40004049503000d01c4040e14a014804000300300e0314144100a854500b920074500701d42814219a001c009001c0c00d103902100942d190358a030f04050048a40507624440754200d0000851248607010445c1e1a281c441174564210f0307848240c03070b00b0200071215500c0d031241500c0900c0d510702c02d110030030150000b0038103a4004640d15052106000310030320441001e41c10b6601036014800001c0d000381d081600e0b0401401410345035507072070421038103288040e80044800e500e482c84481d00c0d10b034000d50800c001c42c040c0ca0b80400c2078803607840c100c841608612030300780144c000707100c4000103c0d001c200a50304a4002c03a054081103ca40d00d4460030349e4424030b00c40208a90004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 198236438 1250 198235188 198235199
    0x516061109062704091a090705120105010e010e090d0806010315180609110d020c010b040207080903120c03090603040c030b071e020c0607030503060406030b0114030118050715090e10 80
    0x11500321881901e051080c1400d0b9651514a41c031b454003000174000f18540005d00c1c142080040c1c45c0140802000c4a81e2000c407800c80034003e000a0140c080c0700441500082400c00f20740f0702803405403468500500390350311106d00444081402500c02703030406454002841526000c030005c000a0482a10b0011001503010040001c54102d40c3c04007148900700314180b652500c15800f035600c1c1000818025070b50b0b14031175038914010311030401150b6000c1c0c400b280702024028424060700c5030343c82c1a821210b5540b03048060510724060030541c2c0f0903542c0200b01c01a0242001c1001d10341040c800d00194950544035a110b082242045500400044040c44904e01400111248000c025841e00103000000800400710700340d449420800f409002000003c03c1450712070b41d0200001315000582017406503114507a440c400c40000b8800780c0b1035800c000c04024442c0e00c2c1da1410032440d500074000c01820740703080c4048000080041c80d40041c0000000700060700607400c40c4d454881c100446d18111800d0406 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 198237688 1250 198236438 198236497
    0x20f0405090603060912070c090614130515010c1b09150609050307060f020f010c020f0d08060901090c05070b04030306051e010206040305030603031314040c051606110906 75
    0x1c2c41c0c64400e034000c9051180f92032000c03c0c0310410000061460765101c009040c00c054988003640843e0b4141d241c4000058405000340c02c00050b914119100c090300b500c0a208442510401e58900314002e00552880896600813102558010711030000000303070300865008114403505a5220000b603a0300d80c010540b4582500c0101409000b46003400d414040c02c02000c00d135076120324080e00043c8400031804006613070080102101900034107000b80400e031003044000351130f0700c40355125222502c200070301c1c45c444a0040c3da0152003040007410814080e8641401030002e040211f1038441802010004007010030310700410280700354000d80f40460b140d40f0303080030300440381c0c101891107100320034004d00b806050ba80401c2041d0030503014a4165180d0311804006030851142e10503c250140c0060b02c0010403083e00d991401c6040000c48003041031040016042e5186c1c0300d200c0c1c8035010011000700c524001512030b070159940c00039004160b41004c0301403001c0358040d4081c04661418903e680302c500d40701e4031030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 198238938 1250 198237688 198237691
    0x405070302041506080106030b040912020d02071a030408091503100e16021b030c0a0303030f0c0f0f181a07020306060f0a121109100f05030307082b020f040509 70
    0x1490f601400e152a000c80207100368018000c60042540783e0a412032541d4541d00107003c00d541041c40c0d00320914500c28041d649840845d41c0c000540500b240000354500303080e00152281c4290302d2998039540e6640d55020701544031043b1298007607c064000b00c0e07401f544001640c8107103055072107601040d0a207141412000c100030301c2004105100030040d0b09403503001c40c81c20260403000320101e07a860b02180c0080d0808001103603080e044003019400009055141e00a103403035521a400420820760303603410446030070307103080782050100300100150105a803203844000c00c40030038059905030341034503a0064002c140302072101c00d299003004034140c801e500e0300340040303a0002021184602c0c00301c000c20101e070b03802c2c1d214810442014103640c0440180921030300c41e0724030003400800c0e1104a00c1c007581c80f031042c100e00d070050103056242c150020555003800412031b00a1504800c403507080c8102a00392422280040c0b00081c43d0381e200960380000e40c032503400986468606408030945072410007081c41350040e0b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 198240188 1250 198238938 198238961
    0xc060905152e090203060f0907050a09050904050c0607080d02030703020a020c0d0c2310090e15060d020306010c140f010b0901030c060311070c0306060311010c05060606030a060e040507030204 84
    0x21000404414090400300003012110300c25030168981e61346c0720001d0761002c0c4034041580c2054142041141c5117600c10010f0907980c501e529800c400c40e44540030300c4440c3c0e104441c000c0040d030000c5010b5650745820005000118400c400b298a800e05200000099810503540000031079004160145501d4044c0140040c81800f40c3e038800f0400d00da9103c0455800003071040030b0b054152080c2800c0d04182c002014207000c45c0140c40c2001c9206100d1008018074024803c6400a0000d5004070312150030a001c4150b44c040020115410441c001501030b000394005000d4506005281e450900041c2040d807410036030f80c1e290005400b082003150746075820741c4e28a030310280c0300f49031400c0107100064004600e1f40030b907446481d0008511410b018160071500c038140001e003460b0140c02c000400c000c0140c10a6042d41c4c460801c51035448070306001903030108400c0ca0000c103a07801482c005001c48c10305070302641d84040003000c00b0805503030300d54400c000458180e4003559136800203074040c000c4d82010700a0108451 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 198241438 1250 198240188 198240241
    0x213060f050a0602011b0315030602120406110f0306060a03060e040605070f0e0d080a020705191a03070c0b0c160311010e071217070b090102090f03030301050307060c06090515 77
    0x603c46d0021101c56040044000c0c1419500c03400e440341d00704003003c1c00780903603404a000c65441e0b00380a4100f03011041101c04442013401c04079a612000d00047c03d607545419011485801c58a4800070848030707401c202020403c040d41d44400180c4a5406103426000364091440081c403402c3c071000080408a20350a100240014841e0045842d1039030f41c0020055034020003100d071a41b0180500700d0600982d60b104030b51040c031103000e001ca44040740e450202100e42c115112003580d0b1a084c2000001c0c0011102c0201080c102c3e00c0342c0c00400c03030041c8804d41c81807060040e00e1420891499000300011107001c2039001400b03801181200c041c0921039012003040800c01000b41505e03001240341800303104800140602c00030300b9084c0e82d080707203102640c583c2c0764040001c58043c0b401c0070714103000f500007400851164080303c50032804c5050100460341681c070068054410581091020741e2a1240e000003110013603514410140070513400c1c0040d44600200d41d0241051f41841d25075800700c0c1026901000405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 198242688 1250 198241438 198241451
    0xe18072c0609060c0111070804080106061407061d0f010c2604140111040b070203010f0608070b0f0f070506010503150c0316110109062c03160213060f050a060201 71
    0x50740d07240107030791860700c0032030f25199074407070813480240074201da003a04612805010034120100729010010308281e40521000700b00540d610203040f41c07021604188400b071250204000e0000c9425034100031659005185140011120b1404c50b0385881b903056980d1b805a5501d02290200319032045a1502c400c425032940f012151450042800c80c042c040c10041218a13408000c00440000303400c1401140c031111540c03625541d41c0d80a641c45640701c40d81c128442d500c1c0a684021300f0700d09110745802c0d607113490000d090b074508281490407164080c4032b00000c8400240705005200e44281c00038000c140c03051029000340e515000a0514224100c00c5c02030340c2c00703550400c00281c100d1043c05c0d654401041e1600e00b42d000400d06040d200d0301ca1002203013205509001d038200a0040d2a0000d840861800c0f160707801c03800300b240d0300f482c61480307180b030401440c0c0040007007205407003141c1080301d43c1c140003e081c034124403605806d00e42200c440742e000d00e03441c02c07030000100076910b02000c00b14000d24042c0000d0101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 198243938 1250 198242688 198242777
    0x50409060f0b0f0703270e01050102010507090311010306050a090902040b01050c0a031d030d021b030f060f0403110d2721060e01020c010207050115080601060e1807 72
    0x32405603080c3c01ca4401c2000c1000c0c000d1501c43d5503403400303d005460720405405040043d00b0302020060046030584100c450002a155205203c1d407407240950340c3c1c50040e0b0a0456942c0900b02101c01622410540c90303a001040c503641d540e007510300410a401d800590a000703881404165140c2c0c0c41028144001441401303c03018021070603541c032607454500000440c1c130001200000c8003681a2507034041c840d601d1a00e4090b0340001d004034940c10f0040c03003e41c4d80b01d02502015a203032548060101980c004d0000704212284589817603401c41d11a08140380c481c000c01100034548030b40003404500003000000020f845000d0a0702020150581708104152181411044124500b0303143e510702441100c082d900d014040c0c241d101036100c03003040000b55074403c1e0300c01407039010b508012070507a941e510703216803002d6001c0305020542c203c444850161074140c0c6401415510140748601d01a00700079400703a0240b002d5040c00c075162050b200c989505000801d40383d0b070000d40f5075000a00c03011244100303801522 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 198245188 1250 198243938 198243959
    0x4020f030a0c03140a021308120a0305091e030a0806090c0304080c0a06051f0806010e060d150f1a03010b030c040e010209030f0c030f010501050a030303020703031b050409060f 77
    0x203000e4541d1501048804284104500800c407000c0b0592014050300305000d207045103900100011080d00340b07091500c5460f080420389036101c103c082c002101c010031aa680349400f0b504442c0c1c1c40381c010070a0301c1440314083e903080490b03480551582e0490300009961440260130040e0390fa00318100b59000358240c0380000d0314495611001c0c10282045002080d2031006085c10420981d61613403182082c0035908012007441a01007406034421031850b42c2030008246207400080580c1200e8141e840c5030002d4640805000c1003020307840c01660014100f070304400f5600e829018040f500c201c50175000520241110300f4904121000441901c240d040015003252a80c0019031403d280e42c0071500080e5081500b072060f40284034440c992605401a8020300c3e044540115000d259010213600b90381164a1140d07410303003241d00900510340d10130f0581d42d0900100b0700c60740c06030100038400c1c1400510428903244848400900d00502c0c030024200040500440c0d00c80d000b20340c0140607211040080074100b510442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 198246438 1250 198245188 198245191
    0xc0f0303020a14030904092001030e0607030b0604240908030705060c22080105070e0d0c062016140105071703060f0d03030509010501060c080304121101060b090f04020f03 75
    0x1802500c2000d844241c604062080700c01c00305000b0810000a0103034501101110000c1488868055230300c50500d485502901400c0b0403c0541c0001d0101d580e40d0300420f0b001001d06035070583c0c000c04180307c0451110341881c1c030420890098010503440008070740f40101504000d0300034510720b8006000403000a4000150f098101448400560300c0d10715a0480b03411401c0c8404081c0c03140c0500150014003e0301c190700581c0940d0055595001042c0c5100c24000d0441c204c0d1801040000d5034082000300310b2040c0200490349807000750103a10950080f480500d84524041000d6044104080408c00c3c16208168004981800e003455800e0000720740380c414220341c0c5c50302003c55801c0b002001808a5a400306c40c100c1c0355500409111020500e0304000f00103006c22a002c2e9007948ca0a030000c210107014100402c09a50f126406502e1983ca59541003459140c0c61040310a004520304403145001003800b07900041d140d419a8191a0000310042043c01d0210480b0305024602c108100340c00c4a040070103c0307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 198247688 1250 198246438 198246443
    0x61403041205130605121005130506030a02060a0f0f08090705060d0e07060903060510051309060b0306010b1e03150d0f05010f05010305060f010608063a0c0f0303020a 73
    0x1280d00e030803000c1c00d40d800c3c45145080788000e103441c02c01044050304000a401d645042c0295128a65991140c0301b0384400580920f6038000c03d038018902d5800150340116900c00d40280543d044100c0c0d507400700c0c4260304851a100e01045216445c4080c01e0741c800300c40340b0421041c0c9000355103410406802da0b150240d901a4502031140041c40004615168021440c11642c28003142c100c00c2e56080000c040310781d10b010807503099003804040388041070122200c10903203a00801e00355100c0c03a0042010001c2450550171a01261111543c0e1030541d030901c03c0301d008089564180b50b40390035404100e1842688121900884c0005006010490745288004880c0803403d6070ba0b0821188141051032501d500d9050081407982410700070b074008219604014100c92280d4102d900544400c01c550b84612802d0040e000050001c0c000100300c0e1034001740412a20030003051010060b20510603030318050411215a40216491407502000c02c505250403030000d04511201246050075654001e4440b201c03151301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 198248938 1250 198247688 198247703
    0x308120a141302011106090c030706050406120906090b0c040914040c060804030507060213050406080607080f0a140906040b0702070f05060a030b03030a1706010905011205090703020607080306090106140304 90
    0xb000c590007151155002d10740704d0708407000c5113000c0d0720103691940c0403143ca6000e4011a500094628082c0040d582500d01c43d450f20100c06100251700e00090080c002d0986890341c8408410010134500e0304254041c412070000c0680c2c650a00c21100d0503501e40d13040c1d0100d000001401c22000c604080e0601d8241e510700d140400e03040d2101d0070100c1e007900510070060a128030001c1c002c01d40c0f107154040710b821148150350a00c81c207541c8510f903035219a81141c0c2035000c601030348001080410303482c11207030784500c0703a5400080000f01e400c20a0b10f410422a9002c000768042824081400380d48503000f584038510784024248582888922088841036100e850300030341010980301d442c24043d802941c0d901001504903a2500e1440c3c0d40102019418a81e100c8011844404201a9481209203000390b030740603101c0001085512800c08010035005240701214000d4480c007200580e05c0a00400800d070050f10003d8481c00c149003000140d5a06034800b07401e1068003101242c0c8000d003042601e0740709800040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 198250188 1250 198248938 198248971
    0x10b310602070b21071107060e03070f060503070e12010c02031806130303030e0c0909030d0501080f070b0d0908040627120b090109020a0801021e04060e13090c0308120a14 75
    0x42c6c0d0012450000c0201900415102240c03007544040083c602c140d0890468060b07594400070503a0300d070401d000b2400014420000a80e0030350103894031581c00b80d0060300c030b01024034012000c83d0031281c1540310440180c10025000b0542c56128510380c04501d801c88179207103170003200300d11018491000d05c0018181501c80400b255401030a0200b0101039001410740380c00391405401d002d4483d401680401c0001e85003100110342140001a0ad0120500a02c01415881d08014041c50076401c14034690640544031200c0000040071b4234081c200401507600da0054046c514803000402ca1104c0070b159401c911038080c00c01c0100c0054100410b082e070803a4601696072660700e05c1602401f00c111020350014801d800000b8103030300550040035a2a8510031603e03003000034080400e4544902e00c940c4001420b0a42e06440c0c500d4102000c03040300030107000c00520041c032980c41f640f6080b460381c02070345c0c400f1010418440041815128030f0b48091450030411844070741c51026040740f980a07050314440c948104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 198251438 1250 198250188 198250201
    0x6050612070507210201180215091302040626071709010207020a080c1314160207080604060c080a0b0d060c02010e160302030c03060f010b310602070b21 67
    0x2c643c0e4158018140041d030b10a44a134510307a0400c04000c2c0e000561a10f0341d407040c0014010700351520745074000d164885101a000f2092800c0d00800c010b10380c042d81c0d00940100a00c80c9200030300050a15449444081c492006417070880c0103422200d042000c520000c2250059200c8200264840409061002510b55101890083c02500320003500b1080e00c0c9000b041322400041c00c1d82c44004202c4032200412140d041c1c11043da100040102505204140415a250072051614418a40f144111008a0740d1003440c01d1410105403401eaa090383d85241c180320095000310099400107501d10300307220820381c11012488500c407a48010f03100320f0351024039a44091003908a0b4040c220801e0441d000840f85003040d0380700e0f19003072000b07e02c40d03c00c80003145058100494540e11440c007986040308240e191010f076802941c001000030003009400c0818801038110303c0c00f0201514429258004091f0030300402030300e0300c0015008440c40140604c940c0c1d512a854440303454600c600100c92048946407107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 198252688 1250 198251438 198251447
    0x3090b07170703020c040e07060905131b05030403080a1a10030b0a060915020f0607030c030902102705030c010e0a050402040e152d01171008060a0605061207 69
    0x40207800a1100006444018541d00044000c4407440445042080f03a4000d41255500c540a1050708045000780320100180c4c500b424801e120f64406040100704042d89000884400c2e000600c1030300803403408400d000501d0360101515a0000b21a038042190f0000607040991402141080512525a0303400307c80d040380c480d8011445508010300301e618950380b80c15002c0c0c19061140034086065003800c1c00500203c0c0300048040c0316092880280c5200d40714040124003070301c240c5071800d060685503151040140c407940c07d44000210b20341c0d61658801118030b1200880c2451002c0b1440041c180750040c06965000f0071600780c00002428050a109250804508002040c3c0c1c4103a03802440420000b401600003290b46101d030358043d4000e80e031a03049070204580e504101d140040c0c24240d400c41d240f00107102400b07e070850032050502d030307200c195441c400c900940000c551541640511410411503484100070403078005121040a06c100ba04080c0810f03083c0c0240310000520039130200c003050785203006 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 198253938 1250 198252688 198252713
    0x313110310050106020c0114040f0303110c0d08030708070201090b0601031a0901140306070309030e091332031216090f08030304030f23030c130806060306100303090b07 74
    0x705409101541e51820041d4031a00d00a00307083c00b0500051031218000da03007004860a5441c072802c2180070074110b0b1802c4942c4961000600d080d48258410543ea40d51400c0124041e144110700040d0303070b0726080000030940d1201802003030a6a0402500d540010b14844940358041002e280001d100e60303a400003010041e515039009034004c02c0d20000880c1041500c0d40f107083c1c019081d401c942c039944549200301d04a50940c0c50180000344640b8244070740e4501886026000108840030550703d80741ca03202d00d00c5035021200d00c401c550404064034120b840b1a0001c401000c010b8a0142d828440c84c4801e690680c1c000078441080c44031802050082c060081041c00054055501d0703032820241c40380441075a035401900e060700841d9100c00c0c2031900d684a002340001c440801d880318070030f132a80007801d1405900050500c4100c0c1400740039500d04010141c0d45a001015410010540703410140249410514007804120303000011110a20200303411001010071605030345a0381e60f5a200908000610044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 198255188 1250 198253938 198253963
    0x10050d091703010f0b03010b070f060902041a0f0f06091c0b0903071703060618010201021b0c0a06030e030403140a06090303020c060711210903010213170303131103 72
    0x10094140d00d100740d1030156050b1025003d41c072071030035214a00141a0b0200740716a42241200300600400102400710900d48144946402700b0524041e50004040e5084604802c07040328008051030a03610b0f0170f00310004821b405039042c3c03901780310100c00728280f84100b028050154407040d50440300034035030340035240c10540c01950441c1c903404d003a0000c07912948802015201014640750b40c40806140000301d80c0944401800949000c9408c0c00502c0200010306103113055541c07d02c1001d0849010034141203828810a026190310440135007040303040c4070290442801c051503d428003441d040c0020444003039980000c41c1c0c5034804194161146007008900d0000c0003507040886401c10160150043e10000307041c030003030340c4840d42ca078142250400a001071045184d0300891040d6141703980b042c0004c88500248011502e841d0b20100401d0a81c2d02440010801455415003009080c00341000c0d420105c0d000d902840c0345061100808058641020002e0074500c821840200240d900704501041000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 198256438 1250 198255188 198255203
    0xf080c0a0317060a0b070201180b04140312040e04080706091e060b010804200d0602120601090b041401050d1803091706190506060c06090c12010b10050d09 68
    0xc0d0703103801000444501c074500506030030700000ca4102d1a220010106552101800780d00301140c540045801c2003a040740c03403010006058000c05c1188900c030040c00a0103a0303035810413211481300185440d140040c00d5494026506110901500d900c001c5000c2c1c006400c03124098603041a400c22800411513110003c0501e40d41103034082c103000d000e80702d10807014080d0b82d00300700c41c1c518980150362000c41110700030001e6040c5504850800594505c444814801501d5920088495610241241d004009643c50900071004001c8190f82c030104c0c4d00003030880b0700c061505042ca0700c9a0413500100d000007582c107111021031200a10380441d80444010450300c08640304a4080d414082c180705400d02541e4440c204030386010101500000d80b0a000d800300440444460900000c4c1100620024040d00d0b03102c0b01c01c000b6510200c00c108100c0b4001e501d800040d0841c260f401e41001280100805110300b0740c0d0500041c00384030340e24080380b1400b0940310700304195101d0440788018000c20a8010092039035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 198257688 1250 198256438 198256453
    0x2060c100501030606050f0f01081b0c03030108070b0720040207242003060405070203070b15090a1b1202091504180219050904110d02071a010501020a0f080c 69
    0x45000741c01150499000f800704205d542c0d01c0da418045450154040f00f6084051510000c02c6944500c624960040b07107141d09000210740350356003105990005100c5015640080018401824140403180c02002c0e0030ba00c0c41d28002da69911030b01d045065141c03100003030031500140d002d561110740403101040e1b0704c070210866030140720701e0110b914180c7d5121a0140c0d440e0020b02d0684140d02038100744200034071041035065a41304000c0001500d03000b40b000086000c01d0051800190201081a000d403241d008800c84580e02c02c1c060042c0058014040071000e070415010f01e50742100d080b860710101d4081d1400000100c42460f00710040c0c442c42442a401c074801240b11544a100040a0002c0e80c0840b0b9003080f103040c105d810070090340075000045240141c6003444d503021500400c018114041c000d070000c1480c0c102801c2da03480c0c03600b00d607150303c00b59500000d03d441007003030b42004041600d0211000030300039412300c0e0000b0354901a00400500706520710601005202100c0c0503508010504411100d80c4c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 198258938 1250 198257688 198257713
    0x3050d1b0306050102010524030111030f0103120503040b0a1503050f030702040f06030506010e04062a08061207151110291003050c0c0a03051c18060902060c 69
    0x54241508001900d0042d010605601c1802098002c464503a45036a951218035607501c192408100c20075890340d40c440c2c0c0c0206001d007407005148241611019207071550b16500740181442030380030707c05007042410410400002c1892001c0c5070445014000001c45060a08441002510580000d40544035410716041898000030040c007100b442502d040c4223540c4441c0c400c5042d2030983c00020f19039086040180804000c45024681c4240981408180c078200200032001d002c80381c244c40860b1100800513010103580002103190800c9040c0c034501001600200c035151904081d00409900204030004210b04502c01c01a031340002e0024425202c00000b00301c03020000300b03084a40e4190b280d02600e00c950185001c0c0c18150200700014001c05c03850000484101c0c010580100b8009a660301403001d4403240000b040019450747c840d4445543d504940c604199040e003004500b000341e2401c060f940780010100c0710201100592100e404a0b402d2803900c0012810302507000841001d03c15400303001c20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 198260188 1250 198258938 198258971
    0x905070801020a02100905030703180308030c03160c1a15060d0605031204120b071416050c030102160b060d05150105041109060901110c0604030302061509041e03050d 73
    0xf0441d03a0b903000c581c000c0829001d80c0d000d4490840f40030b816078005000b00c1000c0780c065850f144a5100181d040b07080d0b0b68495503070701c9a41e0000d482083c071880000c020400184409040400c14040508101150280784e0340c4642d9906ca028442c1032800f0030762800304841c0100c6a0802203101c1000f403080b03481c1c10441c0d049400400701882018440d118440389403021020320b50803102601e80b601417500c0340d100503480d0100c140c40d0140020b0200110b140100d1013407403981e80031707184d00d208000d091000b20b00103080140c80e0001c0b1100c5c192003644108990058400c2c14201c1c00b0103140e00842507600783e030b58500005d41c071100c50031025207070b07024001041c0444561030211030b041e10f1044504205002400300115000d004410040e50082401c21880c051903001e000040a01c021440490f4001d0700c000000c02c030b45400c03aa00031005030f403103903080c402c880f2182c1c0c0e09500329100a5804c08101e244c640c0b907440700c280b007662104240c81c410080010a0520a070111241c0c001c4205050041c022910003281 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 198261438 1250 198260188 198260197
    0x390304020a0b0403021f200a0501060f0f09180501050405060709080a030e011d122803050909041a1501080f06010503070e0f0d1109010902040e0a050a090507080102 72
    0xd00c124429000416081d9691040c1d4041c0d980103082200318401c800b405c40c0981c821503000000340042e06200c0c881040541f9900e424405c0781c60044c0c00c003c1c00c289040d60035554079400c40382090704441d5080c030402d001c1030b05480844590240110f100c02005121080045010401a019500300701c10401880303800203045000d0081541c0b59608140e940584503102c480b040c200400013240c0b01000001d6620415100c0702c500625610345c00c5103007003040091824400142d000e009a0411a90441040f56000d0498200c44404140f080c2501080d80c00030980d00c641c5002e10710810003039001c2014440342e0f2a0981d402d0030700c80503d4a1508108048408016030b104006001072000000101211102122940940010b171680d60031030701e032160f0984840e8001c0781c0e4a03400018440c0801400e58900d0901c50000f801071810513503414442051107400401604101c034014010802001001c50b02c201d000c0c0d010084250001e1580c842080c0c000241c012000041c041c0d01ca40d0201041840040d401007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 198262688 1250 198261438 198261443
    0x8040302030712110f121b1018050d17040902180d020108012606130203010b150304080310080d02010c020f0114011203031104090615030b09390304 65
    0x4849195480c0040b2030b050740b2580f8000c00c4c01403200400711050401002008944a0080600c881001c002c483c00d481e01d02c410094038400300ca80c9403180c9032401c1821400c58801350134034041400e400f5080105040c1a003d1042c1ca010300c51011014050102452051004178019403136076039a5561a040300e030207074100080c001c260240e410360501c0c070ba15005004107880355060f100c12225a03c0e0155451000030782840d0110300002c0011b480081c1441446854070404880030811010790300d1340103050846102200c03103800348051520700c2c029150110196075005038030000c800e94070b582d00b044000302602e41da4031280302031154460380da090300e40641203a040c0010070340c201d50380f485450550170701340e40f81c106810303e1070042d0000500008040700c06102d19540213080100d46c20200d040302100c594001d034070004655555407403d12407080c40310010360400802d4a002e210b030f0321f40d6800051450b8006803030030b5100005540c810020008110b0b9044083d100340d9143c00c8001035001e8000385540c01240d04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 198263938 1250 198262688 198262693
    0x60402010201061d040201030e160905100602070602060c0307030f060306021233180f090d05091e040f050a1d03030c03061009120c1d0c1c060e040804030203 69
    0x494031000c06000e00d94504d602c0340c2d5503a0280c5640c3c00650040802c890181582d000b200e194000c41081151950001c1580d2007000481385001e1205005004003078015808540207040c040203a244d00064482e00805000790340e5959489005081d8020701121034244a0b035410078000005010195024101d45602400c00e40d403e5900d40c09591160711030350070403001140601c1e8203106003034210fa5900c141e4200c05854010024000742007004060021907025091210000c00c01c04144828021000400c0581c240340d07040a019500217084015090f03852201e030480100d0580b0b2640e5103030070020320301d20710107000c20107410283c030260050403840c50580c0c003881040304210403090b000004c03603206089140c4064110784076034081000e01070088200100b0005001d0000c02e0340b84d0f00b56098450340d44250707559141d8a2404d051901e200d005500c0c4010070107844030410a003c1c04c113504440d0750b0600c200340d01d10101d9920a50b4401091590840001003000c2000c1004002c0c40c84010011b8900031801c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 198265188 1250 198263938 198263951
    0xc1c060e15060f0d020d05270606010c17120703051005010903050a02240408030d0b0301050f01260106081e0303100302041109090a0515010903020307031104110408060402010201 78
    0x610000c10303107100314000c0e04002c04010000004a800c0081c03c40080c50000152030716505510f10b0f016203905558507d41460b1280e0100070100d41318074640701a28420000c0c10442c6000000680544610070016028240e14040c01e05c0f604001c10488030300101c0301c20310101d14104003074000d0041008032005080104840c0020425601440044003140d1b40080180102c07242c40c0c1c240444d070b15a050b46003255072403580079242100003032409440036060550085848205844007402564030f1030b480e56000303901d441c00f030140f03200225043c24159001d0480300318031000a2094810840029a0070340043d510300341020840b0f02010400c110603442200c1c0f5240040a50f1946640386d1000791035054040c10541001c00040c10710750800e1a0308001c01c650141002e041e500415896407049401c007540583e0f0748204101940c038540d40600201080c0b0341040740d02c1c02c560102e0340c1c80c040340c003001e002c81e0003801c0c0c0c048440d641c94002046080524090a4440341c0d141c0c03200d0b958070b01c180d50803070141d400c040d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 198266438 1250 198265188 198265201
    0x3090c0a09020403150207051204030b0703110406020a020f0118140405090c030a0611040b0d05091b060d0b150a050a080c1809060d060509030a02120903150c1c060e 72
    0x243c0741a260440f0003d501a0000c0201000035407040b8411502030107143c45100d80000c181015000031401444010103d1400120080868490524500c4c408400707010074002c20b41d0000c1d2036100d03154142c0b4080c0c42c41d0f003034000603158495040742500c400c08030038030302040722120000e000300d0700c040646d010300417a00c444141c0c41e06c032608481c2d0700f90140d019400c4500444e460350444d01034215481c5132945010389035800c03030605502510031f511035a0b80321014004032000c1041941c1c2022020704d5401c11444003100000c00b644915554062026200c2c0062003003941c0b4031108400070141c012020340d88400e440000f80494100c400d41d180420341d40c00020304450184c000310b4407041030784030f49516a02407a40420000c070202414150b04890709c5080c040001e4454482c0c24050a404801183c851100705402441c0c83e881520320305400c0410300c0280803c3d1400265000440d2621582c60019524628a480140985080c00742901021401c2e2407441c180eaa000405030780341c00c110f0380d101e6a80d04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 198267688 1250 198266438 198266441
    0x3080c030114060313230c0d050304050f040f0515030f0c0901030b0a020d05010801060f052704020315150a0611070608060409060911090f010819021503090c0a09 71
    0x244144034018807a1250a8090301c0c10310015984080081e00c05104205551540341002020b000e010f0001742c1c9480244807980f004112180c1f403000c003200c5074082414a9039a45403240260b00c50726001d00c15901c2e285a0a40c0d40703030080b441508420a08000600d02200c880c4403400d0030b5001c41d8003a000310b0000400b440340205400c00c600070080d02103096646103688130340758100001d00740c8a81d140d0174818144000c0c0a8068140202882d0001007600303400d003060080140d843d40c0c0400d1045071295400d0030401070850a504083d460844510041c1d52140007007410308180c0000070302c00b40740c85410008800b01100d116500310030103075150320159484050a44100d0000d898106850b0301c1454100001446044003690240f0060808107800d070351035513468140d60303141000b111200749a502101c5c16007083d002040e403140354104004299490a1b2900e600e8501e0141d54000301d20312594084103546074644120b0b02881c001c0c0344240c0c0c0c0c0c605502c0964990f03880100551040300184400141c0c1c1059 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 198268938 1250 198267688 198267691
    0x903090916080c13080d0c0c21140f0a0c15030b060d0c02120c031e090a0b07030c0b0103050f101e05060a090608060f060a0e04030309110a0803040303080c03 69
    0x60303840300710a0f901c4115030800103800080c21140c1811035078502003040f80341885018800941c03512004010040b619003903044100d5a00003900f4492010f1200c610b030010b550343c000701d082c3c010520728440c5444050007420038042958004080c843d0b0011101004142d0202c0000c43e460241983c4284105d03c3e811415541c4089442d030380b188081c411b002040c051940404505c1d05180100d45200c00701002030642c6d60400d24080103503400100f50381c40608210391618403920a0281164175011404d00041c00900f04e60160104009012440da07042500800605125942051440c1003542e524601a0343c0c0e500d07142e40c7c40c0294042d0301154032034190f49000b80f011b051825140380911140c501e034038038000c0c030f00106000d174402105600001c07146014403440c805441c400000c3c00d014036003000d19104c3c503000503084d02e000702c0d240700e020011a0460381855800603454900400c507160107003800c2601104084405500080c150030000302c00f00004000c2044038843d032514442652040f6905405020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 198270188 1250 198268938 198268981
    0x2040e04081c0606050901120501081903050909010b22050f040e011410060809030715020a050c16080114010806010e0403110609010501030c0522150e09030909 70
    0x10000108002884050280404403109080000c076440c002d400c540c203460036644100007040002400c4012940d10003d004066440b050090241d94540700499945e0480b60a44444a002451065080500c108100c0f1011070006240340100c0d41c442e07460500c10340c401c0c0185c2d140410402800040340b80c0211041007103a00041040c040200350341c00b030201401d8081c041030b5940d5a1989004043c14038104498061609009000c24882c10301402400f120005420b050b40f0383d000f400220001058041400b110700405400941c9038a50900c059484c0e0090b208a4030103800340c2d003800300c0c1c004003c008800840303403040c0090102c20410085107510071000e0040040c5500440b0041c0591903500c0300c6c140d0060300ca072808410080c190101c0ba81085015a9191103a075140c5004100b1311080038200c00c098131041342c5814952000d140e44d411b000c22100510040c00351148150030003c644400e461000304440000543d0130700d0108000e90f22540a012614410025400403e620f105c030140802c51030031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 198271438 1250 198270188 198270209
    0x50709030204020a0203040905010311040e0304030f0305071110080411010f050403080a050f04080106062c09180a03080f01090905071221020606040c030203150f0301231006030204 79
    0x142550280b101a41c004c0d695042544020030001640d100c580c07103164000c60150b08034232001a8090108415a00e4604d03105c051948148000d20110f40c90450085030346a040c00c15540c0d031429450111585032101c003030b00d9407203034403041d9810034150032036070140c41075215055071181c4140e004019210703d990041c640d000a03400340010b00003e410080145001c102c1410043d013011004140700c8aa58081d0b0488044ca9450700c90403c6416048003612145038078003030940d140c00cac031a000000303a01c0c11040740c141e204004003004528000280020f0188415000007074a60142a50034007814890003640e0307a14041d000e04000180011640c803c8070b0003160701001618806250540c0080c04e00c501c19425612080d10020707070000f0400c10720020024001e0380d000340080b0b18041040000300c6074281030304020b041c0100100940a10382c8007214105141c121103c500301142003010a0062060005860040c0c06510b070901100c982486000d100d4480820800305090300e55104a017070340564414144d614 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 198272688 1250 198271438 198271457
    0x5042c04050616031814030f042601050f04120e030303100609080a050d0807030b1e090a110d021e130806090f06060f030a12050a0e060304080306060306031905070e01090507 76
    0x9052840d20801b841c604804a07418007465030030300005584568449412003081840c0703285524901a00804201c103820003c0059107800002c440300c1c0000100300034000081e103c00c199441e8003419904060036005002c42e920b901d4001002e031320002c4617000d400046408280c00003000b413000205000155880b130007501194180c90000e0740c03032a07409414102415214030b10541d0989414003040c900f030348441046103900081c0028065030030782c00f500c031140141c148007043d0024984030007220b111015002e001a43c80d4070140c0c011321544c858030a4800d80002c00642e40e5482110070202c2e900b42c1749443c1c240e4405489d03056555540703500c0f0b00c0603452550041000101a0302c0c00b0303906d0450100e4043c050b1044041196900c510700f03d0082000c1c03010030000305024034182c0e408a201c00c1540001c0d20704900d14185034966a4560000410f03c500c03440d000800900d55490a00c0090581d8102a80880c6010124034055840e00c03154000d15041c841d81030000102c8147c21f0050038001d4202e03450300c41c41c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 198273938 1250 198272688 198272693
    0x9030708011b050318030703050d05010909020a14060904060906060306061e0c140a030215010b040506190302070c0f0e0606071e02030715080907090b0105042c040506160318 76
    0x3c1e038200401c080920092170a1051081d60180010100203100750348240c0d5500c20000f000c822034038107070080081d40e403a003529a4010b07100c0f180d40006032001e000c40c1d042d40d092020006005031081012043c0c120303042240000b0000c82c1900108203a030903584090009a80314002110800140804541c2c4036001090091903140203010700625503003c4c19002645000390740c00d0303515103500751004a0042e4080b100c1070003000d014046850241a0b0507202034a402e140100041040c0500c03200c860308110300d141c0030040c90b4001e0341251000c40c2d00420240710306035280c680700710049062184680c00d40088000419034a060f0301110f4203a0390100550758400c05640086c0640c0c044000c00300d03091720030351300041907000d0450840003905079240c1d80c401d036600c0c04603001d03818000701b640f2090159007840c3c0411840da03007007820741301943d0070b0150903001403c0c49858625034070b0b81c041c4200e004140502c1032005200010a0f0b55101e1007610440500c015081c80c0d007181118401c04105401800c1454103500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 198275188 1250 198273938 198273947
    0x80c0903030c1e160b1303060926030705040905060609030d0207080d0e060f1c15050a090903020705011b0f0c0608090601140409061d030301050316141002030c0607030209030708011b 80
    0xa820f061070307152420440d200c2d9208d008071a00c5c201c003920004042e081600720a007903032400742c030b6480c04944014258141214040c0550146006100d40e00380c8480005020f07443d80c1040c2c0e180f2102c011b084840c08594202b000c5d40340c2880b4040c0d81e2450191101311440c00d4003030180800b140001034404e61524050307840b1003040760041610160b104075034441040355201c0342d024404031540000c9160300100c1c600f00c10080841442e5102e060307d41c1c00c00c0342c03210200c0c2d000308001c0c1c1146c200b82046200e034417a130b03000704440c0a8418001061100703113286500500014004880c15142d0503260b1903066241c0d120416541c040134841c1e940d902c024010404c54508058200400c020311178440030907034564603856401700e031a500428110b554004001009240b5041150500c00b40c400c0c10040c4109081c103082400540245200030700400b5081c1e00b51040c688204202c5040c4001201900e000f0b09003014020003030341c84011000c0c481d1103451801700380d41c0c0040c801d80441101d20007040d109844c00c000b081c1e5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 198276438 1250 198275188 198275197
    0x50703020717070504091a0a020306010e01020c0f040c0c0c0803040f0b091e040b060c060924043315051c0b0c09090f0a0c1d01080c0903030c1e160b 65
    0x71003031f03c40c03020042c41d265468041640200c4441e800940c580c83c000c000102101343c0060000e0442d0f03c428002c45003031300e8088500310243ca05030343c00301d14609001070030354a5200e1910010011440c550b0006203203c0d010010f04151040c1854142032240e40d00c684c404580254003240b86d02007203144038503048110151400101280250000c1521084c0740001501038110b40c1101c030041e0031420422662801c00d1182c007594507209940c2d601d405212009488070034000600c000c24280f03003075a0b00c40031046503e408901c141c0d09001000012100c050349840a0010488443c0758140000400b0500e450040b45c884524180c0c20400002c2d0303152038658100e101c801400b000080310f810001c03400b954440d00394451161a08103607520080c1418103c040c03c40300a0036402c810031020000720303036040801a03042d10200c0c0007440c140002d03850300c400113070280c0300d4504e2165044c4400a4581181d44000c40d03101c00b103482089801859020205030142c40384100b8160350103100c2c502e0414403c0800140141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 198277688 1250 198276438 198276443
    0x50102031b010e0115180e06151c030c030206070203031521060f04140a02010906030207050115080d0311031302011101020c03161101020706140c12030705070302071707050409 77
    0x410f84039080e030348203400c480600c11003599080089400717001c2d07401c2c142c940955815403291b003000804021120641c90f4180a0054503082e1426203050b20300d5514116140600841c4103400e440c060201c2c40c000d010305200c41e004501601030600058030076400402aa4403841003540810f120700e404100b080f0001054884814000c1c4004280c20070350181008124802d01c00307880c9121a90a00e070802c5501886caa0780b0800195201c09222001030340d001c00070710102c44541c05c025031200c8052070240e02500b40e014504543c3c51034000001402c101c00140c0700110122510100401000105180e1f0103100450316030300200c04000c220380c01540304000c0780501aa2490005061640341d007549401e6a00c00960000f4054444001001340504101c015000c218240010440e20b494904050704100b0a0450050080381c00708100900f02010f000c00240100001d0301142d891a01c01c40c0a002c6401031541540144190030001c580d1102c4040704001615403203004041103440c10b02000701804034130008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 198278938 1250 198277688 198277691
    0x6170f07210603032c010516021309050102090f010804170703090f08030a1103180603100b07060c09050a030c261902030610030305120c0405030a060f1104050102031b01 74
    0x1c00803591510310842000e50321a5039000d003201c208607400c6211420080c06a03811150402840a040c0e8211088a00540e4014410880c0e40c1c180d0000482e0781d03c402c540303041070307d00f004802400c0041c194000d000d00e25044584152400c14003004403081c140c01c403001021500e8078149410950b0050000c0c01c034443c805e01d0300d102c89949455004c1c540403801d510020760b07680003080d908080764024150b4203003410030740015401d014401d03e201c0c1d10700c45048401030050b240000400c0e0005001c204020180150803200360b51440c40e450a44018880590440001545071a012506241c00320710300c811250090000400182004652030300d400f031182542c90070075003000d150141c079501801410007150301c607200c6c400c0c05883ca00604d414140000c10891507140480c40520000341c104095404148425683c1e62041c0d550810001d13141c492604490383c9031080d0f08580b010031441e5002030345940d0340c0308000e01c0641d001203400e40d090300503806581c0c05600144403849006407074000c41410000503000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 198280188 1250 198278938 198278987
    0xb040c030e21071b18051e0c0c1b1804021005030a090f080d050702010501120f06020f03191a060d240f1a03070c0206030a110d050106170f07 62
    0x4881c28904406a0842803803400c4c81d600300302140c54035003140c2c555100408240703e140b81c01d8103902140602c0404488801d4103400214010036050010f84003401000c808071440b501c00c6429040c980c403d858205c0f8460381203181c0700f11800c0d1412040b503000b907501614040398280d42c1c2c0400d8840744c000030301c0da0030019641c00403040440c140b00d200c00c003914002e00311103555045504110068880c01070100040d0780c140401009068040b16201c00c0c1b890b007084a001400100d85081c001a1240001c0f03241d07442408000d124807080402150f102d100d60000c410030011000408650b41604801082e42d40510300388060700b0001c074035400c200d000444c1d07940060554091101b50301c6c2e40601d80c1d00051040b5404000922980c00c82941600c0040c9031124030301c0c198600440010902c03100030328020302079000400400c401d6801c030742110184c2110340840640300d210303600c41600100030910600300003c00d4010302100503a100c0c04040c3c0101d510f07850040b41542c4110064803880300c401452011040c1c984c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 198281438 1250 198280188 198280193
    0x6150904060e090d03060e0c090d050303010f15090e072f06071b0f1b08010f0902100302031009021e03090304030302010c08010e04030e010e040f0b040c030e2107 71
    0x4156006888411604402030401000742450711800f04082010715191406c1403000c03800b44000703240d210002d00c0c5200d5a56485802154640ba540340000704a0311000c0000704004030711071591810f8a03d41c250000b0020140038085030b40a1882c801d40342c050107070101050700c607071281540d00c0c455132002d5025a10310320386002520000241c814002e089030002414081c8c03ea42c4010345410845c8203804003140544542c40b84804500301c250021301c2c0d0078461110522034403081004030018041c44008001881040403c54041c10905100702d21a51060901c11034030750080c030035071340140c403000d0f95032040e1400c1c4801c20000b540304c201d07000d800d041404001d07a41c1d210748000441c403811510000d903231a14910300e0b01034255182c039400c00007880070302001807019104080d20301c0c0d4000e4043c030701148d0110041c40103132101a030304207080c0d40090030000c01855aa10542050307440c01c0096500f0020000ca005048084404903100c1c44016041381e1384040c2081e0b550355001030400c02c060030f45441c03c0e4166 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 198282688 1250 198281438 198281441
    0x140126040303060518010e06121009051915061508041101050c03071104050c0a0206070318020d06050411060918090c060403050601090e0a030e1002120a02010b240306150904 76
    0x200028109400e03003005002c3c0100324034156402610540c0c1c20060584250161a1101540ad0559a64a9403081c1d070000f44102080300c0e00d08bc0300080b00300c0d94032412504010312044640c8071102e9030b1604103200080d02541001315042104601c0d070307035a12980c03159500d0f14030101d2120890f60410109012009044109100030036416100300414402c050300d000511064600c000e03d00014400d040c1305140000340c01050700740c1c1c450424500012000b5101044040c0341c1d14a03003002c1e400485500b03524040103130952206004602803d03c5038040c02c01442000342e54442c1d581d0007500600800b200040c91003d0303400c000c0d0000940801ea0720368001b01408514243c0181d84103484036481040104134840107440307005202c2e40038901a0980d1020b40c1c0340541807800c001d082d640a04038020b04fd00c5414401d12465800085208601340c2c1c40205400c0280070f0400e9440d02807051121000034416182904981c0501502c0c0441c0c5905540e9401d0421125040900101c25040010000c491441e60749 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 198283938 1250 198282688 198282709
    0x80310030516050a0834090606050a02010b0a06021c0203040b0304030207031203020708122e05030c0f0306010303030506190e0103030e0607020d0b09030909010f1401260403030605 79
    0x48031009841c1c80c9050304001540c03c00da4171070081a000032801c10009140d1164807020079038034800040c40e602e07848a19560499095002681c00c501d032040c040f440036403010080203144c2440e402400092942810801c5141c018402c40f005a40300000d02401000c1d0003440f460090071a00560342000c4e0399016030300090348204c4003200141c202d0030307080c02009004502e400340e00046103821400c0803101c1d510145144240040320703500b040c4103400603c1084040e125000b8001440c0c0340c410402100c00f50042401c0744ca4014036100c0d0140031192000b606000f04411034400c0014010303e800e0b40707540c406900400c0003401c5650410003c1201c1146042440e801e28003c141ca41d030b125250750300d18103008082c08003200c00e8900c615803c214020242c1c0e0740807100509160450030b4114070740c45120b8590b245200e9a40c005410008001c00050410010803420701100c0044143e10440c41038a0011217001d0142206400c10a103503880442803040c0350b40c08a0350007403107030400040300e686420015080046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 198285188 1250 198283938 198283963
    0x130302150409051f15020c06181003050f0703090b040b06011b0803071704050d080907051c11061611010e040e0c0f03030a021f0b1206010801050708010509040803100305 74
    0x14180413602d2000303021200c640050100e10500109a003400c4c0c0020345400425509610800004c49c0e8a480a2001e0302c0c0011581c0b0010015610600e03602d8015024000c00ca82004003c1030b40000204000d00a00841030095444001c04d0090f542c0c554420b1090303034000d89494100140450b4035030b80280c25583c20080e81e4007482c8481d84034546101e00800985032a091140c401c1c41250900000640009045c4503100c2281408a60343c1e5540b40300c41d142c035601c1c1d4072a643c0020407907400e60b040c8107200e000d00c40c13460080c0c2410796400360036401e0000034490740d5400c00181100c9001d000201e9499a01c0e004040d40514043d134015074058000380a8a002c0f15415009401c90400320b42c1d28a40102a2422000168080c42c2405c0801801a40b6160908505502100b042500402070000307540500694000241914203002e110620b180d540c03c0c090080e010198601400f05194034028034980e41240c0c4c0051841c4050756440d610088036800181400c80040802c0308040300050082c41090302100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 198286438 1250 198285188 198285211
    0xa060504080426010b0103060f050d03140409020d0e06040201141602040213050102010b030c060a032408030304030212040b030411010e0d0b0717040b0109150f060e120313030215040905 81
    0x480c1480f1060840f001d141e070700d42c18185494020070481c10f03407240c2c46046940403501507090b0122418140c802c00203041c42541107030380019000c03415440716030260100015801003000300c4000220741c6540d03600f0030344020f0b0102d4101503841040c045a400107104160b400d5003a20410306072a4080380a0303810618625543c64100c01040c41b072075a09201d21145100e089009080314204100030400c64411710140b08105900c0b84144800300c4c012030181213094041899441e07000d9545d4a02325103030741066404600501400e1440081c03200d00074241c1d01a40ca0440c1f42e546151901e80e64590800661360f076041c14001100342847e03940d60380703060000c0c9450165072921001e141c035282c002c1c107103002442441c451904c00010b0201080c05461400d040d00c805801c00100c0555464a402000307100d68402038460708552408030b0b0560340000c049074541d07070075680b0140e42017506010f59142d0044005a82e00240b21080810152409000c42440d806800c40c0c4c0d01c0c902503d0303a2002e01690012500344901c031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 198287688 1250 198286438 198286499
    0x20a0c0804061e0507030f1d030708070312020303070f0e13020c010c03180503040302041a031c20060f1503030c03040312080f0103141212041703090a0605040804 71
    0x20f0010603007803050000c41d1a1051034249265000742072004262550360802020004030170052104c0380d1504443e403001001c80e51442e5803071400c1a955034442c00110f61103003005042c3c1c100c407800003080d43c0c0036164985034801c101503a03040031102c51658079401580300380d1043ca41080d80f0294402045d0817560325001180c4424041c00190940d9201d20140c603101c1c0122180702c0110b43c021081d0390581e54121008650600003802e64229452a00000c2c4e074140901c2ca00d081c0b1041c00c0003003c00ca01d840d940c461494101c1c58401701c003c0401840a07654554001c08001003000c101e100201d07034002d110b01d401d201030403443d501207407a58205c00e940f5801c44d80001010300034400c10110414035411689807501c0d4624050f100c0001c06181840014240b41e5001c008240000090203a615502509582291a100d0007590b503a002075042d10180d032a899900380350720a0142410840b441042c0d618001d0040501d2079850800504005209840345481400049450b1781144070405c041513400782015141c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 198288938 1250 198287688 198287717
    0x5030d0c170105030318040519020f04060206060d030f050d0608070f030614091903020102070605040c05090f0106081602010b090720010b0a0e061f12061403030d020a0c080406 77
    0x203040307040c1c004900c40c0e4000d02c409244490003c0398482c0c0110103480100b400e0f240c030744102401c10f80d40d14451189500215207441d81100c6280604201c8185500312226900d800d41845090781c088100a0001100c0521401003140200001d006441034000d000076060313900d2150341d04011b103a410a10340047c00d801d04000f48805402071a6641040f1401000c4e20b00f80340c5403841e9955442c00f2038210280c0035120410502d4000c0d4192a441c0750840c00521482c503040c41d001c12440300c2402a9480b83c1c5074003000c40c5c1c15658410405050311416120310305c0c59100c140344404503941e030800c00b50440d900c8003050340441d2540510607000301c1140d202c01d4023203141c21000c4800e40d00300c9040c03001c0981c5404000501640d410f01d10b842140c4481380c072010561038400100e62400c08400b151103046d055013040050045e4060a0b081a440d64010200622503d0b2564280a024860455503050b8418068900036034155070080c0036010850901d90346038500d550380c200454120b0b90021021501480c507a280 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 198290188 1250 198288938 198288977
    0x8010e010c03051006030c090b0d0203010513020304050a0b0c0f040306020d2403060207021203071a09010b010c0b060409120306030201021005130b270102220e0a020705030d0c 77
    0x8074060314107040c01180f90410508105040718800e4800f0141c80301ca058140602a01c4564060141c0c12445951004050140c0020354400c0c400c0c00e000d803c2480303103210140c1c2d0300d00c01d903800303954007038050450380303000b80c131060701000004d4840d490094041016400c41210f41004000440c0300740c1002d82c50f00640c0612004646076188813030244991a81071400180e00c0031118401d0ba54440001a02c8290354004144040140003540f0780c88e1100003441401d06c074070615803803010707040c0d591256201d9840e035000c1d41c01c2e603068a40c100d0101d00c0307122901000500f014807544e40010050310000380701003a5101c0307030702c1e682e02000c1450119a5901091082d13580c10b0042c11a80c0106440500c03290a0100100317001d43c1c40c402c0c015012450a40c04900c07208500005682805010442c50402902a10740c143c000d600420030184190303040b0400c0130380b60042980316011a00c0302c45d030308419551811006006580010b100302c510303001c208100b10000400d885084517440396540c42c0420b0000b420798042 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 198291438 1250 198290188 198290201
    0x1e0e030f101d101a0402161101140d0b0303090405010f140303040609150306050a08030d060807080303130c030506070f080703140703090302030706051e0a0605010c120c0c08010e01 79
    0x81c4420380b81003114800010721840e07600481038001036003003111480200845002807055403007400040c10485802400150180302c038026080b00e0910340500f0015900b407040360048100501c000c0c40001342c0d0168542c001034102034081d040d00d1030300349554001703011510260407420b09040d00e02070600801d00002d81c0c2003074a50083d00210b00d06414910041c0001c1c0d05449002103003040440308040c4070384682c010100501c4091322801c00703903071100b5149803a40c00104a09181c103203085000240300d100010000d0403120510007031361554548600b0301010742803c0d0815107940180c2c0800000290082001605ca0891650f40d10800c003051040100b084202620900800d410503990340048a40070310354542090060400003003419843c50147e00b180110000605400c0c07034807080000c0008141c00301410040d8146038486240c0d01c900c0c202044951034011140081c42102c400000a18901c0c1d8640050081e4100045444219562042c480d40c3c60380002106945421005110130403d00818 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 198292688 1250 198291438 198291461
    0x6090b130c030b06030c10050d11040b0405150f121e09120c120f0c010b0603040b0604020714011a031009110d17030408070b0a09031e0e030f10 63
    0x11020000c803900c4a040034032990001030100d0a001e008143c00795001c1182c41e014040103004050914411800a401a0030010085040c0d0341401000d10a004000c421281501c046d00d00789400d0908101c2070003803803180c410350070030f100f00108a078481ca5050760010b41450403140034003203403616010704c0d011001c5c4d210050450708102c480050003108040400c00e00380550411004c642c0700d49185150903e0242d10802003500b0020000b10b108059120600604800b0444802403000c4050710003400703c41e00c81141d01818004030f410100303006243c580c009010302406801d10002c2310a20815240c211002c195110b600200c00d444900303a0f0342801c1c4031800e03a40c2048401000021116101c0110503000c0c2483c0d2841108021004410494184615201c20895681068991034285861203455001640590380740c80390000043c560242c030300032410a039505903103550b402c00c03022480200c2c5000c1e8600740700921002005048180d1810000050a16542c8004003180345650395058201c0b0601c0e400f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 198293938 1250 198292688 198292711
    0x114031203180a0f1b15140f070c0e09120a0f030f0f020703110102090a030206031f0803310b07031101020d2007020913050a0f0320010501240e040906090b 68
    0x1008031030741c0b80721b1441d85d139840d504040114100f03036403052080c2d205500038000b85100220700315060200c20481d0b41e042d503111070411185502d079040c3c03541c0e9400c1400c00140c400b0fa41084540c945920032035000c1c03109046811301141d5041c0e85010304094a403401d00d10040a540446c510040c50747c0500c4a410010550000714640868600841c02405690001a01824001000c9202860302c40c2c2030a00e0b0546403000d82a401761150809500d0b81e000d24682c560150030030302ca001800c8404800c10316010300141005180b9483d0a0128005d60407407a42a014040b1680030400c0c0010280010200e40115080c00a00000120303045407407440c4d40545601c20510500a880058482c4240903401410058418400c8081880d0881c80c0c503400810082007008084c3d200303010941c20110b00c0c040c1480d0340d5209481c20000f100140c1c01c90b4003d104510340c1c040d55907051a40710b0128000001c211025181440d02c0003101000316040d43d1400382d00b2a81143d0350711508042c880c80030029600203007810503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 198295188 1250 198293938 198293993
    0x1501080c0f1923041d1011070803070c12080609010e04030c12020c030d050c1b1516020108070c0309051012150306060501080c07020405060409290114031203180a0f 72
    0x341280d5030a5207000020f843d070f59411641f0459141c110039502c03407039404602a0750703d2a2400e40105800d03114501110f07501e002c002c91590650060304100e1042700302401c507403901c1e131a204001d6135890f070150098091114480440c0c01189078640c401d40c5050094004200151848090504d03181d0f01c00901e80404c00c091080e01e2100c540498075100c1001c2c0f101c3c0503950401e003c0000385107011808a5400d8150000800b000e08501104488243c203000340c03100c503000e0b13403141e0098a80107411a0010009911003900b40024039040d4032281c0351101c075107003128014000c01004002c42d01000c4a2a03400c0710185020030412895010b0b441c060a0b003840c0040190418403040c0d5150b0280c07000091085498400007006501d4603401120b00d550040c460020128281103818034a0008070a5a802140c0c11000070807c2400d289800c48007200141c01441d414502c1460a90180c00c060004400c1e225405600480c03200700300001100d1034013550500c04945403910740380922041010b102042180b0780c80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 198296438 1250 198295188 198295241
    0x20a0c0b0703020c0405040212060f04031206051008101d040b0a06050d14030f0a26060609010e030a020a0602060f10030804060f090e091501080c0f192304 68
    0x14243c245000551700820f20391958030005980d90030700703d10800c052192504110300742c0082000c1a016600a44039400041840c5203508143c1d540e07405820b0304010041d0445909511445100741d00042090300d8501498031030301d080141840d224a194054900b07541404140b20100c410705400030407161042062070302d80000b04480000720200a400440c00f22041c840b201c2e424011a1031400cce004014a0f130b02c0f400c113440a4150500c040c0b00c2000045000b01040307440c19600c0307015004407401002d075070608600c50700440c2c0c4403140680594060003210710010050710f950b0680e4014003c00d40180040b0300d8100040d00d015000100b00c0380035440d811780c040003c644001d0403070301643e02d10f140c80c2c0f00350a400042501c40d001103902c1174400b030800e00c0c01c205120030007040d007509896110144080f181da94140e6250381d15160407031581d00100c14a4847c00514008040d540340c084c0203d0905803160350b807001d11240f0381241c8000c800a040504881c005842c19115041e40180c00601c250310411010b0f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 198297688 1250 198296438 198296443
    0x21809060306070f11010c03020415020609101109030a030c02100201050412110f061005010e0d020a15090e07020606040c0219081c0f0902090f010e06040906020903010c020a0c0b070302 81
    0xc3c00301030921404440803a0890f01c5001d00e0001d864034117000b44003030181c02e04024000c2d03015214841500503425409a102c0b48042070260040c14410010400c41c0d0082012a0003401c041d8411120350034100f240d482c00380c070140030700b00c074140c00303030710340c40000065401880b600107280641c0c0d4046916210404c030024001c0740038604000382502d0040c05043e10020924039101003540300c80e85910030101040b02c4c500c1a000d045c81038030301c20780e03901c0003800d16282441603c0e408800000d500c070554003000c0c0000480708200249c000c0551421185c51a0351760341f018042401a20030b0001a00a1803c00c041401e05000708210038025200400b030707142d0544800b0036507513000b03000204051070011b034050006002d141b2945041c1d401d00c2d8200070701c8118169000081115440481c003031500040059580052880320a0407950759410591a0780c0d0381c1c10420006002440088500039401d0003240c1032a10244513000b030f0050035800600c0c0b400498108440c0343d10855015014000301044401d0000b90302 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 198298938 1250 198297688 198297691
    0x6110d020303070804030309061b021e0c06250606030501060b03073e03030108010b01050405150307020a150b0111012c070905160e01021501120c0513021809060306 72
    0x1241382010720358485240441c05080100005030106081c09040075000403258040d0303456142e40d400301d6000031041d0344c200c01c43c0400e00c4c840180c5034114906016480c240700d0028940d4020030240f00c010a040b6403580c0d81d242c01c0c11882a9511aa01d01060042000900c6880090b00e020080c4a0442c0f5003000700900310f000780d4401c01102c080c0041403004200c29031000251145400e401004140d00d4461856030301d4000748520070040d8205102c0c1e11031035010740215070a4500142400c0325490320310744000d900d544081c1101045102d2800302d0004229082c0203075030100200180411008469000140403200181c510381d10f5900d000c003090b03030400304095550244005009000c4141294641c494103040c11544103201aa0514041002019120141e907515140c0c80d214448002000001260b852020085115160940030018070607002c00d0030288034054403d14003121242d4440001c224502024001810495008242035440780d0807240c00210b6414151000c21980c076000d40001d6a8040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 198300188 1250 198298938 198298951
    0x4020a051c020618030601120f02010f090503100204030203100606080a0b06040b030907240f0503130c0305070f270c021e07051809060106110703060e0102030106110d020303 76
    0x169031444103008218444007500c030540060080e629803a02510b0f85010124006400740300e401040c0c00811115881c1d10400b040c0d540002280c03801240541c015980703c92107115080c2803242281c0c0014030b60740d00b00041c2054581d564805030703e480c07039481818588808800c042c072115040482c00d00185a1045105502010034007000c29940d180c0782c0420018421904007514070300c400410020800303c0018090100c80c1001d000c4e24981d541c5510002310800c5010442d00022032408009100510410240d034000203000081403460320715540300200c005076644100c0d04c1e504194070402184211581030402003100d000c03280a40b010000c296504241046240280d80d0390b603440700755005108110781c1018824140c850340941504a00d11380d030340c0c5064814035228003400d03980a402941c07041c1a0b14082d83c0d5500c003c285690800b0825141c581d12000103110354402c0309000408248140218051610b60f40300050341c070b50400c40000c02201d4600540300d904d0340310313040c2c600e006a400021263b0000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 198301438 1250 198300188 198300199
    0x114010e0f01050403050a0b010509100305030f07020a0e04140606040e1504060212010315060909020603042a14030c0105040f03060b04110a050901030506120c01120f0203010b0406030b03030304020a05 88
    0x124080140c80f01e000300c0d013000d032543c840c0c83c3d2240100104180494140c03582210060115034400c03140900307982d02404000d0907500148006801c40c818440548646840201091001c40e228800c2140e8000c08450540c0d42000e4201100005c90b024000700c1d400100030340f418410543d10b068560396482070305404040c1c1c2428036000a0900c031665051f19000300c00c0c040c0c6010b26503034034107182003000388900b441c00740c0c145400030014140c29140314000d0b00c3c035400350aa0382190749588079903220313504545040d40700088010f0880601e289200c03505000d456128020311680f002c4030141442c06140308516410f200c802c020511800d268040d440c02100c0d406000802c0b10100240490060011608290713501d04010a00100b1141c00401400300d004080ea030810081e82d44900300809044810301e0026941c1001a90449a520170155503000411800001c601c110000810000326802680070833295080403400303100c5581d00d4003070881001e0007100298118106900040d00f04a12485074500c901c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 198302688 1250 198301438 198301459
    0xd09120e0303120a18050d0206010b0405010e0d05010609180b060907050f160f030305060102011404231504110310061a0318060a020d0b06070503040b0f040f060f080114010e 76
    0xd421607003005d036080f40d05500d8070711030800900d42140c3e100500102a4054012840003007283c044c5c01051720308070799059454040c0c0384510b0060108104065806580035520744002207100c02941c00340e11114400402000c1c42ca60302c1d402c21441ca558090141c82c030480403c424054070030750000a594010600b140303140c0d5120069054040c0d82c807403c0c100180720030080303856003003490b4050b405030b449040280c0007440188002c541c20312219008079001000e401c0207100340c0c154103100303200542c42c1d6a166030845401c0307180650082403240040300c0031208044040c2d160440ca040c14441c10300001011038050111904140031240c955055040c1c4101400c0b010000481c0c1051002240d1410040301080d109903003400c00c914000b9510034540c2000e4070b410410540200e0509208030f6010641100107507040c0307800e00010b5801c40e4400c550b8085180e0b01488041101090328400740010449519440143e8030b15210180002c00e05130f100366441954002c0d030802c6644c000c181c00c0c107248411280385905 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 198303938 1250 198302688 198302701
    0x60103150b120f01020d0b030105060d03030e0c120d0215090304060c020d060c0905040c05040506040302060315060d0c031505010206060108060102120a03020304050c0a050d140709020d09120e030312 87
    0x2d095180b80740800794401c801c04071031030030010750003402401101c0c44180040c9118805050a0360b02c180c4407650095041d102c2c2c4400309100798801c4012140303600681e4218000c02002500110860440070100c1c1c20503d001c41045404100500c102622159900079520f486d0b94019140c0c009d80c400e60701400400c100710000c565881c01a40e0030103921a804002c914251000103225030514003915000383e141c00341c003641c0540504161000c0702c0006041c203140600319400d20035590000b80c404516021400d102c8047e940c0c64401900100c04c080b0070004010342940b030004c0c140d40c840c42d003004030241e41031804d000d141d80c0481c00b164014800c0c2003420399600c3c0c6d013004030303c1d0103100b000e4503401407004261058141d9060f0020340c080c601071b000716011880288100401c0c0d82031807003142c0d0f20950b0341d822000000c40c13020010050a400005540c4000d6031004031906aa00035200440044da99038542410130000e9440085007a9842c6002142910400046540c9114040d140c100101340036000541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 198305188 1250 198303938 198303949
    0x40f080715020d0501170d030e0c100206040c0f05060f03090c040f0605031006060f080c04270e15070c0f020d0f0c0b03091207060213030b010f08060103150b 69
    0x103599400242070009507040c01015000b904034018250f00c603418030b000014201850703d042c0c08005c5071080a1b028414400c54260028a40f46001e0b80e140e01424214004641e501d013490b60504c6807a4026100504c1c00e4a8410080d01c03103504440460307038030038100748070688800b4141c6000107032240440356641c8410192512b0602c0154030580c3c0541840b2004075460042c0d0000c03001c9403415012943c50304240c1e0201400e560490140000203900c5009400e010f40c8a515504c0d00724141c440a40d180503118040c078001e242406207051544050307800c0ca841c04054621a2034441900580a03013880d80100f4098040c0007405400c400802c80c04030440c02c00e02070503a0b0801c88841e40181500008840c2d0300d0440c4030000088422354a025160500041e001014401c0340d01c07a01ba01d03000707007a4402a10900c40680c0d00004d01c00c1c2c9004d6400d001940c0d64203000f0a010300514006d100380e50349513141c95001c40506d60030f074025440130f0704001d00400015196000744000304540c40400301d40354000001058 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 198306438 1250 198305188 198305197
    0x30604020d060f081e2805010c030c0f0e09070806120106180b03030a170c040819021201021206061803120a12050c07030c060f0906060f06080c03040f08 67
    0x141c180c98035070009210268001c0c0b58040383c0e002002e030b41c100809030352801c00c000c83c1d11140b55190340045850f520030612074060074955281c43c955000844a179521114212005640014013007950b8212551400b41c000008080700e0300c0500c2c0209808106101044400c0f10240c100b41c28044000c0104146a850449540040807144000c000c100d0b654445281e48038500e0840030049864601210001d0034040100c1c3c1c000d51b515101d4850f104802008a0200400200b06442414040c0008143c4003005d0044040d00d8908400000251029004018004408000d103a100d03a104000442103800c0002001d54030030411950f150722406d80c012151001c00c0b803c0c032910342c1402100c1d220440008000c000e0040180a941d800350000055909801202d00c29501c0011981040c031039400080d22825144c00d04610886001c69881c2e00046a0070036540c0e090f800701d0340103032200c40a121114803484071000400b8686002e00050074104410541d51001800152058005415400504c41060b0854 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 198307688 1250 198306438 198306457
    0x30327040e01060306060e040b010308090301180515101d09163b0a02070f0501050c041a0306010905011206050a0906140109051509030a1b031b06020307060203060402 73
    0x1e104001809103568003c002074041143d0741481c21b140850081e001c401d007980301d0390740030308045100d908544808440d500965409640b664880c004003101c0001c0494403401148108000c006c0442142418451020010800b81682d4100d600401820709500f0003444101c240f000003100d6074592914160804180700e00d000580d80f060800010b0883d01c210b0350064907082525070030320300c50307051400400340c51041001d032003109a2400400e41014103540107000395445102070210701105541e601d0b085d9601166034820707024010030100a035501444143c00c0403d01140e243d1710350710744103001030404000ca0055604110007100c078642601416441040500401821601d0b12a03840c80d43c10f01500242c010251401f00c0c8151440065018003081c0c825035200910301400c9002002100c403640c0c0002ca080c9505200740003020000c83c0e101c40050449105601c803180e0704909506145800c41e0060030081207806100704100000b55010080d221034aa000d140580d51b51038140000d0301901903001c05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 198308938 1250 198307688 198307691
    0x11121e04030b01300f02060901170901020a180302100e0a08010203090705010f0201020705060411031f140609010e0f0c1c0b040b190302060a0c080307030e0c09040203032704 76
    0xc11a2135500c807400b5403204000b445a90300d00c403204403413004031620641c01407003083c0f00142a00103107802d0019200c500d0041c0340009951030801110100c009085c4c4600c1d22907540020801502581302e81c0340c41e80a03144020403203580380355a0201c1c040e010f800e1406c0b820080c0059103582c00d541c411400c000102880002075440c1d0a1890b45261100303000d10845012840e1341c80028112401802550601d640203030141c001580c032504d03081a010f510b016500d030b050041780201b01c1c1c51403400110380b038001311a0b2000204c00400542c00052160080c2c1100c1c410100b060042181d1200c4041ca5644036171a12a51401601d030a4400c0d43d86004242c0c0d49011010101d103641d08000480e8081c080d036500403541171101c92034400600042c51041401c40440c0c0323280070070920150070040000c0035840381d0f91420210400311901d07460301c541c0058558100190b200d0302c4043c2c3c07685041003d40030b40142182c0c0015103082c41d5000039600d06c5825580000c440c02200d0050464a2801c076240100c90013030070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 198310188 1250 198308938 198308941
    0xf0d15021308010615110613060618090b01050904080703050c0312041101080a110a0509120d080901061406180103060305030c010c02010e03040f05010c050304031704030311121e04030b 81
    0x441e035010749a81c2c080c03170004105960781c240340c281c490700d16801c05080003009020152240c06000b800540892002c0c0c0e06d440c1c80b004001010140001d924000d5081c8030b10000d901036291070650044107041e40700c648101c01260a00c8007180c09081180c01c40c560601f0420f5035601d40c81b80450842c01002c4d8150300e019205c0c0d0170401408042494050041e800341d9403200b1a9603120451000c44a84201449050fa024407a001d08503016600400340e404000300a118412400c40c1000e04e841c0c0501807401c00151690b0038082d07004424020140584101c044c090040301448001c00c001f80655000b0f0708483d10070602c050700f00e900070780c0310b80040d50b040019070b40c1c0c989038000310b180a0520301c1d869000542c0780c9090000f9412002c4190b60690380c0d00030700c0d502100d20300401103c6070300c04801d00341c0c1c0ca070108002c0000081c100c1c0d60000c5146098965241d02c0700e2960034081d00300d81c15900354904680042c09010000d01c24002220441c810f0302c000380c14041a04690816a4011600000d001400840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 198311438 1250 198310188 198310199
    0x703060b0d05090d031a0f0301020c030c0d020f07060806130e010507082a030109240f03110102031c0c09030515010e0601050c06010605090d0f03110105060f0d150213 73
    0x1000301c0d202d00c43c80c0044461000c03070250200c00322011110074600540d445400f4907105d07d080c01155882050090026061038040d0f140b80703046034800040180e6a034000210880007030303010b010100038200404e0162806503e04040030342802e03001817900b445000009114504495158840310710080030900070415494120070281c0320401c1910101001c49a210080c5000d040c030703041a030780c01c80121a81ca03045034605403010014003180070085042c074000310130780200c52180000000c01010301c0390035101c20703601e98244038103440c00e00c1c070f0b03043c2c11508108600d14944280101d02c0000503c2c4440001d44800c2840381255800541c1d000241140201140f09040c84180b8000390f0582c1e043c010b03404519140e81d030040d82c080c031402c00085000c0c2c00c80c4004104040c0190083c044604000d4092041400c1b607a1700c8030030390380c090401140803456040112209800c00d104007030b48000240d800c1c0c3d50000340000011422700c0d940400801100310040322244a0030903405503403002c000103200d20302e0300c2e8485 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 198312688 1250 198311438 198311441
    0x403020a0b06150d0e031605070603051608041106090303040e15100813030215070201021b0102090a030f0c03020406121217150f06130602010608030c0607080703060b0d 74
    0x11201581c00001076408101285407407400300b100345401c0c000940c030309407050001c4006041e40e103105150900040c410226a0441c4007200c00e05144544040c0140038204440a01200c0014040c0914030401d410100301064000f1601c40c0c12540141c2070a20720321112000401e00e1084010098244c0000b0400140c901c12455800e07008001c0003840c001b01210701003d2042d04522210820000b0300d40d90081500d0350004101104000d0092055403200a407500c1d140d0304480b8141e0708a40141e45c000f5460082c07420755601521458100d0001358909000e0000080380c8420500002d07040c1c2e42c080b0b0004013040740141c080c5000f1170b40500140001540c07022200f50a4000d150291540c0b2690610140210301c0341e030000402581c4c003207008040740c40f100c455251030a5450705d4a42c004240100ca1152562540d0103413884424100741c0c51603e90034450300a09481e0154031020b0b1540c4140074407401a40080348003a03000103149071a041c0380ea21484214080c112030ba1104040001c00a0302d241040e00301d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 198313938 1250 198312688 198312703
    0x5011b090305010b060a020717070902070b04020f100e01030c0912030203090a0905060625060f060609080303010305121c06080604060c0c210302070b0f06032e09030302070b040302 79
    0x100004c00800c02c40ca81840f034248150f10b24040143c00100742442140c501e1481010030900440440e41c002c0d80b5480944200d0740b200c0400d8401003541070030001180f0741584003807040107003076030040e000b02d0121501510b156444019181032540b103124001c40c07140714610390401460b00d0100d00010465900b000380d1030380d10941c011802114018408a80302100b8040c99016030340c0500308a190243c0d10445000b804014081c14000380307003600c02c000101d004c50080004528600c200010440d14001d00038144500c17580c42014150070510040010500c08210400c079412102440c40d9694030004c4180705456210b203400004034a043c5c0d000c501c00d840050f04622803482018200102c00507030304c081e1603007000c84a00a00709917910721030640400300c40d01e011501c04050b0402504100851341c1d090031405045824480e090280400c0162901d02000b1042e80c0b641543c114822805144040181035a2100c00700720b0403079140e80100c0304040c42030381100c081a0f0030490780030450900340b4000351504078 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 198315188 1250 198313938 198313943
    0x1603050936070203030f191b1d01020a1a0601110d0f02012d0b030c060d021206040504020109030b04031e05030601030b0a08100b1311120c0307080601080405011b0903 73
    0x44400000c1203140004102c031b000d111041d0a10442d5940e0400109000c101c40c2215069075848014202d601e03254000780f062400001e0301c808101c85525206107890202e03a2483c03038115804644c0307041c08a10040b0710340c005d604041080f10b8081da2650010703203c0f204102e1245030b9a03c02e13005a03280166110b0310041c00040a54020b008030039030034074900a6102a40541f6043c00c0d580b080c80c000705003ca03405030108200c00340c141d40c4404a004005400f42d004031501201103a00060b500c1030f24149420301c2c5a1016048504124508041d00000d10300c00080c00000e10114411022909044c0a142031040040d402d051044065030441c9000b03080780c20640d0f045010034201103041031759207814041002a03602400003040043c005ca402c040141c40c804203070f50307004080d900c1070001055036401000e0b0002107a59816544801800620f0110381008049002010040c01441105030303100c40c9280c0c0154003480c010049454034117210303005205c6401c1e1000304202d01c04524124580180c03c00d001c4a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 198316438 1250 198315188 198315289
    0x20c0906150d1d030714070f050103052e06030501050a140603070302070203031305120c031c1206150f080606030a0515091014090408041203140307030b0a0503010216030509 76
    0x10122915595107e16002d409004c0c0e00080b814007841d48258403050340614080020340264a100c0c1b07031840c0001079407a0b0a100180c1506050000607018002c07180180000e603003c0f0312180c07804d00c0203d40c501500210a100d55000000304100340e02c01d03016074003102d4008058a5442030300122000c04411079124440c000d100d19100c000c51240302003411084c818029002d40010021034080101180b203607420b44e42400ba1088501000c0003180c400e100c003070890a44203040e10981b8650180600042131015410042c107482045819201c0c1c0080d680c020300b0902c404107035501d4001c801c0c41410055540540c101c003da004101088d42c0590000048030b515210400b1000700e880d041c840ca02c031007150b014054610411080004180510b03032201c88900174a8103411202103a00082a81c2d8425581c1c80c00180c0c40e00c50700d51b843c1c90000068002454100c0085117090358003041c43d24015420b01026050040201e8840516110030100551455002100300a03050f6000012045c44080c000c0142c0d489 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 198317688 1250 198316438 198316463
    0xc1207060e010509120c120301090c020705030a080406030b060d0212040308130515040525080c0d020306070804020a09061701050702150c03040606030b011401020c0906150d1d0307 79
    0x300c810322495002d904130350003514460202c0309100ca4107610621481c10640700f06000c1c2d100005901c4040d6020303081c045030100303c04010300d030300034078005468006070700c40e402c40c0141d0000a400c042c00c80381110f07031a080c04500d0b0060a0005005030040100c000107503800050f609401100301440c89115034842e032109000c0c1e88a40798003c42802403c4070040c1198040303007541c004500e604c083d207039001e4420012584540c504142c0c003d001c001002d070116261a03540c1003401085818050b84454030020b9450030a600c6841e00001c0d5250301c0508180d0901103a0008036055455105d201005015001000d00c0070390783e2039100c07400c0310311a8245864075501c1d06011511180c8041000781c10070f1030401c9070740c0f00d80d158210b00110b15400580211b41c2c50b0381d12200000041c03221502c15008205407003d1240c0340c21400c00290815480c080c0c03e43c4603234854000c001a541c0c48010700b04007640c1100c0f0087c1c40d801101d411400418048010b10b41d14070820980519030780d000070007803000d1841003000b10000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 198318938 1250 198317688 198317711
    0x60c030306060206060a0317040b0c0a03170c0d051005060a12060e01080309010f110a21080702190201020118050c0a090501030b070f1803080a090f0b030703020903030c120706 77
    0x4c0e54001c4d11040c0e80040f1400b000c001140d0203510000f09407500e00d01140c513203640c0307000c0300d80d02c1d90006080d00300540100461505241d00300414200b030b4681b180303001809103448603040e9554420309181031813055032080855046141308032404c001d400060a2103139519a03904d0040e140c4071002c0002c809071400d040020407180e0010035030307c0c12921804025030501c0d100c0401074501d40a0048000c0c00c1041c4d400881840440c100510810700f03024542000145001d400c1d465003240f1608480c0741440154014800c10750b07800900314002e05081c1c3d000302c1650b921341c80100c0c0906080c001e201710465604101005100000c14171014180040741c5030081640e0307440c0308a090300c2c001d21019055241d610000303920540104c0786005010194074020042c5d03801d1510b40800c0320f2690300103644031200880c4507a43c10790041d0020b8060700b812002d81c0001c1d8540500950940b00080c110fa04158002c10144c2050700c0800550f45041014000d072144104809000007094000342c0c0161032240c14141130980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 198320188 1250 198318938 198318943
    0x50a1415190b030708030702060717040f030201030f02070c061407060203090c030c011d010e04290f01090f1a070c0801051f030503180f030d03050412110706110106050406060c0303060602 82
    0x5c58091002443c02d01c0da03160200000c6c0c0d045244252440281141e05040a40b00480200701411200a042d421282540001000c0300c022158614100344108a02d80c08200c02c0c0d80b1000c116822480c01c0241a400380845d410940508500286541c0c0040148030f6070f0800030401141c241c1040c5c040711010b2802500465a034080e50018015011207e124000b01c0e500c1100741904214001c0d2020820980e0480e50760101c0d0864042d02a907041401403040161401124400680c4001d1074030444140c14050412021486881113505004128080d81603410082c01074418140c1c0044038203540d00d0360707076800c40d021300001c840c5001210b0100125041d0f006a490130881940c0e0000002c0d8140008401c030b0030718104003030f207506503c640f80700c00c40c1442c0d5400300188007002010780c0d00401d940c202440d117500800d0a41e0074540c03d011122030300080d0b400d4001044011100c04e850002c03ca40b856200c0c09005000ba038100d150018100000403d43c6504a00c100c4003d070710990301044400d0b5201d40898 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 198321438 1250 198320188 198320203
    0x405180f091204030b06190602010c080a060f09090f08210c120f0a0603060e031c060b070803100504050430090b07021302040927050a1415190b03 64
    0xb040060200b0702c04260789071881c0d5031080c8064402041c0360344000390840710805036401000181e44941c450908103510680480e04280040400e011203030501074080c4030740784c1ca4000c080340c0303030b0342c4801c00f0045c080c030b402c0115656600076010640d2444029040e00030580714041001200c14044c0201c2c0c26520800216400754880c01540400c6840f840c807545081c0c0760150000506640b07821012012418500c291040240035030b00131550745100e12038140e0300c1100042c40d0b028442c0381000400c510134006040300c00e03a40d807208803a5941c0c0d44101026070b03148a20b0b040b050b0402e00c0c01040008004056072803444807818107920345411140910440e0b52b540780801c441e00040c641020422404107818081c04003244000e10500742c99050722071010480c0c101d68025260681c5445120310019503401440d6000940c5203010202c00340c0c241c071510391f107005a20009113424580c080c064440c03542400b40c00190504130078044558207103600c4c000c550000803265040030618168000c8102d00d400a4500b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 198322688 1250 198321438 198321463
    0x1150206091b01120c0203090f0103020f0703030b0d0b040506190e071401090306020f040617040c0612020405040f2403020901091a030307080705010f0b09060d0302030405180f09 78
    0x5144861031424404881d052820305030f4140560703818200005030140c06003d0341184560300840e150b4040108210415040da00c410b03050501c10402c12a00a00304412501c08680505000c108269000c0c0414900381805201500d40d20b0b201007030000300310000c00c9035401405541c04002c2602c100d400e40c042156102040d40c40d655114a40030004a500c00d0b10044065405040081100395603840e0300341681d210f81c0359450700d010006414442c141c0c01048130a080c01c1000806d8190345030903036411141d40d115005d030000307100000391046402c81d07a0390111000780201400603c60340ca000c0c04003801400f10100502040111000c241c0b861030f616000d10401c80382c00910210640e46810501001029460660030000310490358041058070100000d15102d807040202a5a4070880c0c2006421a044c52032545861410500d04503420380d02c0307074085500010202e40081844d0f0301c500e4103034514821a8400e5410112801007078100500c030800f6548500410300d003050a554806420b1500c1d21032074001c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 198323938 1250 198322688 198322693
    0xc10020d1202030c0316140d050609071110090804120501021b010e0d0c050102160b0a0501090524131802150702060f0703170a020c010c020d09050d15020c060115020609 74
    0x76902025007101c2d00035040d12424a0903031400e603455201d07056403101e41c1540d18227440d0010320101d410040207095008032503240c1031042241d800b6265456031444003520030320946840035101807119800480d0020300d9211701c90480c22105143c09030207904000e007241c820007440780000c0e80088060040a030383c06c103c0f10140607500d46240050718041000340094890b50760a100f500d2884180032072801c051401410062468500b02194506458058012038146c60500c0c05005050140c161000b4211850203030000900d80071401140e0903080c2d000d42c2c2501c01d030501d0a00e0283d0500c13a1308280100303001b541d0031010100c403840002094070441c54005e400041c204659000507200310080c0003901c1c0300b8a030104c452425202e540c0701c51041501c540602690001d101800011709125075403e0f44040c0c0080c010b40c11094801600e044100d2281900800070407103000304000030f01c3d000144898001c00c08648401e80000e4442d6604024040d80c41c0001400303d00ca1405800040c41074424040f00d0300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 198325188 1250 198323938 198323941
    0xf24050103020a030b030109080417011a0d0302030d1d1603020a09090c0b040915050d05060402150d1a1c080304060c0c0209090a0b070c0201080f090c10020d1202030c03 74
    0x118020f40c020720450341055503032a0750340b0107542c080c020901a10f02030b000341c90300d5070304159200c030740d8154103100f00b03a0f01d07890f108803200c07903020301c84080e84d2001044504921021140c14203074110302c41d540e100750302c40740740c6580e40701c0c1070000c2c0015220340e401c044100c0d00003011000703080d00b011860f400301075484044108104801c020711740040c1001803050040070b02d40d40d40d072210016560415001071070b5003901c840c0d10a480c8801031412078014041180c1c1c3c0300c240603144d00c4040c1c40300000703400a405600e0400350750b44d00c0d511900031140400701c580d00c101308161442c034124030b81c441c141c14801d10809814071540c10840c4000c00c03220300c550700840820720310b494a580c0c5100800441c01800c4c140010701a808004d42e58509a6034440ca601001801c2855003903d0b0850714800001e0501c3e043c041a04070b11005030340e02c07000f000d501400400c4040003507100c40b0046484c08901c00322450707200302540007104041e9408070301841200c04a48502c0310440c421620401a800115010700d0218001d20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 198326438 1250 198325188 198325199
    0x5060f030f0c04031a060f06040b07020d0302032a0111030601120b0d0b010603050405010e0609030d05060307030507120b091c0c1109010f0302120a0b0105010818100f24 74
    0x80c8802d070441100d80070b0301c0c58079030740f5500c01c000921103001c0030121450700310410280342800320000c0880e500440d916494103080004c804801c2c082c074030020340249104944c0408160080048902002407600c0a00d8180d0042c4c41c64000e112164060360590b50810203a249c480c24400d0560b0f0203050140c54144410001d0203400e00200580c0d0312042c2d0007904650306d1170214019810050181090f940c4c0405c051401d8104170342510003231450308005a20020421100303010100036203120442e02030f4046155100c003000285031800540000d000c9001c2c0000009000382c011101a1403540b20750010040d44e5100a00700b51540f0514505142c0c24907119180801a4440e44054082d540300303035401c0400441910101380510426009802140481703001482549410003884c00c254581000034030715000135540d400885001881042d042c00000d2011a0f20690010b00c813107111445402183c85145083c2d060704040c0081d90340380340409203000303420b207400b400003e410584000d40c0f107c02991b1501d0300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 198327688 1250 198326438 198326461
    0x3051504030c03081e01090501150809070b13030c0902070c0608010807090c03021902010e010e0c0609100c05010507020d0801320112020c070302280306020a1e08070905060f03 77
    0x10030b203080e400d25940850031407205c241c207403130f001e41000000003a80e90305154800c46103403080d20b1440240441d01d01000503154002a540054800d19640142c40f05450850328540c0d01d041e420052452491000c040744c92071260303011f4201c480c082c215203200d00d503a940781901d150a003070240ba411a08150b0003800150a40e8000c1010643c080c03030014070344070302e000349070980c60400165040180d440c0c00442000f00e2090003040d03841d4040d400507059405500b00001c030107208446480b0b0117080301c40c40400c1c806010320324070501030340c0184c02409149040c503c003d45585a010b40c500210300d81c4030012a82504440c948054a8803444003030340100940000490303001d40040784641040f10b402d40b81c5501c484540083e1002d84a0307100107100c1d0300e007144100102040c2c6d024400703100c803074690342001d00c1d0140626500c00b00d03074004100503601d0010f54400ca03005040030000ca8007040d42c85d009400a2540040c00902c551000e603108208903444100f00007141c030820041c9101d1744010700116001d07016030b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 198328938 1250 198327688 198327691
    0x6060108180d0f12020a1d01020102190509130c05030f101701091416060305060d080301080d030501080c060406110a1406150406030f030507020120010603051504030c0308 75
    0x1d1a00c040c040140c01c11255150904100c0c54800190b40460780708601c5400001040f02001c10090960925800d030700001d141d02219590b804040f0780030b18400c0e400344d000b98115480304103074a5121644038403202d0003418583c0854806d070701aa006507105008280180314081c03031480b880d910070346503803505001010b413072901802d40300c80303000b440c100095031000705c0c400c185003080d000c000800c022a0908003840812207846280e1140c3d046040d160640416103070b420030940d8a035040000352a20303000f010541038103207510010703c0c6400010002c180c02800194118401c030741a90f09102589e01d4207000e5032111040402140c01050070b100c14007138980900381c1148ac4100f007031708640c8900c110b07031599070451180240c00c00941e04070b05d040c40780300703010442c403c0300d0940141c60034030425103142e0340d081805070716003000303420444041045030841e8070442c175107912103a1041d100708880c2a520361840c0202a2072000b1500c40c445d0580152150072140d80043c071a94040d19080c0380c9182c41e8400365402c900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 198330188 1250 198328938 198328951
    0x160f1404090b040e0d02010c0801081b010c1509081207020a080f0a02100f0b0306090d08070f260601120b0f04021605241807150909020c0303060a150206060108 70
    0x1100c0c00e00c0110303004e0800c840701c001d90941d03001040c60800c01e9005441c000042c0c0006015421015a8201245170514101e200d0142803030031503020b40391424a100e400e841012100407403424405d184040c03110701409842d440114500c0100141c45104007642d45080180000f0218403080c4100c859240c00c16003c0c001608190040e0b50003071094800b0306041740c180b06c0043d4251540c9240000190a00b00f01056201860714001d1100045040002c0c00c80310300101020200005140c44202041c4100d240b401440511b0201c100b0303001e0b2507521150704140031100d4a000410400d0303907007444007150181c06ca54000c054001c2403800b80074000c0c000039510581007024032046003c100e0700011420426004030080c1c54181c030184c6d1644440d002e0038408003500140400f40e001008184035840880d202c2c003212001542da00c81403010600030b9444191647c444c011043c40490198494030000c00114400d44040340e0204685880e11042c0031075070b000c081301c0350050703201c60000764540d409864602d41010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 198331438 1250 198330188 198330191
    0x1407050c03090303030f09010b0105030c2208030d050a0c02010c1d03010603020607080d0c1403060f0a0f0308030a06090c080109021815070605060f0d031b0506160f1404090b04 77
    0x2030860040f034074550040d1441001c50000c0c0741008001003081c462041d500900b46881d0346981004198250140141c040c0400d4007001440d24064040c1d40c02c26040c001e000341c40540381c540020341c1400000346811151203036298141482e0b48169231041c840d24606507480c0e1542d80404407026120b800000d0703107040b601d070590768852011001d030f521540a0306682e8480c46900b0f540300280c141c2041a81c504003041c005100c05503411a00801c0d107003099950000042c1c50040702d200e00301c0002515a8910b61200c20480303682e0034048140a103c3c0d005511980348803006000207561402441c04817500c20f44d1110004079000c0040c00781c1d24054006202c40c070a4040c40380f4481c800c1100241e040031103403c1d41c00c0400c0e40041c029040203400c1c001c1550141c0c0440e0442c000728a039001050f0003075603001d40141001034404402c00a04e14a8410a4000e41c00208989061070004003400c1014030042440000c52400424008258400e40190040d9408002c9a501b003521b0000c1d03600140048046942d03019 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 198332688 1250 198331438 198331447
    0xb03191b090b060412050f03040b070302070b09090a050603120c01150b34080a05040509100311040c111603260904051512010b0f0a12080f04031202150a1407050c03 72
    0x1f500c104007803c0a0908148519500d400d18a001b070324203105a80702e001e04c3c1009101484c40341d903514188a0748801d204a02103660f9503641c00181c10220b0b281c051820080012403a210001c60551048011250841118046c9074581d204204580150703000c12100030942e0b2850540301e04801196585000030b03040d0540104a40d5403869103c1d0400d0003101d00080c0b02150070130807443d2040c281c5405c4200b4140400f4542c4c11601c030303503094444e1181858015525803403600c10071842107070004588040070080d02c41e051a55200425840c0c01480140d900b4031944200b02d0000007603035800418038000310502c0d4130307242c3c175001404085d02006140c800c40e0144400a0301032038a50761244441c61004600001c1c4003840c020070072509030094a2a503000f014050710500000e40a01d40140c6c2c21034100408640710680d50030001e07168030894000518030140410740f240c08540004c2c00d140083d501d03103002c0101c1d9a41d480994200c0303980c280e40c080e04030103c1d40481d0403030b40034400800d0030101041c10380303140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 198333938 1250 198332688 198332713
    0x903052a010503040f080a02280311031612171005040501060e090402090c070807030c020907031419021b1e0111030106030b03191b090b06041205 64
    0x40404190031480010110a03050318640089164106141000d0805500307506181c0c9038030403541d100d0f410084c5030402c0011b5041d5650300810410107030700091000401c81200300c0d00c00003000402064100c000c103040b540f00510001001c01a1134000100307010860040c0c2454952042c176843d026512002c1c05516910488c074a29908001c6110f00000701c41859024648000c1c80219003059102a0030008510002c507102c1c0c0e5111612500542c0488441165842d0b40488004a10075180300501c1c103000012490200b42d089040c5d00002402142c03408036640d500c0e282a4299000c8140110400e10803000003200c80c1c40f0034451400c1c10880100050030101640610030151034482c0d0600715650141005807002046140071101600d4828002c0c4402c0c84164051112800180100c206150303c3c3c554000c130540f400c00551044a00825044410701510300b4100c88101080b500c50242c047d54400210383c0034100c0c000c105882101030002840c01c3d15103100c007030b400c0860007021130380340c094009801c02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 198335188 1250 198333938 198333943
    0x306010c0b070c020909060915060310060f0e060d0c03061a040501170f010e19050a0605040f0201030f050103030e06070201360f08071a07060606050903070608160e01090305 76
    0x1c03840b4a51280b03820801d540c010407000c0540184818000d5002c0c030104000c940c0c0106885001902c108411500f0303486510002e824400e001244514207803400c580040c400c811503480c1302c1200d0415040c540182c0b566800c3c044202c5841001400400058204000284995004113059040c558460340c0200b600400102a1007007070f40282d22501101d8540c100740d0700c0501000300e00c11542002082200d1294030700b43d840341c900031100015280e26065040602000b4444e0841d0154440780400691400345000f03180f2104145007a40080d18004490160f0401d51107100d0680750140c07101c042000c031318020003a0a501c108000c90400c854214540010031501a081e4000803080444006800b41c1000c000200b603480c5e403041280e00703041c0c1401c01c0356034001315118046d902c0100d49600004406245080780c1d200d0741c0c0c4000c125920744030001580740c0d805805002048005c50546090546c1d40070101e82c010802c3c0c0303d21403480c01103c02c00c0b076010301446c14140d01da1010f06024126680c2c80e180d40c0e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 198336438 1250 198335188 198335191
    0x50f120103140712020a050d170309030307091203140307050c03031603151508180d030605010f020706120b1f121b0c14100204060203070605090304050d080306010c0b 73
    0x75a6003016440c4000000c2081c44600f004e00f030419010404000a40c00041190342140306041c002d80d0641941401d100408080003966003403210040d5407800d10904081d600d0f441101c1c00c2001588140740825029132141c103284200d07070141c1c0d40840c0c0d60b06194030307208a40d001074441e009000c0200000000d082e028000b40d4810115a103940d0300d1100e02440c05000d84030b403010200f40c90501c8100a11920340351010480c100c1190380b901b0b821a0303640c05000031803e000b901e03040302c4a1103100450408036905801c0f500030313104284d03902960b14403807800503680d8001c54043c6502103008072440080c0b52403240d100c01c6078114004e007421007170140303400035445a62113074145100099000d001c40c541420139010380c000502c4030b1000000c0603a10a03600030000400b403d002880340340c0340d03905003094000400c0300d54040d00c0c50800840d5241c1d82e440b0041c1d0340f644118402c55041d41448001407604101005881c00c850024001040700b00303690ba1080c5941c3d03c020700a60600900c14084804181000c031040d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 198337688 1250 198336438 198336443
    0x150f030b040203060a06030215071104060305010504170a0e01030216141011030f060112090203011b0810150f0203070609150b09270c0315070801090e0a03050f120103 73
    0x914141c00d0a0041c9418908004c024500450601c10308000503150042400840741000c1401034490f17500786880c40b0b8001c071501501303500508000d008014000c0c19409079014074404d43c490741c610050311405400718000e03000c00303070040341010700700f4682940a500200080700c0351030584c042e84c5820303503241c0329604c1c02001c0c02c105c00e91021000b292010070390b00c903250355024100456415480d00091084480380010000341c100100c0c40000a48595a504070241840e030050090090010b03031550700c0d2144c0080240c0724001520f00010900083c1d95001c82e600395200f00305d90511100c0d079030340141d812044003032107082148420041c90010504074458083c543c0e100307042075031040700500d40d01c13419211016913003440f41c8440303800d1010300d43b422a03600c1c2081a40120400300c0340c0b0188051810400591203c075010f015420012046c40e07000c48800713209120540f502e801070303600d070041642100e0402003c821140d000d4040d01022170301602c090680c8140c44421b89180606415021030400000e80c001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 198338938 1250 198337688 198337703
    0x20301080f030903030405040c05072117150d03091d04020f180415090606030b07081008030412230d02060115120203070302120c0304030f0503010315150f03 69
    0x6100030001400604010700740719004506000800300003030b032203200c0d501c03d03503214940d984900442c581c0074005456101340c00092189444966011743e1a0f0008540400400031b604030301654042a09415503070f00492504030508800742e8948180a24460f500c4801d9050140c10580044c001000b040c1001c49005001408003640c01e142c07042c001841c03c62a03980d440341003c81285040000004c1010398010341040e80c1c040c1d22044600307024014450303464090f01c01403e01c0408014000003403891401603046903540350341c5548401d200401e40716a0b0040c488150030400080000d440315608940341c0c02c0c002c41896544070105c100e04601c0d4011000300f03021503008045801c4401d50180106801450303028285581d0f200311810003003040c0c0b1480507410001e5808008111100d100e0b5040d6000ea10090b040c0c06c0460900a208054903001158224001a0311312089a4014860010749040766401298203603003241030035640e0b000d0203800300101e14444074001d00041000e00d0b21074050095000382d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 198340188 1250 198338938 198338941
    0x120e071203020c091f0506210703020f1303020a0b03010b070f0305120f1006020f0d1202070b01030b0114031b0904050124030611070302070b03070210090605250509011407080a030203 80
    0x400f40c104001703540c0080d2152005004040818444040300500c40d2500d480c0c2c0d012544c1c0d110020380003401485014001da00c404100048094044114001964001c40b54000020394648040d01e0a01c001d004820f0301103400d100c2c00700002e000c5089101d50ba4441d003081820490142a00c070b19811040b503507007031300036055070510200d0b445502c14003000d0b1231588007034081030b61410320480d520219442c41100300140750240d000d405140c0d6040d6207901d6400766400d0f4813940d403400c119080c000e0a01800031744411015280c003652030001201c400030108440c01512100b43d144c1046504a00140152110b540b1541081d5508060400395080f0040310700c25425118114141300007140c0c04c00107805c0814500300300e00e0000c6600080d501d4200e440c1042030a41c0c90340c42c24012401c082c040008403a0756810700d8039550801000d90401d610458803c4d08501d15400c4070705060700c840340000c0b0381c400450420000481c06512401404004e603d0501940d80380c01d0b4580d0320f001d40c42e07111040b0030000079400310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 198341438 1250 198340188 198340231
    0xa26040218040b0606070c080303072304080604030507020d02090c0a0f020a11041d0709090b060616020405060301090515010303080c0c03040b031810060501120e071203020c09 77
    0x4212070041c012015010000d85050b43c1c620300c0c0d00c8005840f442c03140300f000c01d440040007880c24804002d0f100d01004c0e42d8690a040c20060314050011800c4046040320a10206011110100b0348040380d1040c00244036a03103503618191059070042900f66084005600b219016895034040c290150b50282e80050b542c02e0100e80040400c41302c0c3c45941c00f1074002d01c040c0404a04801000b1840c00310031640082e0261450320b03031403110100f001e8140e0307007406060701c0062248502d500c00c0c19618001d100201c82c9503203500c20845e0394460b102891140f08401b2040c040581020383c400e952018026000082d0f00140342c07201031821081d15118141e00c21040d0050003015400112540c02c0203110a8031401d20022000058072130150b40a0389500e135201000244849035402c11031654510b041080c3c440b400e0018240c0f40c098003c0340074082c00f00300b0304180d0901140c6148192140d14841c60041c00301142402c1020040c406e401d081a0118442c0e4580220180c2c2d4440e6814000c071000c0907078607003444000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 198342688 1250 198341438 198341449
    0x70302031503011e1b02030d3201050108070e01080a0e030c0a080405030d170f151206270a0803100902031009050c0306010903030e031609020904060b0414060a260402 73
    0x3136185c3e0503c10b04d62840901954000050324401e500010b808600e09800391205c2240ca921090398090469560704400040821511054162202a0b81e604c5460751401c40c155070110500034a24001415180001c00006c60380d48807600c401c02d0348050340d160489070700d041858040310100035203080b1030002d41005a8038040000c2c00010313070315050202c04c1110303002c52071998003801000413040d817458200141c2c948039007544400c2ea46000610810999604085440d41c4000072205030400e0844000841c01d101020402d00843c400c0440c020146191140e446007001c1c0c001500c810b1100c030903500c01051400403400514804d41c49941c40c00c0100380780048007416541c0c0602501d8510004000780030950741d203c0c0c100c40940703815090011040c44003d004c43e1a006401300e0034004a10000c50203e00841543c00609608404030740500500341c952215800a1095100b94034145210309860900390404c1800b8207059001410244208000716401c802d2001c0905c6014030118000d0382001304500c0c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 198343938 1250 198342688 198342701
    0xd030209130e061311100c06050a0e120a03110a0302070314130b0c15070801080706020c0a03030f020a0c0303080a2a030f0b1c03021c08070302031503011e 68
    0x12800306102080c80340c02a140c0b2494003a00601e40c4152110139081803011640e4405212400a8403046030001c0120300284181c03802d40c0c04407041e50030140441ca80b600c0354000c001c0110007c20103803427983d284007803000a41e4081480316051540b41c0c01d5035481403000c0303c0a01004801c5450160381c0c3c084900e401002a042820310383c24090040c032038007180c20080e03240001501c0701c22091a40d503801511020f4540100e40301d602e5003580c01002005481030744004240d0481d40d000c0115903009440c0d00040c0e848280a054030303600300000c0c00301003021074401c4100c035140c0080780c01621409603103602c0e0384944110030341007600490394240520040342043d12400d88116400031008800c51000d035000841145070000c11b17410181c683c2c0e00243c400856500000e01c00c00d0060080a1078014184088c003114504442540035000e10118050380c46c3c4022064600c5104a030b40724951a034441609034002c3d0005490111014541c03a48030846460034440c4250041030111130890341d20a605010040d03805 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 198345188 1250 198343938 198343969
    0x3080318030418020a030f090609110315060d0c0f060804030806040519050603100609060e0106030b0616050a140318120a0312020c0303040c090b010912080307030603050d030209 78
    0x1000100101408040b0f00b9680e400920000b45e07481c40f8040c000c80182c001e000c3c075284810b182500010410000790b2160114500c42c803403500104111104140c2c842820a0b0035078070300ca41d880b00103051340c5400e4680c1107185229241c9880100e4550030703400d69000164000c0700c041000c18040c042414bc20070486503025804443c14462494540080d44005200a041800c00c94441e00441c250b80e6080c8065540322082c580200040c0d5614412140944818818002c40041150000c21740741d10900408141c42c4000e000c0d00c0c0352002200d0081100300c101c4a0548050141504074000580403a202c080040300c07010003151501400d440d0301e14500045243c2d40c0c070440d0755050511000c4004143c0c403140c1a0503041c5000c4042d060300d04400070744506001c44401380000800c101c100b022880d183e1060b598900d00c2004500b00c3c02e801920f56003820301404504014010290380051440d50045501101e40e150200d056035036540c0c1c2500d01826074a003240460f401040000a50412110041a110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 198346438 1250 198345188 198345193
    0x1a0c0c100504090e0f0609031b03030403050f0708090612150a0f15030e1005010e01060305100e0402060d0501031113050f010512071a0a030509010c1e090f03080318 72
    0x200d00304025041e445030b481100082a121142108601824480318000340303d5001902d44615000342c000752a40e010001032051010240b50620101c9800800d0b00d10480d40741c0c0f1140d1402e0104903080d0040d421007482180c011400300b050040c3c544905001d0030304e41c3c0108455545c40c2c02c09520306050008054a080e010311102c1074100000e038111042e6030301311040007004100701c2021880481c0039042070740440983d881010b840380300446059201904a9480c056000801d903240c50040f0140c0e0b8050751b5441e0710b1102d02c4010320408440709607098100d0301c01003815240180d130001038400c2d103100342e106540b0b005038910741003103a04000e01c100d0004071003140100300900d45007841c400500340602a040c000c001c400d02c1e20351044030410111015081207120b050000da41d4080f900040c1d48207030102c03800a07042401142c6007034030500030f16280c105c0580b0398a485c070703000b04560603200c80449514070130442600000110443d40703c00410107035005035451035032450021040c00582050f4060414640d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 198347688 1250 198346438 198346459
    0x1226040905011421010908130801200f13051c050706020a030507110f06040f080127020112110705030408011b1e0c0b0106050a020f010213090b0a1a0c0c 67
    0x95030313542c1306481e4040c0000410f201030a0418642401400750030402891001d0002d111045101241158812200000000c0c0000c3d81c2c00d00303810b205190a141079001d1654240114800c441c250b00242c000b03844000b030740c441207554400000c0c0e8441c0e034001c5c1714540e1002c00380c030b14020301c07100780050409482240010320301d11156a800030701c030340314007d0302801c2e42d0f00d000041c4da0300d591f0f4003014540080c4003c00307a5403a1921078043c0c40550741140f0442c042c641ca0300000e42c00c0d8400b98038820081104001e50588000c2060b001502c06101c80507042c03071100d0f500c0d0341440020030319001a01e13129010394000d644803800d200800e4219501002c142c4101200002c0780542e140c0d00c52504807003482c011100c5410304885401c00e46104140100c02441c40003c0c0d0000701c1c0c40c40d800005080b07141642da00b1038081a50640e00c0c0e508034415070380e062510300b403452010f0041400a4005c802142405004020800e5840d0f014440300f48601c3c902e0800b2140c00126848501c0003000f8207000304500b11840b407143c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 198348938 1250 198347688 198347729
    0x203090d1b15140310080a080a0201050702060f04060f060906080c03071205031e0c06071d0a23240406140a0801060c06140106020601080d03020c07122604090501 71
    0x242c4561840c0f0024960000001045400c40c490300800034003110040f1400c0102515065500e41c001c803511b580103618110005026502c0056040d00030490000b460200707845c1c5880c1c2030050403442cbc910f80081900c071700b0005241c0ca140d03c1428024044800a0180101104205400e1020a030f00c20802540303240c002002042d4044102c800d02108103c002c0164070303a9481d001118000d00c500e4880380c5c0203e1041003200b0b41c0003054062401013018045401c0500c0700308001a444060154120346a5a0181501c0c52401c4008403040010010001e04100800301c04031408a18610001440c604c00030070100092a00410000c860348511450365040c00442000180240c10512540041110081a15091001c0c0340c0c00b01900c11200d4074402c00c50f40c0c54074006961101c0038480c100d468880d0811a10265110388280c89402c2e03021800360504074502500e101d002040c40509680c4c001d44690700c3c0d54004000100503801403800890642c9442c508403040080f90016031200c8000c0048180700e118 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 198350188 1250 198348938 198348947
    0x2010e011a101b0803010f080102070506060910050d120e0d030f0c0804030f06090203060a0209300d02060709060314040f060e120c0601120b0a05070203090d1b15 71
    0x581141560075040d5000440070440e208920f140c0282c854400c14140c9009200b00f203070065050f00c1803103189810381a50740903400d00b01e204448000d8410b80114020500c2850140b4031a5000886240f111440580300d500184910601c8141280d02064031031001030601c0c1c00c021400c01e102d46c101c4603e103010120f0740b406040441061103000c01c11802080020810802c0820384001d50b40006074212160030030b02e0054001c20f00701c4001c2c3d20a20681d0000382110540c1e0085802401c005443d28240f440840d01603206488482c035070361402010107070b208010510403c4100c415005641c01024513080002018010a24541100d010142484010444000341c0c0381c80340c0e00150b000c6806001030340c0344d09102006281a8078803003102e00500c1c4c0000711840c8080f0181114021400c25254213998501d480d041d10004920000c11812601c00080c040001c26481150310040d1341c01600d141800c10360000d0800310b40884112040c2c8061461082a004007000e4500500581040d5400c04031000c41c0c00b40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 198351438 1250 198350188 198350231
    0x1207030c060906021e010f090302010e06150a06031109370b0415140d090b0f0402010e060a23040303030c02070501090b070624151b0f1b0f0602010e01 66
    0x1d1030544843d00c3c917918a209501465100703440e000100132000040c90000e0113000e516100812138420000491032038030841c0c07180c000c40300b0010a0300d00494644801580138200078404618202014000c1e0703400d036102c04645110142c0c240100307407080c21003004001c020390807900c0c8002440c0c40500301030042c000200221011740e4843c0a03400f440c0c9440c40000c42d107212410110f403030311400c08250702e09840855088650036500c500e070340c034000e6945e04e900c0a05890044174040d0024585030000407007400d1240080c07a0500481c9408144010940d82002c00706440041d001200c4100140030001d055040c490034004904610207411340c42c2ca0711000803c026514010340001c0700e4001441410400b150344480d001740800d41c4c0c290101c5121442c08215041540b103003910540e483e00c4e280c8407240c800c005002c00e0a1016a12140c412034540b0341c81050b9060034000c88014500e81d150754400801200701400502c00c01c00100161030070410024203523000b030460b0f0304c0c0360ba0418024801c2d104903120b804 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 198352688 1250 198351438 198351463
    0x10309020613030b01061d09150d120e09060102030703301407030c05030403050a05030a0603050a0b09160503060c07060209120c010810030b0a0e0102091207030c06090602 75
    0x1041010a50000405602c81c07102c0521030a08240b0000041240c110341c254121078240d00c40d041e800d800c4010001d28a040c00140551005071000020400305556881c461003081c01703001e42250b003016644400f5030318101c80e1003102203124000080c4403403515565140c5d111400b1305c040c1d8100b04050740d01520410b0341c00340b0007941e000d010706288242458512400440c0c680c03024240011200480d55078041d10080d1135050000342000c2c9103d01c494001d00031280550392541e034591428482c000c08481d16040600300121454840300c0000c0424420401c80300c9044c0524030424413410403010340c03490141246c944520b00701c484902009a90342c00f1640b01c0c2c7c000051035000d0f58403051840d0940017486082c142c4c139840542c4e031461403842240082d170040f00b64800c1c1c80740d803501d465205010200406d6440000e0041380300c0000900f030880c2c103170403c01d21802d0f88070015041030810000228a444000448032060344504820014401d205c803445009001608110941c241400c100075283d60100140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 198353938 1250 198352688 198352691
    0x190905150306180f01020403030e09090604080d090510090305031e090a032016080d140304030c060b0901060e04110f0a050313050a080403050c0a0807050409020d0c08061009050601050403020103 85
    0x1c4003442c030014815850b40130902c400031991f03a5101d00e4003906045116045070b001780f4801c00040d021480016429000e580c10500003030500540b207543c640034190a0004a64602642c844030a60f000f01e8001d40205512907140c40751039103050f680c140c10001d4200d400c8041140b800701440174945002c11082070381074151605c4a00c0c424809000c10f0b080e0704820b1010742c42e1103410075401c8090300f841905030079100e825041c0c8030640001e010499000e80d0724448000c001e282000801c00084c041c000d80c0c0d80ea90f1040e400800d1941d8840c0000f003030050240e10404c04589644040c08076031a2074464040b200c4401b6044ad420302c0e107010b0050382e0794000c2c0310100c0d0a01c00c00102007032020091250001c1041c0d400b004480c000c41300c078540703030340c4d103405c24401201d130707407207016405201460482c0701b91043d00c4c007003c01031012928000410010b40742020b070a03a000400806001c1c08215500400005000c1d070308010619400c22041c50035640d002e070380c08031003841e1412040c0f092507a072060440f01101d0702440c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 198355188 1250 198353938 198353971
    0xc0f0f03150518090d0504081b03011e0c02010c08011404020f0409060803073003150e13020a1a030412030f02190207080705010c14010b190905150306 66
    0x41e03201d00c210700ea08466400f003094640f0004421109000700e101e04044c0c010f855482c08400740640311800ba81c01113600301e40101401d01000c802d807103444c0c0c10110004002164003850385c6904072811030300f100401c2c1882e0f2075074075500d030701ea80901419828001c285090070030396140c115142007807480059698462500060075107000c080c000b0954020341004403081129039590000c09650303a1140d0001c5518031740618504082c50940c20146100184100721035403002401c850403002004107065080b0b03001004440031074040d400100c440c0c8501e4170109012140e6000e4010000004029448269044080c20814140046c0c040a41e40c116501100249440300c80400540c003624034052a02e00303140c40480c0c0c1d90001d00c901995030200c252180c0a4a804030b4980d028162540b80d00d01440307010138103120f110b00004203505403d481c510500800000c1030200f6000040c0880d03880d480c051441814024140800c0c00588101900001c0003070490b002552098040790300c1d4180100f03d0040b0005411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 198356438 1250 198355188 198355211
    0x507050d020a051c020a0e06180901020c07030b011a090a06110a080307031d01020306030c1e030303010b03010602010606030b1c03090302040e0708120315120a06020403150c0f0f03 79
    0x1051501514000701400d044295845840380c5513500705805030321070000c1c0b0800190082480c4602c0e402180c0150000341001030b0800b049150320005801a4400e660170030443e12100b4040c40300c0c0001c5c501c960100b480f254504222008608030151704041d02d60030800404c070780d0785c0d5500c494400700c0d01103050140391202c0449026007061a5110081c1010500000704090302d42e041d800038800490354041390060070300c1c04000038200e000481d0501d8155014400d180c07034510304030075a8490380640e1000480f1031001c2c0c8011904540080c0d100002820b4080014850144c0a000701e0000d00200d2508008100005000802d24540c000100185090016401c001e05104030044805540c01402c18022a904040301d640e84000d0340c4510000b0717028001c3c00055402c0d100d011280114101388030080f00b082d46c00304111001d16540a401418406c50001e000001d02c640040c0c00114064a2624616001e00d0503031401e80d1200b40c002030400070310009040c0c00b940c03c4100150302c0c00341c5240000b4442d1148 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 198357688 1250 198356438 198356449
    0x1506060507230703242c0c01020601260a0501021b010c08010b0a051b0d0908010212010312120f0f050903130918170c250b03060114030420010c0507050d02 68
    0x104501480a0a007a848090810802100c46c0503901030744490030903082e040e03280343d115003240c100140180c10440c01081140d80340c00c50920b0700c400b040c01c401d82c2540c000c18018501554180d003214140d4001c11818034012011b408604480e82c41030090052103850140102061701c140102c882030003000c200c0b5000c043c810015a520340b9070303d170015640003e0402c001c50741d9074810503040300004c0d1030340e03004500140107000791100c3c1d9411055016035642144d44035080c001030f4582007010405041c40681200a25014030941461840340000b0441e52032481802078840051910a955208000c00800d0550b075030203810071070350144000105400400540142d0030b401400150802520302e00c2e481c420b1103c02d0042005002c5070040302c007c0282c038a03d1604080285030500581c14071600104140b8146400035640140145000c444402000001e81071035003083d601581e90305840aa0b2145002408401b0304803076209080c485101d02142e541c032980c51805000f1103001e142035190301382c03c64995 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 198358938 1250 198357688 198357743
    0x601031a04141b0a091a2203050c040b03030d0506010201060b0d2301030203031206180c0d06060203031909020a030203030406110d2a1506060507230703 67
    0x200700344403150006400840a01050700c8003040300c0600c08441c021402d0040455200c101d50b5111160600e01d040100150904901c20080000340c0800980414190000603440707044958100c444269003141001ca261140c42c0f01024015450859030204c00d03038000080da11400310f0740700b01240a42c0d41d103004030f003d02800c6d40b013510001c001041c0c0c0350f603107007040d0414811240e00020185590380711006001c4840403c4c030020350035800401694148210000965900940140c48a44030000342e80160310080c0045078205280b000210308403101d04101c0c05000000c04c0306100035411410b020b030024100316500c08a0005050356001a18115220880990000d54008040d00d0f00c3e5580d4490142130640f852a03115024060082c080e02c042c2c0c001e84469403001e8145040420f840c030308a405010000e0600026a01c0e0410100210f100c40303098011400a800c03d6512142c0300c0c891440c055544030700250303141045070f404020518a16600041c400201c2e500103d103804880d064600c0000c18141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 198360188 1250 198358938 198358991
    0x40524041202010e15090d0305160c0905060f060d0207060906020a05130e04050a0b0a1803030b03120f030c0304021306060305010f090c02070b0d1103101706040506060103 75
    0x801140009840da269807885034440c0c000c0c3c86503203501000404101c003e00c9890380084203031106012a0542e030030007080c01c0c7c00311031080c20420729003550650501001e4000140803110104108014040040c0c2402000e412000c203030f07100c00c0010181c0c80011491f019601c2002c10a0343d0105100c2d05114003a04024034141c0c20500c02c55554030481001055641300e43d0000c0410300c40f42c030740010f40ca0013981c13506124540040240c1300d0004560740e06001d0400140003030409540315100103058060841da400d1001c0d01c240c800003501d10488091604002644160a080c000184210b442410784003003126408501000b1030741e40d1765030303510005661021031b400c081c4049152020100301b442d056480309042e5911803040740086641ca00c0f15078250b89854403800c0042e000114200500410400504440030071158003091980c00c0101c0310040f500b01702c2e80325401103041c0508100c80c02120084c0a9181844006810b842c50561a030329511603016251f00d040595a0324200400008070b808401d60a2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 198361438 1250 198360188 198360259
    0x50901170105180309130605120f070b0702030c040b0301090c03060e101b030507020f100b04050907030c031b0312050a08070201020a090302090a1d0a060f0606050405 73
    0x584659a1460940403422611099071074000400c0100401400d00480d50054400440c5888001024000304c031340180040011161141804952a50745030304c00c00304000684020490003200d98889494269913501c02a00352008002690260b100070400f050551010754000c9480f000610101c0d006000c0254043c1c01455100400300c2041a01d421500241940e1004c841d03a10401801c100304403041901148860300c00021307900400703802034005a43c414220f0050b2240440f4000e1a20f06003102d42e440c0d190315554503041c9880c42c0c40c0910038190000740d02c2004180507401d40c2e8800403021341c103001c064007001907480d1055080c3d120a40d00b4010b164032040c4180c0390111a00c0c050101e0700203409580c0481d4240d40003410585c814800e841c00b031f014a13501c01030320034659001c2c8001c1c108080e00c003000f1540c8840b40500050502d0312400401102c6200400d01c8030b080b4180b100840d43c94100613480d0f117042500400541c1e600005807800e903030f411162101c40542005000400c88102081a0046e2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 198362688 1250 198361438 198361441
    0x515030a0f17030601200f010e0309040501170303010611070305030406091404110301231807021006142110020901170603030a0c030c050609060103061b020604060b0102070509 77
    0x300561010a04052007510002c10030089405880103e0000301c03102400074030502860203078042c2c2d1200304540146010140c41c030b044030700040c0d1401d4070100c40b151140b5510010340f0401905191045038010520401c8007046250b043c0000c0383c40744018800c000c1005441e4181d00d107218005c0c400030000716804001c481e41c0d66078484000d00f00d82114400c44041c80e4014034403820a061901880e00180401240d007440c681c2099805814903072030310315a860504800000407559220340c0d0502024810302c807284604c41c5441e000092516200c1e0144460303150400e00100004048024900d0581c03000f218400c018501700c0d42c002c149001c5e03a00240000d4401d592020498502c40c1c1d00407e52010283d0b034496100301220513110f0044026914150154401c1184040c014031031140c03906e00c18801d2800d49650340700e9843d000e1502100783c5141c1041c0d003249004204001c894801c554081000700d00c1d400303801c003103400080e484100040000e400e543d101c00d42081140e201f1722000002d0100106040301c503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 198363938 1250 198362688 198362693
    0x30e150f030403080423150c2a03040b04080601050f0117060d02012f060604020408030405060708070c08030408011b020c01080601023906090d060b3705010801180515030a 75
    0x12030440c05040c2031f440c0701c3d100100b0602c07013660f41128070860b00e10265803c200c608035281030b54030312202e0800015000611011404008442c02440180314500042625505003010007543d160f0180310107040c844041c01062030f018207100d040e540b203042128189091074180c00180c81c03640301e04c1c0c920025034080d6505c0d540c00740c40b100e079203040f5980b541d42120502d42d503450500080b8403990150042652090004011a1822a00521845120b026480c1c01c1104603501c0183e20025030308603101c03940022800303000501c02442415007141c034201281c0f18030030100101075114141200b002d810003e50100144059008000800381030601c04a04100541d0010407400203030a01c0082540d03a0100324181aa50303d4038009035101140b00034000d03074004001c3d5850800400245481a80000241d50104c3c1421458254400ca8440c2d100404581440840c08840c110303500c0e42100f4180540700c3d005224aa81c2d00c4104582da0191040000319034031380d010400507208400741040d0b0b05128078907030a001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 198365188 1250 198363938 198363943
    0x6020303060d3201150e0601021002135603041a0703150b120c160f030818070f0603020903030706150305150705090f010c050a030e150f030403080423 66
    0xc100c200c40001411792600c8403100d00941800343e60390f900690141e078041142031403950003080400004541580c407266910608007014103500d446032201c65105103107280c207481d2210900c220a090032140555841141d4180144004181d0000d440460202c0000c2c1000301100703040c4100020310f0000c00c0c2506e88448000d025100010300784030403910356600000c1002e0640c0c142c4401840059031100b041e9582c8080a040382c120248459040d610000001c000c12040314141d51002d0282d07655440e249440d80c0b6003200840c4901e4144010303480420700304101b03251300311107109031410744c940942c0e6902c41c000000c2c698012144041c06152412842c80d220469184408088030f1007070003a42c03002600c0c001c0d00111044101c03680c6021a80c1004072034054540701080401001050409a4025000c4d48403149040c08110080b008200c1030b04c910140341c900f1100a041c180d1070b1090880c900000381000d0486c5000141c001011f000440d80840e0401410a0711070f05d50040301c22041d00c03002d01c00310945a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 198366438 1250 198365188 198365201
    0x40902090916090504020f010311040b040303051801020c01080a1505030f06070305071d0d15180c0f030f0b060604030203030304110906040612021e0303040909060606020303060d3201 80
    0x2500910190b000280000141c01028450b58008114005007218440107401400203a2080c28400004101c003140130140f00011700055030195a5468591304065803107081030500040c00c5040d9441559007005682c0c1c01103600ea40048811008605e2410309915010120003d8000076030600802201c440e0807100000c02d18807411030340d9810302540d19101741c1a20032140c07021500c0e082ca050b0800485060508011800140e445403681d44100744c40c0084090807a24011080013a02c124850000284500e404102c0098070403207800e40b4207113285035180e000070101840010000c50043c800a20660780c0c00068038001e40e0050292036503440e1528081401c20103108040d0302c40c0d00c80802040075400c0034172400c82034401144030a820f4034440e03020048052890350540654240b07400c4c01e509181c400f4000750004100940001c203010910f454220700380c500e03075000748013154009c3c0f08000d03480da2650410460b44d50003249031098140d661a55201d010150640d840c2c40e0160700700013101d0b2728815030014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 198367688 1250 198366438 198366463
    0x12150109211a011206051905010e060307060302040f1809080f040314010603030905010509040603060c0c15050702031b010f02280207230a03050601060507050706050a051204020409020909 82
    0x155500082c5401d45220b48401c1c0100101103000040d410002030240d0300040c1c00c1000d00c00c00c0032100410b18494000c2e240300741c00034113546004005119107410704102600280049040035410181013503800c00c1132640c18400c000c4c1c40c08450310015290741c881c0d484448a140c022510300d540c0c41200c42d2608580d8410b00c421507250707445000352400b00c44184504416650b140c1e0301d03120450b01d4000116425080f64030712a61165482ca4000005411485000d001d89a07a0300c5880350740d0348a08005046170a400380e0038920b14144010070442da9800f00450b420f00421041d014510440c040700d03132b03004200c0c1c1b94003001c0e114400100f000c2e41100c0c40c01050007110054007010f6505a00500498403240d841c0710b2110700c5840601030064101c200300001c02e000c40c1c060002050140d03a45c0384d0f54034140c02a4090000310381c00044580c18050184000000391485040c054544041100b00402511440c42100b0394500d004000c1001c55990380c010408141e0002c00c641624200704400644401840c4140f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 198368938 1250 198367688 198367703
    0x112050f1518160f05040f06050901030b0a0611010e0109020a030b041511070c050409170c0f0a060902040b031c03110919060909142a0705010203070906051215010921 73
    0x861300d99445a003c44054907117802c0350842507486c0150039901038101c44c41c990b050603201c0c92038250302d0300c803d05aa4010507040e9584032000700f800b031000e42198107202c0b91a04603410450700402680b02c40304540e0440740e0103a944591507480c0d01304078411920180c82281c100d4149490b442505c4949000781102e6801008840c10f619919002c10044800306c1000508841d1400385449170054a1400741290362a10f0007034031060110b44811a04000f003d50040b612203a48007512402d5080c640324141d09442c0950003010211005c803040c9860101c049076200406880d4000320103040415010344032031040180c215940c02410000f691800503085c00340b0070006071140c0001910f4041e80c091040e40d09204406000c058032855101c5038140726610801103e140c581e40030140082c2d80c2001842054002c6000507101c0c00d02240040c20340a180c0e01c81001c00400784489086645104022034000c4000d1440e160308400400c0182d421084030740c8040c0340c1c03403004034030260440010309074103440303610500d034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 198370188 1250 198368938 198368957
    0x1b020d0807080103050c150f0a0801171f0e01200702042d0b0307030203060c03040c0f0b0d0903022d0105010b03041109070e040510050112050f151816 66
    0xc110b50081092102400c641d0200403403240a0505016866084c1d40c0700450034984214140c00304a142d20103031071100050701120042210708144408080c0895110003d009011000c5411030038414000c440f05d01d001d6030342d900583d46030b5001d5010a07000e820307400702c0001c4200c0b90508826990400041640644c0c101260020301c03240c81c0401200301904038858200022560b10307120001c00e0f03071030711054051241c98000300140c1d0701004004e03c6885500c001d941c4c0c03883d00f40b902841211080c0e0024003030340b10a84d41400b41c002e0100c152005021005d00c0040c01995070b0408a00d00ba0a40e0456890b0724001c540c0d1040d02468084125600c00356070300240000d90381c64040000b14401220b010300b14000441c030300034940c0b9046890340d400c00c41030315040d0f1041710310310006412240b00b640e500072013100d80038041116581040e04210002612001080507180058000911510081003080300900c00c1d00001616a14000501030300102c0d24032045c054070344200c0c40e0040ea80c230444640c010030ba100c003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 198371438 1250 198370188 198370201
    0xf02071a0403140a020f010e24010f030201050c01020909070806040c0905030d050310080304080102180d0209010e0a14040605010503070509070906031a0d05070501030c0302070209011502011b020d08 87
    0x5254000c0e54980d4a00041c0451140c2515071030704070100000031030107841d80e200280d41090080c5140d01c003080f1702402c02c6e4043d0309c43e210010a1580300340031420829100400c101080031024004481c0c080c00c1040c0d0310112181120300902c03030348141c00d034098000000d00042c00c0e8000b0030503201d200d003501c04000c040314004003510322507010320070719a159000c11540e1500c0e074440c101468000340f04002c83e24049032207204580c259003091300301c240c140e075010404a00040241d038003503408941c2607940100c44010307900410140c00050290740058001d007000b0590000b5194403803001e207111115208981d0405181c0b41002d00400c0c41120b200748940c54010815103892102c141c015004e81d1154600f040c589a8160302803c2e10f00c00041d07078091000d0440ba1282ca0340284022000e100d44064007006c0c0c01c000c0094121011010340308201441231201c040180c4030140c031541035a04034540d040c042c004108040380074040c00c00302e032410b002920005084060300003440c554202403d1301c40f840f81e55206c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 198372688 1250 198371438 198371483
    0x201140a09080304020d0204091e03081b030403030e1614041121041b03030c03080108030a05090d1127060108040f02011d0909030c0c0a060c1e02040f0207 68
    0x9000150602d6001c101180041c60b11941d100f29080c809070001c070301d040070340c3ca410700c0400c0d0950b444030043c1038030300000d810194070440480c0d01410341d001000c0343d10b42d040c242036040d0200803c01810b00d0740c0c1794ce4050700c0940800400c5071014000160640442c0c84031040a01c81d48401c00940c0074504260309294079a030748109454140e1640440d03904012012101440c0240001e001558003a5460380e07020b48498030400048080c0d4001e448020034100245002802940140c1c032201c03490b003080c0b04441006034860300720350000c4001c86d205500c02e0200d05218131602411400e180d070140261031022001032020504a03c1070f10548141c00e4030f070b0340c2d40c0c006540c2140102e40c000c0001c2020307402080158000d42c4881200a050280d65101c04401000304a1001064800c07201e40d03400840e500091810403c0040500350741a03481e80d0a15252040c040c100051822000b4800d1013255024000e41c9503402ca40d2040c035130020300a000200440d86214000e6000700c000351000d0710000001403450040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 198373938 1250 198372688 198372701
    0x50402030a031b02030102030103060218010c02010219080405060c0c0312090603010504021803060c0c0d050c060403030222091415030a0314090301140f06010207060e040504020402190201140a 84
    0x34000e07042401c8595002c0f1520f1000221254a100d2411681d1025072402d2000d540614821000142d40340c12202050b45000760b07219180341003000660010300140d030302185d15511094a00d80c20051001d15240410440c0a01d821954100301d01050300305400c06d0015101582040076230a864400706c00743c0c0000302e0f91250112680e0048010001044941041d900511500c0e0350710708841c2401c00d803040040d05181098844404182e00800c41b8040300d201401120140071a600b00340b0b24080825102603264000104003500385540440e0075070b21051000ca4041544200e02c10442c4280e45481c200c20080c1917075400080e0018804000422402c1c4514003805401b0004008222034101640d0442c0c003400e800d00244002941840f50888544003406252102b00c6403404282e1646000b45050040d80d00c010030a604540c41080100640303034026590030782102040d05e01040f555100c0c00450068482d0500c24101001903e2600781c6e40313941940410b01c00611074002035055102e0321101c0064515 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 198375188 1250 198373938 198373943
    0xd150f1a0f0f0418050f1006120209010c02030709060303020105060a03050a26070b0a0c030c0f081312021507090f060302070f0605041a0a02031033050a02100504 71
    0x108100c1202140d0000014000b580180c0300418030b4140c90360100b04507400b02e842000b03ca180c688050082418104170810b51118000c00f51100482c0360a00c010107400c1e040803403c03a1160b000412002907407081c105420196000f4040740d070580d0780c13038001200a01561106a005511f49000b051880c0780890a103021281c220340285218070880e100c0510142c0c10300740c00440880c3d07200349001081c412802402e41a030145007540380500d400004207007036a429001c240e04251400e01d0710b071601904010103600400b92441c00d49520b549404c40e41000790781009000d810f040c0d0028003485000d40c00070701d0381c01070019240d00000d5916014400d070703a07030100ea02130b86100245440c400d00c20680310b9030240004234010000d40c5000c6105844050440d44156020780b019008000c40110060100b08090f070010300b0107508501e14501058481c840440718010103503025840043d8803031011502360742000b070508442003c1e40c10081c403080949698800c01c02d040142c001c4080e000408185441803610070341c4c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 198376438 1250 198375188 198375239
    0x1501020c01080720010e0d030b0603041e051203100303030b1503160306050a03140601060806030703080304060207060c030b0f01020f0d03020903030f0301081e030c1507050d150f 78
    0x100d442100b0f940d0400350300c0d80c2440580403250b204c1d50340380c2c0034003403030140504110150900f0914100c008054071001d4020a002d84420020b100c0018118a00c688080d9484450480300c2041c51070500e090550903400c0040c02c91002c801c1c00303444500d0242c5607003124401d07103081200c80e4200040c070000d10024542089c40c03403418400580200c1d025505951228131903c1e0000e800c50b241e0000030b80c1e9402039081902c902812000074030740c000c010090340b17000d8070550800000b5460004002950354809000040c0100408000f04007000880e030180c03100103902c5541808501001c0c00001d0085c01486401c511595030390400d02c0d415400800d008031009170441c0605000b1021a9003030b00a03512021200d80c043c802000041e0329103501c0c1d4003844c040c00c50080609500b002c4001503216030b5929603802c1030381c1c4c0c0081100501c20700c03001a00320f40103400080d41d6021561140803d49907402000c40b449403d506044081015003081c4040c9010b684c00300364411a41601ca0a58400c8400704072403054448 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 198377688 1250 198376438 198376441
    0xf0506010c170a0c080c010501081203010b0f0904110c01090519020f0415080a08030108010f0209060313030e06070804170d020d08090717010203100506090a0314070b030c031501020c0108 82
    0x40c0e81c08001071801d40783d40c2c1810352801501d03580f0009142d01540264074aa5954001840311020030300003100912514840d6504550501d003080380d4500c1420503021a245001031030b02e0442c0c4480c0c01070000d0300081c241c00f9072504240e080b402d0217883c20500c211000c0c058014101d80301495000c6100d8041c1d0060000714504411100b40001410151002e141c003e8525000148540c1c0401c943d5441e18403440c4559120b5241022240c02c0d80c0c2d80c2d03032112510341c0c014001444241c80d01b80580c0e40c4803242e00320070300f2002090300342076400507090080c003600101c001031802c051110703a4000700f0803596030460500c84003048520103602d6250203030300703a801a0801c12205120621070001c0a0304400d0100c141d58003156078a0362003040c0d00311030140e104503035004410046020603401c00440180015a4001d180c030016038002896546180001006a580c80040040030b1070100303c0c134006414000070550b81c03414001900c0c01503810031100310040e15608080e14541e540701044001e00302c0c8060f10b504103603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 198378938 1250 198377688 198377723
    0x31413120501020c0d02070e010f030213020d060512160b0408070521240a06080d0c06091b03020a0f1202100315060f0207080f070314030403050706030f0506010c 71
    0x200d00301050240c400c1d41d001e1041106443e420721100340991240d400503c002890b000d400c61450405034090a010500c010b010000b42e1140700001003101a4080300599034500300302d031070b00113042c240c1185400030702411072403a10100016688491101c1d020422202503500c1084640c2032040d8015844140c1000404114508104109042031141410701c010104112a90545007400c03184240709265040e0020844030340f440b01c009a041130301c000c01840b0550800c0d045940e6040301342501c8013002041869101800341541c00302d0906540b080e084001c043c0d8280e010341d0112554001070f03100d030041da400080c41440e8103400d542100d51810540c0015460394081240402c9148044000d0503103811316807100314809041031010384a40e071590b034022003401000030314000064101c43c103158400d2410720203903080000d0b9402100d60040100a0030b400ca918414114001c0d540010111710076003a0200744650103070407814000d16400000c10407503498000444003038030702820250403002c0900c4081030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 198380188 1250 198378938 198378959
    0xa1a150a0c02030a170a030507020c1f02210d0506060c0c01030b0a0302040e0f010c11120a090e0108073002090a150303050d0b0405041205030a0605040c0c031413 71
    0x1c0303800242a034010b0303845511075800d031074907141d020090700c030002603082d400981512882d41c000070948010700300340740582d021408002c0300d154181c440c559201d18145a903403081040350310602444421501c407403954855a4919045251001d15250800000800d00d0800e2010f440c42d0f000000c0080c07000610020040d0020305403c0b80040c1c2003d00c2d65004405602c40e0300a004005060100030001c042101e1045030844040102003c200300340d80b91101815200018006071141107698065030350600d1f1501030b6039402240c0e0180940c0c8581c6000000c4890340404d400041701d040030410914110540020350200d43e9507402050180c1201c0030328005420080040c0780d018006030300001d588814483c0c20000c00784103038011000600b00140005450500d40142846020291010b00003424030b0b9071941d142c803443c04811350800030088001031340800250000c40c001c003405070013004082c0340c80e1030051040d01134223025070120300c421601d543c2e4810004106d409a000310500515800d00f800024032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 198381294 1106 198380188 198380207
    0x6040b0d0f05060303090f190e0118050f071808060c0d0e0f0309150412110315010e1b040b03100e0109060b0d09020d05060a1a150a 58
    0x8036403400170580301c2010040710342c5050b0840040200c2d1034004482585682400d50700800140f000e4415215410b88990140101d020142c450000b17003994002d46982e007410700d07a44000f840507407042d134803c112294001e03503c081c055139501d1194a04441a00c11505803000020140701400d203601c00e2070095008040a4414184a03000090700d0340038000c1214000c0d000940d00c5510000e0901c1190060b190414040041001c6401c0071226203141a681d503001c0d00c0390b42c060007014401c030a9070030304031405034000c080700e651800100144544111804190741c0401d10005c030b001c400100145218203400f00f100e01d0101e1501d0202c141e002010707407202e26428540f2a042c001c40d0170312021120601c0034090003160020741480070030050160208090b00d140075031818442d1211b5190400d18a41000103205c51050080c0401c1004034441c00d40d1061903807204010a0003075074006c00e09030 = true := by decide +kernel

theorem cover : BRFrame.Cov 198201438 198381294 := by
  have h0 := BRFrame.cov_init 198201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 198201438 ≤ n) (h2 : n < 198381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
