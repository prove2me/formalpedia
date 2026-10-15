-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5284
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:21:41.870564+00:00
-- url     : https://prove2.me/submissions/50ce27ab-f223-4a9d-90fe-c153c730b30a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 950179856 ≤ n < 950359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 950181106 1250 950179856 950179891
    0x130e09060612060f010501140702040906020a1412010501050f0c100605130e072d0b071718210f03090a06020111072a080307020a06030b0f04200a020303 67
    0x940341c84800403188200e0005124004014030341c03056100314000300c2e0460542d8504040c9e50045800e54140380b0341035540700c0d000103c812266900000307051034032180c640079a0070700101c800b0b003500782003041c46618100030020800c11021054070044914070121030307089840d40c007200800040906254801c451103005a2080090130346030364015210310403801000380044905014120940fa00c120060b00404001000000c0c803100356151008090909150803d440d04c00705d140075072202d40741c0501c030010f2200610070440e400000b62848451100c080b660720220060046200c00e90180c0048404103500c201c18410051690110050041c1182a504c04024035112407081c2d017680c0aa044040f800038080001d94045048810713003909801000544200031507000e15003001c01213246e0810012500700103124000c6282142021004001600307050004805080000cac0c088201240603134001c903201c81e614a20214803a0180b00c1d500c0d001c0790b10b1615219001002580ca030000c03120a507881449414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 950182356 1250 950181106 950181139
    0x605280c02010927230f0411011409090613050c07060b0d020d0b150a0f05041a030c010f030b0a1403070905060603131b4205130e090606 60
    0x521110f101c40c3d40c0c0004c80b03000058081c0300038950f01166011581650080030355a681540217240214460840340c2c0d91070802e410810001a208454981403107090002150340c8800311050f10007501b0120342e030200c10b980e01004580c078040e05060302c005003407a0108000e0440c9140f0040c040f01c40c0252030401c2080007d0041c80100001403202030f50001c030181c0d00c0c0d8000b44282c09220b0b40890000b90440f400c440c034102145401030b050b000f09000c260f0580c000d200900b03142c4a00c0d81e98451054481001e0383e4608082600c0d00e40f0000035074100580c0240b46210f85000303801100752011301814a0b00d04547d201001c20003000826840d074031034000d0a6000850540c503014890050b40005c0c01c10b85151284001030b0360b80040d100f03044480040004400360811603031a403e1005104100e1030484042e01c401002188040071102079100d11142c42d484110f810309489a000e01c500d850030055074034984d625115100c82d603150300c1040c410010404204860038049072243c018141a100d00762081381001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 950183606 1250 950182356 950182379
    0xc0d0201020c03031314070602030a110606091b070c1202010e03070b090d020d0204090b0402130c02070302060a05041701092009130201050c010e07171203010605280c020109 76
    0x8000c50303482800400c0505d6040754004814501c01e545001c0c002d181c00302d500b400c0110350791018001d6040840c030720880c182c1080800000b111400007a0016161450018402c0c0101170710807010441c1c1024070a820403600d03c1203504864020240302c2c070081e83c44a9000600d8950b0724224005410410a175201d4140080d000081d07980c003024050030078440f101846165490240b042c0c0c2c0c03002d4140d02002c056120780c07180800140c05400280d00d2340ca000d005114001d0981050600c1c1d20f0b1400c14816500c6501040090550b541240c01a55441100000301c40e1230240d83c114011403203102d9060f004210341540011009880f602424252a201e580710216100e103980419412110400024a00030742d545421002a03105040c1036041a081c40c00341400c5540100d070f00780f4590300600341800702031a0940804c03c0c00324030340014a80d1201c01000c4200074001072113800e050000200d160154407500e10300144511070b409a09c540c407000004402420a1102c2c60141d000c038000803404500c045206 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 950184856 1250 950183606 950183617
    0x21005040608010e0c040f09020304020103110a0e0402391c2a0c09061d06030c1207050907120c08040c15021006030b160c020f0907020f0a06020c0d020102 68
    0x80e222004140c3c80c146424003042001014640c174440300300300202d526450301043c2e501410b48000f0041e280c3ca018800035040b6a181c081076405020700f40b0011146c144c1c461100c0740c03406410750300541c4031159507982e41d801540c07500386071003a40324000c01e0403030020300c0001c100719010f4040c04540030007030850380c0b490805a0ba452036000203a8550705000c181208500c1304a64004540281c1c40162043d4a13001c80c844c045400c4500000e0b100d460402028090483c030b109580700c41000003a581c14610b0000b0340c1d804003203003454081c40c00d07040301c441c3c00c0c2e1003032000100074040580840d0192408500c01000070804510541c0d090f46041840c08409115110981c03049500000b5076030b00c1c5041209035040b1903020408001103108184d8003003072651041c06030a0043d8402c1c0c4001007507051a07200202840c100071010810414180e40c000e015940c3c42001c1c22003d4026034180e5255151444224240241c0201901e228424940e09408010765540100140c0352218150740d40c0130f4010070120300341e1160 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 950186106 1250 950184856 950184869
    0x8031f031709010c1704050f04020c07121b090c1704030e0402030a0f0f060806010b1c1508060f0402030f07081f0b03070801090204051b070609080c0a05070302100504 73
    0x3034001e0040e400c9180042c5140a41414804041c0381c0b1a920041075406036010a0b44440020400308001d003030416284800384021101503042c40003c43d070442d40e4041d588140301c010b01981c0215024000c40c81407060f100050610081d0940342c441c4a0300303016122503440e0f10700107403d059400c039004004210f0240681e6156962403000c00780001080003039000074201020b582d6a5000b4088283e6803449181d140300044e80e004110180b91a08203410500164044102e4500402110b8088032a0301f9404030f440c0755210000901441002c2018072a01c95500110f040388245c40c240441c0c0300d202c1040341d2050307100301c040355003030302030102059141e440512940c2465480b000101c05800e09004034022020740844000035642151f07400245800560750080326541d545200e1a420b505050183c40d81c04100181c40d480c41410420055185104100340a00801c0d40d840840f0104400f00c0103ca00d0544a2800c6584010032403c1c81a121000c0348000c074416990081c455200e64003c05c11fa9044400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 950187356 1250 950186106 950186123
    0xd14011d0f040507120b09070603020c060112060618020702041a06091e03060412030e0a021008041122050f090c0114040302100f230901030b0a09050408031f03 70
    0x1125081c0d006410400707072040350503025048000c100003968540146013035019507440d007854246094141d013002c440341c100307074205801089515481c0d100055000c0c1100e40d46401071102d1a00c80c141500144000d812a0403489100c14607001e6100c403035009001e00303a000b1501003000c0f07001414880380c01201c448040c0d80001003031160540f2490004a6191070400e2060038042802c0c41d030000904044040702c0841e1021502e2800985480c2d0511418403195008801001c83c46803680010f04501c4145115604105175030b0700280401c588a05214031184014180c43d07070350070301713404a04000064420f506011510b002c00107800062081c0a40d40101b030454040d0103401046001140c18454803609101c540c001000b0000050310ba9504082079000580e5400040c4036040380011301e0b450b0005114a110842203c986d88403041d508100d4043c808242800a40352000c0000310b100c08030309600c68580d50340f6103010001030002c0700000710312514107034104a56a00d603880c1c25401c0226a400007425100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 950188606 1250 950187356 950187361
    0x5031c0e011b0513030606031b0e040317150904030306140415031b0b030901020702041b020d081308160308010e01080a061a0910080d051e0d060305030d14011d 70
    0x50041c00101420301c440b8050815017030700c0b40c580d03006a624070380c001c488810710400c160a120300b800c02840301a18010038504210304080c2c400500000f04000003e8000a003040819081c1c5080c101c5032042d07841c05050040785140908024008208a201c1c6032658070102c00c1c3c0b4501858103100b01c1d1100c481d80500d08000c5030a640303c401884115801580c0d91a0b02404042030002c01c11000c0d40c869001c03540003599800340f0344188402c1d00c0c2d903644908000300100b004103072507a0300480c000c50561820701d0304840e1641c66807015201550001c0028040340340c002040c0880c00f81c1d00c4801e192480c02a1a00d0180d079a90703003001003810341d0900c80e40d100b9821a040400001e40c868105c0342c400040412290364594004000540c1000c0c10f030b42c014002118080104460030341404403007260032650901c14206101c40c2d0007440303985800300c5407074174038000000d2000c40c03800c95511080195420600310ba8556a0039488040101509a004d003034070140c4a00014110910320700c017034408171811b001c040994 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 950189856 1250 950188606 950188661
    0x1112030103060b0f0303070605160503010311040c0201060f03150e0d0516051609090b0a0213050439120219030b150a0e0909030a0912030c05031c0e01 66
    0x43c40744200882d401031206a02c0200b981c0e0030001713482418003810303000507a41041050240703241c1c2c60100c00c03014000c0c203200410201c1c42d0000c10a2030141e0584000c00c1900701500700701c2c01000075412811140da07805601009000e5820701c0b04d04e2017900300404100d144401d4180f26601c0004019400000348204010f140b0000d0a141020041d0700c03507421a41c000e0050020888191003540011040c1552032406070248864034400f40e4000d118158110703d0442c6041200c0c14a0905005541c021a140c0a5044c800900000b03c80d601c0c80c0800c1c1c4560103e2409088019141c49510300030340090f001d0828410120b22038401c89a010132905150480c603601c0c188150064460070045680c40b4110290162344d900400d0020100314031940d6482c203160200204200c403c038005440940142d006108098038190452600b8043d140c00c6010043c020b903c5107030031102a082240014528080440ca03042d4128200f0000c081444946c1010312a450f00390030301e5800c80381c030700d40c18980305140d551000048 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 950191106 1250 950189856 950189861
    0x316030c05011103040503060c2503201912300b010e0307030506101e17100204120c0503010c021b120a050304030303050606030411150d1407111203010306 68
    0x140c00b42c180643c0c0c207251b51480042c1c02e0010448a0000c41c08000941005030310802e001c4005121048250741c500403600e440040106c040071a0340141c00c0240004210751311000c1040050041c2541c54031251014149000850910080c14800c0480c0800040c5d2101da4904003c8000034480031225034000340c0d11043c01070190102d070008505000340c0c0380d2030f48003d44013484000040c60040c0d00074102c6040c4840214541703440f0781d00c42d501d80445c200000c0840c00001c0c00ba0021070b90780c04c0e0602002e00000007882c5c10024110a40b0600a03c00240000d440407000351030300345180100d0b411010643d41e02c0034142601c403625030344401600903c1112101c09488042c2004880001d482d0030b00d1051034000c003500d0710700010416202a40f0100f4108201903242c00742039030054003034407060308600b044e0303846917091500b51041070301c2513044540051b02414041c2c180ca00e000110030082c400d10f240e0010300c030506035080d00c0314000102807242d55040c5440c0040d5040c24250348c490414070f10381c0b950325000700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 950192356 1250 950191106 950191127
    0x50d09030f020f0d290109150e060613080703050709050c0702041a04111b030a1403042402071b0807050910030b01081c09121b090e03090316030c0501 66
    0x62040d401500340c8041500d5904002c80c44001284400e01c00b200d0179404034038404140e10008419040c2140110128101c0362108102c0344524480002615a100020028040c007005500300e42548100000d2003640002c10808803400740080e603a209071141c01507400c2c0d84c01111115101a001c208150042c109507020207a40f0906411000038183ca9400040c10344410003c03d050541001c42c040d1030300343e008840a460b0103080d10083d450040c00310030240601c5040c4c9505210344001000160604c40c95031075103200c4440f40359502d43c50303c01d43c91541c400be402070304080d103c042181c4190500500c083c0c017504181e4079604000e04a4a02d4441001070a0030010203510481004941c0080003448529005002e048450040d1219060b103000119403040135124110411034209020807613002d407010684186c5410040c1c0d8882c1010720400300c445440194846d1074034618240c8013076181c440100140901031422002d90380c130f4500802d0441130160b0070380005041015800c2003013000358001d1145a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 950193606 1250 950192356 950192359
    0x80105131b0902030c0403031d030a0b180a1a18030412080d0507020109021005030c0d0515090106020705120f03090105250b0412031505041125050d09030f020f 70
    0x203521600c0b100c025040c1d0f0020307a00f40348007040c0858203200301904405030a000100e05480440046410400695962408034028100203071100100300d21180c80403100b08aa610318084507407615203468500f40d16040c09004100100011021031203071103110b205c40410500b110700847c20141065600c5410800d8448219035800c010801c85040340924041c00d0302c90900b5400011b28007089005012108440c0d01f04101000004c004100e4101c01903000c1e00c0d01c003c1c13020340c0007a065580300c501c5804070b84004500d950240042c000029032590019950003602c50581d0303401842c1484604450380c40301e10105410860300240451205035125401404041d1241e0b13074400c0e140c1540814000041d00c88500c11345104e1020420007040c01074040d500c266070340f05850108000d40380903101d0100c0380603030b004042c450354442c04c442c2480348145040d5592403e4240c103424030a0111090246403601040c0304032654020880e450b0b01c100c1c0140ea112007102c0c0c100c541712030543d19523800c1106546071100c103035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 950194856 1250 950193606 950193653
    0x2010f0c02040e0105010302040c080c030103031b08070b09070b07030813020a0b03040305180105031302130e0d0201150509010303140c21092b02120304080f1608010513 74
    0x2000d40d440f8041c0412020070300c1c000040c0c0b94103600510055500036100001440741314020700070917200c50400c0303a045a03054075010b44040240b644590200c14080405003440707001203045d500340070760407108a014421400417600090b0303a034904894240260b820103004903c0e000002807515007642140002c5500c0100709020a0307848547d0a680c580056405500040001c00c1c50390007180918105040340c08242482402e40c035119000d00c00e021a0880024010f40e58403035100011503568000c07440c0d444903001511207101607040c00034000e10400d258940300e04140d8030009140e0400400141c10b0385e4140c0e403a200c4145182c1030b221030581c000511041c442c800c2401c21703c440003400d00880d4414042c1e690080d9a00400001c02001d1004050070001c0079014001d403000e18044009456665a41a01c0c1c0300002c08002440030b0450207240d20140b0b841c001e40110b4a41048045403001c3c1e5000206024200143c5801106080f11011540d0103009050541d40b80b012903c0750712040b07100425509031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 950196106 1250 950194856 950194877
    0x30f09040209031c0905010c0b151906020a0b131a040309031203090b0a29010e040c1e021903050903211c0911010e01110a0305030103110409050a02010f 67
    0x20a11306800d01501000c80000c3d1814601d0761680101c8a1008000920f03204040c02003507101c800a41d007004d0408884588038580382c3c0ca90b82c448621002001c2c41d0011030000181d42c0e11350294480c05096012100c41e000880003031400c010b041c800c909580e8000b10107440100c81c0911003a00880e0240040e0b09014000c400080040c000c5402e005810755141d40206a88003586046030040401034102d0391018105156074800070b0310640d16007804400c9201e0400f04130f04a07401641c0415031826038540282c10080c4d0094555002121041c400c1c243c44143c0f9105200d40200326103400c81c6580c42c10a2508551505002ca4800c9001c1c01240030001c09482c605510a8042c0b50140c070326080201c2c4200c400318a00e941c1700384843c0070f1848034200d80d030140451191607568022180b00305080a041c4001e240d1182510b034460800103242400d00c904a0b4050101030030042e140b60000d100444440806510071001c50420703000f0b01000640c0000241224406a401542c504600710342542c100444400e8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 950197356 1250 950196106 950196109
    0xc160f0602040b1c140604110c06010b0a110a050604021306170a0c0b130b030a0b09011202030c01032705010b030a140c061218100507050c0c0a08030f09040209 70
    0x10002048a40070f0156901100c050340e208025100010b064100c0c40c0092039056684a1a410740e808101140e0000b0b11200302404480301e4082c07050560480d01c01c940c0040b80a4409900600298101d52101038401c0a40c00121307646080d2040003c045812a101040c014104bc504c220408031042001060403515100590040c0d40041d0100c41242d200c03840748410b00c0210b07a003190140422190091501c071410300030155107a420301c194814504000300240082d82d440e4014990041c0044c03002145503520b140c10003c0e8040150280d05c24017420449205560180c415000c82d000c075401d280100b9048800c1c1c01881e02d10944040e1b0307065403a01c1040040d6a02400b4a41180f881043c070806c214446c201464500101c41e082c030340c094202004056101c8440030012a0700c1030080f549855010703000d0382c1807414a140b0020070455981440c040c0b2102c00c3c4c00902412410007900e0899a0b44031001003005010980380c49508903c4d002000b900b0131443c2004c0082c11000005840275280040100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 950198606 1250 950197356 950197361
    0x100503070b25050a0308010501090815150a060810090b0109050d050a17120a0b0616140105180615060d09061d03040816050f12010f05150f01080c160f06 67
    0x2030483c1c0d40e40000c40d50408146d0814641c50140c8030030320303100c2c20a500744802d4030341e204041d403042e4628010742c0002810030141e48903407042c1d00320060481c2c285640d882401400000c800c0d101c0070000c00a403000030403414034600c01e203424004140e4810850a01d058188251552100030540b85c5000d90341396140070039032010250030004007148043c0c3d59051156860340d0148806030180c0031030f9050a0b550010b55803580d0a49501052250200070050710500d07061107154190f4284898079428002000341a0312241d130100068681c110641c1c0881e51030782c00d014049986c0340c101ca84d02c94018485141d00300c841c2e6111800071441520f0010b4003074039403640184041c00d100d112070305541c000101400b4140c42072101e0345013102d1054111098509000000d10394007130310b05186011316841c1c64406540142500028400700b40c0030420001c6040202c090114641a0608240502c100c9420f403c000e52060ba280f51081d40f0300c0080382e060144079200034451345081c240a48020800d02d4200c4040345e51032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 950199856 1250 950198606 950198677
    0x61206010f18050610080718060207050a0803030424090803010927030c0b0c2a0c060a08010b070f021806040b0109030210080603100e010501030209100503070b 70
    0x4070380c100d0000d29020540242d40302c000302c107419860604051004c40d44944030081701412050034030074502d40c4c408000700c0c1c0400b0001c0c030542c140d4010a000145090700481c18209803001550307540061a211401540d230380c8404c0e9402070209000a080b038034403140c9281d030b00c802203002c81001304101d440c0f034544c0d640c140c100f030300b1032840642e0750390751000082100381c2c514000c01c40c07009030485034840a441c080c3c2308103104917001e020841d002c40000d518410820442e5560503401c0d5804000461404c07598803030010041180340580b02d0201d00748401e1500406a81c004038455443c001030ba824500c030003003184c01510301129031440940c00c14005a45100000c5824132802c400442e26107015402c10095407101a07805051040600702170000d40c071220030402c54210642400b0089459803008603180101e1881050012490300c03080291340c41064100a0481e4000c44032000c0d0b030744a036248002400c00314411960316030300000701040f0004455001d490b0385c003003800704203d011541140140c0d0300c4681 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 950201106 1250 950199856 950199869
    0xe1f0504021206090906060d0303020f0d1407140f07030e040b1c110d020108071d092703160f06240302100201151a0705100e1e1506120601 61
    0x1c2c030810403241816103a580d4001160001401241441000300c0c045583d0300b0405010960001520342ca14003115040b01c542404e842c90400450341d640e50241c000e030009988040000b0800c0c110303030301c005030b09006648100445d81003c525040046e54155000ca0002e02d003e03805c25101d540c1c02031656105041d0908001455010301321284091500808503c401030b41940700320507c2d904000940d0344121940c1e400502c0b030400107041801480c40981c01d8034500e03519580800e5403400c002c01c240d00b43c0e003052408000300b502c8a00c8041161041c0e40c0301c3c0a000200d40300d9040f1100990302203014001d0421106008000001d6a00343c0900400c0303101e100b42551094180c0c100a0803c11030030a000c006108820500c000c011280c003031821041e5083c01d91195005240d082d0141507642c40c1301108846605520500702c4a03030b03100f0307080c40001604804082175080d001e4010912a1424030760340b40034210a0322005040c10f0f118661b40c00700740c010041c0450781c1200e00c1c1d03034982000380300c00c20849000e0810b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 950202356 1250 950201106 950201137
    0xd020a17161a16031a220e030c21030403050f0c0304030503071205070b0f1005060714010e0d080103120e1e03070b1e0f120411190e1f050402 62
    0xb8008400c00000c0c081c510f07044205480d00c50212205181c0c00100414243e0854030f4a58114420a41c080ba41d0143e07405180f46501c0d24150f04901040000201290308200c01941c454054500180680c4d900c40c2910078001c0808100050009100310300406444c03003101e122a0900c0501c100841c03a54110340c000300c3c1c841c0d2000640d403040c043c6503030800c400c000d402e10f0828a01a8560396802ca41d0502804004403d0110b10100d00d0f201521701074800580805072042c2e4132103419007002c01079542c000c0c0c0020641c0d403a0025142054001003011424411540c5131032129034070b9603951800f003900e8607001074100040914142c0f1107540d1681d4030313802c01c4d00d41149004008005420582003006640c004410080d04204050403254030412010350b41d2030103620140c60703c00952101003180700c0d6a10500000344440104410003902040e181e0110b40c09450074201d50303c1a800e1041c01d00c0981c0259892000c01c02d0016082c104510b440309070411000d448041c9a40c0e586020a00381d80104480856554 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 950203606 1250 950202356 950202361
    0x207031b0e0f0108011d0a030c020103061d0f060409050d080a1506020a030305010608071d0402071b0306050109090c050f030a080d0e0c1906050f040e0a06080d020a17161a 75
    0x102402502c4c4000c4002e1141007422006d4140b180d550200f00340003c09100d02000b00906580c000e5100000510000324140602d08a41c00c00001040c0304407041c0640c2d81212002c184e45080034455151035580c004002c0c2510342890300f00303403014000242040c0c4025203038202c6a29007281e02c0354810040c030140d001003110f10b085142c09026500140c200c1c5007080044810403106a911100e0740b01c403c0c0075030103120381103201100400c010303200c1d1600127041880c88800b844140e00a1020401c2282d0107007804210b00c4c0d0b01c07008490180c450b2100c1c09000820300000074041d0789020841059000c1008040764056a0141d60f0402c01b50850f0194035201c0d0b035103c49021524078140074902d201c4804940000c0b4001380440d000c074041480d4003c4c1030403c813002c20016228039034071003198068400742c408100c041c58801ea11030050711050140e001e10307000e000c9080c1c40181c00010909001c3c1c3e03200c5000f0f03440303c01c03903039480c1d060350040302c00841d014021742300707034008205e14040200c004c400c0540b10b00101d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 950204856 1250 950203606 950203619
    0x7020607030f0f08060a05040915061d0106030605180705090d051e030f0301060302090a030503040909032006012c0a0621050c1003020c0102130e060f010207031b0e0f01 74
    0x12a820900f5206003d81c440c10031641740e590504544c1a500708490000e01c1100e1404e020000617001c5c0102481540f4001c8041120266400003105000030241e80c42c043e84c1e00e45200714181e4040d032190f01d070048020f80800060102d1500700650010b40303480c00c5800c000e4080e000829100c52018103540640181188803420392000c20581d90514202c001940f41c42e8800500c62114801403081e00308059010541600683d01c600340b0364019600b0004881d10f96403110761110007455200b60840118040c0714402032514007403808454600c40030b01c00f510040c0e01e0000351003880700c882081e1013506443c51003031204a1034012580d42c010410f42d172001580c181043c400c6010025400c900c110359a440078109400540d0001d401c54140e207090b68800341e081d0340c000b001e4010303009510202a46500220340082d100515040910441d4441501072140d03031954070a0080310802d8004550060300025801e1000c909a120030044240084619411082d030f9251203282c0d001c0141c8a40a400344141c004010b607 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 950206106 1250 950204856 950204867
    0xd050a03111207020102060a0b04060e041401050a0606021510090207050717060402030a0f020612010605030f061203070308060d050d081b030105010f0e010216060309053f07020607030f 81
    0x4000307040c0c41041c83c103000d07500040c0d9248402811004680d40780c0050702100e44a9030003020082ca10b0a0004500e810f09150011a82c041e42d09070801a618040025030700b00045d0182c4811940f40750090015a0962011254440802000c44101004060700003030110054401040f08a009201400156040030205ca10b00c110f407072200c00c0b850b84884140030150750041899a80a5402105002c0303a80319031011a0f1580501c4a2002c2c00c036044030000030710700707070083e000b5445a080e0b2018a4126034070b4508102c990003140c450800e10745e20620051001070b000300e01072900800010032081107146142d450520f070200503a0080009030a240c2030115a04200d483e041507001401c80c56030540d810140000c1081c3d00a000140c02c0107044800146203074005d0011a44144100d444040c406031591809005484015000c90f050700c030340d04900f0080b821616990342c414044080300c03016421000c046001412088142c0022140708014036001a039509008150580c400c1c0c9680d000340e032426001070301 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 950207356 1250 950206106 950206123
    0xb0102060109050c1b1515120a080a140f07030e1804050307150f050f150a0f0e091002030109060306141e070224010317040b04060309020d050a0311 65
    0x1450b504160504c076115504406580c00494104800c448202c0100c510764a0312104401c107140d400461400d2058948621030007c0c03c040043d10a000404c07842445142c0e02d02c00442d002d40084e40511030348000078810400484000d100304c541b81e0601c000044151081c0e845410b007200410804520241913003400b8203031214090f0302d013400445519203502c50799104d20680354020f00000c44480c003014440303800d0f40b0a680244e0b5100703041240389807140100c060060f003515040404102960001c0705031900704002801e54605100348141c151400f5000000d100000d00108140e000d42c08202c4224a001d2000c1c5008000001c008207c062031818980100d45054500070584a440c40411111003c0030307100807205aa01c801910301d940d2003010807800c08090040c194150501c015a4900c986000c1090078140c034040c16850b400c491007894020418812071092002c512000d00080000034003a9000180301130000d4103405441e003059a400d400c01c08018801c41c0401c0010f85040d1000e10100b11050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 950208606 1250 950207356 950207369
    0x20703020d090317070602070f050d0905220911150a0e010f230906072307060c14100606030c11010b06120a0b090702060708090601050604050415180b01020601 70
    0x599a50031601c07484c030348240091002c0c1d000383c000110041001016070440381c6151304004000d107031086602c0c18544079006080c141000405040c000301c2c01d864192962201800c042e580d02c001070749100d0003d0050681c203102914201011000038669807104400707203104141100d08140d8891210401900303c10300810458100718540d00016119030304000b242600e5030300100105a10350381400101c0b92440340c1201c80743c101e0f501107018030070801c80b80320400c0c050144500b8091403803600d000003551003c0c0703840b03103030f00017034028012402051000c2c40e0703010400022829140b24021981a220a40b0384c160310090020b95139070020300060703038405010171580c40d400000f800802c844a0004500d405004001071070701c00c0303400101e03110440c0c546c81100700c06000740c40380710135183c81c01d0041d44035142182c1d004085401000055154480410341c80c1c180c0b98010101e0f07003403d051030240f00040001410703803651500e05034400b24060381c000400c10b803114000a00440c40f440740e200024100300b810b03231008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 950209856 1250 950208606 950208617
    0x20d030606090b1b0c130c080a090203070b031e04030801061101060807060f02071505030106110d020a0807020f0a0e0115030209030c061303061a041415060a03060503030d020703020d 80
    0x2e0245070190f40072240d000c0301d82168100c00312090b40c09507007424181180782d035022920800803140c107490750300000d00306440c0d9129800d443d038034845040265005507800950580000405000c00c80240c4041c6800000d050f07803150a03d0b80710038900d4508141507030300740c0114400d07000421003d6070019540d40440e040100a2102a20704507103640e4540160040130f090101035a40310120b0b9200b0000301c5c2c000c1071001654040d1168103400606254428002c00700014444200820700380340000d4030311081d4205600502c0a001c498881c03a0340e82d0800d1504a9203c424980140b0f650f90716542c940e400b51088180155030755142019841194410611403801c5c98014050a02951740100b215400403109444542d943c040910035450031260702c0d00000c1c105031804641c081481890101415416001d86080100a02c0d001285501c00d41c00c071803001c2c40c032035564081c041a04010b00a0040391107d428081002d5447d200000d082d07401904a02c0354955001c1503000501d40e040110380b4441d000d030300300b5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 950211106 1250 950209856 950209859
    0xc030b09010b0405131a06030c1e0306070203040b071502041806051c1e06110d150506070f061a04020708130f05030703081e1801020705060306010c060915020a020d03060609 76
    0x10042e0700d0070740ca11886c5180200304006010f0307172814030020780009001010300d98142142030358a149040d0aa031418007a1040030000341500e0700000407030341601d85414940b4104840b81e0348294400540d44e0442246917000e00001822441380e45041385941103890003c03130b41908010a1202501968020081a0407ca1440c0c07011829118a140c1c0d200ca20541040780304440c3d003031a078041c01d44440c0c2c440e8a22000103100c40c43d581103a10049d61307500e030708807126003041d5a1001c01c00340703026000c00030304680d2901d901600014185d82c080407568000d194232072010449100003034100e804c0904148c50a000c00210402007200038510380014000751400b5515007070038000440d80d01d50541c04001c14003600096403e1101c480081105084000c410142d41e80da200441d2418486c01d001c4003150240c40380200c0451070345807100c143d91003000c041c1c2d604940c420960300c42a001e072400040540c1c2c5240c0c10f1001c10804040c0740001d20824589400401c01e001141c90010100c82c0168001810881c04050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 950212356 1250 950211106 950211113
    0xe010519110a1b0c081f230a0b03010615030612050312070302070507030312052526010b031008010605030c042309060a0f270c030b09010b040513 64
    0x1034a08018091400062030128843ca403000b0782c494500c0642000002d640026000100060410020f03181001c91140d003405803c842c0c0c15100200f203054244c02034810500c0c0c1042c290040b0907408103041d0408034170180401d0102e42115440d03042110f1500b0080c0c81202140c0e01400b070400184056071802d241c0d50050780391140c41b4040c1c1a0358000301682480440e5100d4440d40554007010740202c00e4a101e06d550381b60150032940d80c821403103c42c60a24001420304592110342e03008541048140095000a1580460390701128049110400c50079a401980d0214651681c5001e0f091a06015503681015900f020201d81c19134003201460381880420b1040ba01c01007210108440152004101c0b00090300741b80c5992000782d002c440000100c0010030060b0800090110f018102849080004986040300c60095664a00c44c10019000d414509030380b080d940710411400c1c1d4000c0f000c03a11500d44a5071b0b298010041514a5440d0f070b034560307900d1001868203100d0300780c201107445401c00704034440c1e58 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 950213606 1250 950212356 950212391
    0xf050f01050a052101090c0203120f100810050403020f060705040605070c170a060b0f030303010329041109130f150b040f02070c0501260c0d0e010519 66
    0x106040090210b600600d0a00441c192140c01c21206030080c00c1c4d1082c01c140c0c81c0500c400740f042189503810b140c18101000d0020088860580a2604064407a035038011002c4441c0e0000e000c4c0d540c481d6074884001481c8009001d62080405000340c0801e16042c5424000d1404540348050b05564200000740520741c1d82120443c0c1c100e030346a0070310070344034000d50414031b51216890740151502402050f90100f04c6401040e40481c00b0310654042100c4144c0b60b00b480700700c9000085450309544200300500109850100f00d18090f0941c1145603081d0b0503100d071507056008243c0e03044441e07407850076905000c0d24111415036408404000c5421159002c1c2d1501e2300c11154201d0301500c0703800d01a20f050340e040b5440d08040190785004e041880300d050302c0c0710f6540080d4061101a160940c0c00e400c00f1500d584038001d011006090b00364601a00c581d01c00c18007483c0400a13105a0007480c0402407409501c00e5070242c1b0644c550070308000201454000c040c00320308100600304502c92841c19101440658155 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 950214856 1250 950213606 950213629
    0x80412030507200c0d06091506080a0b04060605150403050111030c0d0c020c0901180b040203070f0503090a020306071d0405071409060d14250e09040f0611030603070f05 74
    0x1180c0c440f440b50704141c909003450020b2a2207a00030103803001d40000c1c08000d13000854218811021040181040000d010840b100e6001d00340054001034202c80102e030f00c152a00741c0050084138002082a680c900103a0520031091100c4031401d00410200107208081c4101070045c1400c90f4000c0c5035142c14142894240714400b2503100d000c1e0b030b950780c1c03540c0181300304504000c06030003920340801d45d40c48400c84025403001c81807141e0f81604121810841c0d0030035000b0343e8051203081d203a0029407008840c00b5507980e00010010a4135224000c3d0f02c001507030302040031600480064894403980304c411114880c0401401565a004508020600040c19030126022400305921040180c640b80c611001603e10f00c42e080c00c0f0b4041d030381494103075a0f10303404c24a60140144186145034407518803044810520085003800c040100e00d0000b6000302e2810506411030344644112030014142c0c1ca0381d0b80710401c4a51100001411800200801045040800082c1c01030310f001307d03408004905d402d0000341c050140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 950216106 1250 950214856 950214887
    0x1202030f0f18060f09010f060b040816120f150906091406040f0204052211040e070f051302040e0f060901212616060c14190e10080412030507 62
    0x1040000391401c5c1080d031003034109050603541401125139078005050541c1003030140c000316001d022920340c5840c491181a20403603451401e00880c10005071900001e82a85507025200c41540c60b1413802001211300c900100140f142e20300103011100ca050104644081c8003c1c00e246601038424000401d0741c1100540c012130741250081079036510000a42030348205440030206800c0c00011503010001482c6a15205100650301000515184000c40b680d44003144240542c008908000340309508081102e6040e1030701554000d40b8141c0e0ba44203641580e4800c5510700e1400c40240c061000914000000364010701403240c13502c01d40c0c0c0c80c0800e50350701c0d9008098000c0503a000305000d1110811034010b0700c00e101c052001c1e50ba031a801d03000d100743e138000c040d0041213a1040ca881603100429006100001d550340c2c2140c2040e0810003d00410461030365030f00188028044610304e128070310341d034000d100010040265030302503550a0034035100720f44190780c3c1c05540600d814a400c00417410752140110000300030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 950217356 1250 950216106 950216131
    0x21b030f2a06120a0c020c22050c0f03070c0303060b071b0828111c0b0a06030c050405041a0a0b0103051503060f07051c270c06050a1202030f0f1806 65
    0x440c170000740d05e80394401d0222034020040c03100c2075901c40d16560300c1300403080b03443c601805603a03200c1d41030fa811807141c2604680d0f200024800705051070b11540e0b24100103442414002240c0c0e4950103000500d42010008031003100002241901e00c41d2505510002442424010140d00c0c0484140391580300b2a0010f00001c007404000b40780034420840200c251101001e0a4503000c2400410715003140c629000050740c0001050002c1482000c4078840d48040b84d401507584100e041c102010400503020140c420348000e100404418032451202ea86140103440411000907441034403c009000c2d02d40062000740300d07140d02442d05040d0385002c1360044c0d009014680400190396444400d8480340590120407505200b80d140740ea000c601030340e021148117104250700711080300ca01c06194107446032040c00140888103055041086500a4000c1d0624080b903040880311380c403441c800b103412a00708554660528070b040003408001010660081d4100c0846040c0e09244803500c0c04040d6101c0f009080c00c1503218 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 950218606 1250 950217356 950217371
    0x1c030806010c08190c120c02090117011d0106090c020615210a0515220b07030e16090518030313110301020d06060e01030903021b030f2a06120a 63
    0x611a0212600d001112414134441007a02d840140038040d00e2070101c440004041d00140594084c80024014550040c05211182c0c2400300301c4540174202c01c00d24005648441d0040e880108070314101624402c88400007808900d814008030070741c5c80318103182c02550046801d10100960881c014000408240c420041c0303c00104510302c44007c0b00381c3d1a00d4140a0380302d003101004400300340791020b414a44404c1c80305171154805a030f06410102014140c0034025203500000400f20f96109911401da414009062011400050b00300400c0c0038040e81d0750f2403000c1060108201ca4800c040c2c00600c1c8100000c03150310485803560392844080d2a9801d20750b500b41c450030030000d44420a01c0885d1000d0004c4d500c45003620919406400b0500442000c40c4c01c0c02d03180d00403548a03100d140d511b40d406034010560880721076082c0c40565000346515815002d4202c034503110030010455a01c1c901607890004a02c0c008124584801c0b0844c0c101d007500c1031400300070404d4096103104e451034000e100c0c20310028850 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 950219856 1250 950218606 950218613
    0x100c05031512070b07020f040c0806091008030c0102030a0c08100b0c1e0f0d0f051e04090207031206121716021210180210111510051c030806010c 64
    0x100b040503101d0524440c0603004510320341403a01030403409100750390460180600408010070381c0d40040e128030000c1c0c00140006c04603c0c0c00503e058011200103042c04410340c4a03403006080d03038084e241c00e0000e40e4000062150b1905140b041d035090301900d103411491030512441d8006103003100d1007808403450f03010a04084211091026440904049a0b41d441c000c6650424584842041c58240c805005501580e140c550088405000300c1c4600c0e500e031032a015002400d007801d101014900401c2e89010312004c2550003036480140350f01402512003e0840050300100f03c00e0340c11b16004445540d12403001a0005080c40c249601c520000c0040b42d5140c0a83d40725048904032884000ba500202030303000801008004201c4840342c4500241c140090710003c13a45212514200f08001d4000c80b001884228492080440c0b0f04680300160550754010705000310380f6600c0d1000d503521308200318040c0d820025071400c0103c00c404a060269460b08004250701c02606503100180300c02d061240da5009482003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 950221106 1250 950219856 950219869
    0xc050705030105181b01140a03110708040806161403060402130308030910090c0504180b042001030504170d150f0e011d0403030b0409050105090f100c050315 69
    0x30303200c068000c1040349850407001c10300e40f0101d134640c0c1907405804100c0103540003000d00358014a0060312400000c5200392400d038060380c828844801010703504c1c010002c1b074950b00e50041041c44d01500d0210b0701c55003811a010b090040181c8000400508070720501c00b22500b102d030002e03940010008403030300c030b07a2201c0200d030181c41036803540c00c0a022031074004002c10040c800a035001c3c00c0b6030320484150f0040400d504c030032150620f10140a40c008010200301c241303455003044158070141c070015401c55940340d40c0d0346030100c001d0710222000c208440840c20504448042030040400911f410b001c03a0515856104440d034595116807041000003c160b010780c001601b144234555a007103900040c40399260006025a18a40200516a65901c00000d000600100c840e442a2950000340241e40c51315a006e40090246a4001d60000c1c4c96403040d602241d828800e1501c104030070750152081d5140411110300300101802c200301490302d0a03081905c0765074891b09032580211600c40c01c208408010000514 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 950222356 1250 950221106 950221109
    0x31503050a060c1e021c09180e0c060f070b06012f0c1207140409141005060108100b0903010908042301050a050d1d030307270f060c0507 60
    0x10301d1080702a00010021035511240c0f40203030075a02d01c2d01120b0803800d1800c0c243c002c03140300b00059004807109803040600b411102041036282c02c1146c0da140c2e682d1041c22010028100705221540d032902c0d054004242486522506d80086440e03d00d002c00c1c00018603014000c800014019400300000a001c0741d0282c03442c3d40d0a44a026a03049881505007000c511742c031242032140c1400c0c041c1c00c45c1d55a4a0402741031208000724400040d01501d410160204017601c060024a544552520f20080100c0e031280024076100701c010f405000382c44451f9071050191030002d441c05041100f44400c00584407403114181d426201501111580c0d040201d0000c0c0c0903009222001e00740030000a00080c0c11449040411005035170748008804503250303000159258020942060046a41040400c0c5142d10560081488103c00a0440541d4044802d51440d5030011070702100406d081c91000ca462100c045043c05029014042821985051130700640002d18036114000034009480e8803501000350a120100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 950223606 1250 950222356 950222363
    0x91c110c103912030914030a090f05090103080a03020f131d0c1804020f04090501080d0206011a1612020115080703080706020f0c1c1d0a060f020f0601030807061103011203031503 78
    0x1101c40145a41c12a07c1e03902820400021901e40b900015001090700d461004480000301f9803140b5a10f59124401c2c190311544224040607402c00ca0120340b030300c44001400188501e102d03a0002d850408070402d1495855000c1c101c4441c4c2c40a003045600390040080741c680b20500400403a1400000c8003080190040342c4038202d00355000300c0c001c070740b0100950241d4121083c82003110a9003250540c166100c440a0007160913000392280c00003400c04100004080c00d140c22032510203489015250380c90001d100d100102c0040c0d45614144022800761462403020340000030103420454596a207241e40c81c4200c0c0c0008225580200d01148903040310000d60354881400d400342c1e0340034225064291146190070509030003040c0d00705c03205c8040c0142811000303074503180a0814400d090400034103851741e840f031011010840c45080e00b0707011291003d2004a000303605ca59100b81d2520b070186441130556221003990540c009050004100c0c14201d052030700f8429816090001d080300b01c0e4078a9806001c10f580018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 950224856 1250 950223606 950223623
    0x270112060308090a1221050c1c030501060f0e09151210050a0b0906090a060f0801090210110a0f020a090504030f08091c110c1039120309 60
    0x2e10140600070210380c441256003090481e01c465a114a2600880b0050001e201c00362401d06407a200c400505200212410000c1c14181c68201d09494000c204601e00d45201c03040340c003240f2080d051701466014040e40d0030600b403e26840d200060001d00b80b0400d107481400341002042407003241808101141030041e058260002c4010b516a5413640780d9000c0030784003490710f80060140d01d802e124041c2d05800c01401080140ca400e0200415400c001c1c10070104550361340303400920710368035041510080c01101c00228200b5030034010424040c0c4000e103100103226250b0901440300b100070904002e096032000c0390300d500d5100ea0000c5a6401d035141c11000c1e4003458101400141a04440040854069562001c0c03884c0d985540d1283c595102840281e03112040881c80c06040d80140300d0741002030080c804403201c06c002500001d842405c120054400300303400c0d075070122105034462511a200e100340c0410264403038032001100c00c405240e0380064100ba00790500d149209110f500580b04070380d040041c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 950226106 1250 950224856 950224859
    0x120403030c110f0d1b050d1701060c080714011d07050f030105040b130309030516090e0a02031902041b090806090102030906180f010f0e0c0a0b07060c17042627011206 73
    0x140c44a01c5252108c40e04404901c00054071390f204a000803800c0380e0000409084c464560354040c0100005080c1407241d54982c403030703038241c6601803a00144e000c100c01c00404042d85040140420780d41da41c5c481900a904000c20840451160741e1416080000450070300302c0080103003400c442101c69504020903e02a00d00c00700040d400c040610700540e5080c50041050300ca101c1051070b9508403d0b40300070b405402030480604001c070010440d10f8424000381c030100d8a0103903690302c2000703030039034240080110351121006d200c00d0000b000003e038000e0350003000b1869820403018041d0355100c02022400c22428582c182200b010041c440d420101120000a00550321440010400342c2150781b026044da20030140d030411240380c940d441c40c04551048110388d28003c11600d41d400038100768001c88051000b075074070340c04900101001080c4501d015100403041c0600c41100400d14031a820790300600444203110300b03010300c0d03054110f40e00d08400050f0881d0400e102c000043e40c1c0100340c802c0440034540b92490 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 950227356 1250 950226106 950226133
    0xd0b1b0c0115051806040b130204030f03020c0315061306180e10180803061503071e0c3c0503070b0105010801030308010e0705120403030c110f0d1b05 66
    0x2102d62141c84290b02400300f030701c40d41484008031240000552809055000c25840c0c207290380141401f00002d4007800b6404502c909402c00d0740d001c0d0b4800c031900c082004000040c50340c1800f420103081d800b10040c150201542210409200010380340b60b1084205400b0608448113952019008100880031408894104003600c0000c00d00200d0b0b03085079000380540d5107091b907903034824140005403004c0101c080030215100c2d80d0150700010004c98205001403400c25242c00100301551143d082541c40b00054906465400c800c8103051030050184218070400400041c0307681000c00201d864518095000c8840701d0070300402c443c84d18004042c0020340701510341405070220041c82e40307500600c1d240000c0d999030001110076500074840a000100d81c0c100500076000e0064050703401011610380b060600c120f903d44100400c0040c1c500320080f994900015050f44d07000b4040d03401096034100038000d815880001142ca44641c09001020060888200c0f08000e401e041d400780306503000400c0ba2070b85e41600b00f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 950228606 1250 950227356 950227361
    0x20102120f06010e1210091401050c0d0612020a0302040902010201140106050405120c031207050f0303072a0213090314040306051e0106020c010302070f020d0c090f0203060d0b1b0c01 80
    0x203461500007250752200d040340341402186042040800c60041215160540c180702c020164000c0807540f892800400340380010013400ae1034090720391142607540c1c42c504141c5410840316580d00c4882e01043c000c6105001d41c0c3c55034107901c122a01520041600089840102e0041c00e0410b810721684062500202e00c060f07011b00600f0a85000350303401c11201104600041c0c1c1c0f05c401294840d4580e03c12807030b03120031204000140c00d4940c0f08804840c2c004207000310321819900300316004000190071130500290b80c04000d6501102400740340030004084621303008100a00201c845007900c00d0b480c0d441e09010940b1a0603000942c48602d03540e60749480c0c41e80360020191600303990260b000001034441491410314400c0c80c40c100d90203038004201d5180c1203001034004c1c1d084180151144550031003182d0140c0c80302040300e00307000d1191081c18501810541c400040306c4204030355001c0680b046c4108a100c0d10ac041c6001c0c5c0d407580103106e11041c0c1c0e44498500b4140312a5111040420402091078040101c054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 950229856 1250 950228606 950228611
    0x7151211091305220305071202030d0b0603150405060a0e0103110a1509120c0b130e09030f031b0c15010602070605070203061501121d06100f0306020a020102120f 71
    0x4503a000c09010b440c00303200c4180d43c03080d10400030513220348980c408030341e01502041825512904051381001c201d0380300c013940000980104009a040010480102c003030900c22000c01c402c0031130307405046003048852800044071a002150240e41c0c2d40002c1407590f0b59071520303800180045030054010750784a1a045694000400c001c0d4003a2000c890007090102c007c49040140c440566111401189018845c1e406401a4035055820500f00c850200e81520b210380200760241007511111180385c50000c0d01305d44404001c041181c2a0800e101030084480d0850440f81c029041600041c8203e02d00e80b064411442044001c0d1510310403aa100041090380910150480342c86801f60740000d984c5070000d9486200765140298075410840000700600040e00c00c500d8081c20600d8050b101d05038840c010000c0750001d81e030100c16a2034044030f81d19901401c00c8050b40c060f1031b01c01072601891624011007528100d5010062038682c0129100309554402d5040c0c03201146895880003260804054007076440b4001e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 950231106 1250 950229856 950229859
    0xc02210109060b120a1b0e01031b0b131a0d061d060d0b04020103050a140a270c031502090414090f0111031513050c130906080715121109 60
    0xa081e0b2480f2a45000404008003040200142a071207505a4800c2c844c660310818106040540704408521400d80c9416603000c0e5228200780c4501c00346410801c81425015407050240039020056075002c9055001c0440803101d9030889241c448440303802d45011402104401d00d610ba00c1c141c00010107020150340c0d210310b014047d000c069940c0b900404d020211614903c050b0404010030b02042c0194030a030301055000400c0c06002a100000120f01e0003070310300030b55040000c40e4482c08000c0558021445601c1482c03c031080800301d07400903698422a54419210280c00242105052040068141c0440f201e00340020700800070720354264403c0884d808161145040da00c24144411801c500500c80c1c940d500104480340c2d03055a80e1085100e03103810a12140301d070400c500100070700c2d1a4015004850180e10008946501c0e0020302c07650502400555001b608541d04084040040280104140098680c02d10f60000b01c850b00d40341c1901c1d581c28892803100c40b64507040072040c01903100d5000e0282c0620 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 950232356 1250 950231106 950231111
    0xe041505220c0e15160b060301151707082805030c03040f0e0601031a0f13050405150906130b0c09030a0c1e05090112050c1c030801060914010c0221010906 68
    0x284d242c4414500810f060984c000c024031400350081410141c18607030000b802400421802010840400c6000e00d45e402a005502081780440c2d03061030030303c03884000d49003080041820010003030120007240e81d1141c0204007030301c050383c550092040500403550380c4200c03002101d0381d80303580d462220440300240c8160b802c140003101c04910340c1c0d0300c207000d2a0440000485810f54800d000c004100b100c41c01910322940c009118004103051a000d401024825030155000c0c3ca04600d000700c1b04c14500c0e1009003541c00c0d9410103010019a608180d829241d440c7d00581c19007a00c0c2d030341e50507901c4181700701002180e0512a40020004011045001009482031220307840720351303c07045550942041302d502070b0641c0030340110300500c401500d04420891060044044a900c0100300c0080364170300395418104000e540151109005040d04600101d004159a2a0a960031413800b0301c8440340a4018065504000340340c0200810741d9550100d080c1d1410408811201e80c405000480d40204403c0408546860 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 950233606 1250 950232356 950232379
    0xd020d1a010e0609062e051c0605030d05030907031a07120c0c0809040605121b09040b07030b0a0e0921070305090d14030d0207030e041505220c0e 64
    0x48050200ca008000c0a8419001341c3c40340010400042034401400c2d91003040f410b80e0b00503c1c503030008440da903000c00b511203641c3c03001c0d003085200031180480d182d10784045c18002c0800884d10300150b60051500d952806d240c03249c540c01c07680c6090241c903510141c904100d103040d0061400d100c07001280a030030562680c1d01c1c07072103040c00300c00709640c0b4a401900c08162043d02041c042003400c40100005180103000140c19511000044c491503070313900e60004646d01c04565001481200d543c070310807803881201c07000b01900d0a030b544d1090055008000d142016200c14022026458440741c100c0030b0b02d101481e450b106e1420b004039aa480d1b80300040184240a40e00012110520410844122a82503911a0700d0510054280401d500c00712004aa030780d0f8041e004003100a1007400500f0100e0301003600543e81c2d050a08009280c0d0030380d81d64481c8100d140c00c202c417a000803401650310071151b042d61204101400c80c3e00d030405c11410140d51712510750a00202d5644107038041204030040c0b50803281c0301c40d2030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 950234856 1250 950233606 950233619
    0x50411030604150602120c150a0912020102040b03010918060906020c0c0a05330403050105040c061b030f02010902090405061e0103150504140115051f050f090d020d1a01 74
    0x50752580315850142c0c100e020b50b400b046600710020207c10140340100c40b440307410341c0d2082c0c041d1501191854001580e80e2403260801c903031071020150001c058802903052a0901d10840a14401807003071040d01c964032240d04218182e0045022052030304144200710001060030058040c5d07100c010381620300d02070100008958540385400c0c46c15170f0005070041e816045601295010005620000640740d40d561801d807180b01c80c4500184007851080b400402e05003018030f4900070f22441078000c6428004092240c160001c3c006e19440e42c66501840c01a044e620a000300f40d00414007148003a40140c10281004207000000441a0103040ca1100c40010491407140b80d004041c1d0a010060800031b82500141868802e60411078025005500a12400c0c1000c6101c500710340c14500c0d690304040ca0440100a5840d20603850008605550302c2d01d1a12032081c1d03c0200503205144100248100205608445454140c1c417400c244d41d0180c1540d030300349924100040c14100701806041100c0e13120001082a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 950236106 1250 950234856 950234891
    0x2c130c0504020705060c0904060305030316020c12030d0902040b06070b1803090a0608041106070605070201060503030414090a060b040b040e15090c070f060c05041a040b04120606050411030604 84
    0x80d58005002d401c1c10345070804c2c5003800740e004000f1f19500c175031034041c0400800c005000a500892030541c0180d140286d105010b030401c4044001c1c035104801c040074079294440044111507010410600008500130346d4130000b1300808900f00800d0f0040004640c0c541084030103800b55010700710710414a451000080640c6a9a21403044010742144240c20100486c501480e107554206205101c61241015110045811030300804400d9030384a0301ca6040c0300c1441d4080c030440d8003400e07007035010f180380c01c1c14100c80d5000800003081190080f0b03500d01c00146244400d601040203070030400740596640d56078081581075608980240c04100121201148a0456a508910350f040016251072921f40d16801000c016410081d8103036552018000f0240c00070344207228080200c1825141e540c6c9a80c101030b204071003451001d84418403c1000c02080c402d1075070301307400d0320200d0304015410341e001c140c503180200282000d90b00441e0000d0078040012941141040510b00c0344509403000c009000084455061 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 950237356 1250 950236106 950236117
    0x50409180807121b121106042001140a03061a1905071b0e0910060b25050a08090108090c01120e010b03071d0702030406092c130c050402 60
    0x1a00040140000143c500501c00300c02c1d03072550920141000c55200844d40a110109007181e8884881c1d170004182500320054541d81ea40d034800404540c036040d680d00c1010711004208039400c0c0200f40702030b51983c0c440e40010324003042c2e4814060311072003050340240c054000b60040f040351808404405404142c560180c0d8050300d80740c001c0c4056030f55500740075500c1e0341c09258207035046030455800c49190b46101d0310200c000c0000b003001c9511490400d88981c02d218685001081850034044200a075002030400d44840e44850322046020a010746041c04420030200c800a00d6401400c8a40050104030700c06440800000c3e260404541d450b103030825141c81d00c490816011507130300e00048401501c103900911089261070000a001004900041e14100c6240e208180500b40c5040485c5101c0f900c2c1401c40d040506c80c002103091908001c40580142c80d24090b58513540c07000368036030002d510f58188540089100350f00d0100349040c10030300c0005207420808141c8048205c0000003070142880d101f00d41 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 950238606 1250 950237356 950237363
    0x5101a1504030303020a0c02040914010501060f0806040506060705060a0b0310180303090c0506070803091603021e04020708030f16080903160206210a0506040501030308041b1505040918 81
    0xe141c1411580d05400075089a840001005280145400140c495200b40446240103554441a00c2ca0700d1007010b00f5250160400e41c10050a402401da00300d1b0440c2d080e03508000b084178041601c0c0c1c0e9420200e00c141c019101c0141c81d51040c0301c00e00091401c240d000071075049090341554503103605000942e040c7c0d00310141c01242c40351520a0880401d00c41e60000222610943c80b501405130703107400042035034000345019141c046000060210440c82080514007082030120000f080138a5500001d02003035072007000342c040f0541e000503140b16540d103504980465900030358460b12410100c56080740c902c0c1c100c444120303070344009800403840d90280000c81d03c6014a03000452a1490740071a6003035003c071100049821500034480c3d480803401d144004c0440c0901c0303e11103034880c60109120403e1799000b8000da4002c0303280400500100b90301c04540b5502c20307041402d207140403514141b034407441013080d88100c41e54501c0512601034550311000410480d00d80c11000d0004010207040000c40400125004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 950239856 1250 950238606 950238649
    0x17060906010518030f0f1b090f0106202d011e020703090510031e0e1902032103061516020f0102030d051e0f04020f041805101a 56
    0x4854203209070082c451004000e003e69108800b0f00040e1703858030304d12480504c2950052422010054504030391000035a13000c640c1c142050501d4001003804c002d041c012902004510314112030007580529601c0700d0520f0303a40481e42c44c40c5600c4416844044412405504402c06902a40690005016031841e084035042580d04200c40708003203200035030041100300d0912011800005640c0c0e00e4080004903001d980c0c40218060801040c3d00714074034802c84508910a1030424509c851640004869090400107502c1903401000c0703000003032030308081c0c3d4081401c0100480c044804406110302070741c0100c0c02a40c0341a0139005074080ca1400c2d00909034030314080310428001c10058903207107010b03018001c01801500c5c500244a0005010f403807003100d2500c0c441c0d10403145100c100c00208000390740400100c00820b01400c042d40060303401c81030300362928403ca031101e00d0200081a0030400f0502c0382c1d0310400700d4000f49210404c01015000400b8100101e51030961941d03460700b007261442c200556403034580d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 950241106 1250 950239856 950239867
    0x801050417091018080f030901020d1701030b0415021801080a0b01020a0f020a0f090501081902010813060608010e10050a0506130c1209050318060a050403080c0a0b07170609060105 79
    0xc03150b0450f40c071a105a1a01c1803000040c585d48188039245004021300051035684c1528000681b501c00050714020801504a0f0410b4407007a881c00e0b2030341942c0d48850801c1c0c89884c0e5041c2007000c4e1000c00031030117000f44005942d00d05d07492000c0d402200c140080e00c440202d07981d0714100c2d8080302d650010701405070b046107000d1000280b424030610b41042c80280b120216585598101041103055001031440326034500050040d40c404000780c0200701d4144107103030040c0b5020390000300051000303043c03108440764007004501044407075000f00d40504000b6000b000000e00e4010560381d1003180e422690001442c21010998180c080c1c002e032485010080d00440002112a1100740140301000350f520800a01e050281078070642406a6504117005030010b40e103841000c3c810510340c03090061a0340c03003111f04204090b03070140c010741603500300c03500240c0c095103500d41c07401290308200100300b00034035600d04001080320150b0040c0580c105181e10075103000055560000707200050005488460208105101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 950242356 1250 950241106 950241139
    0xf1116020112020d020a0206040c150912032010060b03100b07030207120c0302011715041a0414090607090e15012616020601260313080105041709 64
    0x2500c11078030b004101c005140400d200420b50407a00711700a440300581001080c00144540d80740407202505917110b2904224203002c4001c0d1031803070310b0310512032104111aa02c0b41854001c0c210300d0280e00850440094244807400059121800e071412103184c6807500c540454800c8440d4107172807041c000c9211100f07038603080c80007020464101c0c1104404510501201148401c100c1d41d00c20350f0944a0462003c076a0300b50b200152568401d02003090610400400700703c495000e016540d49901c509031000121002c100d121790081444240026420504100003100f601902094151240d2614019101592640c0030308807900e41e6684541c07200c244032807000c04c0b61802c411108000341d40c014108800c43c803100794460041c6401080c5040303402c022031010403880600366000d25180d010039102a1003150304090284216106403888481840040540c0d4420003c0c20400c42d0782d41e210303204000742613903074038031032140640b4042300e049911128001c940b03110309282109507586048001c0211100d00080075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 950243606 1250 950242356 950242367
    0x606020c0f0616151d01020315090603010f11030106030b1206061507020409050c091b030c030a110315130209010c1401020f070f02040c110709050901020912010f11160201 75
    0x14240c0640f140300c001d0503400039403041c04580b05100d50f01008220495003845100c010910b0100b080400e900400c1001643e117680708a00d00ea02c9021649141e144d00c0e10750100f40180500940031300c0081c601101314070300c1c0041c1c0f0050340c104d130b07126542800381400903018804180808901c040e15580003d02007451844d040d903440403c40b184041041c10003c181e000a030a0380c148000956880d00810008241c0b4100400440d500940001d140d03094218400c14580683c8402440b9941c440008404100c950105411120860f44001c0a06440b4140480f42d050105861206c50344207031004c80354440ba610315030094400d03c05058699103401e86031a00d0f0032203090320310600a00b2a55081014103400c00c1c01300c0c05480301c18040c8036200341584c018414041102e208200120500040d0030780340e006440e000901c00c050752400103000c6096211102000c6c068001c00c0001503102050050b4544030301c0f01548620031200b0085000d003c81c560081e000b5210b480390741c3c000d0000d00c441100b00005940142e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 950244856 1250 950243606 950243617
    0x40b01091e0b1504032f03030906160b1603150501081503072d080304270b0a030803071701180e07091802010210020c03030a05191e0606020c0f06 64
    0x1514910303200d120090040a0b03680076810444403084901d44a8101850420705008440038920306d108418038540006941d070b01820000b28420b0303800058020058010f6902c03a900d150f485080c0c9105030a0209551081d0a4513003100030000f03180010443c40151100800c60480c0d070103071514041c50b255994001071000988035440d406105040c03001403010031050102e99844070552500100291486401d000b0b010b855011070001d40c001e01061040500600c005c10501861100d1a0341d1240f45c0284200549107404215034840c21042d80001030103600b100452080c200e5075075000c046413982c04032a10303000d070038082d080080c81c1c8040740d40c0212001c1e90244004880820865a400303595100213020b49900d50001908254015031403411940c041207a5280c3c48403140c825400c0418440c0155941d000050460f42c0f001c0c1c880c40400e20342e2440200344080708840250a111500c0440c11060580c41c3d2500080380862600600255071031010801a08214004180105820550040040305e801c030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 950246106 1250 950244856 950244859
    0x150301140609030f100c030b090420030f030a020a03030b03010c1403090313090b0118061d0105120f062b17090604060903030201180b041721040b01091e0b 68
    0x180840f41c44c86040401011000c8800b5460118628240e00c2008081d0743c3c0c0301089a0044034418184000642500091020000c00070400d84c07001c124000000c5c5020381100c0c60b450580000100c003480030b82e01041b1041180c0c06078605000300b400b41001d01d42215a04042d130000070741c5c1912021442c000010040d034100580d0000c81c2c0c100030f500b080c0c418480c0040ea12040c40656900b0007818156044040f404a406001140b9181107203050b40191007240010380d168408a01140701e00c0951f03000340192500207000610700c086902e080070000307a03910720a45100d840744950b00444100284440d0442880742c001c1c104039011090199501288000840040030112000303000188894407400d014000400581da2545d116504d90300300079086441c0003a42c41501e0607a44d0119000c52111030740c1e02d4020740e20581e05806411107a000c1e080ca070040710300d609601696190101118881c0101e56401a0701074046494583d81e40c407007020031218480c4110400c0c0f441e104807150810810382c0818a0040e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 950247356 1250 950246106 950246113
    0x3090a1202090f04050f01150312030c02030d0209040204031a0411041112091903080f0c13053f3a2706081602030d180602030a060515030114060903 65
    0x4032040322130a403041c8012320b013400300c1d1507241002407015500000c05018204d007001c00c541e080d0f95000070b44900c159801c4d48070207a0006404001910b841d4110340003142c202800303440821040300409180c481c00e980c2074800c4a43c038548800320f40381c54441d9141a040901a561a01c1d080c0051100051001883c405e000e00030174124400501840c030081d811144070395590042407030181140d140240000d05040740d066024855106015100300d11071007500e0080301c00c440b282030804280a8454092001c044924030083d424182c04540c07098140b030f15900c0710003516001c2d42e01081d00c04180c140036000c0d100c2070241c42c850501d02c8105d0040280f4503281e43c40d2001d40320350300415141285001341e04103500344034140010048030340e01260b0260403004c2d859060703600e01d00300b0070000e50300c2c06134100908215940d485004003080c0940f4501d84031a0740203005640302e1030704101a2004080c0c0c0e05c40d83d402521641d07851f01001101d442240e040c0c80703218001c580030009d09070500c0410b400c100705858040c071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 950248606 1250 950247356 950247373
    0x15031a270108030a2007060518040c111b0a0e06540403120b03120d060b031e06010e040203090106060f031413030512010803090a1202090f0405 63
    0xa030000d6625010b8800d140040d0f55591184000805005545088808041660302155800c00b00890f24800711000c5146c02501e8004406030b254121030240e10940d030061800205d0090300b60010310b03010300e11850409580107200c001c111261242c01440146078807200c0164240700704141c0300c0800e03401c804081d1418203050100100c0250b102000820840950a028803409090b04000340c15540500c080011102e28030392210448200c0602900080510004807008107401c450340e800701d208020005c044520b54070321852210300302c0d400b00d080d01c1841c40c00d142c2d010441c80488001c60340513117510780d2036082d40d080c069000d8035440c030044c0040d41040084049950a69600d0010303501486611000007038051802e0005080e4909a1a10800303050801740c9144180b003050303410301d91002100c451b240d0306800c50710f4101d1b01e610a42d411000511420400071404d6000040500003c403805d443c83c040ca203071074580f00541d1009524000303620206040028096480041300c00303400504c00d90442e032424 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 950249856 1250 950248606 950248669
    0x2010e0706051e0906073003020301080c0303040f0303030504050118060c030605030c01050a0c170f040f12171315110c0f0330040f15031a 61
    0x200325031004000881c00714a14040c0300c1040c144500c100e069180e1180b600d280c07000802c4290003061006021180c0700c2c1c103c0f515035800c60052000f036003014440e5000c3c42d1030400024000350070a018090481c0f0440007108043d0800004030790554006110200c042c500d50365086000e044000c0049966540b2480700c050140803202da840900d0348154004201d1602c2d01800504413841a40002e01c40c0d40285c0e844841c598000e000c0350007141140c07401c0803195416090803005101070504d5110706504c00180790340d04c40d84034030140064613001c545000009a440341d14628086001d5806400306c1ca13020048858015054002c080007941864105800c03691001502841040081504042a00d8031895143e0400030709c00030544103c01c90f08038920000f0342c80420358460006207106042c0000340c00c440d20080050390007425039020403440956035500e95800303818181a510600c015411f080900b40122030007402030395050890a140200b1011f400c4081100c1421103407402c503244640480d5802d2103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 950251106 1250 950249856 950249863
    0x1303091208040303030b01080c09120a02060d0204210314090316080706020d090806071407060216030f051c0f02040f09200a0f051b060907030303050a0e190302010e 72
    0x3050091603529141c51071030401a007681c9200c0100d50412010904100b980c0303585005442002000b42c904420180c8c40f0a00c0c245800c8184102a51107c40440d9501c0d18002d20b130003c5c000d458a000442c020142000b18507406041403213070040225440d078083d050314030b6040c1d0140102102c018100c0c5d0320079100000700050851941c0103403030036421030788051000c16010443c0d0a08500795141c0004190704d80620079844690241a0900700000c8040d41010710054034180c1c0e10031600040c00715600c844c0301c6025010840171101c105d0200382c5000641100034010340541d0742014020440c51007411488102c0002015001c80e043c281035030a000106003d0003190b00080500031541c4005051a02041142c0840320f0300620900c400b0410440d107401030ba44404404140200707810819110040030803080200015182d03050203130301c10301c803c10482040000f030b0320040303a01030f4034208081d80b1071440d0b1400340d5038196000722556003c000a50034450640c240e0b4542503001c0d10000600b00c051444442c107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 950252356 1250 950251106 950251139
    0x10020d1e0e0105070203160b130c0e07020d0f05030609040c0807081005060f181b0a031e0506010905060c010617030705100b0a18090605010602031b01090b130309 71
    0x25003a5500a0031501c03000c24440c140d084070340e500045041c00301190341503802045148005251547c044041000030040d81103c0c22001d6004020500e16602c0b020f800300b4040301141c405005201c0e2002450000d4043d10104001f001030365101ca146a031280c7c107202511030051300488406510100c0024130b1a018002c0c503000d0180b8501620705009100321034001c4e070b00041c010502c98580380c0807080c40e5030344007458a11407041c0c42403050342c60b94400b0090390032810403801803070030000005902109964180d00500e4006000c8030300504006a5600100845a08444e0741740851248a0f040c8064034080c0081d14114901000205290361511440341c0068013034072100a686c0c2c030100d2070b042004401e04c00c5480410070804100001d50b04000020424021307441a100a05206c40303404280c80c000da000b1200258000310700b80160b5030750b800c00039941d41c89040070300190481744900c032009005c1030040080321500012403100a403201e80194102d10607020085050000781d40001402c9801d008603101e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 950253606 1250 950252356 950252411
    0x1203020a150e071d041203110a03020c10050603101a03010e0c09010b0705060622110a0e060708070605100305011a01110f3d05060f030f10020d 63
    0xb403100d40007024a10b4429aa0004182c1c1c004150b003459010741080f000035401600082c2c2c094441c07800000982c0200300d81c5a0b0042050400101c441c41032340c058004000389030440b0110f84441c03103507034040310803a042510500d41c16006880b0a15403482103401c8140147e150030b48190b0784d03401c030b0300020b4212509401c0d02c4840d600003848110083c94055a81c0d80105110000c5510b01001545d4050311008000e0030303140300300001c8103190701c00c0c00702040d9120356000e254010402d103845500400880d40060b11a0300020b044481d514059051140580c0c00c119407100107141005000e55401d0042c04c401000b94210315540e04000000c22000d0103503042e02134007072419082628103000010304000c0d4150628a070395010301040c5014440c002400302c1c000e042c02c440361007203407040b8a840d06810b5442c0c0000140c0d180c50074400c030140c032013603010307a00a1000301e54a4546500e81424103844030342d028071045076604608001d900e11200f540045c0048802000001160701a54a0359840c0034640d44d07221 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 950254856 1250 950253606 950253611
    0x3d051005030705031b150c0615090c090d080a030b0a0e04060b090108060411011e020322080601091806050f0910060b04090e03161a060a050105041203020a15 69
    0x80189050034000c42d03002e84010340c0030302030758003d40d206805110f405003074060141d0700e21003500c0c0001002009480c18441206c00b80c0b000340c00d002080d0180340300c945072407a01c10080340c1d001c202d00503000012680c0c03060018040003813020381d9456404041d007142c043d0100341911804125400d941c0e4580303c0020300080d0500703000c2400c0500307000046403054880c0303070301920f40803005010041c400500701d5800342e440401e410801007803000403500a013007106900308104000040300c04c0c190b0044058801c10b050b401c580090105950010603000d14103118110306a000070006015068030750300064071031080c1d04000c429914659603461308988040310710f280b84032503070310501c039071080300f0f0200c20721500500030140f01680c1400301010310b500c142e205c1d4400e0b06540ea0214240ca04040c01651401040b86055240401007414008040e018420b081140c483c024400038030240342c1444010140c83d01a59140d003014100800d40b50842e0700002c0607001d44c840c040c030010004000d4001101d0900c20490003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 950256106 1250 950254856 950254859
    0x13080f1614160f0512011d0703030e0301060303053403090e101a160209040506090721021512010f08150c1206010915020a030f023d0510 60
    0x50708151100406041e4082c54030000c1000991001c0340c58140c4d501202d402c034410005603d03440c0107007826030001c41c0070030080640100705500420303810100c078082c0d00c4280d030302034401c0b0406080b0b44607400010086001400340c51241d01022226034030148504d0080400848401c11032a0101c0064000700c00188148206102c50780f05400500e4204401702d481c440c59030304154154092150020000701c680b000403e01081040c3d02c00034000314640c02524824a5050500340181c450004688071a00c1e0f209000380018021401810000411403002504616820300d9081090101e52540e0078520b0708424030a660a03c010020b42038020007665103e200fa0b585000c0d003d41c00c00f06c20b0341e41034401c10f402808101000d5525000c0320303200c1015101c003110903584c0e03000513109032560703421000c05c82005e27000c0301d543c0903000242a99118040e846000244004030812070355076180641048240c600130011541046840d1040e07a118012000c90400e40c0f86003d01c01c030102c0301c01721035054a03034040000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 950257356 1250 950256106 950256143
    0x409060f06210c260a050f07020604080d140f0907061b1502120f0618070f0c142a0406051c02041b0309030e01020613080f16 55
    0x100300c03004140904211406207400303898124034440d10407200030481c1d103403548a1622031166010408040080c0c40d030104800c181100240c1d00c013812103404800d0740c030b00408100035881d0114020301c102050740c0104096940c564540259401480450380d0341e0381c8514a015030303418100080c81c0f01e0032070340039041864501002c0030ba01d018610341c00b00c000c2c001956408e60401d440000c1c110340c126009031003030380f01d59180d00368100244a001035001620302c4d442c00340a100001d0300c4030180a10b004441403000089211101e8100340d1095410300c000c0303504103e600d841180a0b010a0a05034041c403a1920340f241c031485c1d05c1c1d041900c0100c0500c00c3c02119070078903286440881d4000d00d07405040e07408121180c104404588079400309d0252042c20004080d01000310342c0d8a801c0003141404034030a4912408002e50058042c003241c0c0411404034000200c1403403654800241c0500c40c0100f8000c4005080058440107540e83c04590040f91002042000b64020b549003100426100e02c07414068111900380e01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 950258606 1250 950257356 950257379
    0x41404090f05011b050a0e0f0a030b0405030304111909050a060306180203011d0622020616060b0907050d0b18091509012a2309011202070203071a040308040906 70
    0x43c4d401406030500860b0107a80d8404041d01414009840e0400c0954045000030104d500e0360344018181d003040030812007004808805540642c1c0300b00c1030421104140400c020007844281c12030480041a0b000030060300e095500202e400c00680240091565241e45802c41510310060858080a04403840031003141001d2080750506600c00c05e8050800f03804003a801e4803200043d1003156100d00d040e007030f103507400e9251540400060b4002d000c1d40d60760fa440310809103100150301040c5c0d0386915106260b001800c010306000e202c1c0c0c01c2036940d50700e0201c0082c008401000000d21080d04010202d5280905120542c1003134007404054000b05250451800001e550690041920740300f80d0401141664045e07100300b2100d41e01241860303410240100a100325140b291895070510003100c0ad01c4d140018040e03d400070300d0000f00a9039016000f500c4e48000318280d11440c6402900356100600030046100b0401e10001c641203401c01351458195603840e0003555070840d810440032203994020800c840030702e10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 950259856 1250 950258606 950258651
    0x10c0e0f04150608040305130e0a290114070807060905070501170c030703110a0e010807030603020609040b01030b0d0302030408210307140c101509020f041404090f0501 74
    0xc40d410302c0480702001503050a0784052054106002990700418101801003003546d2215480341d6011001d10b81c1c2e6000c110a242040e10041704082c9808440c4501c18415400e880021016040002d2030324068401151019415007030340150417414003450300020826002450100c0c00f40001040500250500c103081108561049050240c0c1a421400c2c007581d00d04200c1e8403c440c1007020341c496444040c00d42c042d0a0009210140c1c174800030b003039444c0035002624080c5841c0c00383c3c2e4641a503540c9200540442d0060301005c0d50211052110704201c0c80c0c650450640392a040c0f40118140320408007107141d04000400480c0517804c041010300241c40708004800c40e8600c030001c161081d03000c1050a800c01d220140c40c3c0c4081292a01203040c814600a0403507441c0710101c401c0305c88a9902641400c002e290f4401c0c2c9009070000c01e0000113403d8028000d507031005075950401c510340303440e081103c0c4088070500310003604540c44024101c0801e6004105d07d4070340340900000f00740e079075070580c017800c030601754 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 950261106 1250 950259856 950259859
    0x50a0c11151206030f06010303030b0102031306020a170307020703080f070b13060c08060904060903030b150a09053c04050a0b03010e06041e03020307050a06020903070b0708030604020d0e010c0e0f 86
    0x74085c540c0b40210005280707044a4140c03d000840c5440303000101d046110359000100103842d07124001410645c00241c0d200703168004c003005100380007540080c4410f48402d89070303100142d10010090000c901d400c401071503006039650708545807101d99a1180b090210071540c800d6040001502d04083c001140140c10020f100340c46e02c584980ba007030000a000707080190020340a6070385c0d080703403000f01801307544040120030700104600000351201132080a41e5200c100c80c20005400e4140000b45800d214800758030b03e1071168080f443c4103000b03903200c08151381101d509841000504442507455203891103103a0083c2380d52a0f001c11800200350a040c02d5509600c207565241e80700d0020400421901807500c1d8034400d50012511034001c56042c102d01e1401841c00c040c21034014041600304204041c1c0c000d107001d2206505031244c07540c1c0c43c2d11a20043c0607540002d000d0050400c00140d444c039040e8010030f9210b0709050006501c01603050503c0c21075007510045030219000b070b002e130846442c4c00d0013500140c010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 950262356 1250 950261106 950261113
    0x1502070501050406081f08010b041410090c1e020a030306230919020c0601030201110607082802120a1a03071208071e1b06050a0c1115120603 62
    0x1800d8002800b80c45244540f01c20061103030041045480300c80b00486541c1c2d24414a854140d4881c0c0310140241044044c0c20f1040d46040c942d03400c50390071001c045102d1101001d8480c50f980c904001b05019112024110041011285203004070307111400305418a00300719030007001c09036281e240240031614181c120004107855000300210f4a0400442526254800d03134050001d03480b0a0b4909043c11410413640c542d4a0001c02c801861260002c0d0b558100e0f8000d03030740c8680c001841c02000c0d0f21000c1c10b43e901000201100005079107855888185200c0501c0c2c05107003182c580c2c105161a0890b004003440d01c01014040c0140054620741d070180428072100d400764103c02030038000c0040d980d0010340c070618039045428280c0300300744200c0780e084e01c0d10103030000d03028100c40540c600300880450f85690700312143d034000c4140031040c1a6003500e90003034403e9902d480c2c0c80c00c0f01c0b0641c251241c808031a001c468528403002d0701d10349a202c43c4c0340d83c0c4010b404401045d071100b1442c4d03890044440c006060b80d00960 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 950263606 1250 950262356 950262359
    0xf0d020a2c13031404080d080406050106231305090708270a03080c0d060e010303020706170403110f01060807140f0609101701060e100806010e210610150207 69
    0x40b003000202515410f041503141070072003554030341c41d90086038001000ca00890b1200d0213010f4100180d24031a51140c0d50401223a0380340e040c26600e5144008010400d402d070380382c20703450940c42140140b081510884000d4912070340d500001c0d02050049690000040f01f910602c5000c1a4103008100e094501c800032010441d4500030301c5a651b401ca040240130800c040e00810840044681200d044414100b020301410b9104c002e40800c102e001c2c4411070040c07241d08000a40c09126104010f1005030042c1c0c00300b003907142c0e914110b807212052201c01c1c409000d2030f408881c2c101803d21403200200700c40310203080010b1030024a215489130340144140aa1a20a1906140c0e60791108031071900008545103c2e2005d108101102c90083c130403a00c94545a00d04d0006c617807950060340880d803070f200446454001110000048400d503a0580343c8a020035106449a2800d00d040c0700c207400302d0840740d0342407102c1240e0717444640d160280c107880d050f1507803070305480c01d200360300d000804804000f0403070000f486c409 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 950264856 1250 950263606 950263621
    0x60103050408090d060e03030a020417120304060f020c0f0106090b0613090e190b1005240306060c07030b0709080f031c02300907140f0d020a2c 63
    0x184181c3c00c1992040400580c11400c010060f4022100041c1407004c880d12032400408240003980b25005441403002da03441034042001002501100940d1340702d2890342903890755039454025000003900240c1d4130307030280921201d03100104003154043c1e14490002c10764a00e002040c0040302c1b050040540503450412421440385481c142e00f0702140d610100001d0844442c545250030814800820807401d45241c00b4001801107000549000b507000740c0582403010f554104012207015450380c2001803400300c2c3d02c5001210a694041c60b84044058101c910300089803900300d0030a1982e800407100c2868000900c20126031000c510800f0b00f200c48010300c80c1c841c5d4607040c50b03030764001d040e000040000d10f00e14000c584805078040d40c1504441079200746102070705001c060090100030f241031000074181d000061402070001035070001c440540c070034480302ca0243d000b0305c0f01d1b01e032400e00c1d150b81060160720240300588039540b80000400d65124071940b044404070340d101e00b0380c188007000301d0300280020611180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 950266106 1250 950264856 950264873
    0x30605040617060f0702070e040303060806180c010809010f0207050a0605070822030e0d1110052b020c060708040302010b181302151c060b0f0723240601030504 70
    0x240c4030342601041983e90310000c0f440d0501235040000040c0c449800e100806030141c100400b51400c10065843c5940c4420915a82c200743d203101c0c141603031040c03062030441e5019202558004010500114820142400c00d5061b42e0009204451540c00170040c10300744582c40c490706401a0f42c501c0d12001c1414901e0807284500b6440400c0381c80f040b00107401100305405038105010b1000c0190a004046c040d504083d407983d132906400302e000e026000c00c40c0f108580700b50104c940c114800344940b01140e5802003442070f0000c1c1d000c801440c60f03600b04480c0c0d0000e4030070465103200d03120303540d1143c555182514000b825244d009206601401c030014801008483c012803159100c0210300b0001c81c088607c2c0005440d003503010200001100300020040d415a000700d00e882050040084144145da03603401d940000340c81185002203580d5404d2000f81d0018180080c0c80011034000101c03a4a030042e402e10103070820b0b0608403c02d80c3c8400401194090392034240a03ea0b108c030090a0070480c07481c00c1d443d419030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 950267356 1250 950266106 950266111
    0xa050c090f0c0c15070c140a150e0a081912050c03150f0a030501471807030b1e010206070302160f12021e0a080f040503060703060504061706 62
    0x42ca0300001c202072420359000c00944102c900303e90a075400c3e40c200080003404140c0d6808040c2c2c2c51102000040108040000b4030070007155000d05070440c050307848109140242070140001285d40940703a09100030406003c003424130f882d18224010b035100384010300500480c4003842e08906440c180010170103e104540c040e40c0d442031113801c101000d0507000e400140c10301c0c00000000e83c0a4400c2d040031051002c15440b000514050182d00200d61001c00d4401d01c402403040101190340c0343c200400c0c11405040b408603228110064030031310b41034000182020034181d08681e4007001983d2218034200074640401c8502014400d020b89036060300003c00000d44502004206109064000030010300038030102003c441d140740c205450124001c0307a0314210140c0c90f4401c1d41c1e07800611030340c611803040c200d0034250440d070991100020000c0c142143c1d41c920964000d0030700c4183c00c0e60305010000e15610f090101901c21074507070340c000405506101c02c110440f004c85e000820054211081600312160004003140c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 950268606 1250 950267356 950267371
    0x1d010e040b0901081c081303031802120f0705010212190903150203060102070609031115090303040f14310603081603090803090f040e0c040912030614060a080907050603090a050c090f 80
    0x40c0e902d0340d00d102b1600c451321220001e401034240000f078920392102296184161840c0000d0f9000b26079580b0049a039401c075000d684011100c200003154094400719107040c1032203103a00740060241e5a079100c0b4a15101d04520403440d444e000003c000b0150780c14020368016000d01c0c18003542450860310b03005175007502250001d000b80880c00c00f6290b10b141e241d041d540c03c00b0004040b03942d07a80d100e1a54402c201458821094070070959000c5020340c1c41e2016020529011000400941340c4007042d844036215000403802c013050b6078404006c00401e601000a15030758840900c4107003800740620380100600c0403075101e002c0a030004e1101103480c0e940c0003c2c0c0030340301800325800300311400001c0f40e0a08111101c8202d50380940f408050380d0400100c403070303c90307681501f903201040b09507550496869501c81300c40310a40c1c4000d041100c141024061100107401a6008048860b0280c840c2c9c04140594004d46822090350320015100c010060104001c00a01c0420380f95071990b402e00501011240e9006000b50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 950269856 1250 950268606 950268611
    0x30c240f060301090c06230702030628020703030501051807080c0904110415080a0603050a08070809040c230405060a031e02030408070b071d010e040b0901081c08130303 74
    0x10700c107035003d40140714082e40000007011015521740c0f02505207248454101c0ea100900c0440000c018010020346140d150041c0160180d9550749002003080255061003480e040800810820050850b00c00350507480e01c00d403000950740d4100300803c03d1018400c5001c02c0154283d90800612603481410039030000f1248441c96200d0302014000b401134205840380340c40d40f082c0410006801f01d22540290508150350301c0b11289038440b00c0b1030805640031404082c00562200c2c01e4000000c1c131200c000d000c094020b0000030700340080040000c0a445646c00048001011045002000010302001c012103840740c00c12580350a2510003c60114054805110189a5136956140e590200500d0700b40c4100403107802155249070074030340041c0c941c01c180c0b02541d040a80d80001801503008039007d1034440d071640e80c12680104044011035609503255070290f041030f150b40007845180c4905058078040d0000c0805000c03c000d80080c02d04482d90001060020070100405024405c0445a00103541c40c0e05803601 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 950271106 1250 950269856 950269861
    0x5120a0210050d0f140130030c0605150906030316170403080c21070807020d081306031a090103020a0905090c1c0c060e01090504020904060801050405030c240f 70
    0x7640d040c002c1c0c03c14120201e05103800005110034640c03040302070320440c403000c0e02c03240d8981c000c601601d01d01e15001540620b0032603180175a448408407010b8590310038580f9100c40c58043c2d440c0019100c054401045024200440718100d25080d582203502c1a4158019810700000e00208005140a900064030014070410750204103259003081720003070354000c071403256074550303840d14142e81e00608244100d07550481e0341c89a200b40c1e040130499201640121132241000d80030380800054802109084646500c01c12142c0802140200c1e401c0041ca03242d200050900c00070b0012030f01d02e90400b86410300c40d2402000520040e07035400000e1041d40c40d92200054142c0d61409144c2c500303c400c020965001d41c07501c0c41305001002101c02061103d00c20409104a141d03180d80a45201800f000f0050101e90407950078840c5090542c003610302904010f02c04600c0345e0760b400c0218212841544d00359420307000044c540341c1e8904104014a18402c00c0c1d000310b89031012003091032014140c0a4100410107081001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 950272356 1250 950271106 950271139
    0x1e051f03180506090a0c06030c091715100614040302030304030f050316140f1c030917030a060e070921140f0609101b08042f090105120a02 61
    0x81d5a0a400c0e07102003154203c0c10807200043d5241e50000080741c403810703000c8021800d14441e000301c41600700359441d03244070300c0d050110b10034000014040c103501c00c0c46600003242068070f4102c419030007901e02c844019a01401c015000304440d01c2c0740c42c01b4101084c2000100b0050310004101e4007100d8106c400409000000d160031400d40c41508a11020340d000c03c0310300b100b842550041001c0700c0403550110b94401140303a807120340703c1d440302c8641d4044010b11864551000e0181c0c22046105203e60340c0c04210064049101150f50800e07a2100c00d0290307202c80038850b41d211082d00310780082c298100b030080603240811401c01c0d45502540f40720f04084040300075040082041410400c070805c1002e580c4020410b0000c650f5030501243d00c100588180045429940301d544500b0000718140d490794590600c00000a031440c10b40940122050b050081507401c0c5a002c1005032281e1200e012002c07a400b0001c8020810451410380106200300e403c2004200103403400500b40405030360655905400c903c4980 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 950273606 1250 950272356 950272391
    0x3e030a021e1903030e10020a030c080f040b040e04020f090907140f10030f15030b130317090a0506010501031e09020609120105091b010f050d090206041e051f03 70
    0x60102010b035405920200815411201e0400400016903040c1441d9801d80d5041b030303490403d0311001d40803441c05030300704000c580d0901c0280b2445640000c0c0070b15141d0b85201c0c1d081d81c0d43c0f00d64400e50082c1c0d1f00c6020711003146069409280d0743e030800c070380c034900f24106400c506403244550b228a445d000f9954607001c01544500e050800095401030664004050b8182c01502a008015103c464245001c01c00300d50007100c5490201640d82025a40f40700d80d40742d1159130300c25482c04909034207201001c1c80180510045242c19031084a0700406001d030050140750280c038060060300094141410100070f44681c01c0d000c1081c40319080591000f241c45603103800424a41c0c0301790461540c10002440a045201405401050050080d002140c4140805500c01c5401c41d082044050000f100c000140d10114824800b90040c03000300c8000103a601803d6001aa1030303070059109500c5007104050503400c034621003001400900043d5610f03d400c514000304c5480c0202c3c0300030902e013030560f00c6031030b150051801d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 950274856 1250 950273606 950273629
    0x31706011119053f190305150307060c1716020103021605120408070b07020609130605030d032a1413051804021c0302193e030a021e 58
    0x10140c803000041a442c07401d0700894400308082d01301d400c0d00c4036445040030112890449107100e5200c03801e407942d40c100d0281401800315000d0030b85058044450f50750610100c0d0040c0110349403180500e0703143c40c11400445001413210f0780d4410600c00b0f00e11300600031091402442e0709190050f51062002d0644804200f0900042c2080c41000a0480c494003160010f00c159525101141c3c0341e1680c505c00362005100300300c0020740140091051401c0b600380340d4050500d912100c4800f2401a40b5503020034901025000284000303034441c82c5007000000240c170b0801404044840c1c100d03248050000261800c400d040719852281000103121000c21503c94250380507140c002d002d4000071090881a42030b0038415901a44951717001d002400c2c0030220250300f01d42d65540354003d441030110f07410b04180c0070354a001094030144000302080700034a040d0042180c103c5844095054070541142d003070030305c00c800c5c44e824074040e038400d4140801603550103421001e00d100b500e00d22610445080701041704100c48 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 950276106 1250 950274856 950274883
    0xf0c0f06051612020304050309060c1f020706050702010c0905011202360109060912110319050c1804060b04090c0612270b070e060703170601111905 65
    0x180820700400740d8002c40c031201c151030541e403403c600c400c03c00b00100032840140c0e0000c2080d8000c10030300c003490800340050400d0160307100589014088440b20003030030110042f055024503500040c40010011a84606500b050b950f20003003240070359842d0064511304990150605019107038000c400e800800b901101e1513107034080c4980e400d890680a0317800a00c504951411085c0454003006105948150b0801c000c480c015641e103540b6514001804030194070040c403e07141e0050030300326581652000c0000d0204c0500020800005172070500b0010704000c1c0200d00c040c80755161403641c49020142c9034015400940103280003901108103030003c1c00914040400904000d002800018500c3d004080b01c4003c68110000344111214541c400f07500300f000ca1044441282d000c402000801ca070b0360b1407140d111072035003860262482840000780050700300f0601140000d023031000b40b00c0c00300d4009070910380102003030070f15541c2405043d591584842c46883c108003401c00105013841400420030102040409 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 950277356 1250 950276106 950276111
    0xa05040822030501050714030103060b2d030c04050705092115041709060d050411041b1b030c1407050a090e190308011a04080f06180d0f0c0f06 63
    0x200307581e070550004001d01c0207480e654a400006a1900e0041040c82c03400309500a00a103075070308664411000302400b09181c0c0d0004014015a20049040b0301040d030600345200e040b20060100d0410145040040c00c0054090b07402c0c02e06000840c4d822a007940c80d42c0fa02180e084081c28a00140102c1030072000c050542d0901c80c1c0a0091210b0040c42003903409640142c03100800e001a107183d92140c1d01c140c0c010990030406c2003102d08860440780c2e0003581c00a02c940100c00c8070100e03101c009010303034000c0c85c1c0041516a25183d4422039a802107500380e903c1440c24404c00300035106440182c40c0300112800071740540c00c0712007040e03d200e80900c038071800f403c3d0090032071403582e4071210002c2c002c00303200000343c0240c0324942102c0340030310304107400b142c03500e5156031403418682c208500c030965003490704401048810248400704001c0001d001000210304d042004140620b01482c8851589030002c920a80a030804908409000e60010584141c4284c1b03081501403d001840c2c1a00007611402001d00800d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 950278606 1250 950277356 950277397
    0x35100b04020c032107030e0307061a03060a1d121e0441030616121109030613080f03042307060e10080a0b0102070f0308090415030b0a050408 62
    0x110000940c4c88002c0c00c0c100100c56498071819000c0300c1010600341156482840340800242d480e800c5251504001045159030a500c40042890a8030540d042c08809843e43d000300300000401c042c0b407441c03680c8680103054a0a81030403030013a82c8180111030400c032354005440141c4405010032034000313082861040b14488010003130105403078802b610702030150490484008030300c25511400c010586e00200a8182529040d602200c0411701054803814001c2c0719046046e43d480a1203030119a0300e0501d22079075600402c80405040120042c80c6a0b9180940f098110100f1052015541da080c494040203549031224189980c1461480300c01c060030101201e0250a194004210311b03044414689400701c0c0300c00e03068100074640051066040005e0000c0002450750f50003904440540341c01070050361081511050107070f0608085402c10741c0c11200000d00303038a103400c00e44144905400e2495449188505598804261a034080d0034001e00e10b8490380820144a6184c0450300742c01d0318000c88203800b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 950279856 1250 950278606 950278627
    0x16050f2704030518010e03060a0e010e070308190c08070303020307030902131406030316020409020d020406082a060306010810090f0e0c0901080d080414030435100b04020c03 76
    0xd81c04610107030f000000d902001320003035018000204904900501800040d40c548018100824240e01e92444940d20340080c0f003503001040c403d00c0c0166004000c001d944500b15000351116241c4580306000700860700004001040c540b42c1a074900075410b14000d0790f2a1107884084000e40403403034000c0e501400c20707a6403042032805d41d84a13408080002c964400c3c140d440c2d0f410181c50b800360003140e10400c2e903d42c0c40440189071a038030810445e84020a0300c8179160203034012030100c800c2a0404045541705030701d02e44c0032403070851a48030080c003c0c149821001c440c050116400d408050882c0b0f0500c6202d0002c244982100034041001e41064141003041e1811052100040e02034101518154010700284240700d04080e4a481c1c140c03106038004240800d080407089442c150002d02c16a0412565020744581070b8083c401800103014441000345100e4605070072451780c002071784959001c0410000070140b07801000c174000743c0d4280341004c001510040c0ea40842c007e40705107103229125000026103c0c40b070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 950281106 1250 950279856 950279867
    0x1050703090302100515040e01200c0609030f0a030b041b020303010609060c26160f0c0b07050c01030e0f070801050a11030c0301031b0302100804020316050f270403 72
    0x105019608403942044c4a04002c03080769006d440008120303441912540041c181600900c021450820000507066034a01d501c0d125056900700303180643e50005503204103074030100440d5420140703600203503140c41c0c084040d44031179205105240c403d1584520b203810390b83c1ea40740d1048160816150108400c8981444000e4403a4000d0190a001c00c034100400b043c068410134228003020f900058411112411001c6242e10b0100940708001c0f00504001c0901050b5004013821440c41c415038070000020718900d49a4070002d0290000a9428018800e210210f01b0002d141c0148075402c1c00c000803543c401c21805410b00c0f0b88100d000c0d990348141000012045d405501c82441550015410011181401c201040c0762000340c41407030840320280014008200701020441003081126641025960740b503000c55101d04118815801213082c400800c000d504041c410f48541d50782800a03101d07503505020000c0c12840f05000c045e409084848030303200342e00905a04420941c903103140084018900307403800400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 950282356 1250 950281106 950281121
    0xd030f080907050303070b0408070f060b040605040203060916300f0903050a0e01170f0a14061c061d0607022503060504050a0c17150c0406080c090301050703 69
    0x2149040010070014000c5150340030f840000b8043c41c40c000480e02c54990741e00014000342d801260402c01c2000083c0032401a440c0d192217801c010807084604010031040310030560007079001d81c0c010010828035940d41040198007a03542058565003100c800e100f1560030700700c00c41c1c2ea5070018123a03801e01c4400404011149200d810350605001e0702c04000c1c281c00c1a900600c0000b40401c106114040801d4000e20a4034541b080616180a047d030324154040c01160056401d040740e0400c5000703010705032181e801100e031100030b0f90b0424005070a0060200740b5050881c06440b43d4000301d41814003c109294010f1208810b107444040c10154803c11410713201c90040e42c402c0c0162044000702000034441030b100c41d41c40300104406105446c60358680c10040c00e40200110303814041e02c401240001d01681e10319014004d00c92101260350844521640b0781626070054407002d903044410800c40c1903c540884041c0c1e5698070380700480c0d031200441c600150040000c4140c1c55405d0104111406030b00d58400305 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 950283606 1250 950282356 950282387
    0x6130605010b040e0118021e0301090b012f0c040c091503050903091005070605010902030717090c0f01050c121c0c0e040b150706090501050919020f010e0d03 69
    0x1169990341d5440b4007030322681c424025290401c20040090b0301c5546862500303c01c000c500075140c00d9104106914601807100310942001c6c01100501c41c80e81d5074451800f143d0820708240400000c0c60182e1807a9050f01c4c068142199400400302d000301c0814050b11341c00c10740c081c00500800b10322500c040c00c0d94900380240106045248610f41030307079100e40030312406010103001640ca0315000c0b0080c0301001160081100a104042119500094044c4102402003026003070058070b90801c944010300c600e601030384103810261110f051210140e07001c13507142c240784001c45081c40402200340058940e8041c5103a5100c0b103014801c1d84e490b400802c0700041c44800008030746409813814110b5024200d4910074980000221815080701803403c0c2a400f0305c3c450308c0000c0119054000e0b525031408540e100200c03c5951549034062101000f400340241038119503024003610303080c410442d904424070103191010f0720504400b200c07441c0c0e9074041ca0740021009809401d10581c06410704020b001d0311124203810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 950284856 1250 950283606 950283611
    0xb060f0304140a0c121a0702010b10050a051602151c0c03060608070e0102100f091214030f10050405010b1c061514040906081e0303060603190e061306 66
    0x20710807030b001141c04080e2591102010194505002c082141030b05c5a01081714007001104032a1a88083c000005d80b103984564000304121803a50f050290f100f0348160420107001c4107102103130500e9001404d5621007442c48032070300038403800c80c00040c4074070039002840d086245002484080041ca043d201d5190040400010302200d941208210120b602a1245000082c00c0b080071030422845503d681d2200c0703405104481850780018181c000701c8020120600c004c999440d4400108001459038014182881c01c0c144800c0e5048100c0800750301c401000300d03110440d60b0300041d4071046164204d10180034003500800c419038480b00c512980741c2c0903090751499131240c0318900e02c0c900428000c45090301c001104500c940d0906980980b210524206004042d01c01404041210400c501c01c0c03038002d0407014018582d4500208110941d1440c02d103804001d03030020401c11005803603c0c2e080720f400202881303c0b0442c1e075a06011003c0100f854140100b03c6000e41802e0003480143e001d00c2101990003003004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 950286106 1250 950284856 950284883
    0x15190509090402010807020a080a030c02070b0309060115020a0f03080105090f15060f040302041419050105150a021c0905040605030c0d0f02030a330903091401030b060f0304 76
    0x251400d009503100345520001d048006401544100c1c0c51a0b08038a041c01124031014295035813110540021a4400000c0c0d580da071402101c9604100340401002103500039032540c00d00c160a261910b005008100804401c00700258000c1e2081007850400740d0031801c004c0c2242c0041c6401008014203224581c41004c208000c10100306905102c0d0703000300c223041e10b0303440507251780c84c18070059030003045030116550300a22000025171039601501c0d107065810000902c5034070b0010004001109030a960b0800c0d03514220050040340c41d441d54920740c10b08805030203615840c0103482203107445100c00290642903e0960a2020f46401c44501415100216024405a501e480501d03075101c142100b01035000e50043d08200200b111420b480e4a0640081c0a41c4c145145c0c0d500d5041d00b501000c01c17183d42d095221401d10480c0020f440243c440310101c0041400790a446440040c00c22400703000b03055070310b01e0b040c2c0500c045a02a81c011140ac05c00a0b110907201e01800038030034030942003210107079000024044c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 950287356 1250 950286106 950286157
    0x204200a0915051305010807030917090103140403020a1104060308190905270a090b07020604050d09150f0504090e0c12190602090109090f0510050a0501051c0b15 71
    0x81e00e41000c244c0301c2901910b0f11700300044514070405000742c01450740d202420800b050000d5a00744100c60b80070141c1340c1d40c0d0015000101111042002c0c035440031854818040001d50108101788183d40106901640c20340742c0f030001d030040507280c1c0f0007400040d000030f160a04050846244080301d141341c83c3c0c002541c4d03903402401018098240710743d41c030102029800510404011880f41c001c68507913000501c124540da10110800e5041d07444c1809680044200010414108100c104041c1d49203889915203150a1079912130070101821301c02400f040f0166000502d02c10410b46005003448101482032485003170300d054480014110441c05480c0e03204510141c10800100d0314030b00300b0441145010001e807629408001d402c51850581042004000042d040460740140345844107208000511410003400360208480b0741c0d8481d6000c0e40d612101080260307000302c1501c00306840e140f401c0c2c07440c078288125034004126041c46640e01c800c0d00c2c0600c0002e044480058180000c11243c03041c0070227a03d46 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 950288606 1250 950287356 950287367
    0x70e0102060a110a0c1e0c030b0901020a08010504230c1b2d1504111c0201050d0f090c170610080714010201091410140402060301030204200a0915 64
    0x252102d07643d0604000c400c0115104500c05034042e402103480146032200d40710310050180480c00309441c0d550041c2421f200b440360161003030380c1001d60b81e802140380226612001e01484414401d280c444c9580d01019040701d02c00f00c0c100c2501d8502c6024200355841d000201c00d1042d0481c0c1140084a06042d040041950002500d920740e100e4007140f28240d0907180e0301d1a0000071146a21040718058108100055600640e560f80101d2081e861228004190010b000c516081022541c031090403410f41140580d80003012140d880d909100c02107400b2040540200140c40c0c00200100b204540d920300240b01045154541100b01e068030941d42c03151039641c41c00e0080c810600078000c0c150440c190402c8080d011100000000350180000b0031103080a48450702100d210317890351720f103c3d000031900340c40c841c126102d8a001e0013599107458003d400d00b6008942c00d40014000240a60360300c65003d181111404c00d00300c0751700e0444102c250b445000d8040242101c1c13943c8542035030b80e5a12854281c2d0680031701c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 950289856 1250 950288606 950288621
    0x10204140118050906130c050304060b040b0d0b090109020a0306020a0f081b03041403030411090c07080f031305030d06061709210f0406170601081003060c0e09070e0102060a 76
    0x34000b4903030a0030002004140440070300803944c060440c204640302ca80180c050388080014039101c81e43c89241c00e00382203056a081c81c004d28070a40c50701406d44910b0780c503480401d101940100e240e00342580d404940e20300410308000080d40c40800da40d03000040246030380007441e81d515a550780c18484524060305440c032000c107840000f260024400c0901003600c1c04000386a209015031620b00307443ca02414001e0444e84180e0b410389468421110181d42414581078540e0812441d40b031540c40c141c40c40d15611071034020580c0e004010302e000400700360041d40000300b050045402c83c0903655a00070700c00120008041507c82d00021810b0040c086030150100c01049204400981c050000a1120107000c08088040f400ca4100803070140801820980d003140948094046615031001e540d1520840c1807440300020714590400c1462410403c901003800f61140490368404004034122aa0b0101079551102e060f400503000900d180411040d180c0c40040c1c003500c41400e070252802901c0d400021030644006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 950291106 1250 950289856 950289887
    0x5240105070f030c0605160201051f12050c0303031e0903070f1e15060306140717071403190c021506010f0e0405160f020705031c200102041401 63
    0x6100050110b0702690b854001280300b40303040302d00040113903580300480d030041d94051820003040e00c5541d05103409200f141e40000301040b03540399401c1d858101c0e05d040700c01806407030290030017100701d0410400c04006032410404000e0075030340c0300c1c0360980e20500c0840065400b17000301c118210216158600110840301c80c10780012414400e00c0881c2c0b140028030304405003c00c0300000071103881e00890a0000c80000d49000030340046542491814404280e526070f102c0c06907c00d40c0700044c080103a4000d221200884001004c00323005070b0350410306549225003419100c8c0ca0200020401814088242140070140301c46107042201144110040f640d60304580002d41c4010030710804111b0039070054001480e00402403803d00354050b01000840c0945c3c4081e41e0b84640d407503071000c4e10100250440d0900c02401c03294801012000d2802d40000da44100440442259019040300c84001520801040545030502c8080034140001282002c1c003e500c0307407081609044046079071503807541c0714458003402440c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 950292356 1250 950291106 950291117
    0x2010f110d05030c07060f0c120501050612042a0509010e10030602130918050d11300a18050a0807030803310203070e01030b0a050603030c010f052401 66
    0xd980784280d40c60b07400a8030308111030105000c01c000040c8140205082d02513071070f5021a071080600d01c0501b40b020f1110300b40008a0800700180030f40d44810054440d20005148020015125810b04151800e140010178900318844ca02e55441a10784c42440c10071502c0030740381d256181c8e07030300c0400c1d4400e11016510944010000d100401c04100c4540203800031901c1c81b500c043c43c1e40d90303d002000032209100840c00007189001100c41c01e0140038841c021305802641031180d4005040300d1000d40706e010442c030302c00346251540180c03142c66a044152901188042e0074507a0b0301d050704103010f481390261040350202c01103014004180c1e401c0c5501a81e00701c42c00c90008094981c01c560b94030f06250401406942510051800700002e0908041000310b01c0e010845412247c0d440c500605050144503042001041200c80040001035141c442043d806080c120f000030b030075101c200004c1d00714070a04000d02170541c20081c02c104020100e038425405240740800745900001807003c00d070110818030104601088 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 950293606 1250 950292356 950292373
    0x3010303300902030c060d0e0708070e041e150f0c0320031509010b070303110f0403030e01090f1d0115080112060906020f031e0411190b04080a02010f11 67
    0x1e81e8110a400720301c014240c511100c54000131526a41001d010100c07020b848481c0600c940d4014020780c0050594240034041d5107003000000000d03402c1c0a44014640c0da544601418003181403059410041c0d480544140c0e0520700b02c2140010b80401aa04040c09142c40341903040b490203803150100c2e44030bc45801c2c00383d00b42c0c203181e0315802d40c000070b00004640c901071131482030300d070f4542183d237001c0d00b10030208a88841036810010129101c41a102002070020402042da000914084c0e40403654989020303240700007020012108000275500200d1440041c0c9008035404124501011641c42001040042a079840c0301501010034980e00320404a81c0450040c03010340e40c0d11750074003501c074020301c0b002c58058069590341003260b10801107994090000310a1103500784020503402c120415164080e026800c1c6515440312a00340b04446a10070450448071550602400140c4402051000700d50f5850340c1c2e88000c82500c42c0300c2750f001207000561114414402c2d80c020840fa40003103a95500900d1201d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 950294856 1250 950293606 950293697
    0xa0809070f1a1b25060e060a0507051606110309100503131a0a050117070b032707031202031306120902031b1509010c1112060c03010303 60
    0x31400110a081d09241001502c60302c49080100d011002c1d4210010070b8602c1104c041c0505202120312803218409283d44108a040e522180c00e14203d0001c40c0c0340c039650aa100d40941d00d43c811600010a02d0103842400c07580300c101b061112040b265181c60f500c00b40031811034481e031613100e5460010780c4881e09840c03141090380315102030355000a5041010a004450380c494402c07442108018038080d90340d034030030082d24a02500545006214031402421014411003145449841c07901403041c4e40080840003a81d00c4c1d141c0d0724400301401c1c000f031000c0803131145d0043c2c81b0784400841c003069840c03255106a441c5503510000c1100c03034404030820200129410803908841040d0b004c400d4155254513000c9800142e50280080e0704141c5880d036a140401c10113000b80039021009021030148141c082c070101034240d03048400003040e40d5200280050116040001072003802c00400e840030203204080c2000060300c1001c0c001c5050381d010b6200c10700c0741502c03c50343d030700c07403024500c486103004011400f0340c100c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 950296106 1250 950294856 950294879
    0x501050906121b0c03071b12020409150f02070c300516090c1101060f060c0c12120e0402130b0d09080307031a03010615050309010915020a0809070f 65
    0x400d028900110312000400b5040000d038111004903051504001000401c01c40500d030b0f40b25588501e0702c4400702c26890002c2c848c5555900d04006401039071030700c0c52481008022507078802107011100b07042000203034075100781c03009420029044903030580728580841c242100e0030301c80b4900c24554020000c0f080405c0c06021440c10403660850b01e502c82c03040403d110120340350710807000d0654030100040648100b4001029090401c2d40160540d14210043c480c0b104205400c20545040d03060034000b0b01c0e10303840c104a480c030316544040c20401c03602204804200c221500c0000030001c65903002d1002c28101c003008200d106405003055481540300c010000d00e8100005000d60b0002d1010001d200002a160f41c5120381c0103d0302400020307916003407824102c00400e143c00e24120705400070000700d8100780761411081d0a0485a005000001c400142c10880c2504032030303070056000e0580e40803502c801001074081e40007440d80e03502080c0e0060008900500000b42d21045424020f00d80703c1c45450a20f0041c02c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 950297356 1250 950296106 950296111
    0x5041103130f0503071725050303010b0a0c0c09090b01090b130b03030c1e07080f0d03020f04120c18050610030f270308010b130b0f1c0b0a050105090612 67
    0x4540c01306100c0b1401182a0301415400e8606005045640e107561440c06156140060522444045150340c072001240c0c0000a81e0f05440c1f140c1000c940c0c800d04401c05031450001d01e0002040c80e554220046601c0c14a900001350840c4600c0e01c4480a03600c841e804000e42d40503140e19070300507000d000d14048299041d0412140a0301c0034081d64540b58035013002d00c3c200161840071521041e000301451010841c10400b290003482e004001d820034030f002c522020380311111079080c6420142c005c01c0c0c610050600c1000c440007080307081000d9480415500c0c009080e51168420044045102d1a040800380814000d1602c9047c00400c80f1108100b801403d400130440c040d0750128039507645040341d04c0041424102102d00400c210781604188607031400030540c000581104407513403402d1115a00242100d2203490641d5540420700f51074180405049669000b10b4409001c981c5030880c40d044028240c0c2d110f0081c0302e50545901d08000d84940064900e03106400d1401e800c0708040000384076800d4076024094 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 950298606 1250 950297356 950297363
    0x1b24020a1101090e0405010b0102250e0403110304030605011406070b130c1205071a0c0a080705010f0507080a110315190312080702010606090e010e04030311040b0405041103130f 78
    0x21072244c2c45000f8651100c6040324110780713580d51580740c80c01d10341e01000000104014003034444802010340750540f41400303e41c4100c0030381134401c4c000b00d820107000b400c18004010400080f80d440360380d20304050703010302801e00c60340d420b20103400c05045090070118110b481c4245c01c86d9940c42292120001c2085800c0c0359007041d511540744450125204028a101489560040c030040a01c14141041d00e00030304001c00c031640e403030b070010400c214a912010030071004080c3c1045100d51984001e04059014188045116105501e4441000360701600040c0c92805020000810010495110714140340c0e44000e5408000407400004144218a04012036140104125640076406d95580d5220070000955102d10004140002d041000c0c0c2c03582481400c004108514200340220303d0103c65805121041c001e070a42c00f442d0310001000d15000c6c2e04a00408415400141e82e42d941e00c1c0b51404541c4c00c0350103094031450524130295091903140307044d81d0140c014a400d01d0701c00041940c444901070b01d00c0c1c40c2107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 950299856 1250 950298606 950298617
    0x1e150a0306020a21060f03121106100e0603071a0a110304030f0308090106031208060102010209031e150114010e18040b060f060a0e01050c0a1b24020a1101 68
    0x80005495070024203200000e03504d8040002501d00d40421411281100412419203428002c01600500101c100212a080240307248204e48425040f5480c11242c200c020262044a007400b00031000a221401120a4071801c800607841d504200364480d0954440c044102134400813404901484074014800b14006040c82070300500d203800e00340d007103401c43e0307000351030900d500c0c1c0140c4c040c103410102e815800310b2450001c1242500b0340d69810038100404130702c582007200d040002501c50b4000d504603080c282c0e0040441e071050364850310004800010086414150082c0f1242c0381d9030725004102d56050f104d00384050780c0004010340045513903601070404503a00200400e000c0e00340e94007904c0d0346409140105009100e038035221051040d40745440b20300b1030003040c080200c02a070680c40303a0516200702007480d2641c2d407030404410041c58110360400c00751908011480540a4841941160084070040d04580e03c200c0780324070503d515070007001e06c1400980c20240080380090f82520b0389100d45032050400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 950301106 1250 950299856 950299859
    0xf17030118140f18060c0406020c12030703140c011404060c020c0102122d130f03020d02090606310f0506040b0703020102040905190605040b0120120703171e150a 71
    0x5140c45c0c04d00540c1c00320103000000070248a800e074103100c044d81d00d14081e40e03134200c2c903210424030541d030344589032020302080740782c1440101c18904282294820f1507490000d0241100550400c4414401600e00b152030a10780440381c00105d00100340c00d80b6410058014180c0418a00324003c00796100500e40c41c00d80040f401652024543e42c44004140c0c5803820342603403980d88100c0b01d81203c0029802003540d02e11603850820041c0c0d12606402c0071a641507a04680c10745810001c55040c0c000c0310b600a10754040e20f9010410612081000348103100d03a9519440800d507241460b000c0c01c0c0e180d010342a0003030b00400090040140b82001052032a02ca440014a440d59541030602160010744011502c0c071100b21890014980c28080d4074050030f000c480400449004000203410250b40709001099100411090450400140041e020b080c440980c940d0703464515240040103800c00c80402012402808003052810003d2441c011000e1080160307818540c0312103a194441030820300e00d480c1d011011900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 950302356 1250 950301106 950301151
    0x1b0d02060307021c0c11100c080c011e0c0203091c170306040f062106060308040617010e040f080c0a021f0306080c0a030f0f17030118140f 61
    0x150302c03a01c0d4650142c03a01c801d51a460001d02c4200304c1d400e004022498442c600420810101c1ca2214541152520400c4000c0c90054484200c9180040c05031400482c2c1c1000c4544190480100d40403240c0d03e803000d00040c07149080482d061400303583c0041e40140540031407814621020080e600d8840c01d0b594010300c550391040a280c231044034441d8101008070910078203040502800f41a508000c40900007070381841240807909102c1d1100e03642038220b030611202030000a0303102c0e10295801c45645c0d80d131551503500c09486048803030040c030351010341c10000040390343e141d1040c0c600807544081c04c0b0841c481562100b0140e5048241d030000d40d80a4804101c00694841c1d062601c40071200218044241400760082e040320300326486440d45070404c1a0030f9099a80d480000019281d204a101131907242504010b500a003c0d088000c0c01d007007240346401101e28012001e18101c0b24070321015808481404080d2054070301c0d80d0000e0310521a0f03040030030440f040c14114164007102d0030017140c291618000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 950303606 1250 950302356 950302369
    0x110117010f1401030c08070503070908100912230918150909070e0a0f0209061b061b071410020a11010b0109030f0b06130606020607031d1b0d02 63
    0x901c19400074180150030010012000c40312600c180007401c00b00661100e4038009440708100801903c2040030000c0011511030195401c02c014141e800f0403540d5400c003d544074802411020007d480c2e0010000c5454446441030110f03511342d400042c00003100505410410b803a03a040380075400da10203a0b40c03100c0c40c01ba2120580e201c0c460766018464020311441030042c030400d0700303014002c41000e03040100240030a041c01ca4507290000d43c1003c0008454145050300c80082c007415404c00d601c44d030300060310003110381d000158032203100c00c0310191002c580300c4a001155201e2041407600c41500300340301403004521004242181d800c8500161742804407074910680c00caa1121002002040d410114005212024410201101c07001c1c00c00c03003196030464446504426186034001e0211300410000780340e0740c65120f0080741c28500300409220094856070040d4540900715541e800007450a20000c0740c0402ca00c0d9100640110345025000324600600810120320003000001c4d04161010752080040c3c41b001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 950304856 1250 950303606 950303609
    0x12020a0506030a1d0115061202090409050715091a0903013305060406081801150b07110109032003121204051e07051c02120d030605031911011701 64
    0x42c040041d1490420b5182045184135800404040e850941a0b08032622010140c0003912054104040c8181410007260082e200754a90039802904000500040000018500080c1c649480c1c0d140c24800c401d2034100d455164a00c0b9480071100030000c6449028080d600424407408007030004640c01100c1c0c0244c46880d4160b00c0140301e00e0106101d03010114600c081804041e003800c03030700285007515081d4018075000c000742c61002401c10b10b084451061109501c101c200282d0714449984941e520070240c0c00d1608100707400d07070f20142e1403045807000c5e41c4240c18010036654481c01051400b045100030b01048080c008105030540310300390501442e4203422029000c2e0301c8172880c041100d403a191034050b050649071241d54ac0e640b1207000d07a0f030300d00402c04551031094410550f0100000406a542284030502c1c0740c2c40a9040b09900c0001c0b54032280100d8070303614501032a101481410b42d10001d050390f4030303600010052541140c1d146040007860300b202105032008145400c8442c80e11001d901c1c081a40c00703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 950306106 1250 950304856 950304871
    0x1101050c0c01230103020402130314100605120d0f02030d09290103030503061c14060f0c04050916090b130e010b07050d0c0312020703020604020312031012020a050603 73
    0x1041c0c03005851001d002c2e040610640d4a00f007500300420600300c4002c00c0040c00000c4c400c40c1c01050840c0c43c07841c6011054010741e081410280e0b602c24800350a0385982c40120f070034815034240417022800b800d00307100c000d010b0741800004201c094100d010488106495000e10350850000300841144185607000302a101802000c0300003803442c0e00c03c010030080c5041544034104103081d500400200f0740040c03d6031384c003900a8500c040d50003016400c41d072300b03072504200041107500c0f03924070348410010008207248103c26a6042c001c240d00c4a02d4000c40c24001d6105065209004c3d0000a1069601e030454402401807402d2548019031034a25018058020301e11440940e004400100012007003854582c0c010041404030301d142c41d11546441e926114140481e4050003403614000d410140f017031000f056000c5107000c08545400541ca402902c50744190b030700740e1180c402c0a030079880c0950104101c2340940c000c1c003115060a854207500d0f09a0082c40042a64803c07400d0302c00140c10f032620401103114118 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 950307356 1250 950306106 950306131
    0xc060f090f1608150f010b0f090a060809010b0f03030a1b0b010e25093515010503160302090910060303080702100605010801060e15040b04080f0a030801031101110105 73
    0x810f2626454480351800d00b54114902c0c00c180400b10540c03c3c1c0c200d040d00e0f400c10754681d07644585004c0348014440c0418403600031645550004030550f0007203215004c2c111100027030110b021030390100401e101410102c0d6506410412001e1095406056120345a60703503040b540720b00c4e01903911480380c8074109a0001d600740e4421002c0200400700c07200032800c80315003486c801c1f104510031440140210400c0c0200b0b10300602c1404000d03280c00312a141309201043c030f011950a8588400800c540b200480d11080155001d030382d0000c90340c1d150105a6110440c14201c2510380c40380346808200c00c5039805824000c0c5c038090802510b60301c140c00d0160700051400303521543c44900708684000d180104051004540602c0c003003052040340c0c0c0c0490303040c0c1100c0e40c03071402c6030907140080001a44404204004040c1c00c40000d80010348004101c0500200c03203e0340c0c00d036002d80c11001881911200051001400545208018000903010304a01d5194000600d4541d062500441c00300b800c45100b612440d00084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 950308606 1250 950307356 950307359
    0xa1817010c180317030415060312020d02070b0f160506040b060909030304121d0a03060c1b080313081902010e1c1704080f030f010302040f020c060f090f16 68
    0x681200000b054180300350311941040d0702d103444140441c504c07090011003455002010800340100c0c5648480c0c2900c0d03000c0308100681e0f6901e4a0f0424445521f8001c001d8050048100011400031480c1021201070041c0c2518010303c54543c094103a0104e002e45141000309000c280c0484e004110052103180b080503403540300d080c00003c00c0f416410090525603245c0c81001004001a400ba69643d5600700604021807000e032403110091029140c0a140c40e040000c001e03000052100360f070444410403a20342c03a580c21f28070208040c06815003c45801500d01d80703040001c25002c0301d8402c07130702c0b07a900d006002c842d060281544030007480308014411103005039154080500c0e40501404810403810f6841d05d0b101c5170b44034000000e0f10000b003054800c1c5030109008001024001500211f41801084202650b0b0307070700d080c00074072899175021f000c244d00841c030b46410241c03d100e440c806c035400c000355500208415a540d130504103000400401c032000c82c0c000d003101c091a80e070042000760030400d0103455202c41c8a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 950309856 1250 950308606 950308631
    0x9150905041407053c0409050f011d04060b0a031a2811120708070219080f1305030304181b0e061b03030f2502030a181701 54
    0x1100306201c605410b11039541031041e0710360400c04966402e101e08141d078a00c544c9501c1c10103a401c040da608100c801d0305403c48002d01410000080003510840c3c101003056803901c074401400f20509000344001030704000741e1120491524407800c0c0d0701034403e000110300144120003088003842e90b903000f01c03a11500e0309a03001c1d03a61180404250f01c41400b294803030b641d008101141c120300030162081004950340305680c00c0d81e1503801c41110032100d018020390f070103800c10010044c10b80d0720844510300107029020540c4e030f000384012925050380d6007101d5102d0401c600d0018070300da19800003184243d4000f640200103080e032010302c00b603c024260b416000e00b5480c01e0041c050182d0316005400417a07140c64802c00c00c05035802c03070b0248080c00400e48000b610b8144c00010a00c41d8281454651441d100c0442044030824032210400d1042284001070b40c1c1c40130401c001e500350004049035120141e0810700004003154480c4100d0125003510802c626000b80d521000b803e82e0310310054180d101a519064082d021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 950311106 1250 950309856 950309861
    0x210f0603030e01080c09040e070530060108070612150e0907120c03112b020f0d1205031f1806080a050a0b04140f0601030c08010212060f010915090504 66
    0x4160084c20444103034034150007082c4503840f0314103c19100300e680380c4494046105c1042031001601025100b02d101d28100d001e174108180003a840706901c1e100310300c0c000d10024804143d15040322101c00007400d006080400550300800036a40e420303412699034020011161007503503030303c00604a1041b49109030904d4180c8508044003508808600f22041c1c4000c0c00007a102d2403000c045030340084680302910324120005a140301000024614404c00d01d451502c49082040900602c5108441c2c084150300110b0a106051418a001a16902c1c5581d00c03402c1c6c0d240200300640d401096201140314121400300c190f42e102090360420210880043c03c0c100d00d000b031603c900005480c4000051400154a07500d85559100024008080808260205081020081649290319100420703203001000030000c49550314005d00c02900d03040900030001800c20341c107100b100d040c0130000703c1760083d641d2400103101480c014080140c1c1040006800040d00c5600d101544114090079660b5514182c40c1038104801d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 950312356 1250 950311106 950311127
    0x1208070f021902030a0b01030506090705010c030e0906011101240504021e16020a062601050123071b0f05041a2403130302100e0d210f060303 62
    0x5111046480c030450980018181d80c0c1e807000a03616003200411440480c0c200a0f2000000303241495500011080020100700c01d48130300c2c4035808843d0101d44d20401141e91503809040900440c1107000b0307414450030110400d561040041c140580d15092580445085484004000c40740400402c0e1109400d100030b5034080c0140b034100c0e420740c01c3c085007001c941500c1000295048070f202c8001440e0048100890345880601d400a0030001440e0359a5400303403850707240f18400014103040c5000012580c01180000f0305030b44040c1d41b02c003584000201c80d400b11790341046c441c003440f0405012890000320081854680140002c20120b00e452804038402d00c03a180c650002e80c4524102400305a0000d403213841030390f034244100c601a80015801d40c001c560b0103e00094254000c500000300b01001010800300c4101912a9084072860301103400b1a0080b41e80080e01001c00f6040440043c481d03520420300c94a40e900d689030440d00340c4140b9080038040703401c3c0f805d1038800c8545a000030000c1c5500017003043e2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 950313606 1250 950312356 950312371
    0x30403080f030702012307080f1501030207020f030a06091a01150e060d090506190b0f21060916140a031502090405010308120c2104020f09041208 64
    0x5050504540da00c2045018940240200000200000750110701c02d400029141d000c501e54440c0040d5118001c2030803c2e030440704000407a04160101c3e903641c0741d034954540300d82600e006000c5007030480e50044010f0f601400e000c0c2d03401040e000c1e03e030f0850341c1c05000d1200035034401c00307000074114803d20300f840c0d120348484084522003008600400c811084c00c180e030b940031070741c0d49003421020032650300107645401440501420540392509100410400042c03a80c081c181265501d09c2602a404032082a11403804451b50401514803070950281040c00014004840020004078040084030840d8900102250007603c076600c010091003044801030050f1018041c401d000c40c809402000c00305420031201d100c020502c03104401c41040e031000c107a040d00c0d03075124020004d20855949060141c810b801c40081007011078004008111401150720480304440c80ca0030859084030100c0b8581e01281344010410383c4c00981080e03000c800c961350300003400d2040d4030818051000c182d050f50000e000c20340040142 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 950314856 1250 950313606 950313613
    0x2061b0c060f18150a031401090b03030405060f07140a020112140403080727090e03030f010e1003020901061d010f0c06020d0f0203070504060e091005040207050a0813030311 76
    0xc00982016011070f003001c2110003841c1041820140411514542c50411402c00000403448429032035054000c0c050341007603518940110390302c404060088170040713130140307605a00c208001c0081c0e003003030300203004125103000000f420240300340c40368222052880b101c005643c202041003030466030014000008140080030420030136502c0707041003104110103031014040c840764100164001c0d2042d030002d2440c070030031440081ca4541c600781000b0f50280f42d00690170031a06001d0185030665000058910506645026240726403902c0035003000000060907190b0040761050b004409a29604040b034001d10759542c5901801590080d085c40601c2204846030401c603011002d144c0055102000c4182e9075009180165519071500c5560001d0a440301c5080000e400482000043c58206020340111b13075254030344082180c0072108100b08000101c40303005500207400020312290400d980506400c038400c90407101c4001b541d4030354039015040007000390350520440c4c6062081561013003540c1103401155005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 950316106 1250 950314856 950314867
    0x60203210f010302040f320109050405120304060902100f030f06050307090c032702120303010605041a07051213080c10080403091706010f060819021602061b0c06 71
    0x121038a032081840301a204541b602c0380201c145250390711544048003100c40d8100d1202a151040d0303900c3c00c5200c2c030b401c01c041908000064007021801424071071a40000a0604085407031884581504080c0061728144c0d555030004006071030324208141d14250700e8442046010303800c2401019a4100c0406006050a0032810000780e103001900406641080f900442d10408800c0c0480081c0440000724000f1095455403407451013403201c8000c2154000d90b1001c2090301800000c6660348428400e140016108101c00c0000e08032120008a0189440b44c03080e28140b4035032201031400303141c60070003a41140d0003c0c44500e601c020641c0d100c0200b407080c025103043c003600c5d0000754800b0399140401c0288031020307000030205031040441802a081101c02e200034080031094590340c1c0c3ca024002c0c0f20f2050b0580034003042c4039000b03194992090112032a002c00b00b0700300c07496890183d08040c01c0600300e02c0c192000640141d072144042c102c8480c800394041c1c4030078000380440d4500080c410b80c403800340c5010011b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 950317356 1250 950316106 950316121
    0x9010b0c0a02040b0d02030303010902120c03040f0807030c2003010627090804051e01200d0c170406020c09160804140a060e0102190f05042303010606020321 69
    0xd03544250740e01241c00080e15036050300070a052001c0d00b000258503010003c00031030301e2070305030707020b880322142c0040048a2507a0315043c120040c8829100a007071030001c0e0a407000020030342401005150b04c02d10740600004402d0390b0701011410441d00f0500000756410043d24142000d2244000600310000400e5000d8001c0c2c2c0c40d03008140030504202c1c4829103480e110001d01c0807c0c0c04940040c034010f0320340f180d05c480c1001d100304122050010b060009000c0d40c1903040c0342240883c524402900000546001068000256902c918022085607102415030315401c182c000d0310007030030046c0303d9500030b025103130346c0c481c2004003021000f00380d0001d030354403521100003182c3e102108581c42540802c4010380c0c0c8400c200454a01040608002c2c49503007131400009a01c581034015121809005000c4d0b4601500700d2004e44034004c01c802405c00140060108004020710800c0003003c00d1000c8120b483c1403000381c800f00f0309685040c1c2041005d40c0c00094201c00b5101660207059190f100381e00d20f0b44980c10b20320b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 950318606 1250 950317356 950317363
    0xc130b0f0901230301020f04060804110405071b03030f1104080114011202010528091d070203251e0c06050705030a0e1314010603060501021b091810050609010b0c 71
    0xd403040f85101c044101030710792804d5040303446031840841d25a44551780c40034028454582120100c44c0c01d01c449030080e8040c141170141b14041c0a0680741c1c11342c41d41c41000c564150200e03400e03040d03081685a014981c841d203050301c58281d0b00104150841c0d07940c0d00f4030007800d0a468400e07000720f01c165103060041042c0724900007103400a550910704141d640d101c002400c0c40484003000b0f58800d120b012040c41407441d80064040b81200c21002c280c00c00700b001c1c900321012440c0c003254840c2c0903810070490b43c1181c8416884d03002540f0300c0394005a0b8806600e88076926804e4640c84070303002c0700003240045c901340003800c129000100010f142044c60210140d5425459000345400c1e0010700c0084d03040038900e0f03502c81181c08008011030400700b0100b040700d0680b00004070b00303101c0c3d4004130b450010089169407010500b0f03101401100c80136008842c0c000c0601c61a0b00006242e6080640440540c0b00145024420740f1a00501c600d0081400e061000422661000691101e0303c03104040010032070b0b010010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 950319856 1250 950318606 950318639
    0x30b1e15070c18020d0c0c050a2a09020a1710052e020d0f0507170d02070816060b10081602120f071203060819050c130b0f0901 56
    0xe00d5984424491400324040c00958101d045001c03482c540564a04840e580035014134210140140040c890480d8255a11401440081c000381c000a0144012482840b83e04480115500c0c0c560030b031201d01d11604901d400f0641080102c2c9030001689541641d0000d1882075004408081442074109042c418036040345503c2800c2c060969840c0314526000039020107040c034010b4905060454009420007519400420085004101e44201e6050858840d00c01d0790b00c10b5501445c40c400329012103510181681002e0a501c2c2440e07001c1200310002121207006c1c001600f54007e00c0140400c0c68503012058951024400c3c1c0143d0600161500040d4800002501f122206c0c14170340c90314403101d000720700b002000e4040d900c0e4000001201c00e0f51850171801041c07285d0040000c070400e04039242c401c81c195441742c0301e00962907105000520034518515016503030a8401c1d411a041c15006401164190b081300316208001590b0300060856030403e17107400201518101c52241440d130424131113100740c8488 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 950321106 1250 950319856 950319889
    0x40920100c1205040911030403020115080c04091b030b01140306070c0213110c100f200a020a150501060f031b1404050a17160b040501030f14010303030b1e 68
    0x1400b000c51200e4081e108450243c070030740c80144545450403402c1e1403140e20554040f0f005602c1d000d462001d031f4001003800d00640301d060300a03110100b045c0041002030a0009000c2e2030f0b2038066904100d50072140800c000055101d1428103205600d400003c0114440700c1d11510300030381011040005190780304243c41c1e8410f074115540d02c5c2c960307803074440c60f4000c10750007a10a80c0300c14001501d000300e010008103c082c0182c1c481090084003030845200b0300381c90360705801040c10411072591b4604100f0704000b0740440310f4284101d40721410340340c660f056805442601c29034400c0d62a00140181d543c010001c1098840300d040a02010f84034070b500c11035182002070040d0400201501c00110b107000c072000c4070000d10005096000f603d888000300c55003220404607544107489800042e041c1c18240221230130448450b50318540c203141c079260054003e0030508456480c01d5a40c1c071074000c4200d03a1442c41501940c041d40e40002c50550a00500002d00c0041c86a9095904903900c80d040907540c08a4145d4801c94 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 950322356 1250 950321106 950321123
    0x313200f04020f120118150e04060c021006090914150f06030c0d0606050406050109080703110a09150e0c130b0f07050d020d0e04020c0d03051005040920100c 69
    0x100342800c1043c0e0b0080b448560418940000002481003c0e000c1c01c0c02c54411203101040882241500d1100e1407015201d0310204550354130000c2c02140c10741d80b0110380c3c45100d0050311008825000344800712001c60300030070003c56582642c8018030104950360b0ba80d04500030000c1000c1e00d0002100d6610b008001d00e40c04004c0c00c044001140c40e242840300501c544006000840302d100c251411101512250041d64001c038504200007070650f20a6818504844400b405015110b0a40e1185504100c498500c203400402940e000036071315a46104001c4031100403162051028244044240a902c014207410680102800440e03910381c1c07000394400031640014452651564181650101406140300150070f501409020820081e00800c0071225030740160303a031000c141c0041040100301d0142c1011400650b100b40300c0451100c0c00ba901031500011204652081155a5000282a15100300d421039452401c1105a03e11842e81403070703e0710300c18044035140308840f0102001041406881c4024180f4030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 950323606 1250 950322356 950322367
    0xc030323181c0303140a0902011b030c17070b010e0c0d0504050c060415120c0512091c181d040b07030207020301060e15010927060b0313200f0402 64
    0x3501c105500c41c0040d034510300d207038514240781400b8000740160241144a030540c3c00011b102c20401d8030400308165416141c18003070081c4008001750b055a03161080342440380e11001500420503806560070448404001d00d59140fa6078a0054030351003040c2d010552401c1c8000c240a200c2d001a8190342e403020060100040669032410400c6c03038003840d00a1990009000200031580c100b1001031288800c0c62a181c000200c2c03010310b44038007202e0350181c15200003001401030b003111840ba03142d1940c104401c001103d8940c4000c0040302c03920280c40d05260045a1030940c0c29001c003010442100052007102604400c0030840400c45891110080001f0948120540000c0281d8025410f440300760360064000c01c5a5510b54080c60104001910715007000404104400190f40c821080b940c262030703207000d400c000310703801c9040d10f000c164a200707102d40c10030b45031400800c50502c3c06000d0f40c4680720144000c0c0b0380708041d0500058200301c4030b11740d01d8044e100040032483d54980025584191806841c01a40c68 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 950324856 1250 950323606 950323609
    0xd050c060a0f11030f0d050705091201020901090e060a031211030c0d0305060f1011010207201903080307140912012403030e060c01090f0c03032318 65
    0x1000019125500080c0410840012a401505004540281d80740c207a00401d4401c039242d0789008500c0402002034007080401c3d1a00309940150303402c51158140241880c000c40c0000d07064600c4a071920b01c10307a50108044645692040f1400c00030000b05102c6517103411320101007410b10605000162103c4140100300780020b202c0d10b454089a170f01c21040e03c1d01c03a4905140c03640c840c0000e00b071a0300080d04000204a0910b0500044540f110000b418500e810070f40f400142d404410b815a40301e2155401e0061030007050304601821145020b24801011180d19a010410380710104000f0300c2e0107071606002071001921410403070b508040d0500301843c14900d400d64003103d030300c140700990307411800a1102090003001504124150144128820074416030b00c03280e101117807090310001d40014440c80c150a02802c040c40200440349083c400440c03180c030640c886407040384a4102c111800c2d514401c0400525512104100754100c55480103803400150f40755030b00381c1e40100712038070450902092a00761903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 950326106 1250 950324856 950324863
    0xf0d0207030c020d030809010b040501050f120c130b040501140102060a0b031606050a02010608032d070f0302100507021b060307090306180303140906180f0601090c120e0c0d05 77
    0x116640102804c4004c080c0f4540207281c0f076000d0310400200e600300080441145040d006072410f0740c201a10780702010501004020040704003100a0a10340200d04c4440107a8640707541e058946c101002010584c4507421091108440050f0b00c80c183c010a00c0c00903544a0781c0c04070792103070020365442c3d02140000c0c640e000030382041c0b426005404000d80c0348000042080d0803402520802b00190020411295642801912849016a640300561120a4452260340000401443d000c4009200c1c3e0802c1c04640e50955040e1000b40183d0241e80415801c0e08001e125010342c3d6030200c580d1002d0180e5030341130750000b002a10304091441c07280c0c2000c00010032a0f441489400c4c01150040780902100303000042e4540c03481e40901084d000a03003450b051601c00d4004204e100d00409010300103101d680d4840520f4071004958080d212400d0040003c4040030100070814903001e00018000020036034130146018102e54030401403280200e0401c1d0784031851410115610030051400d413a48841000d040c680310b4103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 950327356 1250 950326106 950326127
    0x6010c080d021c05070f210e011e0e0d0c050604021e0a0f050a0e0f13030207030c09020d180f0209090703321908071e0f05120f0d020703 60
    0x30307442c4005520808050094002500605586c2c603411a10040d02c601191a240404120b10100003401d003840981c2e82d40758408800b00c04118000a00219030750401091400440d054440300d680f904e09444050005001c8442489000d003089500c0d41590b6640c25162800140040e20481e5000c1008981000d54465007107054001400c2c84a2035803900344404c5400313414011107000d59a1210081003030103d09110301c1c060b1000c4503c00031260380b0107426880c0c409540740110218000c0c44800070000d4038401414000c1c01c5605e2000d621103000040441c101e92110403904c11b904154114030000c01c03d510103405450360169a0002e0700ea8500c010240303012860350000341140340745141c1007005540800b60640004086204043c103048007000a5625003c0c00c9a1551b4251200b10010004d080300d401070941d02c2c400c82900c00f8101d2502e004016003a15148283d52110f54000c41301e040010a102d50003103c40a040e48a061401031503401d90280105d15460b04040c0e0f0000d280e10915003c3e021814 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 950328606 1250 950327356 950327377
    0x60a0506070501060639020d0507090b041b0e0907030b0a1409130b010e041506170c220f1b02030a08010504091e030e0a0f0e09030306010c080d02 64
    0x20350718015464818001c0c00c2c1d51041400085c005900e02e602c0e01c1900b011450301005041562641880320307520303080840300c0d20108130791111540e87c41d98009182400307440010515004001031501d1410107010948850019403a00f17140040740b00401d80343c05c88030080341a070054032a025690380342c035000d030000c3c80c1c2045196030006ca0848005064041503405040504081d41c40484640318803c07400c04a842102c001481c202c0100011300c24034584c40700b61540a405112400100c01546242da001c0b142c29420114180f4075a034030b100f140d00000c00800c041100140c0f20800103848203a090002000015114103e0a803150803011002020360800010040d034058811b5078034407000c0b8081d5483c0d10003603082010030042030000903a8a400c0c460700090315000703400361588e8203000710007005242c400003088061151614480710b441d15560b0b820b102034000008216003141c1050300300100d940e0300405c001c015a008104000a99902412000c03055074040d0100f03071240100d5260070003034000c403103200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 950329856 1250 950328606 950328619
    0x1707051210030212070503190203030306010c170403030f110d02030d0b03010e12091503060a0605090103020c1204080106080309030304171504080d141303120b0d080c0708030a17060a05 81
    0x1a0780000100f0745c00c04841c6c00701e00f03c80140e0060310702079a406200e548003035819041440001d450f54069807040c1e4886200c3c82e070000801c3c981503c0d20103103401a820540c0024402d00d0b9030780c12543c016000c3c0c400424520018036484030840320096a902c110200000fa040e1076489003511134030f00b508400f001c0c0711010103517440f544055829800301e40000a14610403260468100000c011040c01c490041c03102034500d44209041000549550344069a0103040503801c209400c9600303030902003960710154200703249584602c1c0818050a481c2c0355000001560010454510181d0340001114100d607002c20a0001030f0307000d9503040d8289000100310702818403510701040b0400c1162801400b010300d80007010808801300c1603445030b14190440308441130702003201501001c0f0780112003201880190369004601c44001e170001c20b03404400e44400b1169141e010031000e000c82c00034081e01c809440140b00131401c0c500b1400d8000c010f00e4494800303c04e40800c0d140410130a480e520318402c06040c014140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 950331106 1250 950329856 950329879
    0xa051c020328080601110c09060a090c020a030f020d2007150206090d111b04150303030902030c01030903080118020405090c190503010f140d14030a17070512100302 72
    0x41081451100002c0e03400a40c98500241c1c05600402c60559019455070007094405803102c181304c924203020308880e9000d800f0200018103d506801f41095010055019200a8000785809031540f00e9690b26441550400f144410310154009031071120030004010901d801610031b1f9055040030701c1c80d00420403806081c1e04040b6080e0f00015141d001e45002011182041d010384800c85509410f000130203c21703001000340b0780380c0ea01000180000b1080080c4005580751003500340e400507100c184c2c8202c02180d203c100d0502540780c113001440d5000000c1c00c0c24000078101e65001000c0c410140035468040b50008403065840a40d903043c2d6010306400382c5803907410304015040000d15007141c011002202c079801005103a007449802035904940d050701d11040c0017828080340040d8100440241c0350400007111894000c94140a1408070a105410140d81d4a4000d84801031034403d80302803609070000d8a40900810660200c00c607589a00013008091591f1100192980d2a04841d40041c2d80004103551 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 950332356 1250 950331106 950331157
    0x3060d050319090807060f0c0c0e0153030d060b0405030d02010e0714060d0203131b150e0d02032e06050d0602030702031c1d0a051c0203 60
    0x8086494002038454200055881343c11680e1095075000341c0d0001800b035520041d10714003419000ba00c05120340224201c0caa110440c0c2c20740c0c00070991003e4040d400c4004640f0503c40200107078207442108803500405103400700a40540081c54140302c441e00754140b10082c181d08003d00c26034454103410724040c007441d0364811210585030454040c82c1d1080c050f00160340005401417007020b00610703c1d00042c0181524000386901c043c261211401e401000400c0304100c90122440118132900792204420320b48070b42c1e0f0406061017842910f485da492040300d8000c0c403511303c0401000c80d110360b0615041d003801c01c0020205d400350241d4000250113101d043c0790800305050041c1070244912040101c03240c0c0840c2c034004002070b80e03014440c00e40c00840c41054000803034002c3d001558010518011a40340030301480c246a400351000c0c444076140d6603542615108a01c4001201303450411800080c40790580c15203500d6142d001c180050700c040e40004100420740c40c001d105036040d01c41500d00001c1128a28034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 950333606 1250 950332356 950332387
    0x304060507020f03030c250308040e01060306060c03020709050408040b0a08090c04060e272a0a0302061c270c1215051302040219030c0318060203060d0503 68
    0x40040740305501414008415080000661b0210503012000b8070421860440d60301004401036641f1030210300328407020020420240c002c0c40200f40c0313480350300420340c5003042c002c007112419006501002898039505010a40c00244501a24001c0c00300090686543c501080c0c14829a8807444000c4070118a03e09030580040c8028480e030107003000d4940e80f007591030800c42107400324040d41140100080c04200c0705030306084603410480703121007881e0401400264603480d1801406a81010b9490b00001c48004888001101c0b000c0100303407890b110b19403c0d030303001a200b4099956025000d0780b40c1440e00c0500a4150882030f0980e8100343d100c034142010a0404030f520710101429240e0401d21000010400c080d11010b2001a80040c1403d51401000b04484080c1c400981118401c810303282c062000340e99248002d1000000404402c80f60352a5200068141c6803900400020f2518100081000c9010f80000740764155010000513541c8d40d5030800904605522413019050707100c0402c40281d00030300d01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 950334856 1250 950333606 950333617
    0x31b06040c0807061413030b0f09150105331815211305031207021c020d030906241a0306031009020f1806041503050c0f1203040605 58
    0x1108250401a15001565551a024420080060004c9180401041717003d03000d8000b0501002042546a54907214040514800c0d144030203c905c1c03580030700c140c05000f0001007026070700c80c05040d900c030340c54100040c2005100c4441d54400c0182c00c0301f000352030300c006403410482092080543d0340303c003440c1c40a40c9902c00d1881100340a10f442c4102c544200142c2d009840d002414195410618601004c0945809001a09001ca019200380100380060007e0000c0e2400c818030580e160003038942101c00914140403082c03071006041c8180010303851284d02141e5180c0400003400e0104901030300e0700d0150f00811001d900500c0990300d080540035102c804c50f24070b604039800c0c1542d01919848142042c00c0700d201c1611201e51692050100810b01115a0007000c01136000500c1c6504164030240441e420a02d4030102162202103101040210315252042110000c0840700c40d050990643c0c1d6907603561840d0342e03082480750216602d01a81665071581d212905d0040b001942e80b119901e034009049038000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 950336106 1250 950334856 950334863
    0xf040501020c120c100b090402010302130b0a02010902090601030c0c170f19030b18060f0f1305010501110d0c140c130906060e041104051506160233090102031b0604 72
    0x511752a60040d62035402003550201c8010042d0005444a80c01540250f01680741208d8894420f00c1c0018100e40500c00740010300310940000c0703152030032403042208000004013898107140c644100352120b140d1002c24883c8050740112620309a507d141040c85440c000c00040c42e106090020308810480e0102103c0c1d8a4541e541d201800340c441a401042a90030742d20300c00c020700e2600031000031180e1403e0302061214803800b910034040400c410001c5100f45551040b0480c949031140c004000075648650030340c008512810182c05201c2d4010001000022031050203030440207151030000b000d02c001e100542ca061b0009080d01101d6810030440d0000d818070b5007054602c0c82ca8014002828608440c580c0d1060754003817142d12500301d4203002c00000740300c09403003007180200f51107002c1300b00c2d22200001d0590107140c03014004001d81e14810000c50f01d04804c01c0545010207200107294641030359105100904c00d00000c5078a404200004074070703502907095060506000286480c0341c5c07070404180140250702 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 950337356 1250 950336106 950336113
    0x120905070515040f0e13080703030b0d03031527021e030103120306051e0d0c0b0301080a0b0c280513140913030206010b18060415080a090b0f040501020c120c 69
    0x16200e5542a117500c0031501e180000c8201d010000c00210800d00402c0254480c0c180040c81ea941c0f400422000341d030085049011a946400700c4410061400b14107000b00b62018203815440d0004000380c0c1c400c00c484261900742500030a1900007840303660319541c4541c160160751502d030341c1c0d2070405501d0700721246110f1010920f0303c0000310f85414005140c04100d52100c10700c00304010048180030140c46004005c5d075218507444d00c003003900b400c1a80154001c1c41800001e183d241e00c0f0341031090340d000000e4004002403008003c00c01014140600e030344c0000e400e61500d52103003800c0c80e10a03100d61142c01c010465807a4203580105582114070600c0540820a98804c0070b55a0b544103601d00e02075880c1da0140c0568031141c01004403180110040c080e1009000c400c1c5120208940440e125811039000100c6a83c201015080e403103901c1000c85074441c0321482e0a100c000c900b030f01c503946485c01c040c3c440c031b0036006410001341c01d0180c01d404481c40540504101c41884c0144084010701d508145000c404600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 950338606 1250 950337356 950337359
    0x30c16080c010504030803090f0706110d0207350a08072001020a0b06060904090602030103060c1d06091210090b16020712020a0f0f0311040903120905070515040f 71
    0x80c0002120300803844103031640c0e8030f0309007161a183c085400c020040344491060600f50514a0824041040100361b20340380c40d9035003032100d42d20a040003010850301c070071544121020030074040301107403080c50100c00034900b142c440d4900c26580d8002c180d05402503224460051031800700000840103003c082c1c028009001c0d00c424400240c407039664403035402c50060380881c01c2c0b80c0200e8440c000042e00200028032403031400305440041410b459082d203066685503400f00c01002808880e00400c4401306541c948a00305a446658080440c040c5c1901207002d0200410092815102d81c00030b07400e13a0042c032080707821452829011340060b2881d82b41c1102c45044240120382c4062414000498091290700a403000509041541d801500c1c0b049007660701034800000001da040754140d005016224264113a800c503070a608001403618030b06066135001352314102510010a90140c0c00c002c030080c80c0c00004c1313200102414854a0701985c0d07007016038004082c07a106540201d00a00420841e003405d940c014446 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 950339856 1250 950338606 950338619
    0x30615090e0f0603060601120618090606090203061c03020c040504081e0f0403060513020904030906031a1e0f03060a0c0e040902030d050a0314010e040515010f121103030c16 76
    0x10b51054a04036015801100810041e600034402520103e5514170001901039903910340300030f428544209114020b90341d5020400b404040d0041c03101a0042213410361544c103210020031081e541d4080e461207401d036405510800c0620a0107111030110000780140150304260619000591056464840d164900c001e040c240c6603458050f00c1407101e110b80c41c07a040030707e9603c0e140054840145603050200d41d80c2c1c10100142d51380e0024a002d41d001c0d9aa0501e01ea0400c1c40240c00c841142020708800c1c403801600c3e4126a40d07003039802c208021a0302a998454820b0340200d809012362000d8254103005404c100000340c1c0b11a448080941e04999901400c1c00555040c84100d48800c88013940540000e030841240304e000b50010f150b5040103140c0014440b00b4058a5024000f00b03801608103080942c0074001845020082e41040011508210ba4594504038180301545114405c071459040d5846581043c840d49202d030502040002d415250780c1d0360359170f54194642e8960035404201804209022411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 950341106 1250 950339856 950339881
    0x1518010308040b0c0a0f03030b1e0d031116030602090102190803040b0c070507030b1e0f060103050a020735070515041401091a0106020c0603041101030615090e 70
    0x403650401101460141005200c03401540580d400140ca88626010140044c0d141c0c200903140d0b03400f03550b002401440103001c010381696294041d2441c0b61072103006840e255912280841d030287d041c10544042005003400ca410f0058090908107008d41d491400002e001c100e070010032080000f64252404520300c41c1483d22001260880509000c8041c4001800558100c1c501078000c00703c1740e0424284561a0f444034500311aa4200720385030703042d00c03083c020040400001d10f043d048003242450000c1c6032800140b0a02500107040380e04040c3c4030008546948860382c120391000350060300902d1015110304c142540741d60b45103007000c04429901d0340c919504070760605a84c8016400b4014142781080310381c684030500406441581c070803080a243c0e0100703010034452220302511500212517089204140d039052a07005034414015500700701d00140c00d40d0303a40760441c0d84c01070303010301090b807003055900048000f81250381007440508910f410202e460394000d40c441044415620b0b0005080e521000003500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 950342356 1250 950341106 950341109
    0x11010504080705100c08041205010605060909071d040204081617100506011704110906091e09030403080307050421030509060c0a051c0801120b0610030f05151801 71
    0x10103402c00324042c0b1070742ca44001600d0070b0703200e54501031015200700e48582155034016409085110702800580c01041001e004180c000c2034200c644a003010702c03603000b00304903000041c220410404c1841d07007464480715915140c410764401800454031991600c040503a12442c8110089100c10111000540c0c1d5003a103003680c02d07041000c07000d84040101e440741c900c003511000c0c1c45981070005803000f8055110002c111309200c0c40c051034030510200112024003602c00000b91100d401130701d480b8100810241405004445514000142c0030701360b94044006045000b01d4000a103007000000c24002001e0740300001d80103032820704007561079548101074001e02c40401000c00502084080c020030802c1e203401d902800054451106950441007650369403403c04100001810707a130200744030811560b551254845014004004500000000301d0f1152880e40030001d00b140c2c407902c0510110341505219401a848011320352030148110700344100700700381401c0804003590241c3c0021a03081500503140c50040d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 950343606 1250 950342356 950342369
    0x9031e05072004020a030c0e1504050d0609050a03080105100c05060112140105010b180301060806130302032209140f01050609030312040c090509070315150e040f11010504 75
    0x1071038000c00b50785520b4074a401d94120607007841181481c0090740c8581c001001061503e5800081c204c1422002415403c042c00f502e9008520301541260314400040c1240c06441084414040c0300d440c61411002501016000511600608001c0780806410a0616068850441c1c0600189002c0f032000c880c3d03410020405011360b4170100c01003104503074000c141c0c021a8000d00c1140503076051110324600752402070388000340c8004002201000110500f101082c1900c0407002801031030703d000145e40e40c030701c0e0103452038000c5e12070651201c0425000300201d40c0382c5000c51011051443d6004a003000440c1c00788148141ca81c14450030072007030406070b021a842440070f40d0044078140d08007001c0c82016048000d20b41d4051000300201010401c602c0b00b160300c10b0b88103403400038401d410181032000340ca601600b4074400f81d0040c28103000090607200300c1d01461501d0b0f00f00089401c003000801040c24100d80c00061a030a0080c1404144018011001d40160141d0301c28a600d0216800444030752180348143c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 950344856 1250 950343606 950343617
    0x60f011214031b07090207020906060a03020405090f07030c0e1020101e020705031806040905010306050412020606060f03040c081207030212092107170109031e 70
    0x1031184449010300801601c0c020752070101030314004000146998001c0c00b0f01034081c0a15400c1c840101010407804018005104d41581420510b5020940014029010307c1c41150040b40303041146101c0c1c0d05503402454020007400c410b007080c0c2c990402e00324068403400c000078282a01c1c0a200342c002c02541e41d90b410040c0032400d140b01c034000c040314440b0b14070510401104809880181c00d500c2089003400111034484000707070714a00b0800c10000c1c0b05400d003c00f1100c81c01400001d003c0342011003540c01c0b00781e80c441d01d284603c1100b000540c0501c129041204079a140200100901c203081e400a03100d10b10070a02d1544424000e20260fa991400b11030166008401304116840381440602a5170040d11480c40d5154841d101c244590414003a5000c4501a0102251400034154101b104180c107000041440f440c211000d400300d07080d15031122005400020030002c10f00408030401c4010300400d082244422804420307903480340a410b5442c815070001c0c6075801203144e11140c121a84000d4034064481 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 950346106 1250 950344856 950344859
    0x70609030c061b02090a0b04051602161a0d09050a0303020304060f0b090a02090a241215030f02030c040f020318070e070c1e230c0a0e0c040906030f050609060f01 71
    0x1700400c904c001002525285c2e11032240d240e65803035900804d0b0284169600b401e40e0006001c400a03d07000340320b1041c10042e80c082504004407900543c40c0314542680403c5151b40d41610709561000d0010314000500c680320300d98010382070552641c090340c0101d03c0340390103008803001404003000391480052165805000c0c0400315416070a10703030040c015040c02a0019600c1070359235444d40c41c003802040000c4c00d0002c0d0081940c00c8190f0250100c0c060b4041c207442000107450008000703140c80318501004101100285110041d507a041007815038940300240144a0300800d51104c9019410640301500c0514901800b95081100400c0300c10540d441c480c02c0303d060f036903007400071902c01034580d03000c0e83c120410202d40300c850003a01c080ba4102c4c03130089100340340c01d1040d0b20340e8a07904412401441d917190042180e281180d61407800200454501441c40c440030b850b0341a2542051090382d100d24030307083c6007840010800041007003e503012800303001981e01665a0a294a4030341004a4035000281d100a00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 950347356 1250 950346106 950346109
    0x50c070e060103050c07122010022101120f0828020d0f0210150e0c070c0518280e010b0a06022d030405120a0209071103040e090c03070609030c061b02 66
    0x6025200d07450314560381d48c5009002801e142002803c122040c0b402d500092030184144941c84280420031400540280070742c9029040c12080660030300040094251b0144c1c00188042041940e035000c042c0f81c00c0303d0703405001480340d62110f22192502ca002d8011500007000726030058451046022268002d0710344607042800c494001d2410500212a16410110208219030000c80c040e01c07901e02c240e042070351980a81445050141e06520580c0b05080030b910b801007101071040305e1a004a003082080310340440c92500c501c0c080c0c9168108500c00f528286001e101c1d01e005412400e20881c0940d0042ca517503869020480c2c40f81c0d48212a042d044403003000c180759003210a51410001039140003505e08203621580042e4440e1140003034404258000b140b00010b625003a10395540005a90a1504241740345110301e540302d018500c214012841074400080b03c1d9030342840341818410004050745d84154071008043c00201c4a400f090715800a441c80104015000e41859540581025095542c400c299030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 950348606 1250 950347356 950347367
    0x1305010305060d1205042301090b03040f02041104030b0a06080d1803020a09020903010c0806011b060e030403030c0b09010209010c0f1a18191a07050c070e060103050c0712 75
    0x2008990000c00f450445004100d41458855550703c0755a902035076580b030441d44290516000e0f0021444403842001c0310340c50380c0c00140820880e424219610380b41d43c5c0b64240f11220702c5d207a801c040d41040c1058100e42450030b41a000300203407441030103800ca007511a4040b40040b42c1c6035000c0d2251075480000c10102480c0500c2941040040390035807000019120360108031484d580340d000a11a580106040425240038003030304021000c4c0e4903021045240c20000200403100e1100b1a041c030140c803441010620001d40c100054100360034042b203584595034503009004034003050003130b1a60006400405d0500a041c021190b0107034059607402c00701c080301e4445043c540ca000200315080d4080c0f10248140314918840d0394407405000038400506801c07605154100003c280000c001d06090203081c3c00010458282d6242a212030100c6458642c0c48420907116445100c4505403640325440001503001200c0e51a684964001c0c1d03824001611000c85100c01800382090090280500814500700c1e1407280 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 950349856 1250 950348606 950348611
    0xe2805060903120a09050114030411090c04080102040806060f031605040203221a0a2702060c030f030403020c0a03030f030b031c0509030606060903101a040204080f06060102031305010305 82
    0x40a030341402c0060340220300b081c4e0140d01148040742410408006661308441010400485240c02502d103141c07030742d1000038545041c2000c5116483c00b0010485d0b400750841a5800f801c00c0300000c5540310385881585a0b03550b02103400c9031203007100c4044289035040126807201540343c900c0320602c005003043d08200194000401d140090b071700042851140031a001040900c0b00d0149160b400240e048a20f5901040c000400e4554014140180c52015a48000c01f42d1000760340340243c110b08038054800100b0500c118187c44405101c0426510480b12059008500a605ca0303000c80380100000d0f4103102508800c2c0c4805400b0501c100091042140a038125070702a0000506842c0b10b14510041510025412400c000c006000881c1c2d0810909080040c19003081d004c885042c200207400000a590300030001340748a400380c84941c1d04034451082840c06001c414000c0c42135440e40e0321141429968030307603100c48105034400c1c10007003030080d4008403c031a2114020f00400640d6410900154040d0001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 950351106 1250 950349856 950349859
    0x80a0c0821070f021e19050f060d0609050408040e061f0e0312040605131e0302011b0b0412020118020603070318050a080c0f19170c06070e28050609 65
    0x22810040145e4450044e80340d00708517550058004001401400505260200710f00c00c3e030b130b9041e1010700155550022000f504401164905d95034071091250b4805803081b54070041105c0d042c4000d0001704007038000504180c07045a86522869600c5108004610030b5a1314034030600804d1001d0b11002c0d0b0f10072003900580d0315000d000ca0714501100c50440d001944194001400a1408101d0340ca40d0b1080c641003400629070141229200c91091010620f0b0f075103103220003811301c008891450040c1c404d035101d1400d010b40042515155140500b800e10005203403072801c4005500e05490800201c0310242c0241d00c0c5e98003e0111825580e0b0400c0c10f40003030103a070078080764040340780c020713030340010030401c1035020080c804d400c01502d81941c10082490007405403101070791a0400c4280480b03600c0110a144c88113600001d8102400070350214a039000d21680c0c81d000d0307050041d5070801044d59040821100417090940748100354a1718503405076425081c65485401103288400100500d1600c080030b03020b203810 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 950352356 1250 950351106 950351123
    0x30604052206020a020c0d0503040e071101050c070c080604030e040b0402040305011805071205060f060f100e01080717010e0601110f06100614220807080a0c082107 72
    0x10082407484141898001c2140d0698000030400603442c0d0500c80049851130944150201c0f05950703a4545d203901070343c042d8032020008000003402040c1b1400030110142e012200030882e0703082c5031350409281d40c00310350103403502a85400001480040029241d1046030996655664800c6000410002d07012503001d03694015000e100200203c1c600f88900c000020701441d19040aa10340d14266040485503804088102c06c0c003540382001c60800300342558440719010300083c86a07180b80006289840900805030070000c000c00e41841d2580103120b803904460b0988403200203a440000441d814501c10500d070070181191801042121110301019030880300505010b019407020424851501c550030400304050340c010b00500045501c2035400c1e4000d0009071801140116006080c40c26034820040d83c0f45262044000302e00300618041d00d104040d01440f0f0907503120690b118a9640e0b1400c51341e106840e500d9080d10001200d100000782d10054405150654001c1c1c030780c001c80b200b5960021501aa036124 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 950353606 1250 950352356 950352391
    0x7080c0a180f2603030c030408090103150303110615030a020405090106091e05010602150f06010c052a0d24180b01090507021b100c0c2603040b03060405 67
    0x10340900902c0d010f4500e00e040059408107244240c0c8214140d05802c25880e00704005010000c11190202c0340e00680081444c2daa80340c103600100e00034003c42e00301d4019035404a13408001c05600c41c034034000800d028403c54000d40c403444d00c070b007400e0100c200c00d40c2e0b4540d00505c00c0c034006080540105503c0201d40c400000c4881d503400d0302c002a00c52180023040490100b01d41c40a01c2560752140310f01401d210710080c80100c5042806060061001d441400040080030001c1d00d80d80c803400b000100f107940281a1480300e60800f00e08005082030007a004038030400c024a4502c5800d20400e8402d8a83e0003014203800c5102d4134101140c1660b440c080c05d108075498a480c083c021740704c00c0c000403449101c6c3c9480403403989440b8450b021154050400030441d00301880e0040100071881c803009054004480941c0800c14008050303610288107580244030452030880094503401207118034401e54900f541c000c1040500140f0b8648902c1140119180c400090001c264941450b601c0b82d03900024000c10030f407050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 950354856 1250 950353606 950353619
    0x19021e131e020406020f0f01150b0f191119050a140304080a050604031d0915010e0a0f0806010e0c03070f110a0c061103120f04030c12021507080c0a18 66
    0x383e0158120a02503444104000503144003013040142c3e43d1030780e1f00208801a0b102d008103116220700c0c41103188480020659100c00000c0c4c008440400d40c01e01c80c0744031010740ea00800741421140b02d40c03241c114020b8003410300440d41c540000c08560750380040501001e00c00c0369501c4004443e82203000c40c2c01c0c4010301000c201da41d000c00c00482214000c0c40141000c0c03034586002021440320790890340c110756001c901c84802d503d03280c0300650045156000704a03848842070041303d495071840000c9510032096507000a0f4006090500310030354850030145c850680c1c0b2071803c0c00307021f001034520398034401e0100700003003a040c41060007015440300d0f4038024600b030542810803442c00754000c400384c07200c0500703a10800842d50130800a500000050000c0c0d070512007002030303800290200508070710401009400140806120b1000c0f40100c42d030102c1109645a00c15000944c3c1d00b4a4250700684401c55002140c2124041d280080c410500d4a40c00d501c0e0492428088954000000002041148420010880 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 950356106 1250 950354856 950354861
    0x7050c0d0f14100b040606170c09061315050f04171e1f0c0c0f020d050a03050316300e06070530010509150319021e131e 53
    0x11650102c008180300c1c500000c90104650104080b9845149007000801c074013600700d2411300c4540f61071400c01c0c0c4036540d0f040e00318203648980c103c4c583d800907002541da0304036182c0020070800c1d1b0b440700e2014640042c071101c0c02c5d911032050b4a55200341036401d00c820088044480340d4050304801702003e48415050a00201018800400c245002d07500010b042c03410840d00070011850444c3d0b0a901400203200d650009441200b42c2c6801401d41a011089203065448811612000d640c4c000200d0700c0f450a58200200b150300305032000140c01c0d81c00c0c011116498807400100f452401c29000b0400100300c046081e651409035004000c0141da140c404894000c0c0041c41918030a160300e441d49035840798000309000c0301c201c40009130300d007041e51000300661041001c07240720f0540d0b9081c0d55013511502d403010344103100401400e40c640c2c58403400c083c010f4621280001c0503032081c030a40340350352001c0d4034a0080e4940c080d0864100e4104000200101c1030b5901c03030f00100b540030b00c8549030405001d03100540c50103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 950357356 1250 950356106 950356133
    0x40b07030204090f0605091e1803090d06200903030a030225060605010e0607050c040c2c010305010503030c1c0521010608090d050307050f0f0d0501050f0607050c0d0f 73
    0x43c4555074031805c06c51810002c0407203500a900f0803640c0d001401c40e403009103000314003a001010864859003500d0f5810000c00c11101541c4006000d44001c4000b450848040c09221048880103447c070364002982c6030300203040d59800b00c0b00901960601e616a04118025003002c01866664a2130349050001e014021111410903030050780b0216180b030030300c00050900c00e00c3c3c0c00024040d07081042058045a00442c180303400000c210b501017400034180004590382401d0b6820b4040020b803d1185981b0306a84500c02e4516075020380b01444542c0e6240200760700c9008034081c440942e08000c0728154071601c030a8828680c07800c141400350801c3e0740703500e40244001c8550a020000e02e55040140042500500402d07440070b140c00c0182440034003c18010614000900702e2010310101260601000c01004143c0d1020342c0002c007466200d20722807c145001d00404c1c03141a0099042d000700000c1403e182c0d04844000b900180241480764141301400030850078903034143c6146580000020008915a9140b034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 950358606 1250 950357356 950357381
    0x3021209040f022d0a0e041d0d1d040605130c030f0903080405010e0a1709130f02070606150527030d02030c071203120f0f0c020d11010b09040b0703020409 68
    0x1013440e24141a90080c0d00c00c6081004452901405241901580f12031010029501514040303090204602d45215110300c4a0031381c14140038451960002d5a803212a0042c96540d041c441c2c25540c99160a200407644203003e000d4100d040c514103240f80c0ca41c0768109850030985850f0006441c007169a4817801c0760f410800c21070014220500f803005100c024051003003109202030152001c116a69120340060391481d5440010741004206640f20b9074502040d40c0c0170058070a17040c045100745420703030402544030a5007141c1d2240340040c00b1402c40742183e180c0c070089403251111482d10b1ba209a49100e803505244c1000000c104001a010443c0c400f403007249101e006030380055464030220307483c0c141031018a40202c0c80b06012009400042503101d180f90710316860002d000030785400e2410404010304078040d616400c490600c0c44503650311754001202c003032040c2d00390790b200c03152204260268240c480100205a000c1462030115000c90106950715410841c941001803030640e80344454400c0c6d5108080d0075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 950359712 1106 950358606 950358637
    0x3060130111c02030607020a0519081e09010909090201050405101806020706111f020912060c070b221e020a0806160c03021209040f02 59
    0x12065160241c803440c01c0d5030007141e10020b0190000b004074041d02c5070400258a162010a6841482e54428041c000723040124040d5400f6180f04001507901400c10420f00c460400b040c1080e0a80c460b403c0e084544a8415100141c465010390b808400d0075800c180307602e00180e9006044a00755042250080c041c40c4c45003100715880d0050011411440388010b02c0850601c0e00001e141080380c001d81e4495401e1050016515120301703c250f28400074070701040c008511213400e43c003d00581e203409413030b600702c0811641410340340c00301c01c1da03c0105061000901c80c09020103604200c0d4000354120306001a03000e081c00841c0c207000302c0c0c03601034a030341307642001c5681841017a5144003400303800914900301203480720411a01d40506a4205504100d03034001c0e8130203a4002c8003102040394250f0080c00c00c04d094240150032170340c00b580040303a200b991075040d140c05269a2000d03008004116969 = true := by decide +kernel

theorem cover : BRFrame.Cov 950179856 950359712 := by
  have h0 := BRFrame.cov_init 950179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 950179856 ≤ n) (h2 : n < 950359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
