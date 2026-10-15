-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4186
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:49:05.075515+00:00
-- url     : https://prove2.me/submissions/8da93d1c-9ff8-4588-afc0-7d15a37e2c35

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 752697841 ≤ n < 752877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 752699091 1250 752697841 752697857
    0xb0105040e07030b04050d02070e09070527070e090a02040b1c110f0c010609090f110a0b0c0309180c070b0c09060a0809010b030d0509150d0905070305191110 69
    0x1c0341540b40c1092007188514010240581c0000d8028202704090340030000c0080c040082c02010035010031200c094074002d840148402d4007200101909105950194410000c40070030b21481c3c0f54426801140f03001d003510015250b13100c032003801003240300f2071080c840600301c2401506d04464211801440f41001c465002c905c20500364181c005a60107030882c50480300c1d0020307010071040700c2801181c2c010440303001b082100b2a15911080e02c0ba031000000100f0f0440e01d117114581c1135a944451130081c1c030400d151540c0300c0070700c840c0103560782e405020350602c40c41924102c0f41d158000110130510070700b2251606c60420380ca0313079a00d18500d0b0019014490b044802c0c8440d240d182c890801070610118542d0b260b074058100170400600b1140c80380a0140650003001d003175210300345c00c401114280f1600742c0f00c03151105001c91f260a03183c061504416506800c0c40140401e022b000580c41301505d01800907110920100d200f4150030026195004003c50b80940f0302d1411072030007110420700c2000c10304003075803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 752700341 1250 752699091 752699093
    0x40c0305010c260106270b0a021b061305060729220803070e04020409020d0506150c1507110723010804080d052a0403031b0b0105040e0703 61
    0x209441d1110034500024090803a000d88003c05410519a0602d40541034030641d4107010307000f80054030002248a5081200c4106000c0c24806402400204004c9100300e446200060000703441e0b00034028410015040b00007805030750b01d042012100c40c0e40311508003120310b82c9071009025464004840541c0c140741d80e210201d000a95151046004100b00b600074101d51038881d000000c40404617001c94014101c0c82d800100042c50740b400ca80c0c02100310b05105c4074815803400002c02030304c40d54000da50303002d00110320401c400c1415040035000d0031040381e0004075000c10740c8403001a402113583d46140e0361f004035000b400902003035002d160010503506e0200c9061400d840440e10f0241c0c0c0741c1c0704060501444408411890030b4694071704104509282c54000b42c18151503d500364010818002d030320640d210081007000c0364501003081000e0900078400d040c0415014441169081440290302103030845044000b07070302c0740d01450202e07654421041050fa908100920004004520030010148101c4030040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 752701591 1250 752700341 752700343
    0x2060a14010e3d030b09030307390804060e030d0203041203030605041b03060b0f0910110607021b061c05040213110913020309150402010504180b030f0c010f08040c0305 74
    0x48000c400c80b104182d40744d1039032411000d43d01005000c540c0c541c07c00e00600404540c00002594007401030072500115540404440780101e0104101075018001c20044108016841c6c02400c02c03141c0b15180d00340b0f40e0013403209041c1c40706003414a5000580040100b48001c0307201c20000c144017402450001101510780020030f080325581460350a0411705c200254000c1f40d814000c8202401050310030030b080003106400c140482c0542400300d44034040489846500c40d100c0c0403542250503010301115024209404040d44803000325051007080c00c1010002c2d007850030310404507841c0d021040c071481400d0a580c080d0400814010b04100e92101584024041040d07640c050410f4403070909031042d9850001e20200029100070360000d150190061042114608010230300007240881d840c40d400242d500c6200480d19031241340c115155544515600c001e4000d420f9005100c1c40c1c03410740032210501c203100b005c03d0b170740e01c3d20400442c0064040901006054411000305420501c100489000191a580c0305 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 752702841 1250 752701591 752701681
    0xe0a0f06080c0f010e210307080714070f231f0e03190203030702131e06080d03060b091c02030105010803070b150d0809010c06050702060a14010e 64
    0xc440c2980448006082e620344440d035a80301c40000d00b8004079000040004c500740c49011009000030042c80305101901400510854550380d5201400c180e503043c642c0741090381140040541c10103881000000f103030050100004209440c0d80d0821003152004182401100c070328104000358100710745a034110256401058070180c00d42194a031549a118840145880c0c600000102e44031191071800403005614080111000703a41c0554900340c040d601f00c080700028001d18191214141d032140604100712007140e1009061720039035030544089003604074080301070398440d0080900c0c9500c20485040c845c90a40c0f160303107101c40c04180000c1e808001c0e0300000d00b1540240d002060707035040003a00c1000c200e942c2040720751281d0030360b282d8403180074414003180d1000441d00000703040a00000e040c0310103a011302403601d041540100c0500403031401c01002900c1d48001e8030102951402c2030b40e035014a802c910042416101c6007150481141d480c41d030b4500460150901d00f440340080007207100401a404050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 752704091 1250 752702841 752702849
    0xf0f081023010e160201021905220b090108090102090a06030c021603110103061212080c120921070b0f0604091b14060313030804021f0c020906010f05040e0a0f06 71
    0x4006201e10705010324000740c4c00c0e440341402c11a441089803892001541c40700f00c1c10711203203181c01a11606801802070601c41119182080140c807460005465002c03880103000c080001c0e6101c90003a1240f8685e80d09030301500450f217038410f942140030302c01c00d0f220b07038000c01c0c02c92406d10440d5810050601920341c401e000390000da81541600f18086555605030080f007000b863301010030b100b5941d580d22011342c00042030200808018081001c0358000f01c0380400d4826083e00340045000710704000e010281d540007811420040543c0100c2150220841601950300280c0c01100c085400c3c1d5401c2c00c02511100002c0043e07521a6441c890640401c00c40c64038103414400003c1814410360922441103409016004601e206040c20402c114001c041a685100b0080d49420000707140e0b121840002e68102c2e19007103102403059254181d441003940802c030556054000c0d1181c44660b00c0b4400110345010741c0808001c080780307042000300700648910000d030b81d2080c0341d0400060034000400f15941603030f207103500c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 752705341 1250 752704091 752704109
    0x290409020d0515090709090c09170a12030e0a0209040f060e0a0b0906040309170f100c17090a032006040308010e090f06010909140d090f0f08102301 65
    0x1c2000f01c0d00e51250b51201400d045441c3c03035003450500002061081940611140c07152101b07802c0d5010341c006d00701c4101408050703c410050741c000810460350b0b80c00d25042503506100005180c44224001e110b02d40c01807203c0c0f400f03064184030035005c1c000304103009001202d000c5102100c9001141e000e20410020f040d41001170841481f0340d0828260030a40030f49411201e40000091000090700003140c00f044a01403031414002c8101808890700b061241034072080c0310b002d0103900c8002001560b0041c07010841580350765130b00e0000c1c6901000e10300021a83c50401d5400110000082401400c0340c031032a003880041000e1250803034036a10308142c010759013100400c0f80c1c0001444503058111010340e011039600001c090171204004e0035543c500061141380d24107551100e0303241c24003502c0c0e03070058030504590084070036020075990000c0607513440348240100303c1000000030643c1c000d1228060101c60580c002401038a20041c0814010031603c9010102485c003000d2840c20010120350312170003008481 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 752706591 1250 752705341 752705351
    0xc0e0607230319050309100e15070e01110f0a020f0a0b040b0405090f040f080c0102130e06030c0a03080a080a060806070f1b05120307030b150d060609290409020d 71
    0x410140c41c0c003e400503000c400d1060a03c2080701c0390a0000d4000d10034518014007050307009607000f1072810000003032003810717500c10344100300720300c69401c840a8250007000380da03603802061017591400d8031600032480a007510307001003c4583c05032900c5200e0620b100303402482c8c214803c0e80d0b19040b0402d58055403000f1014400880c00308802c0c4ae0500c4502c0c6c0c0145551802d07011407500d82e49807401c1e0740c0d1030b19004103416004100c841e0041825815110060071701e00125801649405034480107000842d0340d40c0c4603101d080030003980745c1060481c42c41142d40c0400c0103130501c4182d58007994041d00091035480d4165403884005080d41c03041100c240510311549404070780c00e1b50088001e08071504c410012616414070170880000a4001569a8a809141c01007644944800d0720840251010389902907000040400c5c0d0880442d0030001850451aa15400c002c0c2683e40c00c0d050f42c0324002c034421080d0341d8646040c2054000c4805412510708070f01164400e141ca500ca0540710101d8102c06090320010342d0392 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 752707841 1250 752706591 752706607
    0x51b0f06071103030406110c250b0705030d0504020f1e040501050f0a031704080105010b1b0606010c032303010f030203070503060609070c060e030f0316030c0e06072303 74
    0x28000c0341d070020610b10301074444021590303119680f0b00c0040c000178034241d0307198125121a6244026910015012429900103862143c00c820318811002c40c1030100d980358a00c0002c420241c0402c81d085181e00c1400755003440040060b0a00401c030080c010b0f82c000c035a04900003500d0382d0304050350445d00d4001e001c50044040420070300044405c143c014a0141481d10102180383e81c40840f2102102d41c00101c4541c040c440d0040e110301d900459001d06034940c28440080f44400f1100081c2135480701d4190126190b10b1065215607444034180c42c40750209140b01e924402092042c000005c000380540141191090341d0302e00d410003a4400d90141032403481d07041c000d20452509200301c0000f0402100105400c1c286075000401e0310001400000c02e2007040b03090b10003080b4141c0c0140032080c140c40700741e9444502c0502129015803040310035814400c6803208a05849000344200040440c507a56080c0307940801c002444025400070a0680700080c452024400710301d064401c510414040070003071f580b01c07404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 752709091 1250 752707841 752707843
    0x1e10090b071d130f060b040b0703180e160315150201060f030203060c090310020f070308060409171b010608011a090c16110d0b101a030103080901051b0f 67
    0x2d000107420000704040221499661103594014841407010700002e003c40103d01e040b001840603a0007610345a50210700020381d0301802d000340588c075003c1e8440d05000c214800e2a11442c01781e50042d03010014401001c2440c40e80120076a9200e5080ca060005584005a404852400084d400030003a40c1d40b01601c961029828000e0400410449031a01c0c03001d811580000d40745c02004000341d040300004210f07916180c0d41042080e80908032480c3c02c568440c03450742404215400504e0a03070115017840c001c21400d003094460700280b90f8011004e00745d82001030b800c42ca110380c400448100c285505001064031394100307101d50300c001c1c50703824000904204640c803040403000880b80320034401d202800810503209042c200304c44021601c104c00390111049841c0c800c031162001203c49410400300b640b1a4204001d040c010760143c401d4401d0589100d81e00c21030550002c0030582c0030068090300740300400000d039040c0003420400505042890a10300e00401c2902454145100f5494940c0804030407040030310 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 752710341 1250 752709091 752709107
    0xc060105010e030714040e031612140a051b100e0a020427060c09030b01171e0c092d10120c150221090406171e10090b07 53
    0x1000f500a0400240341240e4020360703614111a45020b16219248450700d04000e004554a0082d42e0300c20309000032481c00c2c04689030945212080200785020500c1088080d00401e0700e2180002e9520302c0c0c90b102d8aa07041d0b403508202c04a500e0014801c02c03c103401c0b840514080c11100081c4e00c80106000c050a0040000391105a640b05040c14403400345050850305105a41700881e4002c01c02255001c45101c04461078251079001070030080c03e0b000007050041c00e0301621140280c08408864448005140c41403038046100388402866119240301460303820804500c4d6400402240382c0c0b810301c507501072419403184402c507000c1d10603101e023420070008690390826200505000d43c051142200555100c084507207440c0201a20399403010403040a5031b200b040703030415240e074031520300c050800700300c0b002850307900710a01040c131450400c0c04c041445101540800800343d6440003d043d0b25a83c1d42d40041f401c10b42500b013056601500d04c040d0340c410602e00070060501d20440d41c5003c2d0307141c10040100000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 752711591 1250 752710341 752710367
    0x20c0a060f0902090609190f0f0e07062a050a110907030509070b03090c0307030303061805061807230316020a05060118290910030f1e0204020c06010501 67
    0x14a844821000b40e01d80c1340f070140e4001c10170780e0469216100c01c1544040c046031404110f000a041100583e89174030030340c000501d45102c500d01408000c3c1010f00041d2264002c2c000c103000107441c0100341058640000d00e4500e0401e24400b850007010072900d495003000940c21081d9040850400b001d0130700c1c1451508558400750915080040b800c04212843e101c541c644166541c0f550b0200108900d440184682c920a0754001c0851320070958926028014040910a4420545448102400e002201c0c007441d072241900030052180780f0918020303081d800e0005042102001401d410050301c12a4203507652800042248403142c4a19150b100390401080a9101c9003c40d04503c1c412400110001111810b4440d4041d002d02c5000002079801e004100c81e85030301d100c000e04140601c08443c030b60a00300d10800f6082d65285d0056403200d01d134107040d0409106c002c1c040700c0e071810f180d00458100302040c90141a0480d03641080034660b000101070760404400201c86030000b4004000a603044000c0c02039007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 752712841 1250 752711591 752711621
    0x2a070614070302060f0a0b0d15150e0103150b03030304060b0a05040b091303020c0a060c0b010801020f0706022203051c030c0c030c020d0605071701080115051003060306020c0a06 78
    0x10020542e0000d49500f00038061029541500300482e031584000d41010341c4800000d80440001551170030144180d1885a449c1c003059840d1543c1d132101c569603e2000400d0318a40344840080743d103507a4513508a410110040100143d42c0d07149080340b5a014001180143d014010200e08254401d08000c004001544918410f034500f110480c03460f2180b02c01c0b9a4442d008100303152141d50103040a07414100c951542d15070080791010301045158002c0c440c84601801054060003a030388039002c0f6401c03842007040365a0320030b0f014490080000c001e60014094082c4540342008142140041080c40010070341044070381d5000041405002e8404500c001021510b515042c803c0d208260b601500300301043c82c2c00b50401c8450f000081c19522000b0140e85c0403944061304101516003840c00424440743c03842d61400104503003000151400c6c050280a094040d420b280c0e00740c03185000100001441d006401606240d140d05001000c611a0710240507204410f101502c0030300c4180c42d240d800c0380da0321203269500f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 752714091 1250 752712841 752712847
    0x4060914210712081504020a020a06051803042d090b040e12090420070501020a0f050a051801020f010c021606031509091a2d0405060c2a070614 63
    0x800d8116008200ea5211400c2211017034031400388009144400c0e0011503045400021280d0205600080304c80c2d01d280160350401664440c101c020b12030607034294950034680d100f0f100c1400304121130740d41c80700c00040e10380401b0031011529072442942c80d0306038404c0352000d584500c9a000341c105401048400c80703044010707060001102d00454418041c400c061401035a95401d200304640a00c80481998001804071a480f170480c1e00c1c12901039407018181800084d1000e6114490501420640e0016840c1e602d440341402c10800030a90b041c244100c031241144501c0c411400d54a000307100b00e0b61201042d03405841c040c0c0700510750340e401c1501035200c20100742c038140317040c000c078010030490704142c03482014041441e0409040844101c2c80a01070079000705810400d004500b104c0c07510315010040b001201d808003c10180b10680c040c0d104982c0a00355402000c000b65408d03035a0402040c0405080445d003040d0a404901c080c009610324061029540c050700702409200e4115001c0042e802d43c42e02580d00e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 752715341 1250 752714091 752714093
    0x30403111903262508150d300e19090c020c06040f1d090604060509120a05030a0501050d0206070323120a0c020601060f08040609142107 60
    0x600403010020701003040c81c40e03d01c060907004030b10303950718a080c40803001c0107420144800c001114807610013810380503c011455005a00490244e84100074900e8411407240da100d040c8034105050a80440d0580601c40079800d840380d00018116041031880d414444035030925074082c0806424503084c2d0300ca4400d040d050a500c0c0c00454010040d51b02e10f841c080343c180220701c0c06034a07240036040d80700e0780000c000c100882c00845035500c900441e1210120b04801a0980000c01034808007959407040030f4000000140c0422000d811035a0011800000c4075501c241071420306459410800c0500c001407070000a014401144c1e0240c14007429046565625a41d00ca50004a13603206004005040c081c00004042e03001d10a041c1004a501c001650035a0b1482c01105445000da01115a113542d41e1030a00006103403807001034201e050710940c1d180c2d042c6044100e4415200c58200510898607562201510b07000540101182e90960010f00300400030800304800c0c4d0070644004103c080c440c1c1e0390030b0005130 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 752716591 1250 752715341 752715373
    0x201150519090e03040b030c130f0b12060a0503031b0114060a1a040f12060f1b1d040608060f07050304030806062505031305060705032b1103040311 65
    0x4070072a01488000151824507140d00d604601450b8007654000001000b08003103582084000e0600c05000c8041140107522040b1000b403000c124001e034440c80f001484080d0400c0c1041035800d0300300e000113080c1e610705591140040c3c555403081790b401140d5003554451421401d024090a042c00c2c03080950702c040b524000022800402c035600c00d082025025105240e001e034400303800c4501038046e030b01035030300169224184148034a801c00381c12180d480c0340c207400301e0017814948038a1403103100d95400c08a04c450310580446120400c4028206034103001000080719980ea4819100240300c540003600c207070700c3c0002065050510060080003446000c008100c000307580611040c0e03009900f1180242c41d040180c0f040643c45c1034000400414080720800c0805014001014112401000a025441d2510740b401e221103406080c8004255510034003000e800c01c00c00d1501c0c40c0c1c0c01e8800100c4600000010f008110603500400d00c4c046101c4800005c1c0414190300c2000e400d07590030010010515400780710141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 752717841 1250 752716591 752716639
    0x1e060507020d0206160506011d13030c170904090f0311060f04020d14010e010506240405040203130803070c05010f02041511160b0c0d14030a020d091202011505 70
    0x82c81003000044100e0b1504c001041750030710503000403c560096854108811241307203d00517502026042200140684915980a41c004c0da070503a51205030100580c5c4070603070482a119038101c695814007825540b03032680d216211080d030041d442058502881e04003e0710b4803c0303a112000ea190407910030442c1c110300301d10407141c1265054079402002c02840c2031050041c0801c8924041c19402c18600789a04101500301d20f0081c3c0d400c54007002c6031070358a480b0395034030518201c80b155003180a10040010349082d9014540c04502c140403500e081071107a0320100c0135401142e0010108038495080424403800b446204030b042950082185402c0c10017000807404543c0c20083c0d01000341c4800c40d00e40340c1505102445c960400d001d40388501985a803501c0d900c603000407900d0340c198410201710410030780c0b1a03e9210b46588200d180146540ca4552421020354450580303101c413551a0513400c1c00050b10340c0030b440000041396000051b15456405806921501540203912070311070364444401e074641c04905 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 752719091 1250 752717841 752717843
    0x1802070c0e010b0f090a15030f05150a090e0f01020a350a05040f05060a09050c0405011a0706060e01090f05090a020609190e07091e0b0910021005011e060507020d 71
    0xe026241c100031000503c906c8441d40041202d000c8404011281a415030403200b0240c414010038000e0f0307540d0240103502100883c02c9a64480401c2d0030401a0100507401750381c0c80c00b0f0301c9095951055007200e0b0b0a0990b44240210b400080076200300700d54200c01c854003594a1403203041194601440141034200840001d0300001c07a1582d1a400b2600f080481c2e048040c402d50300006480c181e191240142004105100c025509400340b01640b00e50b61038544106d6040e100a400c80100c421201c200301880c60304170750011152150750b41e4010512540c0d40100034000c0052039408107429260000175410b542000e006040180c0c40b101c404030040c1d40d041d0503900152802e0300c1d06041401c0603860030030204e000b9800020185240340030711005030ba200c40001c05032050510041ca0402145070014009029031082c0c1001e00b0041c88000b9852400a0103d580c045e040d10407541034501041c0b00ca03003212802e0303200390040301c500c05180091708a0306008800426a604140d410301c2a10f4000c41c0540a0b030f150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 752720341 1250 752719091 752719117
    0x20c0102100c020c0909010515060c07092315130e060106050d0f0f0f0507020703051f0f0f06080c060f040b0c01060e090c1f05070303151802070c0e010b 67
    0x142e6415064820003500414000041000030281000d0b40740714020442a130340e4450090703450380403e4103418a46d08881e02e01c038144c0300608103140362005840080040240942924140c1c21145c400c404090307203054054030041d600044030a080900f040103100e00c1240a00810307051041d0403d00355030200723800d03044402505220340d840d868807420b14010012007069500b8030346028421312203192280d00640c40c2c1035241404000d5034131800c90903030b44d81c406031200030a140d000f0805954201d0780c03004027500c10f8000440c04124111941008000e46110300c0b140120342d0f0380d031402000003942c20088401c000c0d0b070075540d0b545404440750100186120398056403080c141d00080d81c1c3c495107001d602034801890354280c0091107003401c842050b240c0a504031a03921030300d0003492441e20b41001440b02c0881600c941c0b03034a46400621794099001e0454001019031620001c2000a154001c1d404925010590b464006980345c22514080030010140d8100c960300700259401405045600000c4442c1c07840c500c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 752721591 1250 752720341 752720351
    0x50a050f01030503120c0c030a030f0606170414012702010215010b1206150c07030c05220902131a030f07080703151503030806101706040b0d052407020c010210 70
    0x41c80c031030702501c42d444002240303100010350f2627503259240e404454001e01d000c1c0280484d03542c844045441010301450b03e16020020808900007420041d956603c070a5180004502495986407001c0544881150b824800004020800841d80e051005030902480d1800240d61b5505021940e80e032401440140d40304c0c0030850012803466500d01e0107891a1025070858140c4e506030321050326483c0c0b101d500c0b04981000d402d100100306850302c0e000141040e0b5450b900014080c001ea5044006422080010b9070000500c040d802142415400782007149085202081c0c05042004245480d2901d0f50802070107580004000b4415805c012580c08205c9400a0804105550f403195840090030620210310f035400b01407000108040c0c020080d1481001c08540c0b050022030300384001d4480114860b0990841c0508900260842c41c00340c0c8902011b0101a00592031420746a95103407a00b40103180340b42140034400c01107554515035038160f030360160640c80501003000b600d8002039941d140f0108aa01c00d41d80360 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 752722841 1250 752721591 752721601
    0x30b1014090411150f0d0c09140907050d02120a0e0c01020115050904020a17010f0c02010b090c0f120a15050102070e190b0910050306070e0a0b0a1b06050a050f0103050312 75
    0x5416500605d0380010881e0740c0b20740080e484401801005000340225034003a40c00541c80c8520014038000c0030b4040d020604694411904803000e034880203041002e15824003100302c2d100d051481c110311542d06007400107410b452040300c09182c04d21205456046a061000c540300d02e803c141030010490700c0544080b607454607244009295180c940d04a02200151141030140880c1c054001d103041c103080060800150182d030500701e00381d4402c0340519400c2091040802c1c40d86462070b004081c112580107180341000103841d10082e0b40981550b204034800d440b00708503000800c0e12240d800040c60f0134002024407900c0c190040080540042071940c443c800020b05120070180f98101000d00c00c0000c10485141c41c1900d181042041240120b5000740b01e20b80000310700ba070003520002c07049036000b00207481c290b00e00013480c5d413030381d200540680030088092082408103040c10b81461080703118075030105007460491448002c0326002030041d50030082c2e9400402c04614044215070308410300440f5000d042e03541d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 752724091 1250 752722841 752722879
    0x6050d1502090103180b04020901121a06040b060c03091e03150408070623010603110f16050703031101151a032703180303041518030b1014090411 64
    0x21071100119540d01c2d05014070803c00c101c12058440d80c421170f0990036072b0362a50344010110340060001003900303c0035181803100c40c0c0b02ca003190741d1080004001040341c030b15401c08116a82c000c4025414140d0001c180c007002807414641c4034440c98206000d1f03010280070b207800295950901802142d4100701c4c200490705211000e401c0300c882507003180e018841282810386910090f50048034412000203d0400032074082d2190040002c02a51425503609100003c0c0501c47c00340d0007220010303103400740102e4007000200c0034404072000314080c0d200c0b8180344260882c150f003907502c1c5202c481405a409403061204070940c00c5007645450304a5851501c0c0c1e80e42000081c9425044003a26650365050b00156030700e11800001030095000c50780d002031100c0c03000414140c0d0780c080d81c000c0482c0d4400050120003075912615111198541c0c0b0030402c80220381d251902c03080c0c0c0e4003d0311981103001180c0014044441c0c480c030b5809070b05105882c106200c4c41c0584401c20444c01c842c1b10940710301e201100c44409270700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 752725341 1250 752724091 752724101
    0x1050d2d06050403050d14070f1809050f071b0309060305040503071a060406080a020f06030705160c060305010e100e0613110901020606120706032a0c020406050d1502090103 76
    0x1c0d2101c010031403802c26013009061908000b5022001c542003c40c40c260206007141002e0203000f80f91200080b18018400a07219041030348900c00000385510030000300c8004030300565000b02d42450f060507060421180c000e106000880000240130352081180001035840409401152881e03d40042c0c9a00c452510038154410040044c01000c0300314a90f0f01180f01600549010394400c5404000c40380c2d442000c03a456400c0c00304040e502031410341241d012418040011640004a882c00da0315110072641a0700b01921000410349680007007000a1021a4051003190302604102140e42601d250141d5109500020b0380110500380800002140103a1207000a152040d1416030060007403d154207036494035034002000d458014070580b40811860b0030302001058164001a01428206052030002e8010b0118403140d003910800700e0b05c65000f075078181724446100e500b0f15502c4045000d6540104800e542c55038004504c6070750b00c20002000a440d150291040c0c406e0900b000d42c1742d100960058000740 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 752726591 1250 752725341 752725343
    0x80a021602120c0f120a021905030f100c0905030d0f02010b1c0b1003050322050913050d0203040f03020405090c0a15080f060a0e27070e01050d2d 64
    0x620349907410b155000400c485403105001d07140d2103142500364080001d94480c0541c59015904810b4403a80541050810748940d811340c584030710107072640d0b0008070b0b00e4040840606203080e0440d894455900299005001d40c1040515018289030f05000000303460706c3c41040303220180041004514982c60003034000800b0751f20024888030065107014102c080c04900f0b000201ca540903500b00050801c281d0208100c240c94002009505113801c0300c101140e1003084601d400503040685100049039070340c908100307114402801c3c8481300b101c1d151400e41e02d8200d5000148003507420030310007481400b81c01e41c5841d0441c3e4048401041580b00c82503000e0405800c20280e5412102001020804c8600302c41d070340340861020f0361004805e54800d4001e030b0762a00c0683c0d0750f83d8010340b1400104400146400a1900011018400701904100e5032080c2007034004c50110750b01070341001c0420440702e6185200c450040801340c99040700c1e04c840b0b0340e51400d1803800030300c04003140c03100c1e0032800081464080115141 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 752727841 1250 752726591 752726599
    0x5130513060f06020d03060f12030513030606170f0a0809011d030a1a100e0f04020112050403081e0f0c03190608010f06090b0d020405071413030311030406080a021602 73
    0xb40740c82e910002c2d260341008034510003090074074500058800c0103010400c11100a818011050615581d080320a075025419103450380030304103800300c0442c040d0702c611030050007580003500ca0f6101c4201880d0078101d4842c9060300350b4102030125404110000200d079040c01007481c0c0340220310124108584106101004190140b05016030b450030050780308403000d0510419180001a9034501841d40c04c0c8031007500429511103901c42c0070842041740c00c00b005410502c1410110300003002501c42000f120b0040340c065001520090501080f80b0700030100b4265203407040c03001003040c03400368031030384a5150290015036060000000580300907006030308000200c2005070b00788113559440002c50b010301540c69034024075520380f00000501e03086600c20705010440142c446410081c003902000020308d0020704001c103100a0265014a41e41844c0041940004190710140d08509504004005000700da200f010341e0343c010041030000c035401c149410361015611101580d0b130801500c151181c460101002508 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 752729091 1250 752727841 752727869
    0x3050a050708250504090204091209140d020f09150315011505041d060324040606050907050304110319060218060a12023f070513051306 60
    0x1001030114221046590036000c9400a00703030800c0f200d4028615440420704000e01450401c61030400381c000e869101e0000f44000344d03040e0700e625842c0000302c4584442d40000c03180d807005e20845580d80b0b00d0103902c60f4251680b00109956a011030362a594000ca21480341840c0700029002c0032004280d00c20303075000a800d480703240350495801403003a0703030038011280307220b1031041c482100512031000d903000c40f1f00c000c000008240c0421403481c070968018000c1c54140c09001500300100340713040d044051848040c480510140381c039041c50000c840c16a000244519a0703c41484000f96012060b40e4011b0340240d6841c80c908180c000007443d010401c3c2941e4000301e00c1020810502c10f070b90340074010010108111121540100f010071025114540000b8041000c007041300e07506c00c02ca03902030400c0701c5910004180c1c00520011000c0780003540d058000742c5a41070364000508440b07000c03a480d000005401c0407400c00d903040c04180740b0080d850040a00448201d010080e030030806030401801405a0415180 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 752730341 1250 752729091 752729093
    0x6080106080d090e0c031311060406020d03182102010605031209040c08040201020d030c020703050102190210020c071a120a060614031b07030507051f113103050a 71
    0x348415070740e80380d01c000c03440304807001440381303c19048503104091101c1c540e803455403529407001c42c9201c1000c054514020b58410082d00e0303280e42005102409079a0020004108041d4000b03003039a64459021011059104000340001d40c14048986210a01100001e61801d2560101c0c0180081d500c00d0b40c0c548180031a065400402030002c000455044e80c060001c054411003c0d1510a82568003d0069000b0720b0075000d61882540410302100d8644180c0b80500e42c3c82d1281c074213a130004020745140b840c1c40e0b410300030040d404001c101455600c003030b82941010032a484d51a11804244a100f031004601d09102c10002100400c4030400c0c26110f4903200f8506000300e003c8010081c5000d036001061507244142c400000708800c0d00e100300d030034003140d42500da460b002500c040c4d01314200403400d0080078803110340018014004400040003165203200c4102c60b052050f0195084101c1000d691a01000342c01c5006c0007100c1c80a400d40c001c1040900320051100701440c0480700b5a101130504e00828034002c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 752731591 1250 752730341 752730343
    0x4060504060506060a080613060f170c190306050601030212041a010501020a020307091d10020c01060506091305061207031a0705040e040b10030b0f070909021606050a0608010608 78
    0x50103640201c50400190742c80d1424025144909041c0c1d002080c09a8001038240c076025556140301c0150210101c0c80320b644040d0100311f1607035508440c4e444150034084901d0000200414480790703000f01c3c1c543c00c0d0390040101da4500c9050a0002a20030380d100c200044650340680c04a030078a1040b080b41521b585071608104806202c2403840c041c5d042145c400006c2c096100143c101440760f0010007414029140c10b01c85402007034375100c49400c5041c1c2400b8103500035800e01000d450000d00c107001681c0d980070401500e00711100307a00700500c140d00034009030060743c03120034500c0c03404601c5a00025a584584001801410340804180503c1c4039219000c020040701301e450fa1040c07520618002c81645489005550380d0089020798080b0301d00607000a40420b142014440c0c10181c81041045207079143c2d01d40d19403001381200d100426040d00020300803a80d80c030000003002400e42e05401c60501d03505c1d011041c015880280050030468135040400d040050640c40320004042080080002a44e102011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 752732841 1250 752731591 752731601
    0x31e0c02030105071437120605010c0f0b0601020c030304090c1403011505030c090a0608010e10031212020d1406150906041527080708160506071a0406 66
    0x201d01079401c0101107041c560255003004201800d51010f03500303062049042c9032462041c03440e220522051030022150b10b000301c07030b0b61a440c5100c0e50354044044504103210010340307001c0d1344802d04210a6044001c0840d9000700414000b0f1382c000040d0009880b2100100e1604c86000300b80b0358940000200083d0020090340140c5140300191030301a074030403001c1a070060301d020911a980a00384503400d46134483d403046004503032165200107101e040108040103e001c1d40304942081021848120041c010f410841d0075040e03100250490000e0f8003421580e6441001c0003c1ea02c840034062500d00140340749181e50161640c80002d620100640c138402e050032540c1d500c0548040340501c01680b050611354400a088444582c0c002e00803505d8075161510303050600c524030490b036007048841c0b60068171006074142c0c180b0301d454580d0075825015007003d54007810300245600010403540010b006d42c4410380401b07103031012070f0070454020380c640c10b86080103102d51a0521020039011070034400c1004000f174035886 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 752734091 1250 752732841 752732843
    0x6020303070e2b150216150504110108070c020d050c0f24070212010f060905180c10090f0b130f060c060e01060b0c03030603060f0609070c031e0c 64
    0x14503400c05403140d05201004440f07010030f0035400c880381c0e21148440d02210350014424420900308045010050311039040780c110b9048403054000006152003842200c40c0d120448a054040c104102d062079035500480c00014078031981849a42c8000860306405001d86c7c0407403940207001004171030b0461403e152110702d0034040c00d01c600d0082c01038a060b030505620004014800381c2e003c140c80d40c01c4002c524000e42116500700ea007e50391080b0324420100c00c0c0101706050a078420003040c0c0074201440130050711401044500300b000640d2080e034a0750380c0080c1940da4a178094400301c442c40200d0404650446068205c1a16650b03000e00010700705142d82c0007008901c2844507101d1201d0b0f160000d03009041114455600081d0250802401240299001840c480949400054407542e10030002c1c8480d04120301c1420396420100070410303103080501082d580000c02c0d005100c40ea291520000f0420040034061408200014501c50105400398001200034000c48800201c103081c0009c00900000103104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 752735341 1250 752734091 752734097
    0x207150818031e030907050d03020105041203050c07031d09010627060f0e04150b070309090b030d05070302010204030215030402032a0f040605100905030601170604110f0a0602030307 80
    0x1098040800c000c810340c2c1c1e02c09101410910b0f91210026000720640010b04601d41d503004451001a090b41d48061404003603220340c001256a2a0904002e440e00c0c0c2d000340910306144c1004100061016030200b2952015454102925540aa140c41d0600280c84a040c150803003a000700101d000d94202c1068407601c2d8083e40c0c06d9003c41c032040500d5010014600c41c960108000b6440300740c41c140104821800352401400000303031300300142c0d101307626098907502c5484c00140c0000e01e8402e1507803000703002c07000d009422010710410404202181c1d45581202e40c0004100b0045598020940700703404460081d41c0007070580404134680400541264400d442c100c0c403a124800400c480058050700c4401c501000c000c1096406003840700780441184a10461548036075a660049030980d10200300d12000c40c0d155443c09001c5040000741468218180c010743c3c140312200020400070140010f1060303010f980320125141c030800d0f04c00803071000c20b40350031202d03070000450f40d01141c150350000c061403140000d0342d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 752736591 1250 752735341 752735371
    0x70302120f060c0702030c0d03050910051b150109021318050703050915160207081902013207020a180e0105130b01030b040302030c0609032701051902071508 69
    0x400d400c03c40d10503c10001c2d01a00659054405480c060084244040c000c4c01c0032450700b030002002480c11601c2503102004640082401d00030381c03448590f8218040010303402010030440306005020002014840d80040c03e400180d000303492040c80c10002c000349408203c40da0f03118440a4904080c04084804c0800649424001031034001d00052400e0100403078038928086e0b84603078440d001e290300901c038444290701c54a030002590983c00c000709092038082807500380003400d2a1000520a003201e079501c0b00b00c030020800981d00450b403400f000394a04408051540e80301194404688691490749c00f8a040e40c2d0182403401d80400c5e07507040058804028002040b00b40d5030101ea1102c01c82e2002000f0344038007802d200510014200c2c0045640242c081d00441e800e010480039940c0ca0032900f154100c4245c0c00118100c1191070aa4a181c41d46a00390800c4101e9403060200080c0280611314219044c81147c003004441c0600038000b1001505101c2240c00c5641e44020010708149002d45806158002038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 752737841 1250 752736591 752736601
    0x1809080c1c14070209071107080a05060901020403050312060d021c0303110309070b070f06090507180c080703020901090302060d20070206031306140f01031b081e070302120f06 77
    0x42c00000c001801041c44550424845409001800300e009113a8400d0100d90000b0750620102000544000d024080c01080b0505151800a0905801410781c001aa005020910015a0220554295600368407805d06d440d039540e80040c0303110444020182d044551024400c81a0245607d520b400e94000c0d14144841c2000031244481d501c01240c0000d1141c00c2800705020141c1004002e026250054071030542c59107164075160100c0300008022210b80d803000104105103502720b1500264004402e000b00030103400d542c0043c0000d840100300d1420907600044290070313607010317200d01c80c050358000d01407a4540400c1d200b620020941952074003005031483d44099035400018003241c131030780d902400305400c0d61100c1c5424248a00014011076400f6150035001c3d01050214284a208481c4580121f885501d142000030500c032070103030000a0300720343c5603041c000c8036070000301150206641141c10848141e002c00c050305080c2d554200039406004501c42e00c08001c0000703480d00b02503e004080c1e80c55a219 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 752739091 1250 752737841 752737847
    0xf0f090a0209070c062c0f1c080606073305010b0702011b140109021c0c030213060e0a06030209010e040b0604110d051305061e011809080c1c 62
    0x110400c000e500012031030009000034820130080a07481d10a407030100e05031007803403040c0c04042225400d4106100b660071000c45211000c01c89424a80540c6025101c1e121044007184810390091540006001150002c03401135140d030400c440b00c10740c00c40c154001282c40c20005100000344020652081000010408a454040e01c0b44030304071a84e54a501c0d2810394940d0040d00c44114001c0700c44108500b40c41c1810204000721010405d8026200c00001d04403040c0c410095454a0460301c82075410303480110744006001454624244c80c0c0403140c0d03598003554049100080e04042d080890040411804d0048040051b0001b0013940d1003219500d030700d40e0300c42d010900464800c642c00b030408401c10b00030403520b0810340d012a01031001411590714255100c140d100c280d940c1aa400c007010589110b41b10284403040c004207802a242d0400341c00c4a060700803049803a440c040c0560304011140710807000301100d5607072180c2050f80c2e0000765542c50750703111407041e51280521825070780200090800c0e442000d00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 752740341 1250 752739091 752739103
    0x50a060305061f120305040b0703021f05010302130e0c0d08041706090304090f0923060a0e030702010e18010f0f090b1f0306050a091d0a0209070f0212030f0f09 70
    0x1c0304000d00c01c00326103002c02c10300d42c184c50306500398240301c0c0412010990300350900042008600a40080c0741120400c0342c1d2a002c0d0181880c0e2600c01c526040c01440141d403a489030411000144201107124a07100384058106120b0610313581e400050b24000d0b5041249403405002195444114100a0015640b926885d080211414240354108110a00070003059501c40300e1161350703039000090481c401c0e6842c1c41c421024003003040ca000024202c0f03031300042c00402486a001d0034401e4248851904032810320341c1c85c02003120007414400354803107440d080e0f00c41891240030f070741a084c070314112942c2d034841040b00f14040d802500212540c01030041003a186d00c1c020f0034502480681114800903000350703040c0b07400b9005030681d020180c540400151565545800344040c110949000603100701c8009051b0b4141d98001800380c49410081168000da03a074400403550055050801100c0e1042d81c490890904c0c01c10001222104800b10900000c106c0440c413242c0f141105403551807444c0c8078509200d90340c41c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 752741591 1250 752740341 752740381
    0x12060f050618191d0d020a0507140d06060b28020c100e090a0f0f0b090a110c0d05192f03040506040e0f010b16031b0204050a06030506 59
    0x141201446031090b8014103a07a444201031070202c030b039620503a21000545401c000160f81c00961240c26460a4000f071029114240c524002020ba41e0442d69a40d500d52006215000c84507014580c0c101c00c81c0c072400f000c0015254020f0f010002207850703111946d51600100c0340b9a0440c12030901042d060b8030a140b40c80d40c0e40310a90001e04004150f0002c010410803c14006010061041c80d002c5894030b400c48607270b0051040348004550304e00f005010f6403c44081c0c440c011141344c14841c07a4100f0b900c42c0c1e00b04541000703d810780411520900100c4180600c102c009207039140c0706011141070110f40c80000307091341f80c400c40113440401c40000c1c001ca80c2402c5200005d41400601d00a04005903001d640356400400e003d01605c0c18683c0c5ca000244194010350b02101c006ca82c400c007041031b41641d88110341d01410011030410b040c507019103042031003210b1f0480c1c014140950146042007600300da1841d03110240d8014030500c000c0ca005035550002c4e040c20b00c0201d429203d0200031a03007070780c0c200d00445810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 752742841 1250 752741591 752741599
    0xb1201230c030f060d03050904090c061101060e011205030f12040b0c0304080d0c020718023c090303070204020c010e0708010221060a0305030304140705030c01140d0e010612060f0506 80
    0x541301c00c003c010b10144001d03c12002e2000422100100d5101c034090181ca1714021448242d00c3c51405401038201c940c14680c082c09a45003800a0000300c0040c0c600b10b040d0340d80c1440881c410a1a07180803440c41c4a400b41c0d080e0002c20100c0c00b00c01d050541d01c0b00310710030b501c107200600345903c984110312464002614010221001030088000c01c041a82c4400380c0d00000b803048680ca5959030015848c4005100e52454201350002555214091801044031400c289980b1864603000000c0b0080d840368502c419805406500217400c0201c0c0d50100141c43c00759400620456481c080c40b22400d000703080a615542d03460054502c0001d081d10107109945105074015003601507540325104035101024020406540060b140c8008801300e80c040000d144943d2003061840024451041250725081d910ba208500c81ea221941e40034190740c0c02a001219910055103003511359601c1000580a0511000c014029610b4401c0004d0f101c08981790804225000340350030810303006000c599205991007101c9407030700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 752744091 1250 752742841 752742871
    0x180712030e04050f0433140f091c0e090c071a04020618010909050408070507080d0909020325030f0b01030b061801020a0f0308060109050d0c06030b1201230c03 70
    0x4602c55095006c81d062008812254924461004048942402960280095503040f41044c0d40c0ca100c28910740007010b02c9901c101c0c40c9080a000765540c030721989207401031908a584001c0706c074010b21b85200c8801d00146100f12034a800380c2a0011500300d200b05950581e55080381d0541c182640310400e000d1034001d005a440e190161908005100098845a04020707216400159040e1907104036400342d481100c0c4503036200581d003400d910b01141034104654580110004c5408030780c100307803040100d4104403c0540c0f684e65201400000355140620078203207090103400d00000c20f9166004c1080f40c1801a410842000c0c031301d00450460300101005034000c40100111034417001c01e00001c16468005104440050b010741e40c1c0d0009285c41e452003200440d900100340111513802c0b004080140074240d5007003000c0c112584500c0316003a414880c0c5802c2c190380b40d081d4010383c2c50321818804800c0c0311400070710880d0600701a090940270340c0124860b00e0181030010414580f200403c684c0039201d101c240f80c0c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 752745341 1250 752744091 752744093
    0xa260109180506040b10240c140f0105070f0c032109080712031b2708030c070f050303040e161e08090105180a0b180712030e04050f04 59
    0xc020701c0c000c00c0059240142042110000e031040000d80d100303504c192141c500c43e042507281000151136503003004003032000c4e2808400c0424601011b0f9110242035213040b051909a90604500c43c00d00c0070383d04041406900c8001454401c1508258051009507941101031100241c04940301c09000344003c000401c8141c100e008101c01221a065800f03810070001154401a65450031070f90140400f203444407070780030303986010a40510408218100c10081201607003200d0000030500b2984241c05094074040200344d23074955001e81000d1010341040c0381280d584032081c4101580d56081031158840c05042c18401143c281030110a83e030858800201120311603d9041c4595500c4410241810030440d400081c1244130442d2010b2078180b070090f44840a9909012010b9825900000c0070010400d0702c03495031081c0118001641d40605030840d8070200740d502c400d05080b0641c00c140f05000450310400038041090008440001c42640c440d4995200020b40c210500081e140200d400903003e0583c0c00c0010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 752746591 1250 752745341 752745359
    0x712030e0d11010b030d0903050c0105030f010e250203091f0f1b08040905010e071805270405070510020601080c01032703080a0f060305031e0d050c0a2601 68
    0xb10345039480c080089010314662001c24905000140d014000800303402c400c0040c07000500805402407020f2030203920f90b1410042c141d034034440603c0b40c10303c20442000081c80384100d244103101407182c0038030b10401c0764102540003035407034000796200f84c4140040d8080300940501c0c4901c480c0583e0031929600d00d00d802030f90341500c04207180c030300d800d004104110314000000c4201009101414143c01d0000d42175051511584c80800c5c014001001e010f0502c90606c0c2440025541c00c0031503108899240100550042043c0b614110308040c07004514404240820894041040000c2e43c50aa400182850140204030ba641d8800e00c5000020b0f040081c9184155100b9002400201c2040c0e00c486148001c50503181c0c1c00e40c1521030b042c0e0001d500902400341008813030048050284c6209000d0203510f00755280c05407a48109410102ca1502c003000d10003c2d414280305640340096903038420011490603030440c440310fa003d40c40c0103000a2010701c98640700c2128503d51b81d01c4000c0082202c015a082c50320300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 752747841 1250 752746591 752746607
    0x105150f01051e131e150809100e0c0405090109030806010f17060612070e0a050a05150d1d012a17060604150207050f0906030607030504260712030e0d 66
    0x84044504c0d50600810a00700c1c01802c03164000150758006200351402e0500d99480c0c11054060301000544000d0103500d41c0e000a00705103c0711066800990003110150391443c001c0e1032490035810505003401c0088861041d4480e000b80d034000d46803208556224401110790801007100440842c02c02c1c00d007188000c03030f01c1ca41b403a40000c000c2c007207900d0025400010f8101c2c100441d1014001604e1040f0344802e4108008103c0042c42e003900e460310060f0800000401d1500d401e121103a43c04004030341c0c60203020060308404209001101550400b14001e00001d0103040101040c0304048007500e82c42c1502c4400c0c80050585200c0caa903443c0f4103002e560006000680050041e6902a0303040c8030114102124000c007203000c0405400810002d45071800340480c250143c000d140c895542202040050b840210310564004181d1a00054035130316490b020035406800d41609800c1e1020090301d400d000c0610008081c810b0090851941444118101700c086c1c1708480740314040364114050310b0724000c0c021804 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 752749091 1250 752747841 752747857
    0x6080f031c0203070201091a060a1502120d2309010506011701030b0a0902060c01061e0303080105060703110a1101080a091709132d050c04050d140105150f01051e 71
    0x21a0b0200c1c7c2d40c484189100c00e217a0540c403400e030a43c050001e5031500c000600010302c1d00c11204030510040550284d01c0d45c0403844c801c51f03030280c0009c0722205001c6030742c00a100028102d090503405005091145842c0c0ca00300c0f0560403940ca8000800c815600494181300d1040b10b07824003001c0303607080d9550303203840b03d03070182ca03212081c1c1d121541c0d8001a95040080d04100710040d00008245142040b0040c00c60840629646c074401c0b41d59013800401da1007101300e419500c007680c000359540c465150442e4031180ca0441c2e95a240607546281d02085a11110b0000d2005c0c01d0f40da500190301c60404000c101c8a070030b203000340f60080c40040e01d007019104901500041c5001408a21850082400181582c0d00140011045400340031101c1d1700301d0200d9101c401c22122140200806d01c0e060201d0301c558492802100e11492296403050f0800004411454070b41011000034459400d1090150b12645061145d80c0d01c25140210107201310752141c41074409034582000225032183c030201010001d9484848 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 752750341 1250 752749091 752749093
    0x160609060921092102010f120504030201020406030c0f080f0c16111206010f050f120115061b050709110c0f0d0e220e030412050106080f031c02030702 66
    0x2880c5010512128a2608000b0351452100d0b412500d090020402e1555030440c0c484803404c04503244030201e02460703064900d0390a080180428040b04c00546400c404840c0c200001402d0030b04110401d981900500f00700d4449890a00051100910641d00207100c0e6001d003000800703d00011b40e4001c22542d20307070b800061001d072061814110011820002c21401e0054504100d81010008a41810040140103d0994004c1c1070307a9418020b031400c0c0d00800c0d1041c184183c00c0302ca00149603540c4c24210040420402c0000c211142e40c1140e28629141c0758030400020681764082c861110301c090070020606079000c00a08076036410400c0c194000d0111408240200c5421302c00158140000c01190741c10003e08801001c2d010520440104450400324001d03000d101181c8075040c0c0f05244100034503441c1069040852104100b0880500e507000f00da20103442803801c94040000e004040d4814401d03285000203480603040c4521102d5070703901c14591138010500a06106850098440d400f030b45e003250340d900c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 752751591 1250 752750341 752750351
    0x8032d040e1605040503191e0803180102120a1b080c0406030207050705040e1e01060609090506030f1605030f0708030702010f0c1709100206010503030a110c06160b09010216060906 79
    0x14042807400380040405940c0507c4007440d0b00501c0542d0119060000d0130a501d800544155500d1005502025011013030000100c851904403540a405a900204850306003182c00d240c1460150090203020400300c0c00f000c410000030b03d580340301e856007500c600c003903c40b0145410700d8240114020340c0f0100c0f007541d842c040c004000c2000e0380c0d10b0040c0c40c036040c1c9000080424500e4285080d449054007158100260f00d401810040c20fa048125803003251866180001d2565450010a040400c50040300866000307074460825101e00380c2a2581c1510030540807034a210005950944c1d842075030b4060020547d00c01d2015000542c410410020301c81c03528a4610b20303410060f5101c15031040c4184015680c0e88001c079844c1e04c541007000c0c01c41800040e43c8001c10701c5500d080c0203e5102c1c0302d49030300d105c20041e42c0442101541000c0100c143c246c18082d110a03500d140300b100043d000d00e501042220800b6076840400c4902c4014002d0710f8500e880c0001019000199035640c00003440200c10440300302c2e44503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 752752841 1250 752751591 752751599
    0xa0c0503150d0c15120b0d060b0d230f0f0601030b040c030b0705192f0f030d05071106040c1511061603050a090b040f020a08032d040e160504 62
    0x1800030052024440a881300000c42c034018020300c801403c1c68154514240034156103944030000d0050310360301b0040010b0002c440b0070210366003014410005d00381084c0240c4282d41d50500c0d000d07003580040c458040d92403202e01e6044660302d07035410003662003407540141c0041c00072600354107840760054400c0e03c60b292b165940f0f58441c0171728581280d002c400700e100442d80046603114150041c1e00c0300c0d07651804010310000042415501c0000149101448840c00100c2120a00400c00d0b1209920305c842125100c1c0d0820f108600a00012640007000440f605e0010449240009920b0701442e801100b13250114101828901840c44c83d590440800240080104560900f801040d002d2020b1021250100c40c0348130000e0166a0060044401c00e450030042c680880da404400c942c01a038810003080c0c0c005858000a060000590041d4006000c0003030801e840b6040111580d135400340741007440b5807201004060686501651140c00c840084c20f400113090700b01c03078a4400e03940308a9810b01505054a07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 752754091 1250 752752841 752752853
    0x12210b181f0623070506130204150f1a09030d030203100512150906060a0302011413120b06030715110106080f100e010515120a0b041203050a0c0503150d 67
    0x2d0344142c1c04100300820f5003082c10a21845414446070624407580380401c29560507588040c0180880c0190003447c03544011945c540d008202807091030780c6031100683c0c0350811a00c0400d114400c503d034484007841c44054541e50a801ea400301d603002000740c01810b1007850183c000e544000c1c1640c44176640c401003c2001d607582286000034158a50083c80f004102c580421007801b00600320342c40340e501c02c0b400c1120f2561034211181c2500d0782864003036103410040c2024144c600075104c200d1407110001c23201091465104002092440c0108001c0301151120020b258441c9124080d2401000c3c0708120004003600603e4180c02090120000081c0350381c0c1c4001e4141040205510350040360400c042650450100e80900e060a010b035000801080c20848445d0070320415490105001d00a034192a1071600c1040c05102d0480380c01403d2040d180c6440c1ca8201441440c000c5440042842c0c1000316940d0002d503c9480340207122910b0390b03440d5854000c401001f0050340045a540302c11035900038000100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 752755341 1250 752754091 752754151
    0xc06030f070507380402150708040806011e120f2901090f0e0c0604151106090a1205070c030209090106230306180d030b01030912210b18 60
    0x168840301c2040c01c0401010050b011544c001012281d0f40d540140005644c5010700300350744005061500d03070786012502d0480501c0c0500e5003d542c80e0300440c2d0001660460001c1c0c03411503940ca9020321044d65440302c6469500c4c0741011000303484a48400d41c2100001e00100710905091040001a980361030250341c440e5a595090308409081c80d02c031140c410f0403800600032501c17130001201c00350000d510003001041c078038001c40c4103020408201c400e00300007050003000100e017248000c40984e003040c80c0c60030780750b42c0e80c500c0190f007202d28554148640c618144580d00b0340c2c0f149507008090f4916285907400300f02c030044018140740002d5580301c4001601040c0072101d00705400b91036607001c40d100700c450f04140c00e00700010581040c0c0300c11090301c100352140c007044401e041e101c07a040019802103603c0040300107003030104000f481c40c44070f5008c8140307480e0403070803442600c00128007803800100c80d0200b440c1a1200d1707180c001d0700a00b1404010140c20b828011240d030114011111840c00b43c165045541112 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 752756591 1250 752755341 752755373
    0xf0a020f04092c0a15050a0212010b040f06050435010c030e0c04110a050a210207051b0112090218100f080d09031209030c150306080c06030f070507 65
    0x203669002c154a5900c8802c00442242409002a0000c01c40c19110301500c3d00c1314142d000f9050b80d8402c0054161f000581c155203402001d1100c9101d5980c5a60002400b42e1082c000e10b050240c4901300018007901c14030450701035802ca650041494076800500c004240442c542000300e400c00c40e10284c200420074418500c64508594022a4162a42e0011400d00110b424464001c40c1016492403820b800107040301d1114140d8640ba6543d200b00c204200d0f21000c01200c1001e0380740d8145039900d00029180c0280c5001d078041ca0a4440641e0b0282c00c01150011441c0142e0214024001d481610f039600e5001004072800903080001444040200f5134104000701c3d0785580507045828103200640d5a6594100074005560040800c4021410080c2144549110003442c074900ca45e04100d07118425a0248025580080300481840e111850094290424094800000c0c50204005034200300050441c48060000e00103e01e96281c0220301030380c00d100102540c0a0020401205000409000740d000c080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 752757841 1250 752756591 752756621
    0xf02040906170312090106120b070e010f080a020a090b160506010602030901090b0306010302090d0309050f06091020030703080618060f040203191a03150f0a020f0409 73
    0x9281001100030855095412480e0b00328090a00c07500102400003c41d0983e083c20b01412900e552060007072030251040750000e184001d0030185a40801c0303131103401c95004070025110201001c80798401118540d80000703400000452200101d5490705e4158000d00c100c440d286009600d031510781454a6050f440307944006215100c01550400b404428011140036204a1001e18503140c42d10340000c1034030115000d01090400c0010105410340c1c002d504440034244060086003400321207040203411079070039108107402075213000c1051445282800c200c642c000c03070080c030900880641020444150301012101e00703410382c0001c4a0b80b1072001c200080c0c660f880c401ea45181c01483c01d8018003100c80c001e90f10114141800605111503075031a640c907806069410f83d00140c403961904c100b01c2c11024030440e424007461800e52104007042008480c003007000810740450703090010b040d96141c1241800c880e50031213050f000d00440c90005054000340f0010300340d104642c0c01c094503040840200c2d4090000d2500f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 752759091 1250 752757841 752757847
    0xd02040e060603070e1b0d06080109060905070b0f0313060e031207090905060d171608121807120215040801020a02010506010e030a022e2019080705100f02 68
    0x100e28013001541c1c0640500d5281120070304154a450144003041051304640c00804501c102c0d0103112944032000510f000c1c8003e0102c07020b2418202e009020342002512135010301c410100d1130080102c22a0301c107011100b02c00e491551040071146603400303418030485205844400d81036201d0000c001902171441201ca20a0300350400e168050850402980a549444d040c0402c0011559030f6105c500401a004044413000d8ad25484103210144104000702a20840d90f151319000c1c0001c0d01d01070071580c00c0b4103c15800725290710740030740d0315a828038100c81659030190360140801c45191004407521403000c0e1180c8521b4012026241590304241c2000d55241e50101d0081f038000d070b0902895070800c4080c00c1016140e8a00400319031124504130002e401440c01013451080d01c012549485044190540814100d1011a03001071500c0c61100b092220710788458444501942e011032042c150245210314602600002d5940c0341098001000544560040480b134402c0000c45000c0d544c80660807980040c0c1d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 752760341 1250 752759091 752759101
    0x10509130c1707030618240b09030606040204030f240516020c18070302220806041b140108040206090d0b06130e03030f101a120114010903110d02040e06 67
    0x240b0400041050080600f03007202000700881350340700b808400703c2c0e80c42d0200349031440c0322440c08040e80c10400100051000500002d456190101910580304101d0a03a40c1c691500001c10017a0301613404090900d030900c6800c400040c04a804803e2520344510500c003d8845c09108501110412100000e0718079a07000d2400440b941801000240ea0b0708940003001e90a0b1040700100d8643d00510020038103500107010701a041c40301f040052480012080045403580b0b40e03540c15216181650700b21220500c0804844c0040418107900054582004007800c0c02d10740c08004580d4200e0160050340c000404000c0d002160f01c0e032501e08036201d070250510000c0d41c00c00406101407018814002d644192524041181801001c411a0f80040c4604950041c0d030304c94001040900600340d03c00c40c80054002c424550380035103040980080780d40280b08400707a80e80c032100c00360070114904486000904031070090000488441e40e501490001915851070205154041812178001c04400d00c015070003201003007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 752761591 1250 752760341 752760377
    0x50102070b061c0506060402090109050913060c02030c120a05090d050105071101150338090106050a35190605070203070506010b03070513060e04060b0414010509130c 73
    0x1481181c140303560b030300080076903129245c0710b80014000c20301c2540c00017484035a90b8800d030005d9015000062802980d42000122a41040030f589021940581001d0101c0701d0383d8008000c0e9143c40e81240d003e0711030909160b62820460f80031010540070321800344040325841d01d48245011030a81f00e20f00005480c108148040c080c03500060703001c1030a80c1054a90310441c1c500402c600100d9900004402d0b200e070f084c070b001ca0321442c1c00b41c0f1191a000c22204820060220b00d202c59400368151800030040161540280803025186008100c43c0d40d0103a01001c030030001d400c2d000440300c075800d130640c860107003070300000c9007000c0313071440c074100f551560383e00400074007000d80b02d100c0d088942070000750f180951a59078103481d10814801c001102c5008000900007502840890300915880c44070009000c0d111100500300c10700d50a14103006a10300040802d2100d050000c55096980700c10402c91321007110b500440d0254060251745410400311040c03140c0c04103040c000d65a1114098454003000880c046444d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 752762841 1250 752761591 752761609
    0x20c0d090b03010f0302090a110c062a0316200304050316080c01050f1201150f1d1201060909050102041a040f060f030219021e07051f020703050102070b06 68
    0x1810603207082004200442c20144144200c80d4161803480f45655900c2c01700740202500e0503821000f8030000350030001400c0101e0310300d01c10901d0301070f07100c0a00014212243c500c003095250548264042000c40da0a0b80c00d100c40040302040ca00d02410355501100703914144507250a4000216030001c43c040c44113150900c854400391503004080012245445440342c0d9441c0c2c4907403081d0601900052010082c0b007004103c84540e00301505110455035184000482400d001e158500042c500022a030441031244800c1c460300090903505800c8103061601300061201110044a0030390750f00da00c0012400424000e203c01c103401100010380300d500d0945401203110070f14403404114501000107114802050124800359420f0346005044c50b08010000d5000b44610a9803c202c1d01e00036080250031313580021074002c3c0100401c01480c0384290001020ba85910b64044d081e44600d000c1d4428010390140f020a620310743c0a0b20440c1c041e5552074891900b240d010b040155030a074095410810303141462049 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 752764091 1250 752762841 752762849
    0x130507030c170a080d0207080f04030f0614070903060b06130b09010f05040b04120f060e0705040e0a05070e0603031201090e1c05030703050604110c03121503030d020c10020c0d09 78
    0xe80729902e0580d5030035090344550410800b0842d401f16101e014401e802c0c0030b079444142c945482594894581c2040c4451291003031084500340d0418880b0042902042c0226000302041e84a100b0b6150969860501a0004441131504024180142880d00040c40c0f00e09004082000d0107940c0d40541d4400107010b601d61903c1d0310203000040104110000c1c1c10b101300c90407034000801c109190b542074900300141020b181c402500e9241001079000d52180085002d800b2103808890030804180780300009611042c0500000d0501d4000b00e0040040d4015113050341d074401c0b40102907a20b40301021141c082180402e80002580e241d6815220705444820401e50044000080301e136280013102359401095840000d024a007050f84900102d0310b1901d07030f600429001c03010a4009900c2c3ea609200180e034940002c03240141444000003c035070364910030586184403580103000313186000c4090740150065809000c0c0406140300f41409140e54544601c0584030069412020f041c000a4400300180440c1403a00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 752765341 1250 752764091 752764093
    0x914010501080a39020705040b0609040e010e0a03020703170f0a12060f06020d090e04030903120519050a030f050115030b03070f0f1d061503130507030c17 68
    0x40c401680c000301115440706400602051165071403039140d6403802207640107030503210f2155101840c014541e810300c40d000016400c40344502c0d038a808020660701e0f0010f81d00e40109081001c0c200505198107e103c00ca1281c2d0000328031540810f01716443e1800d500700c250011707003140205004001030360309071038440000c8070b4038682000404a1592054841c01e03011406025010307044018403002078000900800d000c000001c812955808080c4d02d50305240024000119800d0780410b0400d03141d05c1890103960155102d4007503e003541d46101d00c18146d140d0b5030003800f0b0240a0344c00c4070301c000d00e5852103148999980316100c3c90703000800f4040d10382d62254164424140310040c004507800d14140c01c0d0b49a0b4a280101b90b030618000803a06051701030b08403043d00e801721000440c0c41001064080e003100c0c2610fa41030704143c0c0484042507440c8003941c01a0780480c0c4001010b080700d58400180da040403030702c10014040300d1b150ba251403500003c0c0c0d10440c2c9503003a4200c100220182440d0883c581c1602c28 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 752766591 1250 752765341 752765381
    0x201050a270902130b120a05070c050d0503181605010818100912020613150204090e0a03020d0203120c070c12051b030a0201020a2604080a1b05061911100609 69
    0x466420181d540080903078a00aa5034030000d2700252140924045454004064801c00c9010343c00052840d0b0044401080c00382e40c0c98100c4500c40000030f608003c003d880314440c6030f114100001103c00981c06054004c5000a03540400b401d010f0600c80c08021802c3c6000004010303125180070f03417280d51030744002002d40d00010100103582c03070600301c0640751030351002c90b0800071040f000c107180090156400c01440b09203440c606007602c20300010417824060098085a400d0301c0384680803a680c5c49000584088000e0144c04500701000550241c4196072181d018501503a031034400407040c03404410300540701940404204032010068510880d11407205901074041394803a600041d40d580c0e6003071001402100f5000351141020365089031349880c2c025840c541981c071a0394000990782c0e0800548291900760842018483d55224500c0c410229200900300b0707410640d1413160f01100d2960b121001090100743c10b04468000b0007441024010321648000091807414100d003003089602445890000000c45 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 752767841 1250 752766591 752766607
    0x302030702370821010f0803070c09050408040504141b211008071203030509070f032010031d1207023307030e030a0201050a270902130b 60
    0x1029000c901c181c2c000410100341c40c800d15009203207200c1c45601310305503102c101c444940110701c000701e24100c950701d0030030003002c94681181d80d032a0720840c50700419000080e40100303e16519500200e134401d00131281103040c10f035201c002c44c0503101d2140c2a030264001440400285104555034005030482220340d16060105400445403a0060342c0300d045444c503c204c0008401d5510881b41c60080c005c98000d44007119501c00403100207440b00182140403a0808001451001c0d0004041003183d40300b5009124242ca140c942d001034000b106550200304505004c80c0840e5181c400394800d010040b0350f000603000040c501c0c84100b8516001d0881c0d41604078105215441c842d00082d2280030750100c0e00b00000e070070701c01c540000e405600c265218801a84484580002c1da096018102603402915010345480c200030401d503c030030b58444004e020030028031080f46d06904c43e4180311007a48010520461a100680c400c0b9025203455000d00905a00041c80002804040f01054000c4c030f64107030254180008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 752769091 1250 752767841 752767903
    0x130510092f09071d10050a1b02030606010c02030a05150a06080a11120a0c080d080106020c01020d05030a150f0311010503044b020405090f07030813050a060302030702 73
    0x1c3d02500821100c1e10720705140210f4641a00e101c1100200b1840b000540c441c00070381250848421040402c800503074259121030000108424294004e004c0c151603a21030300191200c400588090780c141c8214002000022400c201309514007115901e4907a5030f03d0484034040650b03c660b0804016504041403140000d030780807000b80020b070400c40f14002511304000b0814a000c00301e0030054020b072034232000000c000c140884d6840d0203117041e989280f210f80c0c0b9003d081c0e956855610395103005922910003200050320400255400811850000c10805002c004142d040b000540201c45450f020002c20010011440c4d070186566000b130074520305614041c1c5503021915802e03515950364178a91000f020001c0c4010391902421003003082070f030b030320380c0b620b0701000d0b581c0c54000d6000c1303014920340700205186000020b0300b203111440610080c010642903a54920241e000300a01c0c090a03075000d0008181c594540d4004809010299401601c0345003080f0028a04820581d0000301d0b40d2084c1d11500071965 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 752770341 1250 752769091 752769109
    0x191d0114030610030209090f1e0403021905010f0c0e03070e070c030f1205010905040506090613020f0a1d04120c031b0c1a180612130510092f 62
    0x501241c0c00d20718070b8070f0444140d000e8400c031807036541c1c80455901005000020040aa4041d240442d00d11805041c0d0b0304000c1d0030181c0640e409009a4884038241a021801c6103110b00030700e11840002c5110840701620310242c5414200c0a0042504440d2004c210f04017000200d00403c0040300c0703044542003c8901070000355050f8405810851022240700303041d80280300140c0b200c011601e08000540c3d48003c510020302c416a011111401500d01040c400480043d40d240544080005c0c1c002d5144541c1c03c00140744d8a036084160024520800041c3c0b81c442031404050403006500a07180b5071405107086c81820000060480a104290f481ca401080d400344a041040102240c0f80d410300d0700311b0800c00d00d810102d80c010360711820540b810b0745490308080c01426280e4540d000030031001d0f0b90341c1d040004500518008400c00203113600094240521028a0070300140210141d82014201e0308022090300d440343c906850101c032203d01c4c584208401300480313903205003e080c0080240c080e4000070b00c00e0700c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 752771591 1250 752770341 752770351
    0xd05100317030714040b04050f10020d030b130534081915031101020d03021206210f010b12031c0e010f060311010e0604030c06030f02191d011403 64
    0x404040005a40c0f00e001e5440140d00b80c0c82e803000f49844607543d0124820640c8540a91401159051225909070410501e10328110465401404a210142200f180100720b4854216401400305414088034525032140d280155428000034051800c2440500845170320103015000c2c0c0324801d00401005a440074030242c01000213143c0003031010300100444090921410f82c06000504580004200540c035030043c00c1e221800e8083d81c0382100403000c16000ca0250012181d4800750319400651b0614103080e50b40041c174111000120440124214103150400701c0302410034a81d52564001118505400c800b0460029200207516000e01c000800c58134480f81c8184440550701c47c0d510321304402c001c1d0868100e1042d000003c00ca0641d0b40d0800c00d0010095460351400300d50b44c1c501401c142c0c06c0c00b01c01c40341a00d4009030003030b410301d181003421030090120254802c4060b9080c414440b008035250840c0445030305c280c0d00d600081d0411805214203441c510304035810b0251040e06410540503050640e5848 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 752772841 1250 752771591 752771633
    0x503070b06100e041104080105090d030e0d0c060b0102010219051e030105030a120e060708072a0b031b0304080702031c090303030e0f0d020706020f0d0e0607020a0e0c0d051003 77
    0x1500804145c21a03004540007180349508210400681078400222421500b80c59074051040981601c0515144c0e01042c1c0d016001504c980c1d00c44010030029004000b5481040c03000600e055401c1102c3c40865406003010000503e000a480c41000b03007038101022121450113001d8a07552608002941d04c4035210802401d100d021958070710b01500451480c44030b4403000d80303c195101818644003100f54841d00040b5000000c1425440b2190300c00251135201800500e02018000d041956005a941000b000c1911010003a001d00e00d0715400e000c040c42c0241e1055080e5a264501881010305001c407442e07034800001031170000388400070741c031a4103078003100c0d01410001484220b69100c82c4c2040c3c469060244648614a0320707000c542d03030004451048400d1a401d0380e4080301950040c0b900d45070440500000500100c0c002c1803145407000080902c184014000120756554014150401c0d10071034200c0c291a4000c82c03501d00d1a0080e0040d1070340a010084402041d50840d46c070350121000840024600c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 752774091 1250 752772841 752772851
    0x80c0a1202091009050c07140604170309010612060b1f140c010605030307030e1e0307030308190e01150f0308040b0f13031209062d020a0b040503070b06100e04 70
    0x4900c41c43d000007a00191205001a2a003034903500301d10b91058004a5078207a0f5000300320130710000030900f0340c003c540c0034003101d200b5805403074112042c1e00041e2510700c1c20f5680d0a000500211200e03041c1b002c0d50301c40d80010500c11280c2040250542c3c2d142c407404c154003240c4040134102a4411410044950107900081c4c42d00d00074500c0c0b5006042641240d80c040c0310020f10441415007001a00004c40c00450f994944c3d05c0a00445465402e90020701c80d80543c4038410a0000900601101d070348800b05100d00c0c2100c0314680c244400f520031ba0542d96507103955402585171026102061030303020707040c4860843d440500e1036503146c00921441c030450030424000306812102101c4c0c841154031640c120003200880b42c0c0c803410a0f9000444003100c0301c000c02c000c0400050114043c0d84403050014820742d001100b42d94000001c04199003900104045000d540881400104160201ba001e180214011511260380b480d00010250010302914450f682001c3c51b59050b941c000320232031035000d0035500421 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 752775341 1250 752774091 752774101
    0x10818120a050c1b10090b070303230f040b0601050702010e0402030a1410050306061c020d030e030304140a090e030304030311070209010b120601110d110a0b010f080c0a120209 77
    0x203040c001c01000907200c2c01016880c00e5401046504084d10800c221070070201144001400c0e00c0d03010481c8100d190704101444282e020a000780e000f00ca0344184100e041c659482c2d61117468200001c129003020742c1880002c02e20080c0003410078a1503010200303003412450840c103074001074034011075400d03214405c40e0000001124044590080b040b01c1c6484211302c3c5441c10420340c0d00403910024080d0901a110705c03000504145000e1030200e000c50102002d12410051a40a10280090035101034040c000409001516600c041005000520b103144000c256446000c0030807010004960241e0600d6041c440301c0080301030302104030303500982c1c1030600007466031041020b1080d6006036113001c0e62060546000181740300d01100207100441c000070f00349610356164401941c41c00401c0110510940c071943c0c5040310907015070311561801043c3c5080350b08050003641c400100c480700344c10882e80d02c0340250b401c00c045d501c20050106174aa04071100410b003030500703918010b40c000c4100d002e446109004013141c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 752776591 1250 752775341 752775347
    0x1020c04091e0804063b010c1704030201030b0a03080316090f1502060a11160201350903071e020d021e1203040806010b2214010818120a 60
    0x8098509111080104008541010f140d680c00500c28a00821030703501c8184445c05900c04d040d01d926580f41e0541070111071b40d0f084102c060221380503040c1030107011034007070012038103442ea208429104d0304002c40d5074609610004044e106034401d070b0341c0192220002030001991100c190381d403010307103594060b071080c0c250341b41142c00804a0703000d860359a0078090045074002c14000c05500311982034085a40c29120310709501c01701d80009800c01c0300705034144032540c40c051300880c840340e00070300525051210040189541c0380c99240140503d200c81d19040c821030340941c81c0031900f42e20408210165003440d22945071100801d80071010b101c001c1c1100316221045668030461011840e40117171024126204000440384040d40080d40180316150500d106d0140900003c00c5034240c0c0d60300c9010301070b07923481d200d8815019040710400c052403c1c80c6011041000c005031282d100240341104001400230403810003d092400b0103403441c0c000210601940c4052240040e40c10506003019010070b03a04d880c208011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 752777841 1250 752776591 752776613
    0xe1b061608030109060905060d2105070b0901050103020f01181a220f0b0a1b0614040804061403070206040f0203011116060b0a1208030606070b09060703060e010501020c0409 76
    0x10807609010001085880b25603000d082a140e003014100710b036445078800c22118141f0071800500c00c0322100c00c000c20510740c0d0a2000c00c20001420b0130383c03c0c104541e0700c4010326682151480301e941e55640040040d441c0009840c00180c1c000c1c28003203204000816100c2d4151002e0040a104201c01409013940c0f2000c602117031408050390384000580303441841c602c2804011440762495001000c0d4011a021320bd901c102c4a00c45015280c91030b80c6c1402d404400348003000e504003a070394a651501c150b00004090074030320344210b12820004c1da440381008009045603a00078001ca07800354080c003c000e662600003038480c0c0c1203504440c2c00460925a807001a0240c0816031603000d06000200350710f14001c054003444038129100c0c40c0240501074512007070200038000c1c2d204070a01c000c0040712070404200400000c42d08000041d107800e14202c842c2d03d40c0d500b01041550307409000d074055800c015000f0303810300c14440505242da0500d039040d450000000d40c0c2d0900d451940348503075a100700f4001001001e0a134 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 752779091 1250 752777841 752777843
    0xd0905011b03182009150901060f020327030102071a01090207080909041515060e060304230c150d0f09020901091e0e030702011205070c0303020702010203130e0a0e1b0616 75
    0x1681e43c1703038645001d299103606d0031460740502928103600017140b01d5004483d82aa0301031140e0040d41041c9030780072160034000c094105590320001c10319190341281c80a0008205490140e45200c4104440d00c3d00e00e02c8050059101032000e910500c060400500d0140c21103001100460705801c0301d840700d0420b5100300089101d0040518580603490003100d2150b4403810071500251640d129000004081c0102c520040340c00900d09120a40b11051144011540c0125085e003036044034103003540c10000c2550903800701556400c503032001c40d1700e01c0e0b07001e498080c0080390340c00c4c4801884201d2403680451140341c41800788460444d1541041c00300c80c021503240c000011110745040c080e0811043c41d80d0340300d0b440700700c09a0000b54a155001003007422800744c00e00408040e510030304c0c10041c58608600130b40142200301e046020402c960030458024118000c064084401400c6a6061421040d811600e10750800e40072500014550010030b000c013400407606c540103a407003170b0344c81c560107910a0894601003c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 752780341 1250 752779091 752779099
    0xf08151003230910020f0409050c1b030306041d0a061109040501090507170702210715050108010606090302011d0604050303160203010c0c1e030201020d0905011b031820 74
    0x1072140c88800c482c88100e0b00800c0403000341e44a89044a1400e0160311451100d600482c004110802c890b41c801c3d80039541c4031664103149820001406403104465100c24000f0070300f5407011060000a117428802c0007459101d008800108030100c200d4544c450500d642c01914855032054010099a030684c101c405086004108000300e40e12441844c0062000384d0b0b8420001c1e08414107491002c1c84030070312a000e0382c8507800034908083c5c8801160340383c4020785949040d04405000501c00540c6111040c0b584444411022409606042c421821110180c2c480e00070000300040070000350f60041150254120300301d80c4102c1c6040500086206c0e440385a00454042c400051034003141108201000b44151084000b07022004038020222418031203038001038aa41e41b0346110050421503c00800320051184c000981000c000545040c225010001e05403800e0351112462101b801101115080c169111b041c1040326640078260452071907115a0000c0c400c03100c0a60921269103010080302000780014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 752781591 1250 752780341 752780381
    0x15020a0314041806080c09093703020d0216060f030506030106030f05070303090503070501080a090204090b09071d150d0515270a021c060b06040306020a0f08151003 72
    0x354400000c02d43c605c20603005000d03101c0c40050760328280040f180180724680060180406041010386540319495489408201150100b01c85405003004114003d000f50007405c0d855420300c0c4d003e4180f031240000851f00c0300034204140003a40e009004110b561410340307000607a03913a611003c41e0042c6900c0e040900410344140d60310f82042000160002583d100c3e039240c00030207560320249940d4001c14040c0034041405100010300b134103010703030101d1140ca00040000c25a951503403200e2201182c1541e00030f1850f0800d801c14060822402009000071000c442c0510707091510015030f10305c0210300c000c15842503084074106410b0110400c4403160300c40b40440e50782c0e5a410010011640102079100ba5000c0810800d654214401d011404042068010703080c0111a010800c401850305021082210300f03036a6481c3e00f100c44d40722903003c0c01c00b5600c200e0005946859401000d0030f0782050440c4041085812002c1000c0920040305a881c0c2201c184c0302c6456414441c1003d0300603201038a00d90f4424200c1d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 752782841 1250 752781591 752781629
    0x405091902120a1209150503041101050909070207090c0e030c100203040b030c0712110a0b0a1104091406030601030f03080a0b130b19030c050907090b0c01020c0715020a031404 77
    0x90403100c4c0701d071940ba00c0c3d0409256a13040b8001104200040740c002189050001402041d0070400c84060408145009441c0c0205c1c2c10018034a90000d5561400580c010780b0305100b03440300c42c821268420f134681007494442c0781d40d000180e510800c3c021038070301800c0c004110b42417090080040c1e401404120b042d040d1a0300e8890001105904644400d4842182c0454501d5a1500880128058020300c101820b103800103074403a401c0d0600301030b0032807800725034a110b8a082c00b078202019001074035802d14046203100011011080c200d602400e06480780e0807030030040000540d8100c0310328100b40e06040c046102e540c0c481c12103005001400074a900604802515000c8040c958040090107500310b0326488900c074691101028000c09005c0284408860202800303c4d18010020310b40c00400d6240000002d81c8907a21210141c000a029070a00da4020546241100d001c0c0000030240c02d21200d52031144c000c04500070340d2008403060240c03e020f00180e07825550302d07201c01294060411900080000068 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 752784091 1250 752782841 752782853
    0x10020c030316020c030a121806022104090e07030c05041506121506121b02030a0c05030f040e040c270213030203060106020a06060503011a13060e0a0209010206060405091902120a 78
    0x8202c0030310b002500c1d01e00e40b80c2c1000501448e11041d262a680101011007481c1440c00108081c120901e00c580428480080c400d520b9000300341c64120300c07801400740c0b0b80c5145806503541c91150800e0344218203101181c0403480d0407541c400200c0f540b500e05801142802440f20000b0400282411201401c069012449071380100340005c000100030020820403442e104071203610b40c4688503150041e04200304500c406446801d1490040e405942580d107008150b420905590388580c0c860013100d4604001c000c20f10581c00c0c40000100f2010340f2100141d10b007209d910034010303d40c3c02c01441081d40490540d5030b2031300e500041805583d0180c1141c105507140c580c040e40d1031503240e000701c0c0d07200d050102c0403034982018018002d805858010511003214448100006c031028800d2003615103548180010302410348020260045080ca240140da070700d0008002030030190001d040c40e00030f0b410b1006000b00b01c00c1c005410002950603075010800c800c2d8503c001034216100165414903485134045600901c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 752785341 1250 752784091 752784113
    0x9090b1f08040f151a030610050105070302030d0507020106170c0102070314101103060a05040b0a0603020a020f0604030f080106020a0f02060903030d0906150e0f01090b040e0a0308070210020c030316020c030a 91
    0x2070600b1a183c2d045c03c110040540d01c40c401c8440511845c0c0940c8100400c0d4090000740c020300b4800d0040c6c070f050800300708810b4110b030030480b06030006031b44034a005c014500500044420307500c0010040c003030322071203400080d54074540751000400c013800803202c07912018010301c61001c080c0da0012082c4020900d000c20030f1501d0b00207a481c0b03441009203590002c0e0a02d414404c3c030120040140c044030001d41b500f20309500941001c4902001d602880da00540b154105210310b9104a10945401201e0700b0b00d48001046030005812500555100d4880b24010841e00c403101011241e04982d4940c1c1c030f0403aa400700c2d00798062001071103003140c1820700050070401d1b1904460321541d440ca592180141e80c0720500c0105503000d0350300300d20500d1418010321525216030804061450041c2005c601c2c1160428258034210342108142c0005045505120307000d40d062040c110000c10b2580d0541c1010412143e0f5a128403000d0140e40326200300e104c100c0c540500078044804c400a004003502c02441260070b00080c920b03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 752786591 1250 752785341 752785361
    0x4020112020d1a03010b030a0609030302040302100203120c09060d0f02040b0a08040605060306160c17030a0c03050a060f0509040501061a030a0e06040f0b070c0501060609090b1f08040f15 82
    0x1000b00156540f5906051150094102d40100102001481c1c0d4a90b1401009054010f074100b40d020040840541c0302c480020428588560043d1fa84010f24540c0c007200701400381010204040c10002803280b0703038800d0b003900c000b103000410000f5480501030040300280300b41c2c6d02441c4201c3d401308002040c5600b00c604184980d0203410103018555a000800da00d68504440c111503501c0300016481e106445003002c0c4d400c1d0362241040026a01d100030b1450b00a8208981007540951100c0031411020390501075070f0b03040002d2070024005c040c01d0501c021251003d03402501d0154100c43d00003414031400350810f0340201110100742205220031080040168001c98481f18850305003030001c582e804000541d0340c4240d03002000801607104a0b952461a000060008001c0014840300040811000c0c030404000b070034281c448056080c90690504141e40d61244164803c8140703889050786441089105140405507207004040c541e901d1910540c811440c035005404c155021401c1102e030b050030b03031040c8040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 752787841 1250 752786591 752786621
    0x17030d0f051e0a0e030301030605071e0509150f0f040623030c180405070503100f0b0a051605010603061505120c1c020405100617010305070e04020112020d 68
    0x19458102030140c1e14142e680000c15031140c49030400807200d44030a0340e08080b00c0400840c0c0030140051091558100380c00c296241c80e40e480070300c0781964024900c1e00c58007103102c40d04030119034003940182c1180541001240280c000005513500030203010110f40c110710090303042035110480000390070b04540280c0104004200c1560322011200e0103013401010160314003002d6880c42d6a084100480f5030841d5068200d404450100440990b803280165441782c0001c0d83c4240d22442c190280400b490b4265003c0d0600d00003040041c01886101011a8844800c3c0c0c03c0c016524404440004090710224202512075480d00300c0c04410847c03190404213440005800b018034035500d0ba01000f04142c20400708803020380c484841d031021402c0c02040310742c0c102d48090703072141c4d010890340204055403400c50329006007802516040c00001d0700840035140520441210401c1981940d8500d0740c0c2d04510b006d903d903610304083c0010111382c820301991420545100017075407a0107120b4910005014640344c04009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 752789091 1250 752787841 752787851
    0xc011803090b1215040608011e050106110c0607052b02010507030507020c0405190e030301090e030a0f030513080a03021216020d030908070f05030c1213031b17030d 72
    0x41c0524000a440401440c202c0072603560b00c4080900380d11006a00300300f17810944035400002c2480003032040b80c0c2c103023903290040403500b401d00c0d9800c4200c981c140c11110a0003119103000410070400125490420019611650340d02c010b410000d01e0118118007403060754001203410003d05080e40f60f0a07c20f40c000740c000340003503101e516042c1d064840850750000180e00242d40010700349400c0d04022b8020060420243c3c41000c58110300c4152405404204600d600020042082e0351152103400241d1720325102450500182d154000c040c4c40c41c80c010b8008164980010a81c49101c82c0703c0300000c25800300c20317103540d0300003103030081c0203034220700340c924081841d403030019500c080c0080c003484040d8880c0e170244c0141c8008100a4009021034141aa10900103200d000001142200c1c0c00101c14011401152a80c0c00d500104d07252103000c4941003040042440004105005080f81c0401d483e486201800001c0341815400e00d0380408cc0d21070403c2e590485000d54a0007000b000600b05031500010902c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 752790341 1250 752789091 752789099
    0x613030f0e060a1817010b120a1a09070b2a161e05030708060f010603020724091208070e0105070818031e1509060609040212030c01180309 61
    0x151141607085150b0040b60403c2482d0001e4440e0606101c04c9807000807180c400b640b501180e00455051405a800b00d07076503036102c1429031501d601510107c1917030700001c01c00500c156454142d20315914040c01002c0d240b80c008113841d01e2040c0803001c09401d0170720350a03031203840c040b0300803841e200c0f010b54001200c00030302407020000c40007185440c80302c0583c1c0395a071906803030721107200d0f42d4205034801c4003d0a00904004911540c050040000030305400c8018201c5080a6040b600044010303440304040c140304100703c000068605090b80c0c003212080d14820044502310791042c1c0513100100000b0104420005001c4005810242d10390140c1c40c0740e0380d517400340988900107440906c540103001e0b155610503c0745600c659151040f0040c09076001e0252071000a100c001c120104034001202025908060070f000b66040c41180120b40c0527541500500c0e0a003060004a80c65501c05003000e4040d0100a4000d0300e100f00030811584a001d848000704050030194a907240d050111007811800a284100001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 752791591 1250 752790341 752790347
    0x2130203072001060f0e0a06060207030c121a040506070e0102010c05030a1d0a11010f2a081b0307020f0a060813030c0b0109020304020f0303040f09020d0603050613030f 74
    0x2407040c61251181c10040d41c59000300810300481070507660540d901c5010100d61084e540d48008010120035404c202d079420504001029a00150481411544900c1c81040441c0340d082036030b001c60f07607402502c0c038990496051500f444400d0086400728030b540001444100f040024045111301000c0c0c0d2442112050700c001242640d01800c60030001400c140013240a40740158004140d00b000304c2d10b010050805610070904000c29620140e0b00700030798042512807035070003021000010310b45151440d030840000d0f420040e1300401c010f02c0d0b0b2610181e00002c1c001c0000d003e04036103c44130707007a20091f5515010343c4031030358941c4012012401414050030400e014202240ba01d001e6070026220311005640305045a50441492003007030b002c120410091700041001540e90328040c190604000d0307924034140c01880b1680895110540c002d91040000b002000103203081d00c8103840d00301402581e900100900710024024581018105006460038021041014121800d80c031f407298464010405c02d1503815 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 752792841 1250 752791591 752791597
    0x1b0c11090615030919080406031a0607080306010e03070b090f0a120807110a060309110901060f0c05030d110406090803040f17010f1a130e030403081c0f0504021302 72
    0x198014520b80b00c02200740d54a1009503900c11200c60032920038079030103104d40c8201c00304028280c46001000900313003c00395150241030340c8190003682e99103144076114049101d520030200c0103007181401001140c50740e8815141d620304200024204c9038201c2d1519406240340e804181c542d84921114000a100d41c04e2030780820ac125a1940002c2e0a1000300b0b44618465600040e0111481c0840040c02c0c0302c03540d035255a00019050641d0001031074001c5103405400c001c4103c0c0010700c07032202c4e00300401c07a003a4003002405005200d40f6101d001903c3c24945180356000e81085131452904289042e01a209180040c100700d890960344c0050190740d40607200c6d241c3c400c074013410064001300c80d810f20010030301c00c00e00c01001d910200000f4494410203403031011503000440041d89441041212005403421580c441340c10a1032290030040d036800050569520f100c1c07440000c00d154004500d002010030421168449441400b00900c01c106000f1180002010200e4040b84035013080c0522030510103007442a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 752794091 1250 752792841 752792851
    0x106181107061104090e280507052101141b0c07030602130b0703030f050c04050d151401080a060c05070b0604051f060e03010c02011107030c05011b0c1109 68
    0x9051415185440b000c018002c560721015121104020000f0985c42e176200b1644081c09030005421014503013106186000768000c40200300c3d403200103410f8042000400c202c012600c08031110300ca092682c48516901d00542a003440c215440c140d03c908013010706121131072040c145c3e050000d0660140c1144e408a070700820520240543c000d11061000035560740c0200500450200d51100180c0d558030486a40c0d03000b080304400281d20b0b4007001000e00c443d0302445030428400c503903903030403d801c0c2802b00b883c10000007006070000315074203002814405150710007003070601000780d12900d56842c0c4080c55541c00303402030220707222850242c226032550f10410a0b21000395120225041d41c3d00c0c0d04c0c08000103001e02805a9505412460b44c5100f00c140b200344d4000180101d40300c0c007400e41603c10805007101c4030021508250390500e559101c02011110880b88003a07410300784614078a105060541c01401240710301c0b010a03c80c201c2d440409608079030040195445101e9001000e9501001d00ca003070681035034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 752795341 1250 752794091 752794121
    0x608030d020301030c06110717010f090f0506241e0d030801061407080306060c0c06032d0618070c050a0f061a090c0d020903120c0d09080c0405091608010618 69
    0x14084081c400c403c9c14030228100c1c00202d0203490540d2031004a8000c80710488030101c1100101c02001010f028680c1d10a8401001c07020152980c541c060002012445c120b100725001c10504411500d244920341c25480007900040c144034162034083c290900a006030300103d4003a20004080c40c07805411a050b41e940081d01c80d0650321288240615a00f200380700b100e490080116400b415281c00016503c6840b019660800c440c0c2d0ba8040051041040d858000c810026403040140a0b101c4c0c04a170700c030111280042d8140340c0e641e1041120f400262a400800ba03009400d82070040c003200c1d804d42c07c942ca0249c50104601104000c80049001030030540503004199100013540d020302c100d02410316080040c80152a000c917401c0004e00704001e000c0c800c0c2d07005e000440c5101c22514100035050207420a42001030501e070800302121350b10303403517100c10f103104503251000100701c584240405400d0140120440180584030700500340038180351b010b04030758036100740860901d41d441d0340220224150104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 752796591 1250 752795341 752795353
    0x111207060b130f0b04110421020d0c060801060e03030306280f091a09090a020607080903060405010c031a09010902130b03010602030703090f0b1c0608030d020301030c0611 75
    0x10359048080c08034550031562054001c9209000e5042c9030007000c0034450758100c006402c901c850100400c41e85d503408074024000c401d00050003900482c90040401d04212543c2c45d6000a291001460f09956030318000c0c030000c41ea2030005821604004c10606851080d00e0f051802002c075410b0664034007080342d0044e804403004070088504240300d8031280d1041460349601c081c0d65200c45000902c03050690081c0c0a659407400d000c1101c7c5405030b140702e02c807141103401000c542492006196030308868580603205080c002504401c1050711421600b0000c0c003d03081c0e4940745403a05010303000301a02e40c902c9000c17174240303007460b406d15403072070411b1182050007081340b8901d9090540560094004004000c01c401441e00045190000e0750017440c0288031a030f00440d550310207454010404062a80b0030b84030741c202d00307100340a002d200304140c03450b0f10010300d4030546800300101d0210141259030b100d01c03541d0200142060481200e5001103058900682941220035900c00b41110f9240c480521000341c0d80184c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 752797841 1250 752796591 752796593
    0x3030f05160f030203090303121503030738010617091c030e01020d14040c0b12010308130b03010603022205010f050309010905100c1b0503041e0906030c0501111207 72
    0x40b400d01a42c242c000c0c03040300d00700305250000c02d186034030a80103140008114000c1142d0104500f000001482c03056024505014550350740c5042d042604c8140540800c0c8010407045041d06040e6030180ea5010701a028000c4d6515000034103a0b24109003890010950300c8000341000e5400a511014200c1c816035203c41105800811402444e00380440340d010354080254a64070b10b018010341740c5075048440000c589042c40d00c0d001d04c03000ca00e5400307809450824400c040705030b001c0c0a25541141c2d0080d4100c3e588000000e00001a03500540040300070050100000c500e00307078154050842c100756910301d10342d4401c280d201200c0340109440307503034005140d0680e00024030303200e08099a08032299000100d5507104070b59036076080c001d541c607001c03c0302959850016610344e809102d4965129840c0410780b4149500c0c1c50b56900c9109034040c148015050030004820b0300090721211000700b08a54023040010380700d2400c0d00b80800c1d58070655001420141c0ea5880c1c54a0210f090425981d6074402141b03070400c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 752799091 1250 752797841 752797853
    0x306030c01033c050a0b101704020105090d1704080c090f06040e1507020c040c0f0f081b0d0b030c03150a0902210708070602150c130b120103030f0516 66
    0x2d84050303045019180f40d0071198588180c090f4038000c401d5000042402071014090112440c100707135100c020808240c60b0010300e03d04011381c4a81007502860141c3e541c3d4014008070f000e60b001307000700078003200440e84400560103840b00604207554507201030b110505910340070042440c41c15a0420030f40c00b4800702140441c905544010f80c001d94240a45011801e21040e02e80d455004880306001741c0c000c5c1c0d12160a51030140b051000364022400c1052068007008001001c0148514140090107c10000300c0c80d003200c003141004141d0300301b0a6056036544216044c402902c880c0c6400d50082c030901205603505e181c00b02d40d03601c0b41002c1c1c030413070030a41e691403070490302400d0798020a03038001c402036001d00200b000204081070b0f40180701c8020000c0914114100345006401ea2140c001c54008400005000d8035840170f0039003205d03c03000071580f41c00303034103204c115040b006600814080c0700c00a4032150f807110103486503040b01c2c001d07240c900c001310701118161441c4c41000d0407403801d1240503510f9400552 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 752800341 1250 752799091 752799161
    0x30605130c080114010c080d060315051603150f1706010f08060c0a050d0606030207020a0b0a12050604180f030f05070c03020d050703061d0618060714070605010306020306030c0103 79
    0x140514009840c2d460039207032001140e003e0308241c8e0106403204424824000d2502c0001e004611300e000c00c01403486c00711903090f40c04040220142c101519140c1c881d000c3c0909075603410141600b401d03440307801641d032000d000c001d80e01a8000c590500030900001020549440d0a40c2142e103400090f003400d036511414a002c0b03a1040702d00f58180701060122402c0070a5603c182400303000c507900e0040c3e44041c140100440c035040c2d9880000000c808000b09007105610200b0f00c1c00e0300120102c041510380b03401c0c4c00140508034419051103002c07021180310301800b000f000200e071024002d858180384402c0b030000880e20340c480c0c200c000d000710005001c1003005040c0034035034484140c003540507911341d50780300d0740c410054800c50f580e6514001c2c07001c1c03a00e0011440600c811504080f4000309011552000d01405072190001031000042c0041c0c0d590b18040f03400d80208031910306a00200c100507940c1c60780b801d013009400995109009204441c0008041e5000c1e00c14514450a06001c05040304850b44500c40b86074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 752801591 1250 752800341 752800379
    0x6041d1e0d0e1011010216021807020d1b060905011b08060a17031209100606170f0405070812190c020a0b0d0e0f030408300313080703030605130c0801 66
    0x2080490707000d00c0c1320f0003c0c40900200014012a40302c1e204c064010030840703142c1d9840c9401d040c2d040a09004130307603400003240503050580d0700703024176141c5d406411014490740d0714002910803801d02540c1010400194821070003029003490000d9854401801206c02e50411564640c12019262007800b44020001c500e4411500400840e0301c0c190416005201054090314810b207207601c041d80c20007410f00c86000f21000b07444035180849503d500c120014150103030282c60340c410034510002250501909100d034030058072508044510b41c03444030403d000d090344020540403008182e0984088114420b118612a207a0028400404513080003417441b420360110404c203100f40d40c3c546050552010501241004e100c011001d991200d14190700c0c2800d040c20200305212080b08010344a0420712116840c540604540c1c0c02c8545980c0c50315440e8130445c00e0000c0c0682005004541c1d80304256068004505507001a907810050b20030001c41d05058949061281c004549032a0040c0100a20000210980 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 752802841 1250 752801591 752801597
    0x209090622020a12031806050906030a0b0301110a05030105090601090b0a082505030a050604020906040905060303090a08030c011a01020307020d020a0b0f0d0501060c08070b06041d1e0d0e10 83
    0x2e0303560001c132821400980000c4020400e45c0c3c502280f08180c400048000300310740c0c00c0061404401e0b20000c4c40c05e100003400c0020b07031a91607071f2044042c0c6003503107c0c1f0500d001c580303072507541e41c039812502034400e82091140314840e500d90300008a055214101035421a11444581400e24600150950740c0722030041945000f04200c46034464400100c15840c1803040483c0c441c01d070f6a09044102c075050724002032006020b14010003480c2c1c0b540e211501103404480d44940c0c005407640307500000a046100e800300190340320405020125078200040b00400301c0c10a8400204411400c2c650100c0c0c04184541c103060142c1c109004500141c200032005611052008102c800c949450b61031070025900b00030300c0c0d02501c2d20082010300213041d082c85070f14058842d42c144405c0c548850742d10071501c0d106d81c440003000c584a040205016444d55001001100d01d98910400c1007448080d415945150402c01001c5002c1001c0c080182c41b00003090780c0740825019070726001e10311144028070010050f01c50a00d010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 752804091 1250 752802841 752802859
    0xd242c0c18150310090510050925091e0b010f0e060d0b13050403091215020d090c080d0201180b0601030525020606010801082d0f070e04020909062202 66
    0x9540c0500c000c100c400c039410300005d8035045504000d40781000410704072403001e140a051044000740010f00c2440040004401002d0801c0002e660340011116440410a40d0a00b0310319920b06010020000c0d9251600008000300c0300c500b00110342440c20b07200c1c0080850140b4820146a00b009002045450303a5140c1c04289200c2c2d06000c280c12050f42a006250656218184001c06910952040040400c041c0c3e200d050161910391500c0608500b02080440b82d0020320f03681c00c071100f600304a80041d0410060041c495441090940303c80d00107401c04015480c22540104091641c100c200b0002d412800c803017442d58078140190300802d809050707084035210b03400304401d11200c4281d005c3c101d200298007070042e6040c41070015104400c181c10500d61a00081c0324040c140c6c803110118401c1c2c1081035400f0740da45007070001c000c1c20280c140341290711a000b9881d01042080045a5480c06944250b80070304444c0c1d01d504035035440c1c00c1e040d40c40b20080d0b03031401c02d000a4a03040d0006008a940001c0080035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 752805341 1250 752804091 752804131
    0xc0f1d0d020d06050a1104060e01081519061101020406050909090a0b09010b090f07050915130b03010e0c0a0804060c141801030506040b0d242c0c18 65
    0x41c0d50700b41c2000480e4004c0e01c3d4400c224080a0303070b0191302e00d60182050a00d0038982003081c0607000115298101e41080342c56400240c02140034000c0588000b000b03821301c550540000050b91220f2807601654004c00e0303540d442040000d005100710ba086680d6a5581d908004103c030400885000c050b05007080d52144121081c0841d6252802c207000d19680703400050b03942c86003002c4c00701c0030200034070701640c00f040202040038030342c0c000084032181c0808230790240b0001c921803101c008502034000b1340041001c0304c0401091140c0141c00660586643c210322500a91360308a1400701c41c4101c0064500003410300d004200060419005500c003c066420f00094042d0800b180000c0f82d049501d1442c1c0081d03107000e0700e0341c3d156054400c284d008a0152014030401442c20049502c1a001c41d00082c50031805c81c0760a50703201c1c2d03a4682001c50300c01802007400b0200d0790f00b00c080c6c1c1601800c0c402c4041c0d08015041081201c81c005081c694602d8042e21880d070344080c005241c0d603ca0300c0103154001c07002240360869 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 752806591 1250 752805341 752805349
    0x30f030c080c090918190b0c09091f150201020c06060d1a071103120609100308160204020f0c0a0b0109090b070507050f0709020d0f092307030c0e0601030c0f1d0d02 72
    0x2c0d107004070103000610508047c00d210115600c0076106200c011010496018251540d000a0340d01440000303150341c000003041000380d03980c600303580181450382c00c0118004d6120383c1900104075140711607040701c0c2540c03910000c10004442c010001042007280c03100400550403440c0c1010f40c01101d5091006c00980701035009070950b480030904c0302e05c8280d85010045030b4a400050319400414003a20b1103d12401c40d07640e8901440f4026200d4001420808034404654031a01203a180c014a450000d465802c1c00d02c499903607036908002250902c1d10703000081003002c0180305652006411800c01101915091001ea0f0300d42e100d240b0a9a850103410701d01e007501881040300e031000784811100107941e140300d600504200c41810b01c900070850b08000403d408030706036608410348000b51140d003094410541128603d85020703940000c082c1c600b018400600c0050300c100c154412002a2000c1c4401000942c0c2240c03401c0b00754042c00f0108503175800d0994a0600f031040c040514001800c40c0ca00c3e045103800203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 752807841 1250 752806591 752806603
    0x20a0e09070603050f07020706080a0b0d1a07050711150909040c06020601060504080c1509100507200108070e121207050705030a0305040b0c0304050d030f030c080c090918 75
    0x315034000c00e01080996454822290301280b4000b0b031001c00d041a041c004c1d2a510148240c100f0885c0c11130101d000d41c485540403010b10380008004511681092400b04000c1481000060742c800302200000c4041e805030013225070f1282d206900e200c4100c401c1c0200050b001000205600b201e030284402d441a84806907018081e9004000b89101149840c5e070080c41e1002c140c00c18004c00506100c200660350002440060001c421540440c1c40702c0322020a20f4070b402000b09803540041703a40300942175190410014600540a40c1c008046c501084841c59401b0605c4001139002900c40000181040c2c4151107003400c4034001800b01c03800d80440500545441c0001da91241c2c1c603800003a5030f03010058200f00900041c20250301904981880b41c80181860060384200e2080c224005880340340d9070301c10b20480c0c1c05408010700e081c100c82c41c1800d00502903120b01801c0b00c042131415900890f564001da0302c0d640b046124480851500b01500b061054615002c2c0c0440c0151414074a10280c02d5828040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 752809091 1250 752807841 752807851
    0x10503040f050127050f03090117251d04090b0a020d0905010c0e12060727240e0a05100c050f06010e07021b010914121218030708030a0c020a0e 63
    0x81030751441a828550700384015030401e6151b03030303108201d8001d0590308150a2500c1002125081c0800d5444410180c101101c84d5000c076040c20200340000c0d0366540000c401e080322120706014061001403d02804101d0f060000050004522480002c03c84011034001707003203120305254080f034641d50590759542034030b0000f081c8a010650010450340c00d8201024529507409000008090a080200c0701901c03c968688607044641c17071212900c0000c00031560450000c1100d103a20780910002071003203102155140280c280011022041e10f943d52a201e200803043c0ea5008141c0c0042c8602050290361010501d00304a803180142d1221600500050040300d008002d001c900c6d05551800c01002814558030b0114100c55a43c80305680f14188d03801070340b42c016600115441c9200e0714181c400038090010038034281c0d00d6485094541a026002c00000e4500402d00d116180070508500d010551104118020100c00750700611201401c036100c1c9401d4035915002078241c000d9252200083c50090208a075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 752810341 1250 752809091 752809151
    0xc0a1704090b06071a040309030b070503010612090b070e04090f110f1002060f0705040e070c0c06090b072307060c1a0105011e180321020a02010503040f0501 69
    0x50100044105400b425030110000c9821034030344441582d8200890b5003150050104520000000b41014001d0b1200b401940c1c1007512621580b41c2110f00030305960090240b000025085078400102118a00900d82c910340d124107074103440d41c0ea08408940d4401d010720b0142e031007038407003561401180400c1c082040b86030207000303403400405201041c400c02c4110307031119502421740800c941440f0755002c00c20742d070000c0003612031207030648030140b00300d55600503074205602c0e801d10741e4180105a034021300c611400c0d900c5840450b503000e541d0141691040d01600c40c2640d01c210411004002500100c1b00705848003141c2d80640340803901441c0c4619003a8290002c1021600340c180500030b0041014100344203d000401d03500196041c80700080c590b80a004c001c58482c103a40b20102d400034060b82c4a0326009000b003400c549041e80c1c906146c0c100b50008440790030003180c0c48001400041c40802e40c81c2021b40c040e1640b03465612117a0703d0088140c0002c006484039503854110302426000c00314884e0745083c080c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 752811591 1250 752810341 752810347
    0x120a060504140a060b0f120606090901270204060504170102042408090607050a030203070c200109090e120c0304090c0509180402010e1e150301060921080c0a17 70
    0x3e070035084030400d4001381c288010900280c1d004920180490f00c0c941b0045209417a039460b00300c0410024012004041d41c0100890004103c0080030f8034000304000d04030358150211511842d101e02207208a014100024100304014042c0301c4540c18070b90300042012000605d00b55640c1c0c541c91a140090140c10340e01d00b0040881e07008140e11281ca40d41000c4041c02a2205007000040078003a0b1003850010028543c0100000b07104901810781e0354900d58101d0380041400d0409003010418019805041c3e001c554900c00210b1054100d104803c480003a0b038008040f251821303e4014040e0304428000038091004010100d411401d0380203225a100c4a074882d03a8840350040c0c100590042022640c001030081c003030400000d42e03805607210440c624140ca0089451000d080c1e081c19102c0924510b9401050110001145030300540083d03040762030341d584000c046503c5110080e01c2e088039440c1d41c5032203800c0465110225002c00700402c1101c80800c2258010b003020b0780c991500d021401c1409442e01008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 752812841 1250 752811591 752811601
    0x320011404061b051608120405030d0c1e050d02010f1a090c04230f03150106140708040b0307021c080703110d09050109020909010b0607060f020f0c060a0c14120a06050414 75
    0x1004152071425541f4051403c05051501003070340d841c8201d202d801040011003030102400303001d014040c2e81d070940d40316800c02058181066523660035180c0d0110015882d10300400e04801c8244184a500071103001c1c1844406c81140800182072005000031507200e00c01c02001900b2495240c0c0ca00d0003600002c80d50903545a400208200b19a103607214034080e4100b0018901e580802078041c41c103451043c00c208007039070107080c521440e40c0660f4070700800e00e5000240c04100e20402001851142c8116800c9594010300001810708001990014070049841c03000480e10481c080d07040130048407209c8520a04000c08041180c0555107404415180c5955402c400b1080d81452140258411081b200901100c03a4250209034103100b083c07000f0300322694882e080071081c0c415804840008203d20718036034840040c00c007420740300c3c0000e40740c5d80d035454580800080b041d8020320864501c0042d40c040e09040032201711030813425803401072101403000d07a14040480c035591180b180310b918103540f0184410510301 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 752814091 1250 752812841 752812843
    0x108010e0403050306090c1309021c060608150117071e05090a031704030206040f091a090f1308030108070608010e09030f0d090803010320011404061b051608 69
    0x10303004a24600310354010400840c3d0070108880e0003100c20b4500c2d51103a9550451036a0714002c20700340c0100c00e603941000150362a5036030064001400c07d40d10a0300060048000d0604561451042c2c401169030000000c1045580f4480c8031803603507045c1805101c074010b04040c00010601194104003064030140907100003030000301020038034281c5041080c40d02d0b803030f9000104590000d10008107682c0c4000890221040300401b40d500465015000303d403126280d02071000124282e00445821500d002e288803900000503002c80c240c0c2c0809406500c036502c0b44520154140001441450401020038903d4000343d10000114001e00c1940007600c1d115041800050400300107a20021551802c00c040c000c070a1700200444001d60b80000302143e542103001c0700b54000d0710480130f014000403c040000000d103c034207490441c00c00d096038411034000c4c040c0e00054070101c01c54a039000030b0103410b0005000260103060044d80d00d017028418000301c025a40d852500c0c1c54a00c5c01a03181c080f03940d030010811200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 752815341 1250 752814091 752814107
    0x60b0c0f010c0815040207170304021206130206090319030302130504150e18060a140105180121051006031101210225030207050102061005030613030311040e040201 72
    0x100c0c04000e00814000410051005101828030700501321202c0500d0b000c4d80d1643c1c1298210b95100840304804040028a54082c2d0402c5500380d000d0700c240e03104500d45150100704148140038072040c0380d43c14a0243c080c892503411103452160036115140a030404801003c08140005219603400350381d601c1100383d0165495401c0e80550b001da803d0203101e40da2200116000000d4410f14892503c955840d261404442641180040030703d01452040c8103203a02e05822108640380794001842150760703101c05000b0381644c40c105505120800d2030040c86030528500061001c000442da50150540c03151325600d05154110801c08090b5989240802c03c20152165001101400f420008042e0300d1800c142c402d1040341c404614509a80068006001c2440d640c603e080540301c4a50452041002c1c0b501a58403071013401000e016114002c000344401014480490aa0710080e01a00e03040e00d5550100c00c40040012003101031645402043c81c09000000142c000cd2000c1900c4610b2401d007400058040340c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 752816591 1250 752815341 752815363
    0xf0408161a040503060408250309150f020a022e03091205040503060f2d15040507140d0209060f120903070f030c150f06090e0703030921020301060b0c 66
    0x80401d0100304229613022400550054206803001da0f140c80032120150103213407150740c0b012301c00d501648103030600d40d0040c0080c0603110015000d047c0b050f96000117031f0f0045d42c070442040043e0301c00301118005007801901407007070103040414018016602114416816207412490001a80da001c0c2007041c840e106548184011950401c6071420b8200b60100341c07519001414103d860040c40046409502d000031071109103414940542000b1a81d51403c207840c18040d2080da8641510040304032072031404d48035250086030039031100707110000a882131360203582240c1800030602c1d5003803021402d00c1d1600c4004008684540c00800c0da510103080c0e025400000241240c0300c940d00600154000030b4100c01c91207042a0141071070700c0014198038040c00351105080070014542c0c1854040c0044140c0c80c0c100c2030a41d1070b100d81c01d209020300024000d60700c107024817000d03002542000c01000a410150301688070f20f0300b4410650441840d0b500840d094514a52000541020020328074148100505c040340340c103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 752817841 1250 752816591 752816639
    0x150618051206240907030518070b09010f14040f0e09070b0414030a02031e19050a06481b0204052206050609060a0b0f0f040816 56
    0x2124100c40596801000f8000c920b00381e8001d52481c01d840700520000300c59200102211010f18007900d0040c0600000d4030001c41030011351441010304200400c0c09400d907005400800e0405071041d004462a01503103043d00c00f800000d104102d68800150000c0c03019180c001d001035003281c589550041005401001e4522982102c0420701c81204180b0407a8120b6000303228241d44212100d001904100184a000794144217060b2520710409000100d4840c902926058404216048c01e15610070350200f98000c0139904078280080c000b41c46a803101040e41c0c4084250185291200000c8044240160000c2c40801100c4d004810b0075015896550401006282070724120701c00f4821007030743d101200002807096885000103100103420142e9451056031880100204840c1e03828100000c1000391840741c0195518800100b0ba400c024400104036000040d0705480d154012151072540d0700a140c0388a031104040100241801003044040c81c0c80a00c424105405403803c28004aa9040d0f8140c44d004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 752819091 1250 752817841 752817859
    0x3040317010b03040210030609050a060e0106020a030c061d03070f0c21060c02120d06170c06030103060903090308040e1812090d08130605071419030e0415061805 71
    0x20003500001d0340c0c1c000d17505803941081d440c41c002040d000303451250801c1e41d00511f010200200c00d10f458000400300e1722030040142e081c0e40c032000c049071160b21440b0007401165116215034000707003481c4e111620402050b0000c08000b0280d2408505641c0300040580b6114034544070542407180e4508124000c107000e920124409281c1c0c401e0b802980355218024003141c1d907800b400c00c2c00305c0c002c3c022114980c40c40c441c03059860390045500d000400a03800350b0084a4105001020300c200001088861200b0041509003183e10310303690b10000e410301200c110100084040000001508440a0000f40004000310358182c40d0000c4011713040d111040112182d980024852074040103624111041c4040c10b8a4002c41d400c218101800c062003603035400b01e0090b00c14080080e046612102a111162003042c1d00301040c510b10401c240c3d54151210000c100d100081104000280914104001000c0180c40400c0c000c2c18901211141546940504e0225800100400c1c00003034031707403030000278190448045c84 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 752820341 1250 752819091 752819099
    0x1421060702101a0d06060503190606050a050a030803041a15120604020603180f030a1107090506090112030e040501060e0a061107050d0f0c0803040e010504020c1c090504050c0304031701 81
    0x180403d0080031405400c0c1041c1490900c9680c2e0404000f03072002078121244d40241c200c0c241e1440d00d8045081d902186022401300b81032500b01a01021920024990003101e81542c40d5088164030180003103a860b541c1c00711070803e12090426141c0f08203601201c0881005001041c00186800301c4501041074000d5070410006941d0403050380d41250500d20a2107521030f4400842e03151001c2d032013040d8194840891080d6029500086012081802c40b05a40013541e44041c25419100c040d03c420368090900e40043c0170413142410021030a0740030b46040600703604c5443c0031500b11340c42a0811030014071031382da00f00454207000e46800010449482c01082000b40000016102d42150103a140320380528081101407040e001ca441000b41c0d0003400740038489a0314a401507580c1c0c4244180e281003143c140000980d03103020310940b080b902078400503101000840c07090b41291442180104140304110001240b540c9682c451288a42180540141d5a003450f060140c0250080794902c0404a482d20044c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 752821591 1250 752820341 752820371
    0x3040203100b010e0603091e030c12180d050105011a0f12040c03050d11010f06241e020318040605010c1b030b0f180c0a142106070210 59
    0xd184001c00700c500190807102007004a4641c01044040341d8031001c007000b808502c3c100429850721100074050480284409400000d469014110703490b4540e41250300e0040d00d40341000f0050541c0000040441030500090000807603032007001c8030903552a03540d01c00500c50a191a00d1031400e801d1040304190030300c403282c01c1089682c45020041d02c800f405074000b1030304101c000c2e01d140d0085c42c0e10506884404100e844002d000b41c0b0012041c01c0d00d58241110341d81e8402481c404d40e0140c031060022104c0c440014103040269150580203403081102e03a00384403c10310020755030710203042403c0e40070319582c0680510200c03c0744290b80186104c3e0b89820000c0100d0b83c2c001c02402c41d51903000354980c01e0903071203000e410400101940b010348401041020441c0d54500d25442c1d030710500c44540301074000c07050340741440d80e034010a6585a0f00300001200c2404901000001c1e510140c0300109400c0e00500c0c0741d190100c491005000b815020b5005c0c105001c4815014071031003540300e080400c100091b42d0541150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 752822841 1250 752821591 752821603
    0x21606080c07021c170a0314010302010903260406030222050d0201080c0f12010302010f0207080303071d0303130501120b220b0901030b0703060611070b0a2610090203040203 76
    0x280b041d10026050001c13101d0314000d01000c50f8020a802620380c2c1c50700310004544d403100f641d60300007a04c0c100300b504204121442c0681603e8040e5039102c1047e04650390070b90f014000030403c0620b417403204c4401c1c0604145600400c0076041c165001358951044060101480c0111984400301e084260410300c2035484120f1200c066580920f0322601c170f41c44446107200d0700d106804020079a1140054104003036030300440160304a070b2003030b0307030b04148080c600008a03121301d80d501850005800400200e030040b0b12914610448542d455410070400440b9000070b4915404070800038440d80c080c41d020000c0750303006245103e403a20b0182d0203111000151000490b0f01c000d2001780c1c2d00a98094203108011103042d4000c400c0b0080280c000c600a586900f400c0300080e00864a12000a080078008940288034950340240040c1a6005099041c03c0000e21500ae07013000d41040708105100c100a03d41c102c03119511a010048a4500407103400d0401007c4840c00458004106890042041c40b0060b1000900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 752824091 1250 752822841 752822843
    0x61e1b030207110916091a07120c1e03090e04050601090e0f0303040606080105010506120604090606091505030118050703110d211407032f010608030c0c03150a020c07090903021606080c07 82
    0x27100800b440d9000041d0341001c040040a404d2648620007050044043e41011344824000d888202c000c40d501c1851100700303002124000d02e1500300a0042110000540013800b4600c43d18042e81d006039900e0815502d5a0401c88003565181e80781c01080149003000e00c2603034003400c000c1d01c0051078540c40b140c1c0101c4035440540900d0040d9a00c0d404d09050011661110014000804050084051440040744a00002d0058920039480d08009501c940c0740302c140407201c0d0b68404050901c051458507141c450700601070500c0d401803111401c010003c0c2d0468140c015440ca20307040c0f035482c1902110000c1c1240c410302c0040242d402d00300105000720303400040396610580410300d0980c5101241c0f500905029100c24600015824240701090840c4003001030a52280c0b01812550495005c8041541c0d40d030702d0705981c42000101138081481e080158008001c04c041d01e800b15802d1594904050044401d00642540185c10802c10000011207200800004082e00d20705140310b4109102c00b00300501c19000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 752825341 1250 752824091 752824103
    0x5030f07030b100f020729030c09030a0318080d0e0603040212030a1d0604061707090f170610140f0d0f061e1b030207110916091a07 58
    0x800186400e2098200903110340001c1d2107094010003c1001901540341c8450038400740c090131a0101b404201003840110ba050411344048000182c170100580580c005484034030410004c02580c0c5007500d00b04003904080d8441c1d0b1313602c44004420650000601c460f9080a19503410690300203540c141d2100c1501d03543c200c219000780c0d485d1200c0c40041d060300c03401400f0020324003001c106803a005410111452011003403142d4802000036800801900b0b11840c02144003064000b2404801c1420806400d0f034000c48030b080202c001341c0c96407443d010b1203c2d10792003298080c031000a0048404000d01c0480e801c1b2280781c581e5480c0c0e604003100c40c1c94040004510030301960360b2102e008280e40d10b10450000f51b681191141448030358505200d000782c0358000d403841819000000a0102d88443d02c50103900f40d0702c0c6a0650f0011080b80000c0780a07620281d015070301c125546160b10701540d95540d030365014030212070800038489801749010388000070503484010140300e017260301004081c82c01d084070b1307900381d10407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 752826591 1250 752825341 752825371
    0x120c0317090f01090b3c0c0c100501031e020a0302011103040306051003030f021b0103050402060702180405250b0a090e15150405011d0f03032115010503 67
    0x51024600504080300303407010340c00d00884d48188241c9828490058642c126601c0300d1140d00c1c0b490b20440c440a48216598540402c3c04150102085000380d03000000080c3c414585002e82c100d843c40c1101c8a0214080155503000400410138032200b81c50701c0c10030b411081c010360b402d10740010790304200305d11010b41440107000078811503100c28001c0328007560340400b00b00300b1402c0241090300c0060700703804128003003429503544800701400004e288071441038600ca4001925410001100030b0107000d0300c2260001024410a00140e03200c01c4240044621a450f010041c40e240c105507140840549400c000ea401d00407170b82543d60205500c1d40141d400d241916540d40980d48411030300303260701e90311640783c80703a9103400d00001c002505102140201e08540d8000c0510041d00141141e00c501e03c1401c0c0400e24010881c0e06108075000001900d040040c03294900e20303101400f003401d40c1d120290b00d050801000000c498071a40400f40640c00c6190000254940c00380f602c0040e01a00c8041c0201001002407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 752827841 1250 752826591 752826601
    0x405011812030c050c1c020a0501020f03251a190c090603051009090c0e0c0a0915020c1302130801050c0304020904050703080a1e0e1e0415030c03120c0317 68
    0x1c110084440d4000307031a1180f081e050281b55400010600d2080740300c1e410307010000400d580f0001e151441940c0c0708018600d400080711203002d80e08030000c00c0354491004610100085440030101c801240080c0201c08a03030b19100c0d56011071003004924507a0014a49000301500560010600d000c0d540e590800140341c0c1c640148212030305c0b4442d8008400139040c801102d04000000101008403001c02030042c5060b22080000a00381c020911410002101c20501f040010003c1003080b8688071240151907401428001003140b10740c880c035010b926650005440ca5402c00d03003041800003090b004008014500745078145c80d0175844090300180c4900c4445e0b010070140b140900c07128000359070044e40c0e036a644040007009000c1c034481410f1540881d11121140b51081c0c020a80c403c2048170040c800c2030304001840b000c000c2c1c1c41310324425903005981d40128812840000301c95202550040079001100c1c1e01d90b1034546a0302000369400410401801c510b50000f039044000c2c080e030400c05490340b00d199030711 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 752829091 1250 752827841 752827843
    0x90903090e01081f05090a0b0a0905011a01090b030103020d0b0415020309060f0121080c0c0303072d150b0d02100e15130b0a0207031401020405011812030c05 69
    0xc6900802150711102000103001c034400500c403501c000300145030000301c50300d02c11040100d803c1200d107203a6a401118038a000144241e40680c1d21480100d000610784610380c4a850840d007420855000e12115100000701c00d40e084a411001455100e56a0b1320f1581580c0c0803030b01007000c032a4004c00d1421003e0205041200d50f842c03201040c100c04004549a1070001284c50385e6a00035641c8900c421028400030600070440440d10000380d43c24480d00c600c1001c69a9a08542c0d4402012150350b801410180426690240020040f0b24040d0090425082041c0325403291010000500311260001c00746a100140004800016260000f440014003107200008200e20000c0700200079400390008250407180c9030000903071100208180c3e02c034102d15126088501c65423044a031710030300c24424140d0400031501c03040010004240c917807054a03841ea83c1d03030b5100d101c025010204400c259402007028800307075130b20100c00f4444904d0b0032250084035282c801c4038428030658640c050108100c500c003800500c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 752830341 1250 752829091 752829107
    0x40602120711060a050a03292101150e0703050f22020a030b041704061b02030c030f0a060f15031401140a060801290d050c040203100e060102070e01090903 68
    0x3d440365645000b0100c00812503486920f8040110307142c036003920f002c659048403040641080390420014042c1c842c0802c90319040340141d040303034041c0c522010400d6000a002d004e500910269003605d103c0e0030b040307110740304107802002c8038100f610300030030007043c0000200c0f00c0d038104403200d03244441942000c820500c240c22500010350001810740300081001091400c19101d98010100565111542c4c1104160351080d40300c0c0d040000d01034600d0325840301c0d045640001c1d051004084031302a180c802c0101e402c1007404070108901e40c0209200100740f12480c0200360004400c4282082803190b041541d081c01c0145000241c61480c03100e6004280200035800034104140c034601250f03680c0307498000740300505800c3c06144d22075401c1180c00c00400711300da255140100740c1c1d0098140f19011380c0c82404070016040905607614401c0400c81c59043e10340e44000c2d4001c5081c0e401d104541400c01942640140d0050215030465000c5c140030420401c8000019040d16220100800d000c01c183c20200c448003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 752831591 1250 752830341 752830373
    0x6032a0c06070806100e0603060402090301091509053a050c100e0f010519050714210c3103060e012414100c0f051609020406021207 58
    0x110a0009002d0701c240c00080080c42a0001c807549505812072080440d1515840b52505400405c01c0c40480d29a00e0503030042c2c01f11001c05000040c0c00c100079141e01c40a1110b601d0091040340e5203860350428000c00b448816198010000000040c40d041c07000a6000b4561070304c0009184240e45d403400c0380301e2254084442d42c000c420210340010007440c0380c440c010140c0c044814018404d030b0001015641060042030b1140700742d050b2041e0620700c0d400c0800040d00d030090203401008041c83c1d90000d100490381c0030b070400c0381d00c1e540c0b9044075044482114000003c090300c00c800f1107109010800b0365004009240f40b1000c0442007003c101081906103060001c1c947d000146800d003040300b40c2c00741d4001548018822140b00d401100d03c0c51a25051007284001d42c00395076002c19107051940782604040e80d00c2254006107180004a944076900d451850080d0030320100c2c4d0580180707144034201c02c4901c040303901501050350114581858008041c3d9594601c14140c506203601080748070501c280361507881650 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 752832841 1250 752831591 752831593
    0x3090303010e1509160f090503030d0b010c080301030f0605070809031602011e05030f0f0613112104020f0919051503070e0f0a0903090902090f04020c011a06032a0c 72
    0x25043c0440c550a003090200045e0300000e03182a07001d2882880307000c807001103c5026002d036150101e000c1140000d0704c50300c0300807410b1141681c20400010745640056000790b0244030300708202d602618041c4150341e4090002410040301030140200004003101315040b03086000b0301c035802400f0718401a14481030720314180c441003078141c00c0c5000c0c60740c10500541c4190361600e0881101d43c0c2d01c03603c2c002ca2100540c0c0c07041d003103a5a1080160815200e0b0301c14105c400c01034120a041010580c81e0105006001030070480b03c100c400140400c40c00d051740c0071114900201d0320a10580740c4100140c00c001010803840d09480d4480000c2204248204c0c00e124190300007905480050342c50b1021000d0302c2c2010388801c1c51481c051070000b840032449100303a401456040d07076403054031850b007880c004c0a03402605506e58002040040002c00d80d903241b00078150384440c5400400c040c2d038107203841c8524401d1204a00d0107000e0420400501d00e031401200c0000840c580c2500744c0b41b030114680ca01050150341b200c5002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 752834091 1250 752832841 752832859
    0xe0c090f1c03110105010305211c020405010e040504081c0e010504050f160303020a0803180f07051005160303020f0c15010311030a050601140607082d03090303010e15 73
    0xc0c0c20704224580881c1d6001e82c4440c160b010340c8180150889800b4440a030040e0006218805d526603998901c0348802000c0c103150781040d550b120300d03521260400e0907040074140c0c0000d0030405540c11900740592210f08031820005890a502c40d030015105e007814420f00a080011118038695113540700e03000015030070700200041d03e003d2500564540f00c1c0461500244070f802800c50f00541414070601c20340e541980604024060366807a00440d0b00003600768481030464801801d1001000c000e148511103c01008041c42d514001c01d020300300c000c1c3c0e070160381049010043c00704030034055407803038014540c14640180d0b42c100129031130010b8099508640c006008900364040942c001c120418140c81c080c40c45101641c0301076040641e104601e0700014800c4e080200108940300758034841810f042409000d0620304082656001000d90001c20f10b034507054030340400d00c001b00c02c10ba0002843ea443c02d0040c14a9810b12155060741c074001480303541850b40c1d10300001030500141c0d251800d110107015242c0c081c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 752835341 1250 752834091 752834119
    0x2120106050d0222030b340c0b0f1f03031713080706141e151c03110d0212070f11061204061113030311071d07030e01060e0c090f 57
    0x14050341d0911040c0c1b11001d548000c1228000444d08413400e01c680d540b501c3c51150100e0b6880c90320103650425003420700c162100700f4004580ba948495120340340d02c2d42c500c4e4282c83c10f401c49907514503150441040700300743e07180184002900415a40d00315035500c9540030040e5140d41001000c0024000c000348005000714402042001d01c0e0000b02100402000000c420364407092509152a21a84044950500440030941158000a510512032400b910700c1a40300d1031404009000100070400b01d0005001003040d1192000034031400250303041e103101a000610903031201c030019004205010f400f002201040600700a416480060765001c081c0c40da50b119003111041408008040b5000d6501c00d003007501400040007e4001c46490340705c64012801c8450440d24200c031000319030100d441b032901c100704000c0f44620001c00b4920003001100300714681c2c0e1518500c0102a203505803000d2034968100740b01400041c0c1504a6598040c0c14414020b03210640c100025100020304020580c2102010950b16 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 752836591 1250 752835341 752835397
    0xc0c010905030d060803030c0405040504050709110406020c10080711030c07170c040b09181219170403050406030e01180804090e0a1a1306051e0a02120106050d02 71
    0x1000200018003007000607a960601900c6e40300448a0700080d00081209201c289016400903800034041d9040f41d20641d1512254400c642e44c03106145902c80010404120340d035030402580302c4411043e6091109400035400103404100081c0104080c050720105c0035001e500e081040c0c3d07d844109004944145035181d0b040d030445140351006110341e0080003030400aa06140c092625507180c0501480c1803540c40a50400c1c55082e040c1e1140c18502445145580d8110200003070811100c114048940000310000080e102ea1103505840031282100c008110200b500801542d00305c0e413107400c0c0850f000080c0d4684074018444220342d50005020511484140300d002c2010304140c90b00024100042411401b445544035106000100850501c07a002c000c3c0800c05200240c01041002503160310f00e40c00da07643e0090b900c044581d4807400c030802e040302501c4103d11134246c0d005040501e04501d0815030700303006190100f050180030103000c0e0003d1403070b030200c519a0407903000c100f8030440c201d08420200501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 752837841 1250 752836591 752836597
    0x12030703021b0303090c09070212040b0c0d0f0215060a0e0403031e0204050609100302041205060f0709080604260d0504120809073605072a03080c0c01090503 69
    0x40b441d180030300c0400310403400004226400789050340b0081202502d0740040048042c801800c250440c010140050814a002d10162002d0702050035025110002c0d82d104515244000d5611030400c0f102902005890390081600b0103420384a44042c0c9459075640089400c81450758402c1010400000800040c540d260703000b14940200c911070880d41040388106003080e8002e074025944d00440c10442611503107001001000091110f00f409410b00d40d440440005641d18800c1c280c2e402e400140401c560035409d40c0c0200e50129990502c00d9850b41044c844039900d1074001d100821f0f558172b10082c0c000c040b0303403440c0c44040f18151407081e6580b001918501c01c0a48020740d01180c00441035031035001e0036400788258602c92200718004101d5075240403601d10201d244100c10803128071407410383c2894400f121890118036102e0005c0850700e03040a2500800302648178007a540c0c4c50740100c00142d10644d110701c0c0d9900741c82d0113203418070b03094568034070300380d213a02c1451141345042d80381240c9502008004009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 752839091 1250 752837841 752837857
    0x11310b280f02060603071d060a050a0b0301061407081213020405090f0613030230270a0b04061103040f1202030601090b0f011407060f1505010c0213020c1203070302 72
    0x3d6038040d490b803405040e0345500c14010701e0201c0d0140001c0041c000d0031455103a51062000f4840c40d841c42e0b0706c4011403143c1c2ca4940008021f200d0000c01032203800e41016082100e89032903031040340741031015240c0f1300e0b03d4011140070480c0c0d01e030050085018141c0000d1003480790ba80085c001c005504240d13a030984d5a01042061000c2405980d0004d810a07243d83c10b004140e0760560040d0081098201c1c2616100948100c50315100305c84610704800c0e81c01c01405800400d00c071086c0140580040c02410038003002d10841c1c01c1c841c908200080c0062000041520200c0316107040082030440440152030440c02190498405061010000180a4202e2009199181c02501503d42c26607e42c90068165154002c8540d08030420400e6010154420200c0c4400d1400500000382030034000d40e201019213085c0c400c0305000b01d40340c02d410000d100014420b0402072009080c80fa841d0821540458148106d6107802c8000343d03404100c400c4840c8050101280081304041c84a542e131420780c60103402034000d142 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 752840341 1250 752839091 752839093
    0x60a0608031204020108043305060d05070608070507170417061035010c0e03010c0e06180d0b07031a1809070911310b280f02 55
    0x400010000c90100c01c584400524010a68080e6602e13001505c441201034000c44203d8452500c041c8003184003042001d070648070b10b004805882c40c10b0382003c00d075500544154810360201020800198002604500310758032800d0103002e07651041801e481d103016011001d09051480308205c1104208440108180d807a254104002e0741887d10071035680d02000c89501400441d0407006000d9100c880d1401000c2030302850002ea440c21403d180074030103690bd00388411242e9111200c800c01550050f291a0344400c059008003c0c4035008000180a50a003107111030241100041074115408a030340b166100550251904503c0899031a107000a01c5c1c2c212003560000745403c3d000080c441289142c942c0c094002052050901c0396003501d00c08064025160703a82c98070a0100c002503100182c014000b58040c00c3c0c0b030680d140c46901c2007104420303042003092050038203190540e24014140103080000c1e120142c2c5e20782e40750008450616400c54881081c91403c090090007491279551010080b0b004181d158 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 752841591 1250 752840341 752840351
    0x408030d0606230c0a0606141203030c0f0c0109060c02030a03050108192a080c0109090b01020616020c04052401030c050a05070201031113150903030504090b040b040608060a 76
    0xc034201c540f160b40c03011452020780c03201d6091580002c000042d21006104900b42c8511404641c0c50304c04030780c095400052111940d80400340035150040d035580a002c1280051803440c070700750080314064403401909600c42c3d50b02007071540144000f548a4410070364800d100300400206500042e50b030350070103002c42000030304100020400345400300308040b10880c070300e50308100e041140da0b030000d07074031462021300040005503c107580402151705010b41c001c010030307005450b03121a0034000409880050300f1506140d03051035411a0180d0740024550382c0030b107080d0003122460310685803c03800c01036685854de074814104030903c0104140107081000001c0c894143c910070b07544c40401075043d11103007075548010903c188840d00580b0300540c018411244149000501903000c503681480c01d07001138560807091191b01d0700a0100c6403105034002c1e40e02485003044c00c0290f14503500108544640c0c042c103480c040d00d0f00780c2e205450722a60091030800310f0052050000d02e440b0360102d5a540c0d01146c86008560501c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 752842841 1250 752841591 752841599
    0x5060315031603030906080a090c0f090e0105060d030f27060908010903021e210304030809070b03060d0c0b0a02010f0b01210c0504170f15071d0102070b0408030d06 72
    0xb4661000c01c40b80e054032503004061a01d682522041001007003086450384983c000b0000a030a40c802c0009891405016001c0030b050089400482c6d14044404180343e00d083c051260b1a0b8030f08148010441d41490400032090018004403207960603a00800300004112804850051180c1205802c2e64000e546480355143d0301c04000303080c0d83c0f0300240500583c00100710080c0e1280d1001d082082c02d40100700300c545140709907070030070200361250030bc0c1501004044103000030186c0c02a4280e070040222402000a1810300140c0c061511028100512680d42a1103c004014035903c420005102441180351944020340c000381c041c1c0f0003643e0200f5418a8040300844070b600a2034581c0c21540c540d401d01104150030b081600091081d84610000d000080c440000c0a0091030310189200c50800050b141c114080815186440c00b140a40140101300700c0400a42c2503000302010105045c50598030b4600b010707240140d003003c0168020154025000401040c046000001010b100b000303204104500703070307035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 752844091 1250 752842841 752842873
    0x40e06090a0c080a0c0207051305010f0503010606020d030f0b043b1f06091e0509010507120c092103020f0d0e06130906030b0603010b04050c0912070506031503 70
    0x442c50740403001c10500c101203090041c440c1d0200513403420b02c0c0125146192503000051445104030008004243c40d5001400521040082200100010382c002e01003035042282c0079407180303a4049240c0405a480e03a4500c0402c07525000f498030250054000c00000c206d821060008a10240304903078018031407943d900010002004e00b0502c0d29000000d021501c22008203074440c1903500350103001c0d0030744800b00410b2940d1584244000d44e20841e900b810030318409603650090f21002031101c04107901d4103040100c09504005a1848100ca41500040c2a030f450f0405403002c040642004070080300e15032030321100003d0381860484050003a000ca0301e0f56041d0200440ea03a4405081020014021104000a50401c280038000701042000032943c2c0584600340070302129010362042d55600c0224040c403985080070720891800800c2920244a28038182c89041d400384180c601603405002d445909101e59102800640c01501d001400142d0700e0070f10003500e6694044543c0640d200e0f01441c00c417a16040c2e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 752845341 1250 752844091 752844101
    0xe070f0903021c1704060c05070b04050303030a020306031c05030702010f050c0a0804151a0103050609040209010308250804030c05010819021e191805030c0609030f03040e06090a 78
    0x2e4000c1c00740c48000d80d0701286501444078100115040024030f03010040c1507030410054400381c4402c1d5903201c07001c0403a0610602d807a4417907111f071000c54420442481070307841c00300450740e001c5014440542d40b9118007010a142c40d16681d1711040c1010720901d4411b045a0290066029070b049a00030300a4901400c004401c40780140c404e5001000e00b006040d60b981e004030700095009005091002c0702044140c5403409807807140e400c021404161600606940d0303018804d19800290035668501c0074582580403c1d070404040c04003500b074003030115501c007440b00034445084104102d4110802e000d20945804003807600f0901049601300414070000c2807552003178040d20700c075040b07044000000800c0116000300a40c42090b051060604942c0807005150128004016011808900d49034070b07019002c0090a041c1210b039104c010018920040000d5980040d15190440d0100c0f14965201080300020707290201034121540d2a0001003800206802c2c0c11040900c60181501d60315981d40c3d8180040341250 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 752846591 1250 752845341 752845343
    0xa0603110609010203091302090904050703031404080d2d09140d12080702011506020f060627090a0212030316020115030f050a0605150f0a0308070314130e070f0903 72
    0x1a05c00d0107200703c2ca1a0080c2d1001c4000790180005261003a4400070407003486003150f05075450343c8004401c004140d8400041c000d0041040c4441e401c01c7d040c401a50340303514100e1145810025049403882011000030400306802d1201b0740304a014907201c5101134407403d0907100362040303544000210002801c1c02110740e0b001e180d12140b408020096a18240c5003000040e00c000115981c4100700c1c0c145a0f074000010000d000c0b1900200340018200340d00924254000703062600801d000e5038806034402c65036070142c030300c3e03040c10780c4844455944421051900c4100d000c0039601092900600c0e030a00e9005c0000c60148040001501107043d0102c026820b03034039880b082c40c0030400076450400120315440100d00c0950301c0b0b141914090340349030b220801950410341c3c01c2c200c1d00396800211400e43c5490b0082c940d003858180e0b8a03801032407031500d511403140110007000d803d001d1802c00d60344440201d84120340c0301010035603010032110b4035002c00d0030100000300c801d00c0124008044540955009486400c02c030303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 752847841 1250 752846591 752846593
    0x1b1503010e190f0f090210030c0e060706150f170105060a05091302030a050d031505030303010911070c15080c1c0c0302090603011d06010c15020714060a06031106090102 74
    0x40e21450040c2d60704584010a0700c01a036526101650149410b0151070040000c2c0c420108030051140104903c0c00c510f1001e031001d142c5000f82d48210550410198a0000c508035107940e1205114104040908162901e035054000501d030301143d0100062070000075104010214050202450722041c03c8480984400381e01041c0c083c0c00f00700915195460651052001400c814400e400360301081c9803801040c01110f03a500f0281c482840b0a0385442008189204400110741840c5440082500d0748818000d041292752560a10406447c600044507402a40000f40c2c1c000d040d55004800b04042c80741c008180060b609501080030b5000710400d441803a82010401c42c03a00443c07002c0344009200806124050603001d0108420696401c00070350b000704848185020000c0000307400c10854003000381428140900c580c129004501007110b6204c190b1510040140d607402c40c2d041100080502d031404003010700c191000c0155490407a004a001c807031180070848040040c01c1d04010050062604041c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 752849091 1250 752847841 752847869
    0x30212270d0503070c0302100318060905010608030f1905030106120c2705030708010504050307200402040303050c0d031a091f0e0919020a06201b150301 67
    0xa281140814105008010041444442d60350b00d0450b00302607800c0d50301800440e410410350400311061b5101e50854a4104885040d000e41a0107075000218080d01099582c40c0340c400f0010250b014401804880d01126251882e039001c1801d9640b10704681c1c4081541d1030003804038a400707042034074143c440603229a800d01c0300d444820700041c0000e100721410005000c040f2a000c40d96542403110354009110441d41c0d071400c081c1450f1034992240e20181c0c01d80e1402003000041140071066580307caea840054003142070940d0000b400c0454100001d542c1c02480040c0000070103030460020710041030303084207594140c2c9280c107058040303d6132807900785489070600f88111032508c2c5c02514142d0100e500c00c0a8600841d02d0034ec450400002c5411048200c54200140150b03032008010404040490034500c3c0034011072680812100507481c803840092190709815000000b0610400c3c0180c41c07403070422560400f407054031048648034102083c030b0145a40140390300c810450754046a059032200100050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 752850341 1250 752849091 752849137
    0x904121b02090c0307020106050a140319020607020d050c04020a030c1b021003020a140c03040e22030f050912012301030c05010e12070602060f160f052113030212 71
    0xd03504c0240801c0031956950f402040f1076a56088650252444440f02520f2240b61014503261200020894043c4c0900003280c0005a40702030032a03010942c1524040656240b51408601d40341d05195032a40c814000b05900003803541c158030a800c080c0180c0c0d01d40d035194506403031104070600c00c0c46020b03401c4005406c0b0340840c00c0c0660000c19a400f254a0084c0a9040c0303042018241e0b00001403030b10160300006800c010302e9084690044c1c10203140a602c8031242d44101d03001207243d10245c4e0003000d01c90712805161505010b40180d0703000080180201811580f5000d0703082c02014200e8000c0c0320b0b0b01d9501009100039010321011030680380c0c80304001c0010b500302801925507400001d8240c0d404025092400150300f020700c01840200420340040019080600181141e040c008003210b503800c010380b0b61480059440b15a5000e0200e05003842661141003544840078080034108041400400c0350a010381c84900d03001111034503000754280c801c1070801011015451240e81041d52803021a640300d0b00d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 752851591 1250 752850341 752850361
    0xe03060601030c090f0b0705010e06090a060908070602120a05010b0f0313021f030c08060d120e0604321c030e0d0b010602160503010605030d120b0904121b0209 70
    0xc84000c03d900f000e4a00035520001807404111030341151081d40004100c51081241c2401350f85090340c03800c00900403d14000031150364820084c4009041d054a924066040c4a001e83c1103c0e20150450425036407039442c92181130300250280c942400c903a1814000003200c01d1482c041e9091205c281c46140d1843c0c640d480720203605011070354142c0c1e22041c0e10101045103940361703404002c10034094802140230240610041e0500350020a014042d2000b40214000512900c00005402d6224101600304100900c08140c40f40540d8000103803034207100740f004004241503207160361059031005a0300d00302e203a08028450180c1b50b0051550444a182d60342d240000d0050340c01c41616800070340214001c40668960600c0b010080e031245016801c011202c1140310b140075501d4010302010340c000d0060320315180109654a4180c018030003000300300403401c03000d1122604070b003c080000a0041089080600300007410015903d0a17502140d0704012429078415419186080650000c2540711607590725600c01c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 752852841 1250 752851591 752851601
    0x90f010e0a030b06180f09120723070308160209010512030f0a050d060f0806070801030c0513020c01020a0e011d100c031205091006081506040b01050c030403210e0306060103 76
    0x8140c1c010646980b1141c900c80c0c9100c610b06c078030b80c4481101c0035814000c520504048200340c1c10030700c000081204602007080d034107130a81410410b40103401d013000c28074506402c0901c40d420040081c0300008842c24071004040e22201076034000c03100d80c0c4041e40d842c41000306444040c41c0e94440798000307020746040307003049401501081150382401403402482d41c0c050700c2203c849812055a0b0400c10303c09100c1f01408000c419031146042c10102044d504503100e000c40314402d032090700e10030400c1c090041e0008035550103a4003c815000001e40d1503000b1101c010340030900d062060390010302009500030103031179404080425048094000303070b104002040c040300c0e100c103c4035043d03082c000004c81c24180b00d0079030b1242d688981e80680240c100d510350032007602c0c203076041030340300c00d005500800307422524080960300300d600450211000a6035400c0300005981d51302a0040d4085039000208000083c0701e003d1104007103615a490150100c0054803005542c040e0f00a00c0080d0107501c000c001a22a500039444 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 752854091 1250 752852841 752852851
    0x1415070812012303010c0e0906060d06180b1e0f0f0d030201090b070203040302010918090b0709140d1a150a0b0c1603050a08210a02090f010e0a030b 65
    0x1458500a0401d00103405824281c1c4000036012086184001c40c92440000c500c122104030024400000c4100c401040e0850901710648558440300100703000d40d4680d000c80f41d40d6600060140055640c440e590154491508980600c0a081c0342640d0b2551a14280d2960805045225003003422031881c1408507545044c0745031a0011200080742e02e03203030743c2e8007840701c00c851180c0c0c0045007024861032b041051080141003413003994811301c01480141e800040c1c10007941c0c5a0270030550400c3d0f081120034043d01205002801c401300b600d040c411010740c02003035181518000c1c0d014190729411442032041003080c0e048050700d002c0980030a8070140d1900305140741c10140c2010820400d44003800025880138480d8000c4260040000b042e054162051001440c0700c00c00c0384045c0d800c0c92035601da40d602c03000c4140000784041c000180c0c0703961005400106101d66401c4040c61440c5190000801c1e000354040311400d4490381d800c0220141e03030f6214041804420601400004e41c8034950350b11200c1c400c0010300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 752855341 1250 752854091 752854103
    0x307020a080a0c020d050a020102070501030605100c050a0f0f050601061403060607031205100f091104030201200d050a02160b09010e0d050109060603120302070b0408210916141507 79
    0x1c030150340c90060461701140100058003010000340700280c6000400e41c419814142092410813203a40c0c3c0403010311a1103035034108015200b04610386181440420400240b01d41b01c4c0c00014820f0011034804500c61500c183c04035080790341c07038a5060b201542754486082e054402000081c4403414100007515119100b420030340400054000301c2001d4681c01c507000030b80700c4945901004595201d080a00003000c40c958100629043c40c56030301c0c114421800043e040c040b29120038141031010038a031039000c031801d0060b10140d1600d913000824543c81b54202800500c10a540d05070070203043c4010364112040240c4040c83e00004a00658801854044680c2c2c402202c142c0000820400e002d500400c0748075210008500c0c1c01c619002c1c3d5407542114a0b5070170940305009560025031000c1c410381d000354020305020307111810440d0602c0c1001e42c50345a004403105840030b0004080c4005412a0303606c11a910203030890741c4072007503803555008400350740398403032a4440016180200e64004149050040e5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 752856591 1250 752855341 752855357
    0x3110d050f030a0e011403150a0b0a120b041814151008070e040f0803040c12050f010501050409110613080610210b340201150b0307020a080a 62
    0x912200c1c189800e030151031240d600002090540303150b000140004410090800900d40c40075914401c0050000070f0806500c18003500001c00e0319a5154500d02c000e0100c08801a070b11101d0313120003071200d000d0000b03100b002400c000b03036402e030384c6001d015005110401e8003180c03806c1b8586458030005800d244400c19198000c2c500c0701d10312005190402c074440e040b1405c0f0741d0007052815605c1450103003258059080c18050000703000c0010103160707000754110303000150b4a443e5141e60500345c80181302c591140f001c41000355680c9003003040c04910038803800402e00003000240e985a00707000684129180041c603071110141c0400e0ba5251400107002620119440940311548400007035203010010703a880c66000e02540c608110850030201043c8134000712007401c2c00380d00c1c038a0f900c4a000700e4000e0000404c81070050706412480386c40c1040c100b0307200d0315500086104008000007a008044c40300c079408030404e00c96030100b4028602002c40e40501101d80c000c0c024019507494040083d00a1301e0b150003042030907 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 752857841 1250 752856591 752856593
    0x210902130c030617032d13090f1a030c04020c010212040c08010f0b060d090311070b0d151401050703030e10020417060106050f0d061e030b0703050f0103110d 69
    0x1600c1a00c038494140d0b200040d2890904e51103040d0800410115100d59100b044400401d0240803442c0c0351509400181c0c1c2c81c0407924061440031030003940404403d641204ca00040c03500c0c01d40c2c1280c0d40c1b100d030610040084950810054040d07003c4181c40581590049500f105213090a50081140940c241300040c2080000c00031121015801e45050368204840b1209100505c0d080c80342c10078882d96608208603c0d40c0e0139010441e54041c00740311401f0140e44030088030915000d5000801c0c40c41108041d00c1da0f0a88230f41d0308140c0c136001884242c6645203041980145030035011214015a0401403406904404280c01129240d00c40b100c22030400d80c072050318000d46281003040298600340b226001d078441303081c421480b60b40304103180d041203542c0c40800100007403078014080310b000100f0300350801c1c0c0e2044890400b802a00c000d0b404100a015810b103800441001302007010142c9200ba5109051622400c10441c20745205507141c40407030981000410010b00c200710103a04001c0040d01c0007000b03101e1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 752859091 1250 752857841 752857879
    0x1090f0303020d180311090606070b0c130e010f0e091216021008060108061201021b0307060e0307080306041808031603060611031c0902060a050c010c210902 69
    0x6240d0084015070300c608040401c1d20f800c00014806440314a156840851540d1540b0340120f641c0d2102038013075015240854a103880c0c481c11280141c0d00240d20950703605006420001360350046102050801070988081442159454010704a4010341c6000a6081c140707040b41c13007601e4001e040e50362144510343c1c2444502c4000d001804d61440004003150108a02e0f0041c41038002802d191602001507071800c0102e6680c004e515183c004805030340840010444005450080c482c01c0c4031901103c0250000c8611601e00100400060f80304010034030140704840d10055603805100c9000342445020310003d11141001da003c05401d031074880190703202075950b2b19160400e600540b4a81c80048000400c81030240d010b000c1d900c01001d451130b0040d40c81c45194000d64503801401d40f4040c1d04a03c04610412448654000c0a8400d070014025a511030317000c074012340241c0c49485030440650030400c000740f04502480d03200091a0803110110300c06802e600d20140240b00740e24080360301440c5001c0e00152100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 752860341 1250 752859091 752859119
    0x90a1805010509010b030106020a121101140405150907060c11040f0b0a150c2307080714030d09030305090a031520070317190f1410030305180109 64
    0x189610008955040a040c020039550582180022001c2080100074513980020030242044d000a50100107070854841254200e001c254498402c2d828040f03121101014621410300680c850400c45010300ca68840920900c03504551a84085d000b030801044401d010700d980549241c440c0d0f80682090740d0b80c0c0300080890b0341130511114415590410f032580c50410100c1840540114106210400040600201380070040c102c0204042110100101070b648212601042c41a00c94103441e4219250b05c0d200ea03548500d8480d00010304070030210303074000d82030104030094801141d40d0303143c1c42c0c1c604586050310741307500c01844246c0140240c8030000110300440007100d41007000000100316410285400d203c50041044072890301d010030031001c0c00181d0800891800b01c1707156005820155117400e0020080714203180441016801c0a1007803070240e0b141d40c0001c14003621450f401c4074a840c0e859400b01c580281340030080105808100e80318160f031601c141c2030102e00e014900170714890741740c15101c0c070783d030b2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 752861591 1250 752860341 752860379
    0x5280501050711010c03050603030a14040906080a0308070f05040303031d0f0708070527070507060504060209040e03030702070303050319090f02041805070b091512010608060607080f090a 82
    0x9243c840d5551012882800755a20301c0d900d40c40c05006c1800d000c400243c8900c24544001c00780300514084204840103402550000d0a003102e00b0411542e58190140d1a200d4958045000034608800902e1b4a401520791241c12403455541c14100f509650b4141d000b403600c800c411101e2a81e200c0c03104c2c052030b000c00c40041c41c1c0c40c1030b402402d920707850000241e180010342d03042a4850a40c00184003000344c44a40204845a0402010303541c1e0b8690001c241e805115255010304441d041404002c04c0c0f01043d0000c2ca60408207a40800c212140c5408480c0c03640001d03200c08006030070074001000464803403c080d54002c1c2685c04551f00340212003281c54200d889400d800c0b51400d090030040340551819201d07410040814001e00700d07100710540e8030302d6110003050240c1296811f01059400d601c3d21050b0002814008000f0480ea0364444401008a40c1e00244540000111184000341c200d046c04002e4460b500c0d4409111410709100e42c10301c1180350440044541c124040007000107801c40e01142035060b070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 752862841 1250 752861591 752861597
    0x100c020d030e1e0102060c070606051314131a0a1803090306060b1e160b01030b1501021c1b05030319290402090a090203010b0c06090604052805010507 66
    0x1219074202030003010180108841c034560f03801d078007040b11640c012403c194044600071903c0d41c3c4904c103207849002000d003074001e039410600202d100400480168407010713011010744c10700300c1166a04a00d8007210032100400400c0d40e200300b2807a4900d003064030285030b04001180000301e04074080c091050040c104901094000885d840c600f0428002180f1510000c0c1100100c92451701013030900c600c51041c4883d12401280700d00140f0200401021183c4020103030b40201c2d18601940e680c01c0040c00c100701511b400709000d02e440400e800380d60000400e07003c0f20095180f03e1069802080007941c52403c00408401c42d075140c50880f1000401c1030000714401e47d4040000700c00303c901002004201e456060500c1c428240480c000c05c603940d00400006c15248049901580d2492041c000c20101c904c20307070003028403070f00100c00403d015002c54080e11404c83c0140484215546a003483c641d20141581d015110390440318601341c50b1801c608012a07400740140054030040c06583d41e807806c4400440d103040c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 752864091 1250 752862841 752862857
    0x1c030e03120f0a091409040f0302030d1107050c030105070e10090806071e020303060306281505030111040f031e0804030506070e03010e07090b030a0c030f06060e07090302100c020d03 80
    0x8190400071391000307000c0d4058086030000d140d801180025002800103401c50a80409403401c01d4820421500d42c8100b407802841002c550b81d2038008543c01640e01110b0724001d04100b56118101441356601c510b000b903a842c90035201403414024070031016001802000b541d0040410580c00400c4107030f00803011565059000c0701b00007030b42d40c8103102064080013150030030024003000303513800110650820071502c42d6520b074801101c1306482888848200caa80300e402c216800301c2988402001d0000c41da0103500a015140042100740e2482c0302c0c41c05800802001544140301042c0303001130601414845085030110403885858103803958001c0e0b4422900d079486802080b01065100071560b850390307030950081c011158550741a80d1103000d00d004904030169954440e00d142c0e03404001581d007454106511081c45922030a1480c5201c644d1241503400c6030030050b002a1b003502c64050113100300050382c0c07503010326800c5a00b08082a0030100d64002008522503024000d640c428200c0055188a0345424031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 752865341 1250 752864091 752864107
    0xf030b190801050f04081c1b09170304050604090b031504060c02010b150304060b210114010b21060d0b0c0c0607110717010f021306030b1c030e03120f 66
    0xb00b907070300051030f00d040151034201780f000280c80342c800d40b2802d103a000400460001d1590404005281105809184214040031001076513000035003202541c0c44000407101407800b0041c0d4a075684a20f115081e080306041004100c200304950254003240d000506807458030209110a4503000415601952004c0d030360001074016603024440d0f400c1c00f0505903141404040d0440511006000040c03010b40314540300d00b003007401a6120440758003001103034620606007000e4080e10034001d00e01c811940c40329000a41c00030481d0385640080c0c586292903540b10980c0c04240305082e42c0142030191100e500003116035909400101410043c5105500290700e95880b02d001800c440e02d0400302414a2003408072840302c07101000004200101913610407004c0003201a1000308860042c000221403e01c0d042c40494001d03031006241000030115903040d6024803100c01071604002d08800c01c03020342d00044119180ca0800240501042c08001070000c0c00d543c078141c0d8130701c00e40007598040d007590502d520000034662 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 752866591 1250 752865341 752865343
    0x1120209250914180a05090c1e0405091606180506070602030603100504260f030f100e011415070c06020d14040320060717071a160f030b1908 62
    0x1000421003110008403131070071a24892480072016040710300c1241c07904006160b8400811105100710800f4091240c0c11482500c5240d484d4040c02e06148118141004192040750000c0c8425200c039040080a80031460000203403060f000c00300210410200d40311000501d90794510140103007a0140a000d43d46e407405008050820030b40071140005a40750000780300c0070030a1750032800030750700c4810a011100c0c031000c03031190f00307901070b01c030b6004050035000040041c00061807040c2402104030300a0030004985410041003080d00034051500460092100e6480c1032908807c0303130f40c400d510042194506190354071107024443c0d5940240c009a80048c4100e5041d90b031205081c2c44060300750080500345411175942261050404213015a00e10741c4000d03480c115a9518212500f1591094000b1100f03020303080342c2e0059410220017508c1d80c2001c801e51502160180c02c440d0311903000854102d080e441d0380c0c41c3c16516040480080020540d852600b034078141c40f4074071104045d0b260342c0c0c2034480c0540b9100f052 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 752867841 1250 752866591 752866619
    0x1d060c031005030319111e0c01080105150d180609050c100201060f1412100902030d09210602130b1b01062601020f0406030510080105011202092509 65
    0x19a00a5108000c2178a80c880d0b43c04818204001d10300d02003a1101c8031140f100d1a10b0031212801c161444c00700001d880710000024941c488031402e880320750a9070790b608100002c444d4130340c42049140004005181c51002107a110340312085541218605c0e001c8140c540a04680000e07100711050350101c03140c840185454404111090703071030704c000e01485003400b80810501304988900a20160100f08100c050b9845101413070035800d00d08104c82e03015122100940182491010a82c004d0180d044481103941c480e926810907184803800d15006040c809a05e5900d1081c8440181c80e5645d007448068401008800c0f060018040012210380301d6403600300c07409800007840d41030300c501da03d0201c0801c150b0820781c2c8218040205041340c040d1b102400700410f80a4882d014404c074200702c0014020a0464055000074042c5000c0041d426803180c844458500700ea8081c01407424001d4503481c564010300d400444207074002c5000524002c026100c880d40c00c9107414420500c1c0200e83c0d05c0d2400c2c02444114004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 752869091 1250 752867841 752867849
    0x1311070c17100b03010204051002060a143310030902030c0909060708100f260c090a2a0806010f2102071e0b0a0606030603080a031d060c0310 62
    0x410400c1d61107054800b6074440340b40d6849001d46464070030148550783c1c00e50554004200c0a0034035540796510a82c020746070380040342c0a808003880c0450300c004491000c40d545129000c500000140324412100001c032140c807010720a0340407071041b10300c18019154000d2558200b030fa580c4010415004520426090090070945103029624030401c1107681040091000e810207074504011009032200c02050342034124a1b040449800002d00e0000f800314250040381c8411034508003e007084007401c1c3c5e030741c54441d440001c0d91944540108042940c40200307901c09111300504219000014a6450a00e14485510410540802c042c02d0170400b0558008154101801207031420754041244410b41800c821072549450030381660101d5818100030003503052070b0000d511909099845401858690782040341200e07482c01203803c01c54001000380c020300801040e41d034021283c60411600072000c6008180301003500c0502000c040c800581d040c81488128000c1c584800e815583e447c2c1682c514a2124003640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 752870341 1250 752869091 752869109
    0x40513091a01061b0b2a03011e0605090a060f050d0e030408241317032502070617061507031805011e180902160209060f0105070803061311070c 63
    0x14007000030a10415158095003884150f0303413803102401b82004600380100c1040000000200211785030038103240703400341f988013401c568110503101c400869042c0030786e200c0e4607008000a031050000314010804c02115007c1443c1881c10800043e80c44001c4c0c40300041003075a944c00018051007544810311501c00721145800140d040002c042c0b40240054600030f00308244000066900020403030107190310500003022200701d54882c14000c01000d403061000042d4044040c1828400c01e805002080342e50407181180c43503618800c4011080c90105c0030000f001340c0d0f031102601c1303200d10400880c0400f9103551402a030b114000010b40030074503060b107800c61308040c0c14030207400440c8400c0c1d1048d2094101d803241c1c3c0c3c030304244510748000c030b070900c00d6559411403a400750000c20411040301c58525088141c41c001c03102c00c002038660401380040a4102801036000034000c0040c500811240e400035a0449409040031a0881c0c5c1c148810040341c0b107040400068190000e03040e41031004090507803010300582e403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 752871591 1250 752870341 752870387
    0x130b030f0f040c12020105090907030b01110f100f0f02040308030a0b0d12050903010e0f03070204200328050106030605030c09150d020d140703031b0503040513091a0106 74
    0x9121010f20304441d20408015003809103850045911500983d04401405041c9120714200741d07001034007038841c8141890025170b10110f0b56910310b41c005840200e2441d400023401c40c5128040040f0003410b04459a501465141d00780b6003041841171004000950051400540300d0821200c2e040949500c0d4410a2054140110031800706600d080c0c1d110b0b1182d40c03070900d1070f070300c41c11180440c1c023412409121322014055860013504620340480113014040c402c88081000030145100d5100303401c1c031008001c001e003c00f44005260700ca000307142050844034808154112500c0304206500340c1d8800d8001070b0009450b10300030015400c003041080d00d6410115080c84003841c24140c01d10728040212552845106400103290940d140c28480b025280d4000400080a034031004410343e4541c210311084000903040e05020402901060304021680c0d40709010b103103080d1400f000c104811003045101480103641c0d1204000040786079400191221900040403410343c07520101078841d2942d080d4841c0888669 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 752872841 1250 752871591 752871593
    0xa06050913051302040e01020a0e01030207171b0712060b030303240d17090f0a1a0a03060e0a091106040f0e131217220611130b030f0f04 60
    0x51040c01c1101060541c0c001003d9031050002c65090040e81000b83d003007464007500150400040d00204108620f645501503005d65520045003240304642c1c2c0508101c000301e02e00c070b03525504800100b50813440d02811803034800c0703031503c840d080c110b00d54011042640c6d0318102d03504010f40c0340518051240c00b24003450441c980003030b1121140007100e100c051000001d0148803402d5540390741550485d41c20004110034802c0c1c01204c001c40f0b601c9812404e2044217040341619607482c03c10190001c0c0c904050495104078000b003c0c002840d002281c5250901d0f0b210f0b1808211841921a80c500c1402401c0010480e00c00310704050041814007155240202d40400090201d070205500c0c1c00215070a910050b2000e65407002003200038036010200804034401c080b1401c400366800120304144a669242480240c3c4854003910784091500f00340c220100c038060316040100d0242c0d23206503074024207106564600303074001da04c040d0000819002981062400310501c880c1c45403c00e040b5900100c070b038072900014106 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 752874091 1250 752872841 752872849
    0x807050f0a080a020c010608030403150912030e07051507020405010603051b0d06030602031017030405010e1002010b123f0310050d0605010312020a020f19080a08090a060509 76
    0x501c04421042c0280701c008100003021503412900040e8030f4000810203507499240705c40e141e41c41884141e48900c2303081c84400c0412264411170002e2030b031001040c81c84000c0c9407400e9001d130411242100e90350050003800a10b5480e640521100001c50700002981c40c0d50503c1004200c990680008080628200801090003c18415004800d400c44003482c0c444500540030030290070103810007441c00f40040b0500000305203e4984405a9901007441905202031096072503403406076106050008510611628003800e01100501f04070703c403440040380e50b03000500441c50561010081c908268481076114a00d01c0c0410b00c414042c0900c80c40317501c039900e14020151404810a03030034002035280080442c840c030000031414030003018041c20342c074400780150520400a1100348829103880d0249481c0f0080d451000c500e81a44541c010004a51201090207000140007000b40c0c051140300760780000720380c60303004000306070134148100405a40c1d0700100e800c1c400c2c0d600080d03214174188481807002d00c0c43d65607 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 752875341 1250 752874091 752874097
    0x10507030902031209030a05010f050709080d0203040902180a0602030a0e09060906090903160c0e0a02070201091701020d020c01021305030307030f0e010e120c09130f0605130c060206070807050f 85
    0x74a50051074541a4100006e803c090344041d0041c110340c03800c2c13010100b02c80d0341d40115228001c3c1d600d8894500f0b640d02c0c011510f03551860a0480160001c100503c42d6420030f0340a00007200c006013616011400840214074240d200390810b50160344045030070444203034004240c1070003180c142c601501c03e0420394045000c07001d02916540c8140f6490000401d113440400070b4601c2c419103000300341195140d030f040450303003030589004c0c0f0b007282c1001c800000c103911004c0c000c40d5071155060391900d80070f924003884481604140102c48403295003c1249030440d030943d0018003603060080d0f000503551000d01e007e8484903100c6a0042e40250828411000441d41060ba8640075a948c2c0c1007011002c107100d0012109040800f0071141c0c003e0100811a103180e03000a0a404989001d0791030209a413200f10418210395030740da0008006008800c41c000c00a12150000754000c560b83c00302c1c0f06000440d40da4580d941c03510f50030000043c3d21502c1040071546d0700208403508203605040440c500101907803202140d00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 752876591 1250 752875341 752875363
    0x611030a202b24050102010615021b0a050d0b06090702010623010c210206010801050603071a040504020f07170304020d110312040807050103050a0212040f140d0f0201050703090203 79
    0x40c1001d4140da0303190203250040118100c412403280c81d403c4410960460340d08443c002d540c0190300e070120129200710120300700e040c010700c581c00400d0740c1400c11440c0500715203447c5080c1d4108080d90000901e50b2110030400018a1140e000300351640741c030505008259070010007410441e810503070100308008610b0130b82d00300103148050301c0c004c5480240060b116041540002084841d10f800c0d1000b4090b41c0300d028070310030400c40e0309590003030f40d8031301d42c15003070340e00c10340701154542c100100400611112a448042440e40144100d052940d1440040d00b00e8211031a90b5414210014040c01004000310140a404020503402c03030660030310b60086100c02840b400014103c52010380b4100040d03400700031640480e10000020b03541e0b540c60349401915a900c83c030890b80444e06200104904600300d000341c03007420070700368200d005039619921241540441c8003000e44103010b0003011140700f000b080c84500c22080d526102c059400140c401c1c0203085500003412002094540000d030401a940803501100314 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 752877697 1106 752876591 752876647
    0xf080415050a0807021506062a010e100c050f0309100504051c361703040609140a032307030f03020d1412040611030a20 53
    0x1d07480d460851201c6d5060800000c1103030030301c81c014051800100014035040b10030040907400210061003c14150394480190b500f2680b010030940b00311054548081000b022501c5004146004201c005c0064900c0000441c00200c1d08204080501c090014100520700301480d045507100084505600040d9003070700103071030450003103451400c10700b5020325041c2242d4042e9a990742071942c250b08426442010745001c24644818010100e144180c2c000450341c1e80d05280002e0002d0116030b104010100044100c44515201c1c0008071046070b40c080e204040d0f8005140c03020f142c0d00345000c0c0d40d2089108048000043c085034003907842c4a18083d070203491707204c0000715048620a002c1c45982c0d100030702c10000345c1c07a016012440140e1041c00b442c0002880c04080200b10351030350055071044d0350350342c90b222080200d030421440d6803404a904c040c0c003071608600e54035022044040031025040 = true := by decide +kernel

theorem cover : BRFrame.Cov 752697841 752877697 := by
  have h0 := BRFrame.cov_init 752697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 752697841 ≤ n) (h2 : n < 752877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
