-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4099
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:34:03.333331+00:00
-- url     : https://prove2.me/submissions/d432f4a5-1e67-43a7-93b1-890c1cc12fa0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 737050359 ≤ n < 737230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 737051609 1250 737050359 737050367
    0x12010e010b072d26041a0a2003041508040b070518040e011b0f120b28030c05060a020c09130f0f020108010e0f150604050402040b07020a08030c0d 64
    0x54942841c0d07a944200f03880c544601124003810980144940015500000000e184080381c1010786003e0342c000780301c200030425103092401d800b101c6543d8440e945a09194003110140005140b003164400003940c0c215041800001400c107483c10010b80d071760401d100d8882601e4040741100d0050043c811840050100c0c0d1084024060070242254801c1075020700c03400013010b03035000c005026103e83d503440302c001641d640041c42005020041c2003000408603080c50007080c001ca0100d1411207203840303040986050704c45507420745405203080090850b0702c1500070301d20803031140d038802503c1c229a0404c0100385803038000f00b240d820f014603030020b20800080c6402d112407200000e1940080c402800030030b0011480045c420741140e440390340c2e46080910244009014450b040c1c0154646008100030840c054000030503d6800990145113003a03500003000000d000c40c425500032a030050700118000036410f00c01000791012510841d5031020f910745486005940703025454010380141d0000c42040100d5001b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 737052859 1250 737051609 737051633
    0x4031101031a0d0b0405011a01021b01120203070201150b040f0303210c09240c0f1b1203020c0409030e06030c040f0e0f071d040f0204080706030212010e010b07 70
    0x12000c00181808a020b001035140c803102c90301598595002c000300400c003c002e2040c3e241640c0940c45540392400d044c0c00003551920501c1120440d40244011091142e0003903000070305900c5044e0081d5900e140c03002c40240a4901903030345108032414601c021550b500f900003564181d410034461444864038544084504406071a05a41d1039180c001d04403185899034092020b00680540712214000d2600500f410201302416000c11500c24030342e50803030b16651201118400540056a0b02c85189440c03c010b02244050310500c1d54444061400103960300061003159611406502900c02110b00c0c8002e000c103694020000600041300707051a1801071610401454010061210003030900d81c82c0d2100310301080e12070300b100c05030044000807c02020510b0400301d80c04161480d1000d0050700000045921458000d5114403c5807180340360310502280b030303040e05e0007094090300320f8280b103075030f4003024000350702c0304d148030b06070704000000465521016403c150494200001951504d40f140d207442008001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 737054109 1250 737052859 737052881
    0x50315060c1005010518060607021203221503020c030306040e0a050610091d0a0b0a0906050c0403030206011e060e06040e04110901091802060915040603050403030507050403110103 79
    0xd00380410001d0940030084420021190b020014065042004000950906000800358450741004101c02038480728140c6240da507056030f5204910310130f25000c44c214002c540f540080386810b042c80d022244803580500c0201c03640d00c60700c011001e49590f0110700ba441545102c010b5a03008001180003400c05510148400c0f50781429501508070b2551101d0400c101a1406269840040d030103010100252090800d4a003005401c108034807000e0796000e8440201400242101c00c685c00040c5000a141d0084030003103600a804004901d417000c0c60702e130369411a00042c0d00511a034000801c091074140840b40b04800c00b40030100100c1e1901204440075810039405580180040c00001b0b100445042d1040c0503a1081c80950080d0030303075130705000159030140e10004005040422620040c113016847e91038241d01038a1159907030380c41501040c5006003111a074212040000743c00240a81d0590190340142d110395000e2203292680c1b04104d41d180a5404003030903030002c50b1180c030340c00c0d8020740c0100702005c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 737055359 1250 737054109 737054119
    0xe090a050627030c0c130b100e01051902070911090120010f1419060f05060c011803051206190504020a09050a060e150a0503010b0c03040506030408070614010501050315 74
    0x3858030b42411508003509041917980000c030022241e19040550000703c1600040c00c1044400c200c0018481e003c240313031000c0911480402401c201d03481901200c0c4041400845040ca0892400d4002c1d030340e00144c468000f1080c9426014070050340364000300e880b15a416520b03285000200d80303034107078a04407110070010190350307402898811031528060003002100780486100d55240c03d2024182c1c05104600b00d440c021b10340030080c0800407034100b507841900e43c1a90207075211144c14058500600c211210000400c00301d207440020942d00000410300000200c15880080d01c5003c00e00440c1e51191811002221a9044c18040e41c02c185d0f0141c8210485c524140c1c03d4560b0380c0703020a9041034070360080e50000c2c0b440040d117252070070211f051520041508031a02c4c41e152400c5c03c010018007041c050300d0b20380e0760009000310160004000780c40281200828181d0340b8241031410a803242d0100f80304440d10f505284e5109040a03411400380d0480b101a11894a180d440745031502613908100c2c1101d0b802 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 737056609 1250 737055359 737055421
    0x607111014090f01050106020d05130b0f21010617040221101a0901051903050111030f061f0f11062406030c0403030e1c0c0e090a0506 59
    0x10010038094032150075184201c10398981022034109081c40a501c0003628240c3c1410010000c41d5400508800f0014007490a00d45a041e0741d80710160103001d9520150055101241c2d103180401680d0090101c2070501423101900c641075001e140c01c1800c248580004180010a25003070129810b1074240d120348018484410f0b04441150b8941e421140038980e28a640844900901c5c1d00c40d601c101d00c0007000e03046030028900401000681c4d805014007a086c080c000b16681c0c6418689070101c01d07009560710400030b0000040216a0b1074454204440ba0b13032009800d034021410500303200001800141582e40c0300c60043c0e0206130140c1b8442182540b44003003010141d88001031220a010341800348001040310324010840c204400701240c0a02c3e4224422a410018003446000c3c80d811601201d50505104070f000e00c2001c006001203000c511069a440700d4100214100032400d28040155584d6042c0c622403620307840c01203a51034a510303500a045502680c0030038148a44202c40914004840c0030803050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 737057859 1250 737056609 737056633
    0xe0d030f030203221110020c030c0f0a0f0b03060f2d0a0b0c0f0d140418180501020d05090111090906030106030609030c0b090312010e091606020703030818060711 71
    0xb032404c002c54252458200000d507a0018030b40341c1b98200412581740b00030300b101040c3c2c40000e138079603070000c02d100c0c8036541d00301c1d1200b0700340c5036000720600400710607005008e030584c0c0340504607043d401140d5040c030030140c50056804c4c0e40f41158144640d0364946103a04603c1143c0494807480b5100c1c4050540d1102d00c4c000000340c0e00c3d20480082c00c2c0c03010303102d003d018030210348170810b880c1080c3d1040e1a028000d05502c21040349140038140c500300c0e0310803618121005d903040c007240d000f45038181d12141d0061000304070005104054000f842400304810301080165078170800c007422506819400c90035440e040141400a142925803180c00440040001031103503036a13540c1c10b044a961010850200f0200c2c980d182c140450080b9003548030800f0303c0134600c0c00030000c00e01804000c050291020302101900801c13800340e41040541142c510420784c00c1d0b1780640b900d40c040c0d902d88151100f20005140d403000180501001d1036440c2c03241c90740c10018a0903854241085ea1800d26401180042d403141c4828012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 737059109 1250 737057859 737057911
    0xf04090804060c1e0503030c03070c0605180f3012010608100e130b04060b0d03051905070206180d15020d18020d230604050d0e0d030f030203 62
    0x200a941c540f0f0100208901e071510340c0e400e0790781c00304e1081c284007000400070900100440e070b40100c122551640c0c0341c0e1203c0d000c0c0d4040825010180200c0c1c0f8003c200842011008100c401440d03901040361344080204102603a18a03035070b02e1903400b04011200003680c00d13004000001c020703071424800d541071104003224402d402009a01600000302030109211096407001350200191404032500d200e10700c1c040c440248100320440008001c80203501c0040c0503c9900d5200f03050b2400000d00d518844505814000e1891304242007000c4503242c2050000388680c040c80071540c1e40c1d03071f015203000d0800000c40007441e9000e003000340440c0c00500c5000700030006041c4003007000e0849a07801005231a02403e11861080310f242c00d0910f2814032200b060034015a80d805000342c0169801421501316540c0704441540b40c0c412010501d5841c031850060100f003000c0410101c3e52501581c0d207004591480c1000c0116403203120380b014022401440c01241c4d00d9102c0d03001140d0000b0107400801041c400071994007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 737060359 1250 737059109 737059117
    0xc10051b100b100f090308070807060203040b15040b012f1c1e120903021c0512091c052a01020a02060619170f0f15091203060f040908 59
    0x4107295580c0c14485150701e00070008081c503075aa0324202071110304650b00500b84070030310b00000d030820502003140030801c440340c030456045660043d01903442c0e0400349054600c0e03c60986040321201400c42d0754004e1403c0510850010b10b8050350350311020718503000442460360301c1c4400780035140c05100e12603040b06002c2042502901040a00402135686008001e100210310b1644101c6800d10f000c141a0300c075840320212010620300c0e00c1c0080c1100c107034a42a850140e00d110124400070340a1840190309411070041e2500b8480c40340251010350341c80000940b80c0c00401f6481b200d4070000030701130250904c503001a03ca00d403650750351800c04d001d2100920410141c81c80c440e650580d000034401e2145a4184030441c0c00010648000102204102c10703a4500d40441c018540a40b95403075050300307881c0c000c03c03000c0c080001401c00d4074540da40c1c107240380e03460f512800b4031400325901c0c103c0414070380100051015060030100d44000c0c196140c0d5010080d0761040e50348007070340c0039407106540b2010907841c0c0018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 737061609 1250 737060359 737060383
    0x3150907110d08071e0c062d060602031b0c0901030b01170a050d050c01060e0f01060807020c090406091103010e0303010923010b031801060312110c10051b 68
    0xc6034064030165071145001c0450740c1d400c1c2000801d200b4804c107260001e1040c410503000000c0c07802c2600303480a040b40c0a0b4a1910041d04603070404c00a1050003002030840d0344100c0040d21001800c10803e20280203543c91841380c4d1340143c3c81080f5461480d507092420000c1c049008050341d841c2560200052041c003800e801c20b950030003c040040207408900c0c105004d00101450140c00365603000c0c0c941c1c580303c0c10034021601c01d220001910030080c0341d0070761080000e401221401c0d8124100000381141d100024014400440c10280c042000d59000140c10a05100010507035595603030307240d4919010388114001100d4507034048980c0a13450754203000e0140030b90000c00040d0749942c0740c0f001100c155600c00700026600810300281811000c04404954103652510340e80644c0ca40380d2036400c1121480c0071000346d0a551814001008002105140320310a01030f550b0f8001400540e00821034482c14502940f0741c2c0800d01445450708540503902900ba1100030340642803c1e0420002201d081c121004a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 737062859 1250 737061609 737061617
    0x50a1223101a0423010e33040605060708071101111902010207051008041112070906031109060907030b060903160509070c12181203180b09130203150907 67
    0x126407043c200791040300440240900ea001214035030380700e0b401d55100c060095081d912480340c001500100301450220420511504400d2490781d48011001141015090b1a10660500d0400140d41c81e2002c240e9013110f8000810514040f66951000c1d02d40d42041001414001e078204026503d100c244040905000396450900075604548002170405900d900114400c825007440748441c2540004066403080c0c1c040b002e6402940b01c5400505107440200300b84c4554400e100f030104211344103800c0001100c0c0701c2c0c1604c0c0011035241c0c080042c42e083c201c0d20710341c0007048140015242d611170b81103660080c1c00030b0065440c00c01030304080b0741813640001404001601d5280704001906007c85010340c070412038504100c00306c91664a402090342121606401c0084061a45280013800070342c4400030001840d01485000140c640685950743c4003d8407200b038500c0b41c100066213010a021070300743ca0030050214102c0383d190b50008000350405001c00c40c1500004100035490340f210112305008101c1515 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 737064109 1250 737062859 737062901
    0x103080711030106060c0803180307030f030b01021c0c0f020618010e0301050c0403030815040f050718320a030602040e0c130b07080d1104050a122310 66
    0x401030340c8119981c0d04903000303130300d083d100300401544601c1c0484003e0f8403603252544c07611810340c081c00809241c03c3c0e10b11b0502000840b42c040607042060070700081c0e03060701d00f40038a00702e42d4010790311074035419104500c1c0040d4040c40706c0c80303034480c081400c0034030b20035160310301d09503040c1d00482d40d550081079200000c2600041520364540e04108805481da8044000340203524000c400d8182c14019803000074180203000d00486c5100032a41c0c0e090105140c040e1041280715100e101c40c1e8040c0c5800d0301c0f081c01041c1e1840d00080c10507420080202511410340ca40c05040c0b000658050016405014001804a0301031909120b940c808024000860195002584a601300503070301d0030b41800581464105401004400950740c60121401c0c100c030b2000122984402060410150f6845060030809201e454034654407268941c65010307105580b804c4da020302c0d40071380318204115202c0050030041c20000c1e6070040210812406903200700b406c0c00c80c0041d9002458801c1c0c02d0f80907518900c00846007201310324 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 737065359 1250 737064109 737064113
    0xc0625060b010306080703081e21240307060f02010204210b18060a0209040e0102033115090203010603020909030403031d0108070c0309080f07080105011d0106030f060e01030807 78
    0x401340300050401d140c080d1142c02d145075a0301c0e1251041c0e40700f85001000304180b0310b440c56101030030b40304003c00001c0c00b00141c4625640708486000c04864090902150743c207100a003030038807085100000c4000d001030200c241804800e9401d40c130744c1e060f0001150740800010590007218100407850448a64800c4968041031400380128100100411309200a94444111408001174001d420854690006070345111100110b40500000070761301e080e940c0004180b10400c224881c0c08268146032441104a41c2c00b20703080e801c20000000e50103050142219404801c0c030003203600508600e4030003400010075903a26404982503140407208064103800225042080c1078014182c941099580c03030107003030f005c4600b1001a140307400182004d000c000c02070100004050041d0b100308081c04224044900381000b40c00c50542c0e4040340c0c01035040369400c01000148401a200f8100030f04001c94284c03088070b0382001000c400520382c1209104045840300307800584581100c6443c0e000c0c60084503000da4a6080d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 737066609 1250 737065359 737065361
    0xa1a03100602030f190e0a03050a02011403060303071407030b040c0f0b07021806010c0602040b0406120e0a030c0317070c050c2209060b10020d020d0e030c0625060b0103 74
    0x55201400350340041140310604c2d000340084500e09486040d00c44001aa0644100c03031420b209903500b074001081c1c030008820f0240000d01c80c00018404d0f03803030030f1080250032141c4020f400161000354260740103005c0000021702d41e1041c00c000310005011901d03101d0352074542d010800030130340d415152400d8140c028004040c803202000f01400e40300c480740d880c3c4016039000c501c0c207007401030420301c40b80c03d401d0201e08541e104408942180c0d0b0081c0302551900e072175244c9902d19074810322603180400d00401c0a0128800303a809000010200c1710701804a4100d02c2d103050b101d40c1c411110443c100200194110184c000070001d06010349040e6584800ba01c445251240c070b03200b9810007680c480d200d18000055a4894152120040e40e080000861a4005443c1c00707000303003185d03c1d00b86500000c10000c4150780d41d4000303514105095603900719640004050400d50f80d96054824450700340d0461001d646490816030028940c00040d24007003071020302d10700811011131008003800c0305c4c09901d48002460b90343e41 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 737067859 1250 737066609 737066641
    0x9160507021e011106011d0a0b03070f050f0a08030703140705060405061909050c060f1615050c0a05040302010c110414010305120c07090e0102070c030602091504060e0904020a1a03 79
    0x3c4e80c0000d01c40d55042c030380c0407503140040549400d0a880b0311400500c42c001039400ca842d8101001d400c40d19400d072640c241101c83e410500416001d000d402d48031007540d250000d5940304446114018501c3c01820761000c60302c0319401d42c0c0c2c10954420400c900c000042c1c0801c9114407940c000c4000d00b01070308009000d60341c107004100105691a003400001c0001c550042034542e924541150415510308030b0010481c081d004240c07071741c0c0072404c080b440c02c3d080c00386c1e421004141d54000801046241d07070700802070400c0d0081e00e880300d0018206100900040d405000c1098441d4087e031403240b00031040c140001c041d24110100c002e002c2e80b184004000b004402c000c0792421202c0910b04034100041032410941d117217054400c3c12082500e5820446d01e90400f9030403219a540c2020848812544904000c406036204180b82401039200300d106030400700051080c0c40607103019079250a20385080d1000c0101601002d00240d9006180700800500220303c24504a140e02011440a0300e0346004900e69400c201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 737069109 1250 737067859 737067887
    0x30d0609020705151b040e0f060111030304060506061204050307140303070e01051c0e060108120906030408030603011d0a060f06060e060a1707120b0d0209160507021e01 74
    0x2005200c0300002030000700c0c04130355400c8600752004d0780f5501c6142d00c00c0e60714003004124010240000e0085400880000024801c2c064a400e2541b03946a01c4011a420028010600d1302c0e0340003440490700146070780e008070780c001d100107140c2810658036800482c40790b481a9001c60b1164000604c00c420002c0c0f081858019240440155065142c0007802800c201009001581006000100900070703281142c0d0307856004030301d0141046100701c401407d50b61500d080c0545901031282151588c2c0c03e01410003200c1c1034200c09005103066846036551481036800140c083c0e6415500c51010060b0700210594005c1e6820041006201020003410800100c8204807080f507103083c1011414803600344c01c8a089620101c0031f8603644d0b5250904c2d10100c4220000c05041d0745101c03644006d00c04800c0e80040c05200340f00c0101410415841080100a03940d4651180250010302e1b0b6000a41800499040710301c1401207801c103589843d0560b4002800c00c181e40d1004000c02e144080d003402c0c1540d000820300d132018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 737070359 1250 737069109 737069111
    0xa0c060306030b06091b090607050102070c0305070e160c03120c02010b130204050d02012a0b06120102091e0a09050a050f011d0a05060a0e0a0509010c090b040b0c01061205030d0609 79
    0x400e155500103040380c040c820940306c02400040401281e01c402d0100c0d450590004021502d039070061070000c1c90566140f00595081c4503c00011402600c071651090049031804643c0c6006445104203845500542d44103034140030752041310401220150081d0728002c0155800000c4c9444004c0412808100c202011280c1900c1484140107580703520031601600c9809003010440b0740305102103070f9248008200c0c00d114000d14440c000c4200107500301818041c50003201e041a010020b920300780d00300d0040b603a06652094035070141c0482c0c1e5620742803503243c018000e800740a00e2500c90f96030303c042e50b009444031986113542d501003040348100305240fa40541000d15600203030300021480b04c0070041014103c152a944da800109007250303601d070354800040c1542141c01046d841c01200d05401440200c030119055420000c03070600280c0309001040c15034844c4041c603410b0904103061804207410010b200849590b0314040401c0361040800c255044501c100000c0da5601074228401d03090700e0b80b0b607024401035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 737071609 1250 737070359 737070361
    0xc0809060114090114150d1a040528020c0f0703120f0203040b03100302100806040614130207080f19120902130f0b10020a0201021b01080f090a0c060306030b0609 71
    0x180d0f42c000100b0704503900804442c00b10440d41001a0141e01200e0a00c030300603c0006100702400c02a03088810081000780c08145201e21680c10710003591011190740c44115400760700c08164030243d10f80f08004035402e880060602e440740c104940344c1440400d4001c003a500040c0e0810804c1a1101001348bd801c81e4030308040d80d11101a4069a24040d42c0210310f080403000c80050208828200d503480190703001081611184032040001e00f401d90142c0d1503c0c002d0b400d01c50003055440e4410103229120340080d000b02803a0240070610002500040300460b210502081642c00d003e80c00c0c40500704004070354078086440d0864000141c8159200110703e0301845c24a030301d400140c0e80300b070540704000c0031003040030441c800308400c0c0340014061075140c568024074110701c4e02c0c102680007030700c007440354400e030210340324914007074440540007503007080f0f49001502203400a101c440b0040022908100b00c10112003a003410b82e611032519600c01e41054000070b540c0c0000704248000c90100035040300d010340c0c1070005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 737072859 1250 737071609 737071649
    0x120c04020301141908030405010f020c180a150e07050904060e090309121207200301050705090f04060302090c070512070f0b181513020d080909060910060c020a090c08090601 76
    0x2280948d11649040c4450303e8031050100b0300034012440321030348c014540d200d02c00f000c3c0c00307910a01c0b8050310225065440c204070304140701e4200c2580c505a40c10b01584001c0703566000b60882e9a544a40401c9400c60b403184400240919418101401440d503003024548441d105010302c8503100b40c00c5a0902d40f94842d0346100010100b01d82100d900c00c3c0c0203c040041a24844040c1032943e44019505806610b440100091551b011002d00300300a0212006078240a03c40c0802081da038440c0000b175804180903012454841800c4002c0c114507119000f5103e03411440880e43d48a50080d410075030342014044910010003050214855014803081166040302680c030940e07564407111035603032040c0765450002042c814012900c50b040b06a07802400e1140154503450801c0c0d01b50070043d07403640901100381c04a002d91408006103803103002d40300e0300011461701d080e00459010381d540c102a6000348038030b4000715104082d8090340303090049030348900e02a420101c0449285c034005074001d4901c0001c4c0c0c84981b00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 737074109 1250 737072859 737072863
    0x90304030c030210210c11010c05160c03051f2007020904052e0b010305071b020d020d03020a05060610092d061701060c020a05120c04020301141908 65
    0x1090b00d405803071007414a5010302c001e441c0118080f1511420490340a480680314109411410504006590304031110400402907400d841180c407810300864800d00118800c41e07010500d00c0d0719140550071a0303182d80d40d21746602c0d040c0148602c3d041245d86221182c42000001401642d80a1204640803200180c68251180701c5015040380213100d643c440004c1000e021041201c2100701d8549441c0344407070b0700504074840603403541184082c070450400e103040060b50b0181c40b960b4424802c503160b41200128191034201c16a40040040348d102c0b440c812090050b8070342000e070720415407080d001861102c40ea4245145003031002010b907413007200f108003402c80c0340354001d00c100205c035140c4008001070104500c84100c1d508c4603501a03003590400d200000b440da5070003c1180f40d15514480c03001f80a036207842003160303118690400a50040c1c207031a400c102500700011100840b07148401542c91602e90306000406991081c0d2143d40209080c050070030a81c80c0c04454403150020a039040d80300c2c1c1307290840182d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 737075359 1250 737074109 737074133
    0x161d01080307030c02010302091f0210060e0903070213060e070e0909060124020708060901140108010c14092e0318020904030c0f051002040e0105030f150a0212010f050909030403 78
    0x86c10141c011840d80b01540324103621484d01200046469035500564600a41c0c41ca61039083c80011820100700140da0302c00342034020300844021010310715118140c1c0a20102c1d09803900805032066a034400056858050588140212450b40e121003508600d0410041d0b58403000c2c060391419005200104807000e14042141c8801080809180f109000440140c1c01d040c101e5000c02203034010002004213842c010b50190419115442c2c4030720780b0346d80700c052941c200c62002c4044404107000f0780a003160101c038034025010940c001840b07600d085020158450340340c00503c560410002900701a10302c02e940501600c0c0000a880c0d41040706580540c000801210000c0c0001c0c0500201420f44814030a40001c4451140e8108003151000020402c145000358000e100c0e2803030220030700c80049202e00d404289140040019001010b4140707840c04d4850901707101a014041070707a0f0070401038000f40b1168680a00912005100c0c1400c1e500c2c15007032000c01c01c3d00800701100c40d00100028400101120000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 737076609 1250 737075359 737075363
    0x30907140f01090306051e0a1506110a0803150607030e0406091a060a020a05060c0a0207050f060d1d0d03020c0d0305220f0605010314120a05120405161d01080307030c 73
    0x3040756192801f100e0103044008903526580b03880780d005c00c09072003101d801003403100e0803d12040c60b0381c2e507882100b11084c40003804d80c43c41c10340100802c02d001c500350f0409103400045090b04090440c250364002143c5501c1004220045a040110508a89007078400c0200a100c000b805108620390310151714031001c6041d186500c41d14000c284011014400c000d00d040b0745031300800311559418500300104a0b0307000200004010710628201203820f00f8200b082c2220100064029030400844009241c060300d044440b41e079003054010a4840200360822110480f00c0c01901c1c01a5a446200d001c68140003402500700141800c1c00c0034006d040c0440c1c10156841e1007400344d1202400342618181c40c400e41d070454007a020307034141030010091200140340f024040d1420812a540c50700710076050f0f000c0f401440c0b800404540c0901c0100196403030581100e50080c8207a058408110700f0101e544415080c0e50071600c407204268401c41d402c41c00c929826805071080344021420030345160b400401d0440300c1040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 737077859 1250 737076609 737076611
    0x10f11070306020d23040b072c01030905101d07121e08130501111b011b150506031218060906090a090b0112020408120a050d02030907140f01090306 65
    0x4510002c074802d5101007100c0028881c07007455081c0721171002042c035000352800d449074080c00b404031f00039500541018074030040916035080c054040c0f081500041c60f0302040c250526823540c000328002402401642003a0300d03000c500050144c0c4480c03440d101d0700a079038100040b41d0b0240c0c009004240d440a909158558012406452031000c18035038501801030110041c010034001c5551a007015550ba510740c03e4031400c0c8d0760490804210b080b1a80c0c4c604440c19500c41c07054440e0b00d1840154850590000080003111403501d054440b90b54065020f441d0101000c4450765400c01e00025250030f100d4000041c0348118014146400e60050b4003c3e520710182d680d11408001410215035140c0d081929920350004002113440e540c2c9050410241c01040c00c0d450001da030f984820700030a0440d01c240c400307948601c002801460000c0030317020b032158821950340082c0030050002840c80c0b10280011842140c1c2803000c0c01c642c40c503005140d6031160002203401d10400348006180441d90380070008104907508550 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 737079109 1250 737077859 737077867
    0xa0f0204050c040801062603070c0302130908030901150605073c0302010c0e0105042102180421050322020a080d0216050f03030301060e180114010f1107030602 70
    0x41502d10501c1160b0202c000c1d942041400510090740c01c100b807141107407040310100100840d8481c2c2d85c580c820004020300425404500307002504050715001076010b0120400036070206c0d1900d03028034680080710341c2d1903a691190108040382407201c1c0103400178031030f0703041207805c098007a5200c04103400c8480c2402003161020040714010740084030b4041c800610805961010706040c28001e000c0c041201000c00810010601050254490805c407002c5607805d0600c0d150b1b4110f800190014191080e0042c1c0c6d00003a00e0b4104429441c80b84080d502481c0b013400d0400c0803c1e40b07048051018048805450203025050003005001d8201c0b00790001640300004407828000428400501e601070580c202d80450b1040c200240c961b240c00048052010b105e448804656a6540c3c0400c000800041c20203034040e00113100420840c0d002d0103821a1212004207000c10300c2260781c0070940034010981c482c81401072000c0300c08509581200c40f50140c40420700e0102522021900b910b030b500c0141e44402052258009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 737080359 1250 737079109 737079121
    0x2e0e060d020d140a090c0f06020309090604090602040e1b070312091401110c1627091a06010e04060305060c0a0c0b10050a080d020c30030c0c030a0f020405 68
    0x242c0140220034548140200c40e0824400e05001005c40000440e1030540c16580441c40094a150001c00c4070400e5000b58034054803d010b001240c00068005600541c8507400800050040d00151015141809140e0035925021a1038181d00340d841c048225219410094500420b9010140c030494420b207102c0481c52111a252080b400c0045e00c5c48210b080d480d000100d1095007050f4000c018003030784d460440d01661106a000c076900407039449092100c9001080d08004880c2031340310300070303202080c45c0b0020740799030701d901c3c0c540c84a90300342c1e0584626080307001042015038100d0020600d01c02c00792000c10100c0e01303590300d80340d4034a00540720150078038000c1a022180b43c410381001402991040c072603007490600700c0480c004004d0318021a4803500c107004002c6a040b0002a105804541a500410524000c1801e0141031119100550384859240001070601a014550100c1074481400190750300c824045c0b0090420354a4500c19119810040d0704401041111451071440d5404a23400699a260342c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 737081609 1250 737080359 737080361
    0x6040905150a061706130b100911040306050f090a03080a090503120f010b0307050910050c03070f15020c1e03070b0702060f15010c11030102092e0e060d020d 69
    0xc100025605460741046007000d0789030800c5085522194080059945041403103450340d40880c0c081c4e822014082c0303401c01241140b001150412140786064040d95150b0107500c00b81c54880c41c0b8022518000102001000514130401d075020080c01000c1c24079051201c0a6903c504440b040901007000c1d09d80400c4810103141e0240555541c4141225503e5010041800040c5012540c4659500f60100001201e50215048070b2080d5200c0e52001e142c41c240700100310103080c10603445800c11006110002c0d60f114104010710410b0b000d00c441c146500041c0c40d004021001d030760040d2410134010301c4901ca600f81d00150880002415030300e2107035808540e110852550084640141c01d084501d4144644a50085103050003006442c2904405a0301c2c503141c8800464000c05040c0003800150741c00d000314200c071019002c7d86500800241c40c0280040005102644044911007004070b012184508041018600c243c441f07807030300f410389a8620910001d1070754010b007601200644d4001a0540e100315030303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 737082859 1250 737081609 737081623
    0x3050f1b0f09071b0f110111061303020c04051e0901060609060e15041d060109030f0b041406090d03060e010302060319020705030a0f11070e010b07032d08010e0f06040905 75
    0x64070601d1341c4102c2982c00c00310010908a4020384d03200148171100105035100b0684105030083c688024a8991078507101680406070750a0250114007640d041050305a680d4002e02c0e00840740c03e041c0316103e1404007814914040702606100043e85048810894160040e52280c22039400b8200308408030f5101001c9110500010030f6810f0308500080c003c00c40c807049030b840304d0041e030b2007800d043d059903240e07801551101c00c0e03400040d040491508140300015000d00311954090303c00d04c01040b45c103089200380c51403e4000e48052580d9004401c06001999161148078014184002a102c0f0f55140d50089996440043d100e203110a0040041d0302c403641058040300e41096019007180d9880142c054000c021404001d0140000382e05010b29a5035181d0008110081d00d03040c3c00162520b0346813615124a540c8040011014400c000ca0540d040604200b044a1903080d44420b00984a001e15030080a401c01604150381034000a824800c4c40d1100c0b0613880e501001c10740d00050340c51414144039180c064 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 737084109 1250 737082859 737082887
    0x1d0601170a060207240207081b0a150e0c2409010c0506040605060a12021020060f0105031533060307030e010b220b04060e0103050f1b0f0907 62
    0x8000101c403010030903d07030001c094100c491490622420405d400c910160301c1950b40152061805200211400c0406494100d940c1100800c40760020a0b070b6985117a8900382d403005400b0a46e4841041012503018030880c1d00000d400c840c0092800c0d14074040c1c1a0040c08042c2601d003181010600145690041020002d0304d40c0000c1200c030305140c5440c00201070a4100e41e900d000324030340d0200096402b82410400c103003981c0108114211520600202d0300715200700001c000356050025904040c400138404a07001c0c3c40d401c01104030035814107040c14903203407200c0180d1007410540c00800c6a00885041c45070401c403907184814490142c1002d21210b400a200112507100c20000107100d80f06400d64410a10740c2d4843c0000d0100040e14020409150826925080d01200c2c0c10203d0514440391750000701d201c000108001107103034035102c5984040000341c0080f10070364020b424541400000b00015040c0411101d0b00310500c040760f10105024003813034241c0038041c400c80004212441d02540440320500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 737085359 1250 737084109 737084111
    0x20d021212060607240f1407080a060f06052703150901060e0f070212160b13050706080403020712030903260a030207030e030d0519090305060a0f1d0601170a06 70
    0x80c4c014954000485c5615151004145401d0103140c00d01d01601a5001030f68024000f8501030382c0c1d4580540707aa80c80180300c40c0f443c40d580c5102298012004038550080c02c0c2d2170b0340350384c1c0b034034040c0103484c0303840300300d145222070902440d015445203a0b40065101c41c0040e070301c004541d0684903200d407240501142d800c80c1800000c5041044101400810380a1281044d50708407101d82103d100301d009940310750313086242039000c160031660104002c804800d41040c480c48049070201038540700c2a05002e000d401c0480050094402e00c01419030402111021700071605200c640e6282c603a9002d411014648402408207440d400380041c104085040103420605240c1016038402003804010025800000120b01054041d82400b0311420009080700014026407a81c0f071400800c5da00a00c181c2c041c039000340082041c0b004022000500074413a15003c2c0e546058042101c047c55030241e81034980d4030100c9510703074036491004c0042c801c0000d00c880c110384089000c1d101e22f02c6c82c214618208502080702900705 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 737086609 1250 737085359 737085383
    0x1306150311010e0d08040611030412050309120105010e0f0c22051302030f070309081e040e012102090a061d01150516150902040f0c020d021212060607 66
    0x2000d03031440c00031041102680d481e042c0100c3d80041201003540d207003026011000c10721081c000d0303038060400040280810802c890506594a2200340208034081d01120590404240a0b004e402e08449096007129080e000b8046981031820045c00c180c00204484001c0d1250b002146c03250340d61a0466505842e620501082c403040d9000360700400b9a00d1181c54000c041e030341400b020b425418800c0e01d000e0601140c0350760300c40d1200e04044001e041848002d40e20160200010703a425000f04682d10750b1a088801e80d0360320f80d8645100c094440c50160701c12690741c0314a12012031403001200050720101ea045505441d030761103001c440d4000700380f00c0c0c10000603022910340355143c92010944031812200f08481c0950320f04040b40c0115211f0103200803603d008021010490001005090328541c400b4110000050484250f000107098810803a181094540d5407a40c4038003851741405215001407217400101902c00c41400e02404502c140b60514112031070040100b405661014106c40c07105401982c0d0b0881 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 737087859 1250 737086609 737086613
    0x616140105270703020603041b06080907050406030506040b101d0f1302010507080a033216050409181403040e01060903031e02100e01090b010f030b13061503 69
    0x9000a507900101000b080410100d98814002d85040150500e80034100c400c0c950f900b07102d801d40024100b203d80035085201b108991071560072107001040381d0341e507415650802c1000c0314109a25a002240103500301003040c00464000151941c100d64031003414182ea5851036007100c2070100581042d200b814816401540d2034112148032030180520036108400ca80300e00b04007c010341c034103c03002404540d0230b108182c003040a80d001307810702910717609001c604100387c04540c2c126180304801440d0300410746405140c0da81d00740c820855002c4d070541d03040503291700c1000026225000d6403050448550f1103940000307201d0140d41600d54104e038803800d00c10700340c8080c940c4241c41e60401c0c004c909000c2141400094060300c0340012b4403c6070f415440d02011014600d901112004001130007006500c100c58540316860168810711444100c0003000040d280c0306450400440481a403245401601501040c0042a0030511a85e04420025007035081c014080c5800c1000c2e1040081842c1408000b10000007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 737089109 1250 737087859 737087861
    0x5180303030910110a140c0c09070801030b0f19020c10060f240e010f30060b0315010813061b14130303140c01021306020c06040605070206161401 64
    0x420082e0580e060200b40601319031074600b4016425a100000d0400c0b8013002c030084803900038000e8200c00c0b03007913542400001c00411052032080da503d41c0000c22a00041007407001007001550800c4010005c0800c40c20402c52003a0112408203213400c14650015500c1e000030810054418070800c11082840455520300031a02c510b0360508c5800d40c26490f1958003621621002d4120650310001d4032000e03032004092004440c545004e00003c402d1114000900b40c00440608c82e150178a03920404070760f80020820054800e562265201486c443c1d002e0040c0088160007a0310590420f5007031034940c5039a0b0700d12000c065921007504000c1c003040c2c0b42800082610301071801c40e1085440b241c4500410481c003940310760311441008404460a183c0d5001170000030720420100685101d14040c02c6d051005400c0d6080c2264055440c9907540684003204202d4140c041c4590201c1c0071040ba101402c0c5031400102503c64403590800a12500700041c41f00e001c111000701000c51250031546525030b408040c00781074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 737090359 1250 737089109 737089123
    0x8090a0807140a0602060c030a090825030f14092b0804090b010e012304080f060a1505030a1b0b390c040e0a140703030f080412051803030309 62
    0x25010f40180c04021034602c0c000031b4400d0203005910401403866070f409509100400081c40b04a407025810070100e0500c404140c0c072452a403800b0058019101454a00545032610521002007441150301c038a02110242200b0344100038002e40e0800c69148512001e901d003803c40825030b0703001010351400c800c140001d50b80544140c4240280800034511860300640c0c0c0d40b4160350046001480c440e5030b40c6550300b40407030600f82041e8031109603418241c5030174680c0c0c100b40c3e429200d400c1c254000303000c00c0140e084501401001001894a4965007400d02001c0b1340c440b200504003400c11540d012461002644a04407040101913074010940c8a40d001c84d65a65851712589800c030003413082d81d4902402c0f840803100b01000c80704040007840344010034010300c0003508a11050003114003d17440180042004005280c09814405d009014900d0540c9130182510004088841c2001030030030800000411048024104000e5420b0403515650011210090381c001d010810703416003c0401400b20410001812f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 737091609 1250 737090359 737090399
    0x3c1804050102130f030501060b040b1803100612051203040b04300504091d07090c09170d020607030b0a030303050603032b0b0414010b03060604080106030809010f0c0209010308090a0807 81
    0x244230841e5108540c00da076002d00d0241d581c112004000305142c0c0c0151014503042e200c0081c0a8030110400c105007001203680a50007480a040449070b035904206060140450302428409802d0850801e5258008106c10091004242a261441c04072082c04802c80c0402030b000c81c107400b1000751290210081c19034120344a9400081c0c02c000385500000f40014003e982010048001c1944030b14100c0d24170080c142c0785c03030382030180300c0b08001c0425844a008030041250707503498024601d002c401c48000b494502c00030704850401d4a00601454540d840806010460350507150101d12500d841d00002d00f9807041d402e14422481408488100d1220b40120110001a0000741001400c0244090000b52515400318030281c40410005212225451014607000350b0f01608030307401c0a45a01940b4210750440d0000c2e140194045102c1502d5a800301e54405e80309007515284049114070b42c00700345904010300005104480100d84071405440758440702c0010f06020003120300c15599041144004d24498640c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 737092859 1250 737091609 737091611
    0x3090c04051321111506040c030f020c010c02160f0b03181e010e240a0917091c050a030f110106030b090c010c0309090b01020307023c1804050102130f030501 69
    0x1303501022840480e4030711003c084185458015940c240411001b001040700240a040d81c550700028065980d02c0a050315941e044000a0a024081c0b00a4500b0446494080090407d0f4105002c041c40380655101141c017103044c41c43e140c2e1616001843c0801d1040c45042d03681c41752002c40001c144100c0950101c44404074020411400086202a00c1e1050fa00c4490740d0a00c0441d8603d07801d460b802d5240d50302c66241400040d0201c100e0380c9810300241c83c4d910000d5484804500743c515840d001c03e5481c14030303803100441010f26469503650768032480484800790911164044581e025801001c3c00c081e802400e10080200c1c90f103901e07200f941d242098600a84500c2402a02040e40d4050f000e880380035030b01030700c4480c0030514010054010b005a110b42a0440c0028050180161a42c000b040c015800100c0b82c6c00031080044d03504004500109286102504422000501522507800d4902d540b507203017800542c1d6981e07505002e0302921030541068205883c0000005100c140700c0414400d40c4e100d00c3c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 737094109 1250 737092859 737092877
    0xb09011223280c0c0b0603010b062b02280315090606094103031308010e010603080f0d11030a0501030b0708010806060f0315010906080705030303090c04051321 70
    0x1002c841110b140a040c1c0c004603902e01c99407400709848111307032688003c00400120300303401b102000ca07245170480082441e1030036400c840c04140c00030154427000d12242458085013030000b08a4910302d00358a2154541c80c0d52120320b02e42c0c1c0198800d401c200920310307240551104680d40c4032010760007041140306400c0060454000418881c081e909640c0c03085020703058008005103188600d01d44401d18103405450841d5206c0c10300c4260728203001500000a15491500f504d40c0f0f405c0300359080d80c1460500f0020790749001c1d802e00010300c1c16010f44448240c5c11482586541020031844014840070001c42c1c400000401000456401c581095060703d10840c4452070644400c401076440740802c3c061041d0301d4000f0000601503081c2180c0d000e070745c20001003c0b201e40b03100c02d444d07807082c10308207030040b04580e521240300340000c443c10401d04008101c00e41c011440c500e402c460f480d840d42c0e103001d2440c0c4119100d1000c1f500101c0003004642103d83c10051102045040900402e848080b00741c0e04000328103012 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 737095359 1250 737094109 737094181
    0x220807080c03150606091c0c05011e080c090a0503160303020d0801080c0616020d05010606021e1f020403171309050402090a09020a0906030317010b09011223 69
    0x45900b41041c002c42040c5600c90710b8404c200b101580010440030780000c2c24807002003109000c244200b0517240507a10944d015401c12000401030303008405880c039a00c00e032114560549900c6402a40e100000200c80c03a241c20380c031000181101c64035800981e0500c506400c0c00c1003041c14000d180102c80c800e03000c80d03400c160307000e000f604d480800b441030303003010f421205812403203082c950010300110f9001002040300082c0e960008424102451050f10560b6403440217214981d010010b4101c1c002e210031910b810700840500403540c401c003078800311411a41c2c0c21240803080d61103070140c602855000107940d44005081d00705842c0c5400c4102002c0c1800d060f01d800003880b0140707100d443e001e6a0003070440c20243d615083e8800c090710400000301d070030080a61000840c0d003007510840f401755110742e9405521540b0604000301d4070031706030001a0b450760f0410203010103a8100c400c03c1504482040041385200900140e1042c0441140f448400e500c00d2504100380301c0d40d143c4d0000310344900302003400e031040300c06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 737096609 1250 737095359 737095363
    0x1302030c03070b220b0d050402060715090201141611030c030d1110020f0a03150b030702070302270612010603050312071205040512070c0b0706020304030206070206041502220807080c03 81
    0xa201d1641e094008020414400c9003071f0708807a074040c3c0083c190515100b805e45d1000d420848030340720001d40556400c003800442d80d000c2408001410502c0966081502c40c0f03040150146015000422500c1c5103030440c0300584091220a0100d1001000d8803016021010090844400180020302500070300c03243c4402c8080380e04c203407411110310340903446c01c0c44840f100c240c004200ca01030400e510a1008030028203100c010000b0351054041d03a000e00612899413050004041400c90300d19003000701d071100a14200084510b00e035100c0400c85440e004840c0b00f00c1c100c2e00400301070300040d000707000002e0074100500400c43d01a0040003140d03200d810360314802801d0b008903807040e40d00400c160031a980065103030700060054203456001d0000b00c81c1c07003903a8511004850748900f504072519900481084203041d0140a0303c3ea020242d070028002d140303802e07500d0121407098021000040c070350220b41d41d500d0000c07c1500c0304030828400b0007203946603104d5441ca550f035200d62282000c02e01c201c5041f260340d8140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 737097859 1250 737096609 737096677
    0x219060210051302030d03061a0f070b061f020d0905120606060d15091d0a050601060807030219110d020705060d0c0c0203191203060e1302030c03070b 66
    0x65001c1d0000d41c0480048001408002c2c14414000055140038000b5903010b02044148a4842e200025018a0010b03008445c002240400802e40c01c10310090f05140d44070000c6440c8690b001c644c2c3c0c10f040e40c8160004030300075125a500e606000c009540303200d0054002a0303a9609030100d032605a8410381d124100035100401d024002030319001240869800c1c1000000740155240c2605e022031301c8922548141002442540000ca0042e100c500301c0c1d0703429140300c07865004078010350f0107442d10382070310348809507192818411181009a9480000c0c542d038420f074140c07031081080e41e109801107138120034024607a287c01e2080003494000d4120083c003013400015820110380d400390447d820f0901d5581d1003c01004604034803401d100f0150b2059005070b50910030405105507541074582c0c4c840a60400f01c45400c240402c8105042c5003410520002984185003680040042000601c5480710310100f8144103440d919140c0600c41c004000c540031500304090480e071410030500e14101d039041241002060b071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 737099109 1250 737097859 737097869
    0x1609140f0412031109041e060f06091202041e090203010f020c0c0d020307090c050c010c0309020603011e150e330c03040b03041a0604050f1303031e02070219 69
    0x25401e0b0b0340c040700c0c0240c101030204110070415a0916603c000442c041d140011180440203040c04040304440b21a40314100152201c03a0200d03c503e400e01c0c80240035502140101c8018060b0204c1803021595203400041c0e0b54a600040004e04065604c03910000e070540c40c504900c04d500b0111170400f2025644240c543c8205224001c00010042c1d2040c454490800c3c40282d03058064a1000f00c1c4101c0103000d280000011035075000d903901d000c1c0c0701082c21a400c0054407800c15081040c1e10003d0b9942d241542d055520103036054044180800c11200d690781c00d0740c0403040801210481410f11030704043c4041c680038041e150207444900c110f4020701440ca030700034a082caa55155a5510040ca0b882d0040c0030030b000f00c10120f0b80b419407140f901214035082100c08030b9281002c9801460b440200642d83d0350050320940f421301c46800c114001d880030050051007082c07000180b007041d1050500c6908600f200c5082c000c21006400b824241d084048d501c11001070340510340030a40000031000c161200c0007124 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 737100359 1250 737099109 737099123
    0x302100e0f120f03120403020d300e0f0304051e1503190e0c0a0b09030703060b190f030606050907080c1e130e060d0f02040b031609140f04 61
    0x110480204100c42c400084004114440c101c03840c00b10400403c01480100810f00c42c84002c0d25040c90300070319010108154008015041200c4984113100710001c030542c000158810b03541e03150608134100100b242c9100103406106031003c40240c160080010025501c095800594486000d01001249440d458a5507040035440600c00c9201c14000d0155400c401048507e0f1404a4405000381c2500c10481c141503090f0440e14043d415481c2c0501d01100401100c030100d4205080480040e484001c00d1001501454448481f580580e075400641c0741c440403044018100c65840b20003000d5110141d010031694140ba0070b6000c10399181c4082d049100d0500ca07a10044241d0714041200d0403a0800d0201550340fa00a6000e011a0600500504104d084011005690324500502007c48107009400a80a51041c0c2101000f26a2070b41d0000c0000d601a140499110344041c0420300d0408000d00740d4580c0c00d6601c002203180001c0350004850800040e281901907224030500b006141000d9034020b28503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 737101609 1250 737100359 737100379
    0xc1b0803060609010c020312090310090231020408072d060c0f0206040e060f01090506040924030f05100203010e1f08061003061a010c03080c07020a0902040302100e 72
    0x42c0c07500070001c3c00148018544448440382d19400701c2e00d050048400f0f0340714020081401e0359142420003502d801c10140c1d023028030201030560040f1390381c00b5240c5007020122001080610b850003420400144a06901c0301c03c56890307659130529521807105014101215800d0f542491309054500b40c950b55144c40c40250030507036490800c081e40c90002c5210120b0f0641c1d000c03000d9001680c0c404000d130000700700014045e00f0b90f140c25405c20141c401032003201414492000c00c00d00c031540320a0242e07800c0e121034000c0041c01c41480c14240f40005002286541002603254010003081b100301400207240d40705000b01c0301d0107110420608181d01003401880103100500340068078207050715500c201c4125a9107079000460340c440c114503041010440f0003200104861400f0402c00a2a21815244e5003481602d42d4040c1d112a00017442c2902e440c101608004c0c40d4000700e000d900104e03040b02d42407179009220322912907855100748040d402601c0305034401c821914100e1000380c0241200071094074010048610 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 737102859 1250 737101609 737101621
    0x90606050a05070c0801050f0f0603070303080109020c10180302060a1404020103020a11010f060513060312030207020a0e07020d170403020706271202100c030c031b0b0a0c1b0803 78
    0x5207420440c001d81c2c00004c07881d070014801038207200301030180503481e00101091500100035001d000380600024080d13406684104040782d03001d0f859a040d6800540050790b078070760380f1010300d103030000789070444d001c16142c04034001d600040710007180300c940d119800b03840840d41c0305028102115200b0543c0d040c80b840303130303400200190300c01c0d4010281c003001801e100414000500046003152200e290042c401566103105203d94034002800340ca00d085038070300030700000c2c1c2187c0e11010f4050200c0c1c40c00c0213141d004204941199145140c03003005c0c001405002800e80761141c0000d545203006441800405d007000100704c0c0209480e040315210725019001810280d1a0600488014809061040c500300c140c50661408100c000c211000a100415220b0303910600e500401444028000e84c020a00546a0080e40020340007100d03a5566070305400c108105801d0701c08511042051050010403210905040241d43c0c0505e501c04036203045265520814803d01256500c80c000d8090303409040d18000b0302c00198 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 737104109 1250 737102859 737102867
    0xb010e0f0121092108160c080703142b020c0709020c03041701150f05010f081b18030c04052a0f03090f07140139030c03142506090b0a0c09090606050a 66
    0x889200f4a410001c200301e0a01010741500320344203513201380120394033301c0d0091294000c0f040c0914018140451409402031502990782d40ba41c07040c005034640100e5070040608040c41564000e000700c40c10201082e0320015400d0080c0311012a0744081d1f1140c2d8808110004030080200c181e0303406031203102107004291000d680c40c0c81c1c003d0602c411075a00702d2001c09110020005443c2c0b401101406080d10080c0504041c102a040c6254500a07403a0400f0050205148044007107030700e40084c900e071a220181e0703046017a140f143d25013242440400005000325290001030500508202d1010780f2800e0780c4450040a44203094258180041c40030000d4007002c0c1407034100d4248924a0301c9401000e8904450042501d00300e80000790045000c10b5102d50905420112113054483e080018902d8402d981103a0700b800c144ca584200311041e200d1141104102403503128030340030341d00105400120318000021801404d0042080320028003804000280080c140c01070341d05940701a201c00e400d000305100116 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 737105359 1250 737104109 737104117
    0x2041107030915080c2a070f080d08010618091e2f09030c0d051c0c02030d08060112090b1b03040b1b040b0406030b010e0f0121092108160c08 62
    0x10020546d41020351002141400308041c0101c000c0d01074546c951801c60118110074207035020742d5480d080050b9111259500290f014155003160030725407080214034000380d00c02400364000501107031034410071000f01c1d00c10710843c0311264449032050080001d80b101e06900c88845070101044490002c005107031351f4040300041d055902020381180c0c02c5001800000c0d0600d0042d610944203a0048258146c02c6034601c003031343c40320b00220304106651030072039070100350307a031101484090800c5004004034034282c2c811b032001103002003c07140a00c46881d040c1024450b50710240e49070108602c8081100b50800c01c0c04081c0c9101d5500711300003180f0350fa01d4150000f60705e150701c2100c0c521224104000302e42261200b002d80003503e010740e00014241d810000250035400c201d58022302c0707890408043c4405030ba2082c0f00902c100100c06291a510712001e005d40090b2103d17070802000c0655651005401d043e49900e8841c87d00c14a9686140300d8991000d07101458401030000d00001c0c40000094000c00c0e0000020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 737106609 1250 737105359 737105377
    0x2060a0b060d0f050406050f0118050c04050306072c010909050604020705030d150b040b0a030f020f071a060a03050d08040f0c08060601020d11150405010902041107030915080c 77
    0x95032904241502d41411078504500c80c00c45940da4100b40424096240f09040c1c0c088001c400451580d41810b807880e580d40b00d084031008042d51241c000982e0820740209980007408060202c6282f41045040a0f0400780441c40036081c071051110010303440c0001c00715121101c441a150420214180780e22017000e0b1400030308042d0856020010580000c000f0402400da88040880004400d08040071500ad4040590f00403048400b051006101c4030391008225070038a94a81800695040c2100e0420080d000c0c00240499030343c000308060003400180180108030b085624281d982e03130b640304401c000f440c611070f000140559201d20351604001e409581c000b41c000e4000d041d40c0080c050690b9500410040e1608203c1301030f0880010720400e944c04003c0ca00ba48101c1d8200300c198a01c518040c903a554038201500369115103002c1c042401e003e429480481810340207002800104c1400d864890280c4c0300340310840000701d5041e03000428016403620410f05020541d40e4500d20307119a070042d80550454514 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 737107859 1250 737106609 737106619
    0xa0f0e0a091805070314010b1008070810030510060617090a031422090524010c11030a0c0e1b0702210a05070611010204051807180905010312020a0302060a0b 69
    0x495004070b1000c100e003d008510441901b002025400181e509440101202a014100031300540703070b8281d00540703080da0090540c40c1200300d990324078400b020300e446a0760028255014101001511a100d50800b405603080354456520030301680349400d1915004546101c8660019035003800080d128003640003200b541c06002c2414260394541101c940d100c1c10301140e1124804003810000420f00e8040c180d440060102e290380040400b410310042d00e030501c0744180c10000c403c0d005108009640001500c175110280403500c0c4142d0034941102c070480a8061074003480c0c40000010701c4036010f03076021002400341049042c1048025424010b000b086200280e03403000409410160107a810000f045240f4080c000901c01c0e03620b021009031074000c04000d8040282d004010034416525540d042c10b08011000310000c01c03541d160170b0125022482c40360700c0c0c0030425104000141d42241074010034140c90185000e80c000492003103041c2ea580728050001000750700007400203200001d040c0d201d15a07203900a02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 737109109 1250 737107859 737107901
    0x201050309070905011d09010902010c060507111b030606092503270c0b09090103110303130305060610050415110f01020c06101d0112060212010602030a0f0e0a09 71
    0x783c080c0e582c00d801850104503140b20645404840e0862503410030340c2c1c4c0000b0040fa070150f400080c2401764100c00600340c00d840701d0108108500c02d2442c18085100b150079940e89841600b4114640041a58000e10030b11860012038078070300e8496117281c0a0107285464100401c1d07050b0a181e100c000c0e5525482c241507803641e0358602d0801c0071030b0070150350010307485500d1041c2d1307145011081c0c2840f540120346180030030700a80501e034a501110300e040d01c4e00814000d00340c040610009280d8820004c8406c01421014800020800000b91290080000303d5102c841803c501404584600440c440c5503c0c046003402c54483c42e50181c52001400f49a4400350b40d4002c05999006003a6401200e0300385d0582c2c800d50800c180000e01d00030321000707404500889110a21521140d9425034018001d4800c45040747c8105010002991f04484ca44400718030608259030391400044c0d2a40c00100d40038004c64503010a01042e940b0940d04035020080007022103650a040c1504d210050030448810301c41003030144e03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 737110359 1250 737109109 737109119
    0x12090203011e050709060e0a030305030907031704030606082a0f0618040501080c09010614130b0307111c11031b010902100912020d02220507020c0d0b04020105030907 73
    0x20b0040d0000e003031000004a01130038907500061000b0080d034409001c000040c1030250032070b0f4900b20310300101c0303030185003441e140e840e04cbc00c00c21b0804284d54001020000c0c0201e80c1140d0321a40c0010b0000c80b03014a50801c406560b4089164a90307008810407048400c4074400048509128003520129003000b400308032847c816000442c0c2c2d1b55015440a2107486500d0b52000030910b06406610301500100c409000212048000b092100c80180250024840103070549542021140c042d5200140e8105610071303069030f80e20040300d80d81e0040e52180001a403480c100200503d000800c000045407000c1e9071000d4011108084400c6915280d42c0c80160004000e4202002e5003078003244420062040009031026070343c81040950004a2900300074403503524410002540111989494a501a9241000c3c40300510004564085414442052036611414045d111550303510542c0b18490a408a601c8040000100462020640c20040842e0065800030300107500ca8400743d034101d5251030803565403d40754 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 737111609 1250 737110359 737110391
    0x10e0f0712140a1a03030d0e0f0a080904050609040b06100210050a0c0e0d0b0112030512070c03093503071707060f1b030b0604090c11011a011209020301 67
    0x520340380c0e81c201c0c0303041060203080380491081c54040721404d41d02215044055021948174040c03e0210180d440d0b031507605c005580018000c9403034050f2610280c0b0402c0e911864411440d40000b480c46005516080014069003005185580183c1e084441403905690304010401800d840d86418000c40c080c061110721500760a0240c1401652188070200703142e0003c070300090210038050b1001d40300c0c103490000343d0040390502d00310fa81512124050225200020300f8187c90ba0320461184407015510070082080d615404031410f00898843e96400590a6031140c041550b90502051403c0314403a40c08603002100024004031905000b880543c1e003010800c1d140c0c1c1120844c4d00c8160700303018400044500400040d44681417040001c0d46081256045411041c05018450403006c1d040c1030f0781d80e09813000f60340d9400584d40201038801c070078421680744440c02480500e070706a5280342036003042c01000c16071701c4079214040700100682d542c40301001e070194079102500c550201643c06560350500b8071182064 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 737112859 1250 737111609 737111621
    0x160509040b131505040e060624040b0304050d02010e0f10050a110c030c100c0c02090a060b180a09021815040b0723070614071b150206010905010e0f0712 67
    0x21084500301031444e05062009881000c0004d04468010340c0c10444c0a54400c00c0309424244070441c8070716041d0100301d803001d061103550407030114403c001c4100f0003001400200b03180c60542030f034020301c00080c41d0591180c2d10420070890780c04640140c018081c1e6002d8991217564040000c00c00801c00344400c1503605125800000300d1032250b000060303103185e206403c2040085030760b01500704010002c0c07540001402c814031180c00074445c25000000c100d041c013041d00140003808540100ca40d58100c0c4c0c0b00c203c034004040030b6121780500500c0000140c0d5484510a803a40d000c6d8141c0c80700c0b10364801e081003091020700341c0c1516517613107000c0c480440e082000d0030141a40074403504000e04c10274540c1005062890641d66141c1303095021a1f02803040607486200040d80380f81103000c0310341341d580da4600901c40316612440c9103450242c4900000341c07a83d180d9400d10f811070301d41d0243c58490342c8891804081c0c48003401003404660700c20000c58682c41900b511154000c61700d10385411034464410382901900d80c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 737114109 1250 737112859 737112881
    0x206040b0703080c0408030a03091406010806160203070803011a0f120604050108031c0f0f05090715081501120b0d030c051c08060603130203030c030c0105160509040b13 74
    0x40c001c00c80900301608404110f400c940d100c9452410302c0e29001c0703460b540e03100b5003100104242c1c803042840200413006403408070a05120090312643e603140c0e60859a10041212612001a04a207000098034004001c8a90640c1c10540b041d196a00300b0806400f039a05640d44600010810000d10301e1010201c0013500b2203040001e403107807203030504070200015030300181c0204629070010041c03210210340d6040100f100c00c001000220f404c1c60b07643d4003100104080c4400140007410b1008203d07900001144404c2505c81030354039070158455410040360a88005c8070303690101c002104015036a503005440c000410420b1140100301c0b0311040d8040703103aa50180000300c011422103207800d000c03c0b8003441010111101240c01629000c1d03007000007002d00300081d0a507401104e000011810703001501c1c20b14901140c002c2d0449595007240380a1a41d0f9a0000d15081c00d5540381602051600081d41d598154030180d0380d481c5800c00c9440c0c820070000700110f9020f9a40983c80e42480702c0842d05c01d000300e844d01c2c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 737115359 1250 737114109 737114129
    0xe1f08010b01031b020a110f12010506030f0d090b0715060e0601020706020102030c0f07060213030515060a0e16020c03010501060201020d05100f0e040501020d0f0c110a02031f0603020604 82
    0x20200700024050310585240ea00405401d00c41e00c074822079001071040d0b405030700304860f41c039013240300300c00700e0005c020f200c1130190452040390034865010015003040740500c606404994006642e001d0054590049014031400034014602c1000070f141c0100c04ad281c41c600030003a61146071440700c440e07022140b0950000016090102c204011980c06121075002010680002c0d46507180074103000300356100d82421203003c1c4901098010a128141d4161011100c003080040c030030360307102c0c28407640c0e6691125248800c020681d0005090b41800141081191400e0340300310300c40d464203a0100202000c102450045106540c8900d14a950901030300c1d00030b140d10740005a40302c2010103c0760940c1c5000300581ca40400710501080300c2c0c004141503004541c800c10b020841615185401e601920072004078011240c24243e01a0b1000b10343e40c030038000c10082d51911481c020031001007a45480c043d4401943c190407502c0c0760000084100400e20320103038050344c005140707500c03940091400e801170b030803d0b0500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 737116609 1250 737115359 737115371
    0x31503030a030c02150c0d0911100e131401090509010f09030504050a062118060c08100602010513110a0317031e041e060b06030a0c081e010e1f0801 65
    0x994050010071601540d445e2200d0481c0350014003c1c96a10440c0e455012455488190300b0500c11609900c6030b072410000c22124a8620a10004241c228070340b0384944507818030b440d02c0d03221080390712801000c2d91200ea038070320443c2c1c81d2811420041c900100004865501e0342d0010160f52400d100c0c95095501c02d03204c06807624242018000c2d00e003216049070061040260b9011003001c00304440ea01d00907215000402d90300d1540c403510400072080e0100418035803c00346040a80c982042141d8499580c150107400d101e5600c2408909031101900c05160000001c0460b101292850161105085001d84100400b0b6130300d50340c100210707203209145c441424020080c426840c003902121540701540080084c03c1c6e00300f603103a40e08003517890000c00003107030380c110b0f01c23641004040c1c2c02095031401c00906154072440c00711452806011407009010003c5c07600340025620707001500075011010544109000517138200928424124000303825000a002c014001500c0f41c1c24100204c000f401d411400420a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 737117859 1250 737116609 737116631
    0x1905100c0c1407090f0921090b040602010f0b0105120f0a0b0a140a08150f070e1e12030a1d041107080c010513120e0111070f1d011208031503030a03 65
    0x100c2e541241e1051700241804058000308428049001c880f9500b541110114007000c0c0080c0c404108541c40700003030b08008140054400e40660180c4030750300c0740071001d0003505215001118280304e40d4001e5905800460042403d00c0204024640e0040342400002807114401d000511589050b6001c4002d410204071030f8000d0b070500c000e90030f00401110f4000c0c43d600d8411044044400002003540d503409039031000040e0b1281c0300721555854840301038504405856080c111240034522609005d0003585000910220004004121914004140e66859100c50380075208413010001c040d002c0d030f22a4444001405425900f0000c2590500c920b5401d507461706c04d104500d003587ca0040c085400c8000b001c0d0000085081e20a07071f00241c3c100c82c40c18020105c030410050b113a050507411072000b188a1842d0105001d0507550254059a1402c074192400d10680b01040034402c02c01d014000e40048060003580005113428040c41d0071076035225039526841301c603202281c6503801078001400042d456a01c0075107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 737119109 1250 737117859 737117861
    0x2102040e062a21130c030f051e0606040b010e09010e06030d0201020f03060d060905070e090f0c0d030c1a0c120718061107050a171905100c0c140709 65
    0x2001c1203541c5050410803c41c030f81001007960803003104000c035105400202100c2440c0c0c4904409948824040a03854030303400d060022845205003100c07240b040c14414100d00001100c0700684000e00700040c0002e43e21401031001600d10200660f042c480082c104258548d125201a8082d060300031180c0101c1c40d06408041c80c1c00004c114072000d5910400c2824460350000c002c680c0e10100030b96501c2d415108524040009110f4407a010340b01d801941c00201d4080e1b6140c0b0703201e020303a00c0d0b4422101c52100510045490b5000f82c12181d40c1f01010452820000307000d00e00a00c925400b4012038107150384600c0d0b02d88045082101c3e421501400051200301c03140015103040d400c41078901d403088601e240855400d032070140c54061001400141c10703d81c1c4000b01d08001c0000502800381003008800d60398018a405203402c01e43d02c1c20f581c080c142e80ca2140c10300d070f0703195032031140d03008002085490908a21000102110b88002041041c094580300201d1180002e07158450b500c480100300b1640b410302140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 737120359 1250 737119109 737119171
    0x80f0705090f070525030206070e041e0e03040e090a050105070503192a050d0c020a02030d1107120b09070603050603100203060621100902042102040e06 67
    0x5108002410074810110b021151199100c40c2500b000c0790360312004142c2c0c82042d0022207941e203804040b0010b03241050303408101d46004080366196002140c1d140307401c00c001d9a00810140e40e00c04000144048001c1c0c0681003440c14651040941e80303040c5e12001a0074104600302e0303d440d030f42c0c2e1110651604000c0c2c00d01c04d40c0c1d80030001385012400c508250050304460403211080d5200503072512603c88602c0311115181c115a00d100407880400c01c2e021801420b6a040411611752292400031040c41c501e001099149100342d004002e050324284003001680d8004c0194880901445002c03170104150f000410032380002405454030040c2032911200d40e17407500e0b50715080441090f042c401405403030303100002c1d9240048200d01700540c4030341d04c0f000828694002c0005206400207101410b80e44203d00311b42c0d85028082680e40419900c0c2c0358468a03080c4c0c0319521400380100000ba0004880c600024217002d54644014004210b4500507056245007050555a1403080034400b80c44810b400d0030b01c0010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 737121609 1250 737120359 737120369
    0x72102040b03040201031e0f0b0415030503070f050106332d051204060b030709090203070311120723150406030c0504080d03020403030e09100303050c030c0106080f07 73
    0x1903250074208074200e4403600029100034181510b07940c00404501d00d286c0c1c41c00030701060003030811014030740e403407188054446502c55a0040c0c0c588242c0f03581c900b911a01400a070782e0000c008520704445590348220944507603034144c2d85175680b80310204c0c1c0d10010856403008041c50418025800b48200d40c080719283c24103aa01050001d01140c41c001283c0d00000e0040e139450403400d0040b0f044807143c0580d6a8415503003002440c1003081d041208000e99070b807100400c1541501120f4583d51181e02c00c6045403403e2101a40c1544003200420020b0300c0300c01c000f0700402e0060714516050340340b8900e0b00c2c0303441403680104200c40d400792004210b4070313084a6500c154041c00c413101c4c60743d10482022201203200700d000d444209600c130010b5040ca203000b10308a0b8000c010050840311481000c070310082c002d4019000440002e000554054914585951845d018604404441d03c1d030a24507903054907598041c4001e0f0311140070501691080c520700b8480c15005010010103028211341c0c0701d003828140b032101c0e005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 737122859 1250 737121609 737121611
    0xa060305070c020907170103080a1124060d0605040b09010c05090d080d09080a0c020109090204320402160507090603080a08061306080d17090c0103020d0605090721 72
    0x4001c40203a110b909080c0341034055034100d03001c1c0c0740d0160031036207100015030300e003101207030040008200010074009040ba5800741d80c0382050500412186034840c01f005030b0080500c4605038010015611803542942c0000b0000d0510140b08503a550b43c1007921422601130b40c1d0106501c0c200410701c03400f070007007140f090005d1130850701c1d00c0840000204450112030001d806108042a0003003019096889501c0d065000a04031ba184d081c803460040c41c503010004c040b4005440c03004001210980d5009490545024141d0080502c00582541c1e09481d0074a050b01410044521100350300d49a0784000c26850708484400280340480b03040042c900702d5558030460201d8075001040021412150030740f120120039241c42661031f00c50b0400540351284050b900041c0300d25007034001441c102d0000b0a00740c030000340d0311020111590a01d41d035294001c100c0348a502600200040360540d880784d03004110003000c0031000075509440d000800d00804044a01c00c010400b411010f14400740c42c41c5040001480b1884 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 737124109 1250 737122859 737122861
    0x4060e0408070c0b2a0109081c0e0706050f090d022223010302120304051008250f0302070c030602040e18070510210507030614040b06040302010804150c0206060a060305 74
    0x300d04a14280e890300300c1d04170358001c1d000c0b01501c0c00030b410508010b038020740d642d81c43d0103c1c050b5900c070320f10000b070a1107605403410304490314812000c80c84001b1205036849060500841c10303c40c1505902003101298041420030705080180d40303440310021000310041c2100b4040d900d4490160440d5894040f4030860792180021036141c80e510007502d419650b06990100d0f2442024028618601071a00040e42c4414010880d20700e4a40c46281d00d4070a5002a5050390342206000005070054880a44ea01c00150103001440c1707400d000c0c0e0004c1101c0303403152132100c41c3d16981e505ca88003260050b400404004450070107200c206104412490002041103000d071000b1850700001a02c1004e104d001e15052018840e0440c00f8211246120114003903210014402071812880040090405016841401705801241005410103101d5a030078102c001d007615140c1800d42c0c006480c07281c401441100d070640c010a0280711409140a4400108140d07001480c41e42450303010400c442019030010310805107820 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 737125359 1250 737124109 737124127
    0x4090c030b1509031e030a0f0507050703030f120f0504020f1e010e010e0d03020a0201201b030309030d020d1d1f023f04050102071404060e0408070c0b 66
    0xd00c50b80c08071400740380241e50b40c030580c3c80400d05010b4441040310344500303048605016007070040020088005141e070740ca104030103030202c181c8550003038000140081d88a4942400004d00034402070080090500340124030048824403007054615040086d036410f51510140021401e180070280401c1d142200c014409401010030510b564030340b021038604110448618892990095115452040010349640c401d1011810041d58840c0b105404900098002c0c1c040c1012507904c0342036200c85d081d0040608524810030107001c08405441c81030903858001002005c4182d6000c201c4545282281d40140400c03100c01c2c00003034104104424000302c8984d01d94040e5401b561341c0d20455003040800d5000c0348a560880c0700480ca070200ae41c80d00020001d13101715180c400d0700124600e40038410020032200090500c1d038180c40c614011445201d0150740410018400c200d02040300101004000d8000201e5135500c8041402910041d10140d8081d0b5002452200f440500098200138040f0301302c1c02840e20000d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 737126609 1250 737125359 737125369
    0x522080f070314280804050a230f01050a0c020613060f12020f03190b04021b10060806060d0303020c011103060414040b19020403080304030e0102070609050f01030c020f011104090c030b 81
    0x11920303c440c1c84c1414101d004001d41d4400f40c401070200030305400c07502521100700c20403541050401c030310464081c2d81c00c10010300d02019035101d6858183c6d18981012554001a40c0050325103500304e0780700605000a00c04085664641c10040445030740c1c114140e1011310000e03200031210381c3c24a400500401070480100260011640c20a1021003a00d021f0b0b000e00495034000c2c000c103190164480c0c0009003240407810400003803a1014035600c00d4034100203008070880c04946080c4102081e0f0b40100d0002101c500c0c14101c464045400b03810007600c0c0903040301c0f5081c21a43c81c074001d40480c0c8000320910120b405d06100700540c054981c070030301c605400c0540703c02a0036800100011380b80101000c00c1d60301e08600b40c0507034004592208031140c580c100344c80c1c080c000c2c2060139100360052046810008056202d00150030403100701601c01d13407030541487d004401500c4280292403e42c802e00d205900202c00034459101150000104103031124102200d80c0705540400d001c040805080201c44000d039550 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 737127859 1250 737126609 737126653
    0x40804150926010b0a060509010905010507021c05100207030f0806030109170a0e0a08070e0f041101053105100e032815060305010f0c0522080f070314 66
    0x100b01c022003103070005111101d01401481d0041d982040e800329000440701e4121019052044007604c50a04a42d26080110f83e41c1c007480c040a580f08100c0101603c4054418580c001411b0150003514001d500c9022030780c059038050981140080c05888a8400711580814610340280c0101e000f402003240c40d8480b08580360141d518144104400202c6d00d4241e4002c03404d00c0e540f141c001d4062424503a1f180405910760850748035403600d501c07100700040c140303036404400240700303d903c0f46100c600a0110001180e85800c4118440300c5400b1001c10188030360007120720300c0380480c1c84841414880d402e0001784440c2040002401d004e10101c04600f40f03141d50040b0b101c0040d294170501d140c0140300342c81d07403d0000d001c0c5a08050203d5110b82c000b08403d0304150080c00540e40140700a0001c040340d03003d44401c448228400400007001032081080c00040d051a180502c071842100785142611210500e003060505040c2c05120340c080c0720104100720562840884003016507029045900d80754603071200c8000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 737129109 1250 737127859 737127899
    0x7170a020607201f060503030f0f090604320a080a0b0408070b0f070e09010510120e0105130212060c03131713080c0415050d0510050408041509 63
    0x40d084100f0000d407050010340351042e0b142e012298a4240f2204100918036081c1c10b001c41141000004102c9050000440740c0300f0008035a40361910f2158030f40c01405400003081075500440c02c02c800035a2196180007003d103a9040f00000c5803122100c0ea0104c0c0c0580001952800303030094031004c0040d0000445c4c2c0c1c0510039004a440d034010703900c901c5c20910724480d00c0e03401402184207c05001800c140c0c031140d14411030f05502c0e001c0342c8074000f9040008203030091290a9010b5002001800114402d080c000845d1404800211740c058001003000c1c03d660b0100c0c0e4040100d0f240c41c19507020b504d4202d200c417800310303e00409000d031070a048414003640d00c001088140078441c500c01d00010400d41c1003003244a62000c3c48050740350038550036015100002c510410003140f003804d10021031441c00d0f10840d0801152005412242d81c6007605010040417410020703119402040804080b02000c2d004e02d0b446244a102c009030348904012410000e903000420351001c0050705034040c40800e1f00c0504d0f003951a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 737130359 1250 737129109 737129117
    0x130f0c1806050a03150e04140a120e040f0905030d1404110904051c0816080f011e0803041202041103040f0f111201091103010c050f031b0f07170a020607 67
    0x288250109401621058241041c12545c1c488000354124040c80d06900640c4034041e0208404c040c6d80d4029900e00305c0003005820004d05102e209906402010100f4030100c006d040419000303203200c04403003200c130b01d0384065540e0b80001940c400c00b0740f0715208400f076503080805000d00350f0130701d07440d00d6288440c151903040c01011400c0104003805410403000154285008910002e84198500200000002d035001164580c00049200031720703002d203d50074422408220324490513860485050319500000d41c6a44c800e4401d1b02d1702284d81c000c184001d0010b030000200c1102140ca141c4140002c07600d0f0400c000c20003010178814040040c00711042142e10b40d400400b5041c801c14141800b100109034403003003d9000e03120324a1143d0513030041d00201c80041c001ca403034882d40b4a00300181402e82e04c0308031f15100000c201f0407c5802d0000d0800145411900b0315840c580380000701c03a66110564080520581e100002207106000c100040b68151040b41d82a416181001400e02c0003a40d5184003500350410301c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 737131609 1250 737130359 737130367
    0x6020a1509031106010b070203102901180609080f1f0f020f03041104050108011e05100b04060917030a0518030a351e18130f0c180605 59
    0x414401e02c100c1d5401020101503138583c0d656a200e801071540580340480c001d000300c856a4400704020320a00440c5250408002d8030182c1e40300c544012420050929410b00218a00c114030f44440323204010040d03c1030f52a400c0d42d0390300700862240b9060809000201a60000100c00f001c0341c101c0d404030114240d2900c0100c2ca41507508800300290240b24604c11000001204110502c454600d405070203c1080e501048166211401c0b83d0030b8a140f800404180300400e18440703081005548000c3d8422004124040e0080d107820000080b90b0040c2c1c82000015503402092000e41510f40c1c04420f003052245c021440e021112001400ca80501d1444e50441c90801000c012281c84c1070100c00b400e6540040d04850b03200c9800002d94403000325500500e1000340300042490520304080c2224001360505940c90800d0401d80b44202d007030b80c000c50b44541489aa410340c01c0c0d16407648a8110143c0000ca4800304000034514034203001c03141c16401d03110800c50302030400780940f40b6104003281500c03081d00d07240d541d07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 737132859 1250 737131609 737131613
    0xf0f050904051303110607020d0e191d010f0806040602090d150204090c080c090904051f14060105090a0512070f0f0503012d1d03121006020a1509 64
    0xa80a0208403503001030800301086105a0080c0640359020300c01c5e01d50688500c00741541c00e603180404c40300000564086445810000d0240d024042e110740018100005240c254500b0072821b003a55201e04503081c258a24410050844c1e0180c501414841e070b130302c03c2040c0c07800038050741c0e803400904040c2480f54000307041400c0351258502d031224a0742020b184141c001c2c81d01c00ca100250301c05c0c850040f1885c0b404034030318501da210b00d0449010f20010441a0b04159052080180401020303000300d90070303c204500e4026000c49035003004589100118009001d8617246044800000c00408003410000304015400256072803254036420346170181ca10f001c3c07501100f0320840c5401c083e60000ca140b440f040750000340303c50031001c20780c00f070724415030003400481042c2c825107650794014108540d01c503564010392441c280c5907030301010094141d140e00c0302307451080004541c1180c2c040d01070410041c07961400c0000c400703a94000b03a0018441407006001c901520384520200701410b206071b91140d9181c144101c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 737134109 1250 737132859 737132867
    0x90b1807060e0a0b0c0a0c060306030c03022106040f030801090b0306040f05011e0209030c010e0a090c022409010606020d020d180504110c0105100308041203170114030f0d0f0f 77
    0x1003d484e056500035a1030b0300d84500d499440740012005c6420076181e403400b0500c20300c03078020b090450b5442418010300700d085608101042c400550940c5400c601c083c0c00041c5803d040007014040e50061701c00200164581c00c00420094050300150001802d250034040c00c0d480010f40365a11540001d008400c4101c0d0f407601c40d0150599020041800c030106865008801ea60307401044001c400b10f01301c6070800302c9035005444400e03407126400d501080c2d840c2c081001304800e4010ba10398903464410360b40845c14041030f05120700f008242c0c00d081a20780600304014160b0910070398000d4500b134002801050b030448002942c2d542c81500e0310040010076030503881e42101d5006081d0103040d00900c00e2003221070aa61a000c107800003480d0380c01d80d60038003011550403152600c2c6002070304d4001e503500346400e082c224004080503030110201d041090101e40302152075060010940a08044030f800c41c18406103071300701441c0c9070a0320340c43c080941102115115681c3c00808000541c1c04905100b00b0145003074009603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 737135359 1250 737134109 737134129
    0x307050603070c0f0507080c0a1502030301150e0907110615150702120607020102070b100501020d0c050a02040509010204050a051504092a0201020306010f0f121e0e01090b1807060e 79
    0x40c124400c1c6c02010441050100304c0c128071190079240240c4031a82e80034484038075420031a5807000f6800c104014480c61b544403540901c5403c4a007400c0800c0c0c1c3d000404030310001b10841e94403000034901c4054811501040c401540c0021401e46070100c800b01d000005282904030350004111410002101421034aaa503a041c5072120b00314191003840c0b40940f03020b0701039400420122020400e5100207241da03a0032a0507a4182e45041c1e00421424000c0e101c1640c03c9021070f0703402d40c9d89205003a20382c00181d555010b181c0c4101d00c40000580c07218a001d050100c50071407504101e204001e030800044142000c0b030140d5084404d101f8010504201c54918103a013116002842c0c585c00c02880080d448503901500214080c0200b030343c0750390608185070300840780010308055000000f12000070702204030010740c00a600d044a2108281d10498058002000321180c0c486541444d1b512036060074180207100058690021030f003003071001c29114110303491740c40790300b0750154006201c1d080341243d4041d11144122 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 737136609 1250 737135359 737135363
    0x108010504050a14040819020f0c060706020910110d0912060504060b0303120f010e1323010e0f0d1110110d020d2414060903012a0e0307050603070c0f 66
    0x82c0060741068280320509602a82c0b0350014001401c2e1309241f124030004204031084c894030050407410011408102099002c1304c02900d0040e000c0c081c45441d079071940617101d03914103551107280c1410f102c1e1411b1030416100014103000c0c0408103004001000100103c004501d501007400101d641d5a86008801040d41ca20001e03003510010914114ac1c983c2086080e01490411f0841ca00f1030703a0f22442c1c809988411100e44070300c0118140f287c000503001c1c40141b00054450f04498008141d8080b1190845080c041d8210300d65101c039040030b11030b0006101d02c01c0b4800d56840c08195108000c0181e541e503400d0b401d1803101c101d030741d1540a540e010f003640c00c5c0e84038407120881c00e558900150b40300c280600036882c011070710040c4541f00d5095251030380005400310707070b14688460180c04a1000b00540e84d0000d141141e055501d4240a18003400020b0001ca141e410700c032900301c0c0e03010718084020041c82a0703a000341d010781d10421090149560f0201900c0c2c0c0f02c070884c9003900e100445450618680300c030710300d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 737137859 1250 737136609 737136641
    0x70219021903200d0f200603070906030b04060f0b130b030123040504050606150403120305090706090b03041707021005190801052b0c0e1503010504020108010504050a 73
    0x10210420810884440c0d04040e00c405850f0a001c0c090200f158400c1880402000030000486050001e5280c0d211000410800b00e00f1800d191641000716040b070307008960820001d204041c0500186270076200c0c1d032408620a9070304201040c1001c81415107110107001c1c24141d0100492003440c00c08130180c2c000b000d00780c01507003252a960348055000b482a00b00c143c1d440e10705015201c0802c0c904062252510858000004110750b8994909002c0c1c00e13860001545602e0f881000080046030310020341c030407403601d155400540362030a1614030303042100c0794004c80100103194408021560010080d80c0d0041d0b00003020950040040c0060001445130100003508045030010034880250840c010308050329851019010f20080d0f4082200c5451090046560001da000541011500708801c0ea0b82e0540b491468001040d03525106c0481b01e48041c2d012480c5e2700341c0b200c1040103000c55642096154101030b4001c0c041070409030f002914100050141602940c0da42d000a240120075400c02140c103240800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 737139109 1250 737137859 737137909
    0x4061235070c03020907020303070804080f04080a29070504090b131b0e0111100c052104030e0a0e0604050604110c010510121509060b040e030904050c0307021902 71
    0x80c1040c2d011100c1e200980c402c00703500000400543c008030031244079540699400e186c0d0ba490307581301611034006441074071000741d0034030006c10482e4080080e050380c240280a8100520f004d103089602105101c941c112520541c2401c2c00510785d004010b95003654103042c03000c02d040d0180e4001c1142500100d8181a40740e080000e2224034851000c440c800d0810b09940300d9a92448010040d155400888031181c0598032105001266050652000c1005003091070400c0c500340c06106050303601810810401d60300c40b0113400307220405401c044c011542d40b0064480a65480c5000c10700d6180d4240144403c3c00f0b5501d45001401996560b4450400814203200ca00d4581c090342c0900ba000780802c07980f090002521141c082803800c5824103210780141e0040d001002031400e20300200c00780440034022102c950704c421404034980c2d154003030154091078201c020b40c1c85690100400c003d442014100e0702c1407038000c0042c00510740d808190003c422100d109103005100980c4040780301d26140b21900c600382840c100d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 737140359 1250 737139109 737139113
    0x90804031202010e010e07050d06060b0c0607091e06030c0908010c170919080f1303110118150e1201050109061e12061a03060c090406123507 62
    0x10400d6500d078041540204240b12040d00f0090072685141000348659002c00000c10080c41c012201e8808244281000700300e040c0d0b140342c504400d0b00400604071254110300208002c59030f000f480e4400400303070040303072145900c5610508280440140115000c03da03e0710280d0701c80c50b00803440c1070002e040440080188055420000340500961000e59800a600380007141d0324050000d5003d92550b8011462180c80d01c15684084960303020404d220031000003404103201040d165508500113500035115a003000804e180010b202d00c00c244012009104255002e0100b070440880c40c50700111181003003241100c0000001f80f02c502541e0780c1e803900d503090a0001c1303034003501a0022070864021440300d20001d04920600c1c0c06155883c042d03042e8091300c5a5410380401d10640250800e884e00601304403c0c10350802c003003803c2c443c00701e903941c05118002410780140d0403c1d1088500400c0c0140c150004030b0b2166650036041c0094450700400f044081c500a1b8036000340440c0c8489602070180800d507070784114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 737141609 1250 737140359 737140373
    0x3100902030c1905040f0605040b041401020a150c0e1806041e090501090c0f080318040e0a0501141f030b060406080a1a0a1a010c0305040510080a18031e020109080403 73
    0x502070300b0013000d10100c000603803500403000c2d09e081c2c4008410050805050006200810a000051a0440c410456a000130461020a03103450504100000c41e400ca02c40c2d00242c1302d14103414075640180c10300720082c03144540b00e92501e40c0225040b1800310f081012900c0f0014210006444030a0740d919005c50881000015441422030340e1082c0300b61118981d0300d05040d00c5456030380c86121a20307001086560103412004038040c140c141c0007480020380e42c0030540d445280c000b818008956980d9035809002080e480c070003c003980a426103c4c52400e00e29010b820301504041840002c1800869a0201d1290b5440b600060041c20107001200d00a1060b42130011b80c0030600031501d5070700e440442c01f04194003182c0c0655101555101c203d080707000200d00044070003000010003903041020078400070400703584003040010041e00f1130b9550000341c20321403010011102c401201c200003444032070700003001a0700320f64081c10301210300041c134401c103140500c00d034050050fa10707004050f1000010080200956 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 737142859 1250 737141609 737141617
    0x807050712270e01060311070b0603210a08011a0406050f090d0b15190302010810181505040b0d02190509010902070303050603150a0905010e0316140303100902030c1905 74
    0x48040c030780c0050341d84001c01e1b411510124504130012400b04104408030b1402002290081d1010f0301f1110402942034407100700510080000e0040e110010300810207e03440360b641405002d040748942c010840001c03030040c2d04d10441c0719500c140140440c3c2425085d055109030385031000082e10782480d000403480c0c1105018422240910368403100d00002c01c039400c04083e41c0b020301e0b980f010001c0080d420340c1c0041d20340c840003e1034668045801d44020402c0103c40580300021030241d4000f06a40560041c0801c607507269070801402103250200201d010707940c00642c8001e040e012385848055a100c07080e0340c602c0c408290031460304901c0f007000024011082c1e5001740031b014003d40d000c001907101c1104140d1a1101540049a15000360000c14000900c640c03110342032501c18000010149180b00282e42183c000c0601c3c100181c140502d0325040c088039031510080c079441c0b00c019604c2c0d854151040006610540174500d1044e40c08400210b0803015141120480030003452008015845250001c149503c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 737144109 1250 737142859 737142869
    0xf110a140708060c0f1b160608060a0801020c071202150f0d061e0501030f0f050c07030f110a1707061404020f0312030a0f11031303020c01080705071227 67
    0x4181c10001343d204505100342c0780503124048056240643c4030507011651024154030b0030f030740d00403600702c1006002c2003106000104800d8640c502a46071003030400a8144c00b55100b0f02c1c00383d00401483c034001c0e801051084c00d070b45a429990111224034000715901450300070340703989117050000d0078541e0040c4a10244c070b41c41a0b104018400309840740503d203042c8002d00c404511190110100f8000c940c0030ba00490032000601e10700040e00011000540249d44051740c00030448400003400500307140c1d10801c0152001c445041200c2c40c8868030141c66540d60360224040c081c00001441500e000c044c5e242100c10454001c0130509c0325040505d02514000c4040c0c034120301c0340d4242036901030f5034203010a80c2c3c3c40c80c041c4112500c0c01c6a84030300540014005020016038110354610780900417907407240c091405424209194521480309180280c40c05044002e000e0501c50342d00b080101d019403200440c0d0400c2d0b801050320f0400b07040706c5402c0e03641c1c42c2c00102ca2a60b800000c440b52148146009801044507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 737145359 1250 737144109 737144113
    0x30d0305060f040c1b0305220e0601050c1908040f0902220501020d1211070302100506030a08030105040c090b04121a040218150d0602031e0105010f110a140708 70
    0x21000400040302e101c02981e501060303070036031140400402141e1004149000741001c52030613a8070403015400038014510000e032070650340230503c41a841e280585511410a0808500d810052000c40380c1e00c2300141120b2a00c8024950380d41c042043c1141964000c01c52000203040080c0c450080308003035008103000c41110b40c0c2a107920000b000380441200119001a0060455a030700c50004a032000c01c514601141c040d02c881502c0c00745107002d030040400b10700aa0103401141d0541d80380409807800a41618401d501103101c42010941d03c0b030459044600841d800189442d2203041030354458940d90100c0c06103003000c41d001500311880310004188901c0b501000222100c07151858907904d0050b01c1c060f40200e0304402c18540503101200454100c000e01521410759114003000403c030f81d52400048800da80c01109000c44814034a83c230705c2c43d02e0580c250b9800c4039814400000e142c55403202c20141040038184129080c40070a0000e0000d16802a83c400c800750031042032243d4454403031088403454 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 737146609 1250 737145359 737145379
    0x50a05090c040c1d0301020705060a1e050c1206010e0a06050a17130f170d0b04110c0a03120e06130308010b0a053009010603020406080c09040b04030e030d030506 71
    0x181c0b03040d209051148010b40c0300d0a02d1a0840306050380c0c104151800c03a60150b500b00400c80102e6001c102da144907090084d40407030502401d03c42c180f50801c3e0040e284612030b06290900c84071500220907507200c1c0013180048122030751840b00495900343c0000c0141d810238501c52010404a5104009185180454039091f200b640034400f02500c1041c11100b4421403023006022100281c01001c0440c107040c09401d111203245c0d620303881610190720a04030503506c0e80d982c40a603800b604050042001040503110f0190422048905003525004060402420040510001680a100d590080760810172550840310030389001030201170340c40c1c607460050f4080340c5090000a011108281212211301c4aa5107443c14032131003494400300880003031040783c640840f40c80340c2d0241549040220b486010208004103039980b4600500c011100c5075040404541c014182c151001c1d19100003a9400541c48035000722107581d58101180c9001400e18015410f0083c003842c1040c450740354000501448003141d8000f04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 737147859 1250 737146609 737146633
    0x32c01050c0a080118110c10060b04060c0212010f020703120b0306010b0409021309050903130e0105060f130806040506010932070e03010e07061706060403020d080706050a0509 77
    0x106018002d04803000500d080018042c1000540c0e0140c01c6401020000c1180701c65030f0040c2c00d113500130300e42c08025944007003620305200500b4045c80703008014803000c440c981810300398010140503060a019004600e00c103074000305940d00750300c0401005002103046483c1c10943c030300180000703055101e601c905801c0180c0700b0403500d00411624102c1d84450100e0785414034280421020390850082150790b02c8900600040000e01400350798480d4070504051551610700c5034504400f01100e8000c03e15251900c4014052912080129144a224542180d407949091f200421400643e608400b00038041c7c3c0e81440100180054994180c480340c49041c0090b40842009041d844c28814030100700c0c10342402300080d44100041c071581c100e40c6070714103100b540e000900801e080d907450800e240c08650180d40200945e82c0d2000d01a050500c0c8101d00c00c40e2030800c040014010301070350000bc1d00c11001c050714141040b40900c103c0d00c0c000d0348000c0600c154909a0702e40b40082100303c4070a80c06001d00c5c1c0c10820 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 737149109 1250 737147859 737147881
    0x709050c04060305010e360a030903150507050904020903010f060f1a0f030f04020f15031506090604050105030919050a21091e03060e070f050a03050c090601032c0105 73
    0x2c4160404401409115501c451880e11fa50a514030b50a12225156190f0380c104400c2c481d421a05000340ca5080803585540351103030181c0800f42801c49058075020078406800d81c0001203408840c4222405038464401000090040a01c901c1c030702c182c82c0c909000000c0340340408a042048a0790640a90414030a50400050034411000c20030980201000054028480344c1c0000360801c1c0094509d111110200011a501c2000d283c0d0070118a1004010060b10080310b01e41981e40d5031043c3c2d000b0b810304080070041241c80c096801410305100011000500c105002c11501d034910080c80c03e103000f001d06070708090303032581281c1c803054481c04842e0100e107440441d070095642d04e02c00b5035034401d5965407600c403210746011500303070749000d400e001408000b01084850041200e25460800500901e074607140c14451282c060b0f51002d03010b900040c4080003c42c034082100c144d122015038014500d95561401203000300807448400d402400c006c9144105101c80700211050043ca22000300055160000f040d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 737150359 1250 737149109 737149111
    0x40f080607090b07080f130503061311010c050a02120f06040f02090705120f0403030209030a08041508070c060c0306050d03080a0506040b06090f060d0222060804080a0309050709050c04060305010e 86
    0x982a407800300f06c03d4091702a0f200080a8400b1061094682582c4a0300020f05002080d5148010030320780c1100d403c107002007500d0034094050f09003813000c0404102c1c1c0da655121070100e0380c0a8454080010414025603080c843c81002040c50400d84007240340c1494903d500810081041c2d028000e46000207918501401c2210701b010000200020780e5034401000c01141200100118201602445407807442d84081202e030010501c05c59919407540e05200941074614041a5400100104507051003103494112100043d041c0c4c00000100d8101c0405900340c01402c500c0d031100b038200754411002c4041c5584090f8082c0510400741050000e501c40100b0001540c190900d0f10f42e022004001e0101e0f40d20b400391403105ea445010301028100002d91800c0700407604640c006030461031040309050003208201c501d00029255034204200603003481c1d121480e036400f0341c2e00b5650a0580e00c0103001d052000411074007004203800e41c0140f241c3d01c4d0811904055070410720802002c40d0501001281203402c0310003c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 737151609 1250 737150359 737150363
    0xb3007020601150801030809030c060406030603060b0603010b070813082d0610060c060b0a080c0102060f040317150909030901020f15060105030c070f081e07050d0e06040f080607090b07 81
    0x251342c0513421501d03038480682c007007074000740d00d84900e12004805891b044090801404203890000380b491440c00c0c034009849100c5140e82c464401000140b1000006009481540b41c002d820191100206a00307480c4c085103d41200599102c2c084015507519064044400e0607820401c02103140800142c0c03003652490f060715120303a03440706030209005851254060801140c000d0700040f54000d944404941e080031141c1010803e500a564072110a507010010b2a401c24500200015585415280200f800700500f03811100c1c0c56140020480c1c44c080b100005003010401484402c072401c00211441d41c0e9444280214054020404603a160746ea000c039810040352040c00d0240d803182d91701b900443d9258401080030303107460018040d1001084100d1500d1203450300c500070480d590186c80066250301400c05100a00c00001046200e00080d00030030314905501e90b40c2450300450416400091490080750000c50b0900c40b40f03a000901202d001504501860094458104142e140e0511102070301c580000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 737152859 1250 737151609 737151617
    0x40315060e070f180902030924010e0f130213140c0403080708030603010219030c090509014e02180408040e090109060204080d090503070f0b300702060115 68
    0x507544950b00a130f040301085008084414019900c0300e110400300d030419942c00b8030700d5010407480f85010250a0030401c12002060040701c05615210390440e51035001000301c0700c80e00c1c3c2030000c034a1001000c00d503545115402440307018500340032001d80008081c56524030740f600e448440031824030100d0000320b400340c9400140262070700b0855152809554006405190159800c0112000e0010345500340344507103c01f41d5001c240141c4d010001420100c16400c10b034801c4605500411481c010003015245014016402807861900040190400c01d500407241ca4402c80c068035601480e061004d084181c24400c8401200400030000003542d1560f044070001c1c042507080100307000c8040c8003560258000d45040002c41d15222030740d40c1009136002680800d900e64021032644010ba500b01d0038100181034164003e1103103c0c6810150140810b40d4401e15991003400200302e40014410b1840601c190880202ca5540000e0000a848005000c580141c014000d00c0000b0170b080c1c03a90039094940e5089640c2d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 737154109 1250 737152859 737152877
    0x50906030c19050d0c150203030c1804090602030c040303090909030219050307050d030209010206060d020907030f0207050105010f051e030a12170f070212030408030106050304080f040315060e07 85
    0x1c2485207010340c00309092866140290b0000701d580d40e041070240102e1041440fa080c8910344001101030341c000701c440c00d066410134000c00603200c5070002130710004a0301703c0100c244058103202003801420340d5071340503080500000c1004042054800140112403003540c50013403844c2e8031004502101c1d00c02d0340090058001c190401145441220285003590103481aa460001c080d81c500d441d000754407000002107034010840800700e40c1c0601030310f644004180c44540301204aa0f00003411050000d0040080c9a6942c1501a42103c1e6505840540754810000c10071542c4828207020740340e4807031088030300c603d0016004096074192a001a14449005030003000750641584da16440010545014410031114125a86131b003c0342c0f0f007503280540307110340341c0031203d0400180080c200340c403030b0540301e1b1810820424000024140000c49044510038500f45850fa15249030224070380c0b10740060503400e12400709000c814803a0b1100c4942c085004488100074a69803941e0324003012808031150030110300001c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 737155359 1250 737154109 737154133
    0x1a130b01090f180e100510210203340b070b010515030c030604110d05100b074101020a1b0203060a0f0b03190c08010525020c0907050c060105090603 65
    0x10700011421300d4048140c54480780c11181350300848204880c0d024000741d00400410942c84480100710b0710901c154100c5070280229008283e542500d4182d03901c55060008100c0200d10210440144108003160505820346d6070795000003180d045a01d0580e031490800300006050303e4035020b03110142099600f02030555580d05c01d40002500010241c640090b207030140c806078294070400501080d5029140046e1606020f9006903006a45820180015200b04011408551940744105034000c03028280300d94403903c44070344802c01002880600b02001c000c004800342100c10f4000d410000f40340d40c3c4040310205041c180090130300048002941540008010840c10784254200301d800d442010004555485080c001c02e2a0042845528566000066070001004403201509000701001c00081c496420040e240244515458125544018204600c1e100150007481250041c5030024449122481d04440151080e400084911950300904e4000700f500d2800e076091600504001c3c0062005103004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 737156609 1250 737155359 737155361
    0x30a0903060c210e010b060d0e0114190506061603022a09010b07111201020705060a020424030f110301180903050f090a080715080901050610031a130b01090f18 70
    0x101135180255203c103102291a00c0340300080c00c0308006034000080090440000304c0c2120f85001940c100501802c05126006a482607919a054082030700080c0c036031103c2d00000c4003441074002c032415200c0c0303818100c0181a000710780340700d4261500b868501c2c40c41e02c404294240c95441c2160710703440b9076540014008050064060481c092080c0d802411152444000070030340410940a80202e030b400007a103c0c100002070115542014000780b0940c01d00f030a04c0003c1d01007100e00c020b02c6049205104010700c440f840790300076034401c0e80c58200330402000f2142c01c4003002d0b4000d025011030362001c0c00c2d00c65048500b5201d040d10b0950565101400c4c02c11441c100b0172298402d00020b42d000c003844c140410380a40500606000348039070106503090b8440781d100901482d600806420040e49000c00700629501c3e0004100c082c4242481c0028404402d074658010199401741d0480c0c00624881062844180d20b03480803207001c1c003d03203800c8041c95a0b11070034443c0540600074140121001c2509207165092 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 737157859 1250 737156609 737156621
    0x9030503121f08030406090509060f06031b041410080405060109021608040801050a06170607030507030204030b0403170901060807230d1505010509070f120e030a0903060c21 76
    0x80366011008900d60030a5440400c2c0a0b0402101d540000404120700c5400000c2e40c40100000e0300d00c81c183d4a00070001800001100781060b0203004000006070704100031110390341d800c5440c45400d43c0c5980c1c641c0c043d0341c80404400e02c882d008070751407030500c1ca1300d6003d141d45a100729440402001980e09107010750002e03400c118441c2012401d09001180001d1107400508080e1024100000f40340ca4911010001d035183caa01c088216481c01039000320921000c00d4044e03008245080110311034685141c21402441580d01c054a4502c0a02c107120803d40c0c070000700900c00c41c4086104407151035800800e4222041e602c50181b00d580002e408121100c0d4001001004a50280d080341808816a000c01c003801426207003280c02c0301c2150000000143c441c80b606015100a5034504007030701e00400c02802c083d042045040a03c2244132004598820942211800300101420b80b5210b07444888090500d80003404100c3c2d04a06180390503c1c0144604d480c1c400d000901c028940c980440300c00100d00500d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 737159109 1250 737157859 737157871
    0x101a060a0c0510090311010605010507050a060c140706020a1e0905090a060902030108060103051009020a120c03020406061701090b0d15291e01080c0d02040503012a0903050312 77
    0xc003021801e1003c15803040e121058002c0e03c1e40c03c3c07117080d15066142107841d540c01c1a41800710910590000c5034001400e0881d07664000000100d00b9489081941d0302100001e0592110200103604010404550094440c09040d0b440b19401e640000e80d401c03101c070780c20a11010004001c203030f042240707240c240d80803500207460901c0003401a40f1a40200c060368002d03000340d441035004000400400c2000c02818540100f1581c0030041031010798001049100c1505c16682003450405945d401d0110303c504810007513500510410a01c3d660b4440030b000c0b144901c941e505a045140c00004e07005000d80a60f40010704005c0c00c01b1003100f02c40d40d46464442d49584201d200d41e980e0400003070b110050343c203002c0701005400710f010800700000080105803568420100c800d40d410502e40c00c0c990340c20006c3c40c0d41190794000030fa03441e4102802036400038003640c0d01503070f0f066003000900c05065520312010a07028804082e00c208420400c041a55403030745034400100158401c2110a074040304209042c0d070012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 737160359 1250 737159109 737159113
    0x90f12231614240c180414040b011406040b040509040302030d060602030d11090a14042d14070e0f0109120b090705191e030212101a060a0c05 62
    0x200035071600700b0202a019050a036940c030070020210a114144210a10002200c4102c602e514160b43c0c15403050003012441d80e080c0c42a40452125507803150402d440d01d681c81000b003480c902c0d250904501c01002881244280e51881030a810941000d000316000e8400450a4502d89841c00c4d06201c40c1060040c07007039085004c18025090300c0c1d10729000f1900280010350055850b4049030326100203e0f194000744003e111400c010070056500c1e00c041c40802c039290044d80f14007441d03c080120b4043c00152460040c9450000e00309000301e4a41c030900c96481d0302400c1d040000c0c409031000e074020300c03406448240110b035010001c1c03802c1d0718054090000080b810300d000e81e900c568642d2400d003d01150355040310300100000c01c100780c41d07204110741c10040504903403404804206203501a5060340038090409501222035983c0d4440c2104c201d40d0000b0742c0e000d81407040444424600ca9202c100c03100b11903082c54104400806410b5410140e59a81d1500520091a100c0580010b552001c038041c4210707154 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 737161609 1250 737160359 737160397
    0x102030a0806240f07051204080c15040f0e0a0605090108060f0a0908030a24120f170c0f1614040c02010b041803020f120a0807030b04090f1223 63
    0x454000c3c40a414008800400f0584859903441c00700d04180800e040c2c0240c0350401d010821101c030340014076002a10040d50314083d00460400c5a50440c822500401d01c1a0102d03c000940442941c6019104148070b00c3c0400c8059210000c000003500c0c00c0c400d40003580d01002c0840c1c04641d0a100c0541c0106106400180050712036641c581319400807074840d904640e50b840c0350101c1241c20120359031842e9444a500309014101080101e03402e2403800064200055079280c902040042d02ca41481640740d10111070700c0c0c0e00721405075565206804100b24050007403918605817260a8668070703065404000b540b80c5201802418000106035003880c102c1150340715458004252210b03c9403200c1d00f400b03041d02040c0b0400d9800c0291030210302c1d1401c40d000d68800c01507418451004c4054400c2e43d0740501e4891056112440d04802400c494441103512906d004100c81c01c01400180400c001c2d4840d000703450b02418034801c10348101d00c01043d842004081b208a800c2c400c04240028035075008107000c0340d908 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 737162859 1250 737161609 737161669
    0x1507020c0613182301031e020d140604031101021315231b0a0b0423030f070b0a05040c0905060613080706270e072016050102030a0806 59
    0x504200fa00d801c00c650780d0343c0d260f004a01e96030800b440940c190f22140c04185945140ea44e00c0040e110340d85407208510028135030b00110f5035031149024005403c40081c0d082c0780904611240c031002e00750703421000300d25800e280c028092018002d840f004d10508101007001c0d0b103803002100161082d40340950420052a44424040034011161030148400200013030300c403881d2282180c400600e2010b03015250307000c4100b540c00a06030340c2d000c50780b290340305400e0181e0705402d44210087c0441a040c002d0310b80000304800f0741c1c00304048060080c0601842052055403114060ba004482c070540b000780c5002c400032030910120310642c020316007265001c1d0601d0301c1d01c00a45001c10b81803450303802000702034100c98002c009c6961b2243c0541c4d007a0482c0d00c040c1d40c14150169103654454200c0c8640301030f01903940006002c540c000c1c0c8844054101040c003d5003c040152502c64580342480b030300012040c500400401e05510000545032030340d00949908800745c4800007044215a0050844063b0080c51603104030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 737164109 1250 737162859 737162879
    0x80c060a090e1501090f0b0301170304030b090a0506060f091b040f0308090a08071d040606120b06010906080702072102040608100f0216061a1c03021507020c0613 71
    0xc0f090750340c402c0004035905030000041881c913844d400b46e00310903281007092054a02c540304a03411180d0507800c00300044c07484102c0c0e90a40c040c1e42d00140040c01144100450746402084150740c80c1d10803010341c1e4071a40c03260108580c00c500150001d4110b400b120010b0101101a9030400340150f09004030750410703941d0a00c0414024a581086600d1400840c48045908042d02001c0240030f2110152890b64282441108440d10340449c0b0450902d0110101e03080c086030b5400708014000b88004551081c025040c614400750301a51507031b000a40d00c610000d92144036482e400d006405076400360411501e0081c0000081000000c140701400059580900581d5103101d120003c1c520340c4080e1140b00a000b102004a503d4050203441450040007840c09000a02c8010403189520400006941440114502184404001d042d8000010140010f0f000004541c1303514041d11030b50072100c041c0002c1003080b10101c410740701c03400541d0202c601e40f94140392040103030440780c5a062100380203942d034030781c110303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 737165359 1250 737164109 737164111
    0x90515100e1e03070f05031c0504030b040b2d061917070f0f080d03020a02031303050715020a02100f0221030f0705070210120f0e0606030c0307080c060a090e 69
    0x161941101081c070b80d503681018070142c1c0041200161104c106803921000c0b91700c0e0f1084c002501545a4031040c1d195a144c042c1c0180d4001c0d5800c034050240301d1400c2d10341000d0700d500079103d0003106980351001c4205111100300f01d598103103808491f420307503843c3ca2041c0005a80000301c0300030310345240880800c0c8855a0100d01c1c0d9080081d0b0002c1070001e2800c4084040304590750080b081e10390701448144428a0005581d80c05220145001a9100c0b04603404074150301548039200180c4030451b400000b48407000802c101078466883d0200c0204a9510041e6503400104500079040210321445101d01c9000780031a2003068110f005a030340115000c00002c1603103180c00c00690b002c0d8404010b0069101e400d40f40d11740d00403a10b0402603e8405150000742d0031a40103040d40013008050030301580b440e080d075000145c18804601c0c1c1400022070198901e80c0303800301156450700902c0fa440a40c0180d04d0001002e00480791942c014003103190550060000507800341114200f40081c0000000784640c101d1849 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 737166609 1250 737165359 737165389
    0x9060e060a03110f12160f03050c1e03060702280c05090907050603040803090d0c08070b0c0d0e0a0b070314010e0a320f01080c040f090b090d0801090515100e 69
    0x503218041d1990f085440131034951704500c1c0e48806447c028030009000041003000d582003110721900c10401403041015454596060540601804080c891156000545403001c0d540c14014180c1801013500070501c1000c20344400f40032001c031007c0802040c1441038946400c40c10203c1641e441035158000f041c0780b41d1050302c0c01c6451090020030070081100074000410401d801b858403551003601921400501d000b19071015001440490214900000110464404003141031080c8030300c207144280302c0d49615001c038082c0c0e59041040c0003e4506446882035030141e02000d80003418030790900c02c507031140a20081c05031403400d6448460605d81284200400c4031400c1c403d200d140700d120a2502c0c4015184084c004403101041c01c2c0040c4004240071400ca4039002d42620001600422042d4400140510303040203050501c4ca401805182d100100c0c481910015a4881e03138403e90f41d49901004651007100c000901000304108150903103401851400004241e150424000c107401002840240d9641c6207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 737167859 1250 737166609 737166613
    0x306050c0705070905061e0406030c090c020c060c0d26010314010e0d020618030906070602040e01080309010c1205091203090414041e150e01020409060e060a03110f12 73
    0x400e0030882c04104450103480078150074411030400344042001c01c1410f01c014084011800c941202c0c0791603a07840038004580049160070495079401641004100c40da8803070005010f51044000241085022201c85604030300003084c600702c0b050003c8440c490500d0440c0c94500e8804c407514a09007014040b0303070180d03020f82503129400e517035048400d0841c1e2003003190790080d03000700041e00099900450300c2c0390300000b02102c1ca0390404412032214210300c165652140d1080c030202d000f005001080e805032041da22000d50080c1143d880342ca0700c5669014080c2e04c2030010b42480340d04030004000780031305010100380c1d00b01a030410b41d0398000504c401a44e401c82c024142e00200d0800e005280c0b40c0501c0c0c00d06007001460064030304041c0c03a00c03c20140070055011701d022090010314108030714140401000d10700a00e04114010f85071203c10701030b6200c0d2280c00d4449043c120081951031205415901641b40140001d0356503145070303626200c020622242e03d920540c00d01c6104001d440b00d0642000b10030750840 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 737169109 1250 737167859 737167867
    0x70302101407090e060406050306090610120807170403061803020c0f06030f09030c06130309050108150f010905030a240e060a0911040e03070b07030213090e03040306050c 75
    0xc440c0211207080e45072000d940103500034800503a80041a44081e0754107091003401da40c1e035050103c2c014201551060740c051107001c040003141640464040c6c000c40c0b08403c4104415070719500051051000708020345510000c1107100000340310018034545e05090f01056030308060f0340351600b10407200502594004035610b80c81050400d64140101c082e05041101c409240c2580c04010448900004042d034100501d0740f001300319103d008000f5540507084000c1201d8a62400303249c0301d407602c15112000c9012800a1001044560143d0365030f81c428084410044d00d0543c461081182c900c5240d0b42c401d0602c40d0f400400b28a580b0705100303110001d401007094220000c1031101d0708440e0b0130030507284250039140c039060980141c40421050f030000c02902000c92040000d040440a0140c461901035020b468043c14068061002c406441140d004105800c035a03174440b070040e002d034402c0940103c041036003944148090702496000b207410b0607000044904154803941c1d0201154010390303659114070300105d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 737170359 1250 737169109 737169133
    0x7021005030a0b0d031d0301150b031003081909090c05030f1005090106050a08090714152203350c0304080706030b121203060f04090501060b21010302060a08041502070302 75
    0x100758001c3d051b10a800030000b101000c800e81081c0c110a0080f41c54102d4000302240f021070807500c100340919040403005644116170440403018804403030005000c603040030000100b0500f14418000210315984886e403460350b50340084280480700038140940c61044040c0407a00352038040030280a8402c030384030250340e84440400a415446c000380348005075400090207001d61200110b0010a10380e0070740b401110754a0300000419280591440c42c000b109003420206496400c1c02940000c4078017891001510321040c041c200414078038034824020190111003284802c025400c0201445203a0405590070240c80d91900c82c00e10429a00080000351601542d2909241502090310b0284000c4c00030220404081511886d03804000c116601c2038104c803d5035030842c1c03610380180f0040e56204008011068503880341e00029041a4031030509080046030907418944020921410b0700c1d00180694103010003d0001c490025004008071800e24410710008451402130001d040c1e40703886900a045400001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 737171609 1250 737170359 737170397
    0xf0a051c0f1a0d060b010507051002070308010e0907170c03011a121f0c030e1f0b03010c0203030a0b040605030d0e04050703020301060c0212010b06070605010e0c07021005030a0b0d03 80
    0x80300c80504016442c0307200540c0d4a514040c025268400c130041500401e61700180c0390b6006400c0040c6c81e03401024000c500503940b87d8000c1107040d02c01e031205440ca03621144074810103a421121441194444070041c0480c901000d54142c0f03c4121000300c075140401c8602090940729669001d0108200c0e000b04000c42d480c20680e0301c000708030310750000c001c00b98080c0c941c030b642e100348001c581c01150382d00c100000040344242c001d01e10701c3c04118216180f00d4030711000600d084204490401c080c0e458901d05808030b1606000741d80c981c4032540c3c01036085484103c02d042c014401c002c1d0140d4020340d90000058982c0b81404003441075441500c86801450070102400140c1700c0081038075007014410001403103501e4011500480e501e4050f5540b90500c4000e01d2002e0042c40e010404d10b038402c0c1c000c0b505800300222a008941079a10007039a004c2c01d512a03401e10301c03040c0607404000b58030102c000600e048540c4104007955002d02d581c0400300d8181d087c0804520680804907080e80011b90305a40c0342c0e00d286103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 737172859 1250 737171609 737171621
    0x7050a031b0b090303040915091a010210060812210123090714030712020f0c10050f0f0a06090c08060103181203020d0e0f0a0b07030605060f0a051c0f 66
    0x209081d80340f50500940019850340700e20b02407032100301d550364010464010f00a540d50007501d0070f050200080030705d40d101c2455181e20025010b006224260b1414501d1105004a80445020038001e05038043c04d0b51400c005a04000c21075100742c050201e440c1000303010055018020500c51130100812030300c0c4416800c1002030250b145000f1920002484101607210742d0415080034035001694694413070610888400c00c04550484116001081824000502c3c60040c805004280c085500580c41c140023141510812039001d44c0004440e00050b180712001458107900484011000998644403028601201d41150003880040d541d001002040e503018440c105017500c104110300500c05a0780d0754026000030302d9002c0003c00d034000c203004100c801c840d04050101c5004030255011030401c48034865540b83c6055058401c03d010001084e8024083c2c07103681d064600107842640f502240e00b88400440c1d001d400c03500102b100406c110815003890f80301d080c580806555010034903a40d0b8090076030503918 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 737174109 1250 737172859 737172869
    0x4020108070c0506040b06030f06070306061b0b15030307080a0c060506040e100213050a08030705061e0604150b0a0315060912020f0a0b1204301107050a031b 69
    0x203464001000310b040024805c0c0c4c01076014030301002d507036244030100c0c0c01c04d661102c81c0e01551084000b40803629406820004c1502ca142d581d880703820616241c0a2000800d059000d00f446881002003405801c0003108041244409011030703240c280e56a5035400154003c000580024002c154030008000181c0541604040115420b116518000998540b1160400420078685078000b804084030302c91011990000d1030300070941c841c1140c2d642040c50b120785c0800f01c100c419000e00000105503000c05140000019035880c1441c50035900d0ba030a0000a08010300504141c15190500140507074800b8024649550300b640e001c81e00c00350700401d00c2469199500008284a007010081c400d000f181c1c1918032400750116a28441000c6040114041032102c0c0c03c01031b0a000006410700307103049460103143c06a449852030b0f844001c0190000440215400601c04034031960002c44034800c1d1060030040c8c0243c2c40d80054440e042e47d210001b800d402314940c02101c14640c43c143d15007001c10904200c0d00146 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 737175359 1250 737174109 737174117
    0x203070f030b031903090503070603061409040f030c0c18020a200c09061915090e012103020111040f06030506030312130602090d030c0501391e080402010807 69
    0x140402d0002a240d250f140354100040304801d028100341481380103107000411004d000e650300c803a15200000c019200b54000c24080c0c03030010003142e005081140f440b0748641d81001a500b02100e4540d400c036122000d44506072545004403c0104440001a140a14607002ca400c0180c2e6030002c50b50141c0312413410340e000c0b00342c200240001a5028800305549410820403501000d243d500d590000303001a08064080c60014207080b8007141946490301003052548150300e504446039500c90103203907860024080c00303540c0b503030307010200010159110b4107400c0d2900c6170001003040142d0b0900314555400540c0521618146104100501e9030184141a04640c0681c061807911011701012888850090308440400c420355600788103000095040d10003500c0000c0010700c0c000042d00780180700340140c04040c2c0e101c0d40f9087c00241c410380c44040070350005e98000300005020740008102c45a4035150703401641801549610307880800084070003151600a56214040181040c2c0001024000e000785400140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 737176609 1250 737175359 737175371
    0x7120e0306072a030302120a0510270c0201020904050f0a0e0118030e0109090203070c122303060a26010e030a05040e040309090e0c13020a0806270a0203070f03 70
    0x60b4a01000075a001240c594a601c3c80c04680781c1203000f4070542d41c605200c010048144042504281c000302d000740c800710901c000a9440c1c0d820a003400c40440100e1906040c2d290360384880c0000c82d0085101101c0754000107081c00700d110302140030758030700302da881c410205000b080002c117100d60311801071102242002000b6080d060341e0307000c0c446540c01c0d4000e402c1c030443e060401e0085e171241c460b001c09008140400d5450b82482c82001d00864000c0201305c500340c410307102c400c600c0c903c501c0705400210042c0c0c0813241042d5031403101c1c070003075070002d81a103410021008002c10700c0030a0540d1280e4000038500114011044003401a0845a0341609120503400811200c002e243d881310903101079036003221000300c0940b074520302902c00010710b43c04458168100220554203000218402c107801c40700b51014140c809121038078038102d118840c400c40200f140314001c29418104a02c2520b2001d1264490482c01800b0b8201158840002c80d030b10070300981c000080095840c1e115500c0d41c4088602c1c01d09000c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 737177859 1250 737176609 737176637
    0x20703030c0b04082106040606110604150216030503040b0f060612070513180b010f1202180d0c14010f0c030e0f13150b040f0b0c010207120e030607 65
    0x3081c41c8298040c04441c00c02c000701d018405070804840c80c00f105c1e940900c14414085102d22070f16101285d43d54031441c600301d000546180078080c4402c1951524001d842e03141e840d82da0b40043c90903ea070100710240d81c03e100c03035900440b81e0240030741c80e14007070307200c0c5602c0c3d02c0e2600d40040c841100818604088409400b44041c0383c84120030790358580300c4481c103a4880d9641100460311801480851101c800a58100080220244810f0103022030320308401d01004000000544004003220000c8002600c040501002e44c08940c2c09032071541804104420308600c5240000d00701d000c283c0040d6410818410304012108901c028602c0601c0e0a0030500c0300c5a5516101070445007405101400b0b1000c1800054019070318082d06c0c944081c0d00a20307000c1c40f5584450000300500440b014030038003811040022410280540030740342101c00032004028401d0034081081c009130008264940150740922180c000100000080501c0d00c8007a502c15080440010406150000103000f80080c08034084007114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 737179109 1250 737177859 737177867
    0x3090f0501230114150c010e150105100e06090121020a2006010605090108040f0203160602010b0613090e0a1401090c090219110a1b24090527042102070303 68
    0x40524844100c00c6e80ba201440c0c50103002d01103100b08290607000d0500c00308040e0000d014458140d03602603503840407200c9450303400d886400c00908800d5201505001d00b0445600c140b629180581c3c0c2c2ca0f0004805c01c2601c240b10007641c100078844004104400d5008074002c0c00c0300842180d804081c4000c1500e9490100090a507100d04290726040003090000107003844001c90350b683c81a90301500300e45143c0c0c2c0c00b200d1a1441100c1e401904015420043c0281d0585482820b1300c030399040c002c03400d420035072800d1303582001041502481c41da90b00a010115021480120340300c4100c451840002c00c0a003503034948096140b03010f4005280c046d1051050a1a40c01d02002200550520341010f036858109068000e19000c034200000b045810042400d0b00c0d6151117070701c26801c0745c0c41d00011074409003000700411003204940300d1007800524091410441860842988901c2c0544003030780e40e20040181c000540d1013941280c0c10344007200305070b001214120a40600d000c8260542c409009032508590f4020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 737180359 1250 737179109 737179129
    0x12300a0b18060f061204120e12070e0a1107030207080607080103080d0e010e01090323070308160909020a0f0e010810140424060e03011b03090f0501230114 68
    0x18003d520101441c0840c2d1101d20851700310302c650442104080c9030520340a0700d1320b80200b07880e10001c0d0390b00d107818802e8203110351461000340c204006801c07928100703030b0405451b0b00001c16004200d40c484080d40f203400d0407040202951806039002d41440317402c0450701450b000010300200c041001c40c00040001c00c0b421070648130300e03998000780800c040303c425803450301400c008286210154a044002000c140e0842c10356194441101828904181c1c00c7c80d881000340200c400c003a010031840400111000d9440940603280340860401c404003d0701e4100b81c80880c0c000300712440c08145040c2c035034103059401c6034800070814000d20b8500c92501c6c080340e8440c03d02145114800e60f0b2804e8000e07031070340d540d503079002a0066401c2249880c0c080810200c0118020305c9031050320085040c90307800741000d007018001c400904016082104600302040011030050140040c10750700080141c4801001403001e002d102c15444170f070412481c002e0f0103440c2c0014207042c181c0c0500b07116100d20545141a4541607150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 737181609 1250 737180359 737180371
    0x130605010e0f0402010c050a05160806180a030503040c08070f060e09012102010e0612011d3d030c1406073c0b04120305040512300a0b18 60
    0x5035020304407d24100e4900104403d005043c1d000f407140c41501301c0d0b82c081010f02103070010342c00c1311035a464100b180c81c0f009901c04903040080d00441ea4000209010700019508036126010035003000d5a2401e5007402c100340381e004480c0446d440c100c101714281d071005000301280b404441c03200c0e071945004410041c030010401503014100c0400788050940e070050000039440c2c500071b80655902c02030581c21140c0f101c0c090180c01821640d24550220170305400c3e4901e0710a841c0c8071055107105039034070201c4001d48400014401c0304210350320b00d0110106000c11040c000c510503100c1c2104a8200b0810b400480d42060015029a505008200110300350240c88006814040b840812a1004890b00a0102010f200e0801c4501106d04840c0402030029000c5100702e0240482241ea00c0e030800c001c8003604d000352405007065000c030070a801205110001003510402112141d950020b090481c01c104691914196100c46540c4041140390400ca01614684150485a451580e0104480d40d10540320140c05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 737182859 1250 737181609 737181617
    0xc120e010e150906070c030b090a0807081b030d06030309050d050318010e120a06050105041107230d0e0a0605030108030a03110403020402030a020919120b040f0b130605010e0f040201 80
    0x12403682c0c980c4080490740318180203003c10780d9844281c00c0060768140c2c203202c100c40d0300801074001880c216021130000095644295070b00d140003000d4070303425107903008900d625415000d00300707483c0482481040100b1000040c900081034072441d5080140454003a0b41c403950040c0c00c44144130001440120407142e00d00010840c908104204000407140800710210040e041511280c0580c5009000102c4000e420710030041030105a881d5000e003c2900c2c0301c0140c041d81908244005c1c000101c00c3c41e94004080141000e03080c0810800b4240341c0761134104851003000c55680c0c9819041c60400da00260050300a50030101d180d0352400403001d980303100d0141c448041542d00c0c4040700d5000484403c5800440c0c005000b0754403402c0a4507000000e502c03c0580390302c02c0500e017140700851042103108008492184590f8007a050701a11062188100180b045442c4d21180011000007000000b60f54081d6090941f15030300c001c8140380070340c110b40040c2c1151401c45007140400a4480011501d61351195081ca4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 737184109 1250 737182859 737182879
    0x11214030406200109020d0503070b07030606050a030f14150f0301051021170306030c0d030206130206120f0702190203071502150c03070909020c030d2304030c120e010e 74
    0xb0401c4c01045030513030007944000484c1c2c0f00814010000081c1c00b595000301000002500e6542d0180c084030300ba4414440800e40a00c913007410741d4000d505c080d0039065180030124404d202040101055901192003444803608101d807180c4d18208691490301d0380310180e00800190416900504513048103204205110f0f1070b81900e2074001104080c1050390030ba000d0710501c170703c400c0915841203c4d00125080750186c402c02e000240140b40c501011074ae96501a00a80001e13203c040700040d041240c080c2c1640c00c240704201201082d02101c201c8c0f44115003070003441c545802d1044000f03052030f0030440301107107884d028102100580d03004107106e0119441c45050165540c5060b03402d9003405001421f407500a0400000c001030b03556003100441c0b0903001d99070307005110380e00c0d07031809412070207524442983c684c403d00480309245040c0e0702c000924841c10300492105115003110365882103086404400080301c2200520070040c000300c3c0f14150f140a801d0807031590484800007030048a201d00e1492203903000345 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 737185359 1250 737184109 737184167
    0x160618090b0105280f0f1e09180207020f01050304211101020a02060f07020f0709020a0e0901140405100e0415020409060f031205031012020a0905011214030406 70
    0x20403a03440050404200d82c42402e4405500300c421142900c90380481d00c44c2c1070380b85c05184124100010250b49840d00c00314128003c02224910000c15840d0040c003d0310180400c1c510100780000381d5841241201680d04d1940780305214003d03c3c02d02c441814400113006000008951040c00c4614240c5c04404c1110382050080480f4607c01c0904040e119500c0003414001666010918a1003060300c000650305035100c0c9401240d4640d83d100c1408841e822030312080c032544100b9001032480c08006e260069480001c14009200131100782e00005d40b90603444214041d9007820b01441d6032140001003c0d40049107012080012494001d000901c0311030b010121510010140d4192000f502011004106407030700c070116440310141d507000a642c141917100074001807902c250100c0388100c5500f007291001600c0c000050440385c40c10041242d0104101c20041100032480c0301e0a0700030708107000100d00800260030a030032100d850700591035182d04100802c0c070419400860030004080400f0b1810066070500b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 737186609 1250 737185359 737185367
    0x15030b040f09060c020d0e010c1a010e1510050306090403090b37020a15060305010513030f030506011d0310020c0123010f030b04051e160618090b01 65
    0x59055621034a40a84851004115403001000c9882110300300448480b120080c0c0e560340c120200340c0700080c0180a41c0170a03500c40ea5545803940d21901c00d40845440001088100400907080221011855801c0100c0b041425030200000c000650710450380c170041110090152000601e400d019802072408601010302c41c2e9040070040c644030a480307459140b03205644e8030a03c14807000151585100201c080348071055072920840d03969a40003481541c00c6a500c2c1c407140c2e9400440844c2c03181c0e407001b0000210340d080c040c0521541422000c850a00c01500e3b0260861440001c0c01c0b0406103894200403ca90f00305202d40081c88405181c144224003c2001030f00d4440d4035500004070f1800403070349034030002c4150400601102d07007000303002064281c0e01c040d2403011801d00c00c00d005010440810030210310a41601d540190081040e10b0710040c0803041d2140e030001c8895174107a143d00954a100c038030084400680041d00c61483e0045203015000d110230182c0c003842c06150284c41d5180c1c80c1058503802 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 737187859 1250 737186609 737186621
    0x1011030f0307050c1e0d03020c0c0f130c0e1002010e070e0603010204031704210c141c2a05090604020c07051e1c020913020109050319120203030601091503 68
    0x13801c0b03e8803d05c0d800750750300701c0d001240100401446407004e0140707224044d00a840d0780b09043c10081c4941c090f83c004204600d10f9814101c0c2d082424003400114800542c025284540c0301a00c40c1c49541360303503506110107a902c140d070000859140c1080c80c80b0000002c41e00304e084404506405e0420748401002900901c5140d0009101d401383d00e03000d090041001010348212142011611a4104a440d409920f4400b42c0c40080401989020602c0020f1a4401500c005600070382001003648402151030b00c0c000809006540407019600048a044170201c061008000802d42072005a8900404a8080c0c000946654071aa1b000300c1d50001704a0100180001441c00401a625801c0c0301e203040c60400e2800c4103502c0c01110043c680d240c040405150510030a80d019100401030764920003480307480d012000c0700728100415220300003200d58003008101145010160469000341c1e072460603030340b85020110110195082482044400e80e0002c1007401242ca03100c1c209210408840011401002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 737189109 1250 737187859 737187877
    0x7111306031505100803031914040312050c16080c0f0d2a030504060e190b0a0206100602070317160309030201170f0a020a020a05030f091011030f030705 67
    0x8584200081440b001c1402c10b00141d415582c10030994075040c0ea003400c00542c0f4028084164000c1010616180004c13001e43d054980e1030038006280030b03075240980729585040e101600001d10302e03485e450011040344520340d00150200d00d19840c058084406152640d41c0000140942d2408284c05651500c02e20180c0400c680c1102921012004c0c504c002c1e00410100c5a410b40380d0300448440d81e0b00715000c401c5840c1060b0503442d800e00b46441c00c00120b6504202122254210340001c1004a803084140f00706006000100c45c2c0c81d4460081c1c020003460000c0003000e9803404a2011400c00203c0d40104041c015070b900440380440c104003040c1c2c80411881100c3c109040e40d446411054140750307016000c0020750b8401d80ea581d0820714215103d0003202c205507441042008041d022030801441c590041801886038010b41d15202e0007a01c8050850b04151a681d0030342c60006032241203841c0c51140700001c0035003070070b01c48441d00820004580d24002c03044070211a400c0080070540a90144003a5000c4c12 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 737190359 1250 737189109 737189111
    0x11040c0c0b060111010f0f1d03210c07060f060612060e0105060708041205030a2622060213030605100b030c281106060a031e0804030209100326071113 66
    0x8000f080c00d4801448a22008e22003821060190400c00001100700c0381d1a04040084203410308070074012482603070f0081d0096804010410003c0001030041c081c80e2a00c600d02c4400058079894494007502d064181034112009900d0020140005c8030020706150565205548203500d41d400c7d807400d00c3c00e5104c0c68000c9107040440ca0480340821200000074503000c2034035070307030305207a00c0c45801700150400c1403146092899451000064202000f00f816900c1000550181c15860003d511201d00300d0303201911407244920306c15024028400c590084a421005d4140641d0440f03140500c1140b00c1d01002d0300301703100e41328000340b04000b442031070724140c007aa10501240c18052003102030161090701c04081e01022030040d0000282245401c4d4a040d0850750002d42c003281c08070700002c000c0c02d0449455011201c0b0f410601012003da1102c41401c2d209106509000448905500703002d100c0c0609601d4603a01554080f981c89600c2031188155600d43e54880c0083d00c2c03210050000070788030b1b120441401c02035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 737191609 1250 737190359 737190371
    0x41e090204200c120403030c0b0c0d0629040f090b030312073603060f0f0e0313050f060706020d0e1b090c040302100809011811040c0c0b060111010f 65
    0x110500b20080c241083c028046a034864985081000d0900941c170010707020554072034a02c008281900000e0368000030905100c0d15049026154400329415030300851480d03000c070328030501034140f0184140003d11601c0030003400d040ca441104240414039008034041c0310b440d0040000c41d62030420941d044c240e03d444c0781c0c01d5103141c0900010040a02e50380d10107244441c0c1109051480701c502342620619030b00200e800025802c54890300054410750307085d800e28070303078035510803000540c10310a00905000f05006141c0c0c0f03182e4035414024460203034004c40d203d10101a80c407045660f400044803002c691100002d601d600c1004022402401212000b00060040007400188880d0b68424a10b80240c12210150240c60b021451100340c062400b00070741000d000500e000c5043d02444030558085182c034000300362007074090403100450900c1e110484900c0c641101202c00341c6403501611440c55210b1074801d0810b051a103078851001009442c1d24180700302034078020203029003904425082c141d950818058 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 737192859 1250 737191609 737191661
    0x81e03120f0a05131106090102030c01090c0503060901050105010f0c0303021219110702030a0f0c12030305070908010b0d02040e010f020309152d06013b041e090204 72
    0x3040760480c1c1004040386031000003040e005580d40c1c0e10042c90340100440403204154130500400358400000c090540c0301c140080940c5920034040c001c2c05a00c50100605614038100a1500d041c2c1c02030003030007123641000010700169034000080c000c1c0140c076240c00e8600c3c0d906070070181c000f8840c4c0c0070500b03440302c881801c1000460071489981e082c03000111080120800e0310344150041d024908000703500d40c00c48090b01002c1503031500f10a1a1320700600c15207800d15581c0d0b0040c9000c42c3c44000c110301294484c0204226036400040150041034900024400e0342c0300c400004510001034500244120344d42d1000d500d035540258410754407030522141c00c40d601d00f880310030183da03280302d0f0040849005801001503940c54191803e0446180c01a540c000e500a45150034404a4401041e0504100400c0c10030814841003480038243c5100050034142c2e480c0d0090b021a80c0751110504041c00340742012458a5405618100e411030380d44003800028480f50b2510024001d404031589502c2107001c08400848 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 737194109 1250 737192859 737192881
    0x19031a09070603060b12091e0a0c0f0509040609030e0a08010b0f03010b06040b0c0a1e02030d020c030307080f1b100609090b0408091306230604081e0312 67
    0x4020809803044400441d941c100c11425100a4042d03001143e205110b481c01640307041c0764040d00105542c0c15160509911180c00303880404400e907103600c96101484c142d0901490090440103400300c0150101014100000b16059050140c0000e00e22507036020007006140c4903c0c942c074509400108032001e81d980e035500303840c06440c82e1480790748103c604c3d100e03a460310301c0c05115a0503100e038040d01003414a4680f0f15203a40c20f4003c40352260312401040710030f00c0001e244e002c141c04001d0800300400102080c5005041c034100c1d04064a105560252903119074650f00042520200e540c4002074a684070b08403030100ca654001d00706441c8241e04070400d114440d030030105100010000a5030200701c00c60342c5955a0301680c240c1c1102804a40084001c43e0100e1a600004c205940380030740041e407030420820080c03045800f00c0e48805c02054003560380440080c21081201490f07a8200c40c9913003410305144c899600d410f0580c1c0c901800c001c60070a80400b909041c000d490002240380100c0000780b92505c1c650ba = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 737195359 1250 737194109 737194111
    0xe090c0405030f010c0f110a020a030b040b0603060c0316090e10290a050d1d0102090114070b060405071701140109230108060a080105041401141519031a 67
    0x1e803182c0250049840b1155052003003520500b0b060351804070326100701d02e0030780d441d060708001c070071080c0617034038000c0c1c050382341c205190b8002e511840c011003851a16080c03680e003100000e00034600c250485003e10003001c40c000c040e01c0c0c00c00d100c445010405000500b0070703500c0c143c0550022040706035090400c164400008a00e0307003100c0d1130000103d0011101c07150300318294a20366105040000501510f00001d20034000307414201c1d10711000260344255040000c00ea102e68a180b511160340000e824140c44d60712100400b81494020741d2075090656541d2001c858240042c50705014668503000a01c42c58803071941c1100175400c1800b9141d90b540c64100915611201144290105402a60018000e40180c2c4041c0e4200e412944820810003400c004480c0900d02400050740644103c6000c225150207100b082d0081d032203510300c0806000800341141c00c2d902d81d00d5403409566400f10801c40301c0460481e0300c602e1000121440c1c1c007500d1051061540c2500343d0b800151500d0421041c1d10b10703c1d80c20320905 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 737196609 1250 737195359 737195369
    0x20301050109050a0e1c030f1d07090b030c0d08031308030403020d14040605221706040b010504020f04060302161e0309052b060b100807090e010e01050108070e090c04 73
    0xa04c904100400490f9072006e01d0781e02c010a4010800904010901c85c0e030044005055a44000c102c4162403180c0310014605001c60407095001010200a00b21a034480c01609890513005040d1401151000503c0c1c4098004050310040340000020011840d4801506c8220741c000c001c507403a4201410001d580d104480d846101007598034980c0404101c0d100c050f81c00302c4d62a0b90703440d4500748202903180d1541ca9400102c0c190600815000704201102e040281310320b03012040100454a018200898241c006a10131342c02148108180201c0c07038003420880e010b882a0b41070140e0303200b299050303000d0480104c600c081c000c8000341020511600704400c4c01e00b02c8070f000e5940d4102a50f224070400c000e180d5102460303201c0303103070894200d80038081c5140180c0b1f40d14002c02c4001003015109010071500f01034012060002107200c030802c000184c00010000152505110100c4c00d5030600c030078112510010300856051107140b000250a1b54840e80124a5445000d0026041070030018034400b0590058020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 737197859 1250 737196609 737196611
    0xd05130905040b0a18021002010c120504030522050a0b0715112b020a111e0c0108040f0204090308150d120e18010e01051f2703020301050109050a 64
    0x20300d8038858011140035a402c82c03080100703034640111480c000c2c641c0f40b04503006101403100300c602503542c501b80e10344c0070482c17600042404075031580c000348084840350a8078041032900c4140700c00f01c2da0140603a0100414900340440340804859000810810390303000540c0140c15200114200c04038101500c1928428000d80900000440b103c000b40e414441300d20126800c18421410200815640c84070309103201e0010980302040c04204030140e901203440d030400714252641d1100840b200b0822000c120205032481b11043e904240c05a4907081980170b1030f030411540001040602051103c40038101381c0c01482044140780310320b8043c192030f1086030101e11849152241c03040904125014164140d0702c10050502e409403150291004001403207001c1d0442415013103071500036010780040c3c2c0038200860000304a03600d44402c00c50800003c60351059004141c4511000070f581100700d08481d000104880c1200c034262200300c1010300c040b0303800a5070660034040006005001a48400c0c040d040c0894 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 737199109 1250 737197859 737197897
    0x1005060618060a121b080c03070c061d0f010f2301051513030f050c010c0809090a200d06081c030e01060e0717070306080a08070f050d05 60
    0x42120500a1255810010900300380c01c400030300d00031004080c0c012807400e141c040055691034020881c1c0e00409191030044450280000d03050f0012031043c0d01104a000366443c51409800040000c2030705040180032981b20070007015a45000100303144025054011074500e0040114014041c00c00c022428803403d00d40104015070070f890544e81d00840790541c10342400c6900e002e0034031010350048000c1c805400410f01c03001030300d4084200a000110701070302004611107100d0a14a0030304070070700b440c103044c01602110207002075111020f444070079000f125030060030790300c0c4605280503040010402c0c80c9442e2200417401d003130b82d09030007802d004a0000410040c0c20f03120036100369509405400b21420108003c100304d00d40b48680c101080000c0c1000c00400ca0a655000440701108161401c04c0030a01410100f60a100c1141401e80e01946618041c400946040d44440d02c03025040c80113440304900040c440103000310400003010190b800006c968038a00c40840080040c1c0007110403003042c0203026 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 737200359 1250 737199109 737199121
    0xc01110d0f05010e0903160c09050c040639140d0203040801060f0e0103020d0309032003010e2a040204151806020a03020c011218030f171e04051606021005 68
    0xc030003486a95144015850b00c50000c00024800705418011501b551402d840855003c0190007a80d001c1c6d1712f41050740e501c0c0ea05010380035041a1604002e20105040715804c00b0f001d40500c950306640c402c1c0c1c000b201e0b1599040c1e0802001f409555180c0720040e11680c0355112156600100500403101e0501c001c001d40364441d41403900109861003001c00e00c2d80c00100610152501d55018080f40c0d101c0d0404012050340c1c0d80d40c1184140094060403c054041c00303642403141400c0c0940f44070088641c014101c0d001c03c2a8484003050f01c8028001c0c10160784241e018095103484d4101c4010301050455230300d03540b48030640103000a01c05c15070310010f6805400d000540c90b00010700445401e625401a0411810040044855401404034400425110f06010145d080006d00c410b1084c3d000355107250040b008618080c003000b1030022071008948004080000c80810039030483c003128050381204000761190701306242381100007040c00031070349a003010000d403160300042c0c4564651010002401565660 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 737201609 1250 737200359 737200379
    0x60e030306121f02161403071104090b01231e01020f1203060618061207271505121024050d24060c050105060f010c080c01110d0f0501 59
    0x2028030070100b0841d80c103081444141c01404285e9240b10b41c49208000c0d40d219035424000c2c0c5880aa90b80d040020b8460a00c1100459860240c60030748042c41098000e603200002c42c00c1c14400c04e0750021070740e0080c0e00d0b00c48851021202000d402490950390440c240030100162580306202405885030f544155103003071000c503401807001c08480c6040d0a40c2d480d2024021940d00c50034180bd0344040001d43e102c00355903806c01802605000c0450485245003004010b44003603200c0c904544000418200c54690b00c405014000c281e44504205070109400520144c070580a01203000001d48501000c004000d007400e640b5070115220000801980e04010346241050340b01070f06000000f403c01c11148171041100e4020595140c0c1903160000c012070030051400030072100b0b801040004201d9040003081c0802409111b81012040340c000d5041c81d07172400041e120b03155803a401002e20501060500c00c5540a5200041201c1e200075080e03580c0241c504140c0052071f0002c07140c1c0d03c070b038a40000801c6d44403903 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 737202859 1250 737201609 737201623
    0x203120d02120105010e01270b0403050105160516060207080702150711040c08180a1211070504050c031f030b010e1806010f0612062412020a08160c060e03030612 71
    0x40e1156900140c0c000102000c0540441c0c03804110a40c12310b0000e00010900000d000441c01540000741c0b0341400d46102e5135210707000c40c4002c00c0103018007241241d40b45038426180c610760f00140069507000c542c90001c04038000c201020354450345040000d11072a000b00014901d40b032003000317000c038078010349000c002c1207034030400d5960000f840c034000184e144071006441c061545003501c00c85034211401d54a0101c01d05401e4484da00081e00c15058140052040004202038002117030141b0035858a21084c101c035000003000d80e0030201d1781d4600d011f03040020418103000b5580048406503290b031142c0011500c4401960740040001245c2000340d0000c0002c603009058604141c0d2003a0720514010044940048150207440000e595010000302103043c420445205004240d0581d404004142c01910b020704450780f01030314600402a410f80f03d6800360005030701c58200100d100c02c2c00102542120001c1502c003000300103074604481d070781112000001441c41058212400c4628205204404d911168 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 737204109 1250 737202859 737202887
    0x18040c0f18020c01090b040507060e040203042d05010203070804140615040c05160b0106180f050d1109040309080d0e060d020307020a020604031a15010507020d0203120d0212010501 79
    0x4207000709103844240d19002085090070403c00403640d08083c2d100c0100c0001e00303070780482c0c0303903408400104040c03074111004100307003c0100c1d030850461078980c035519803c4404110700319682456040c1c1031101040d85000e96801c0307411800854403450518405440c0c8031040d40c084d500c0644505801c1d00450001408901c9003007484001e041e540803100c00d20004d00401032108c070510005001c0000010b001c10356000200c1d004000380250341d450300314003601d07945091a01c0d20700107003808018000143c8585074403040342c00c103541882d0701c130119003804001c41d00c03241040b075480030300721060100341030348a50b0705801d4036008030036550001410300040d0390080d9545107458110005001d1640d250750070380d0103941c1c0301149005881c2c2d41961070b0b000820301d9210360004c58041425062071040c4120011045e503103c580c000c5010440840700700060b04070701400030001e208061080d81c250454405201002c80e0301202c00c856030b110f8242e1100000a900041c070402c44003a8440c000180755807080b6100ca0160f5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 737205359 1250 737204109 737204129
    0x170c1507110405190c0503040b0702070e0705070213180512030709060c06060806070215011401301b02010f090809090c1e04081b0307170c18040c0f 65
    0x5050784240405400010f00001d036220f0382d0b6002148240d11401100174030035182e45c44a0341e0780b030203280c50010b510b000b9015070300b15809401c061240072208005a0781004041c00d1040d103c0d1000c0c0b00285030f00d081503240d05102420310501180f00c44101c0d00e002c0303160303102e0010385024140e40c0690700c13914041101c981000408030481000b4039406810007112490007150045481078440103100c1c604041a00c0603c01030b40050060241c1c03003040030106025094880c4e840080d43e11410008045a00b00c903850b004c082e440618848200c2d0030442c001030600803130b60084c001000f641c5406100300f1284e0000c1405542410480e449190b094803881006070b40c8103032098249401e600610090a400408420001504001804800c11010015413103030101c03e17091a91141400342541c00c0200701400c5001c0440185a139200d15070b000314503801074550149113013181c0c0540d1071940f85004500c1e5210f40d04862062039565090b10130204c4203108034042c01c100410160f072103d00700686801441003403a10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 737206609 1250 737205359 737205383
    0x1b0c14012d0c0204060306090b0f0a1a010e0f040507050d0e150a0929011802031302010302180d050a0b06120316020105120a0c031d150907170c1507 65
    0x101e801803004a54450021308006006910b0b41d0300e0004840309804d0a0f5041c03c1c0c501c3c108000c0105510001d83d001c50060000c2c000210030031216111211004207542c14130224090140c543d48507459600f14180000f003084c4114145840003800c0c550002c184c41000c00d00301000c0b100c0b460300000e000c81280140421103400c030f680b104c0a0700014205005d00310740380444072140d100940c0e0700ba8844213040716405687da180c0d514006d0140c040041e04001150b1042c01402045410310340d0500070a511902802c0c09a551800d41e0079901034141c044406940c001040ca00440c01d02c480082c2910201c0d102d50040c022a17161001086030b40d0195100640540d4400c0020300115803030341d11440001441030600c00d0401101c2c5400481144049994100c0143c1d42c1035010401d5a15014015880c0341080154030980300d86c00e4003507110303050008407803004044da2021812441e8108044001000c40e2031903440c9074100369980c1e98440c2102d50303200c1d202c0d41d141c18800d00c0388540c10044980c1903a004d4606444 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 737207859 1250 737206609 737206697
    0x3030e0d0c12030507080301060e0a06090308090f0609060d022104020904030f050f0a11010609020f1e0d021605010b0a0e0103121202040f050a090b0603071b0c1401 72
    0x2c140e02404404002c1c0a01c410310000781e110001c1c5010308040e80301d485002c125031041c45890700c810303808681000081c40782040441c0c1068115100e4000030380781c0e400b5503140000032441c5885041c2402d60083c1002072502001c4034035a010301030000021001c03038408184c14900302a107290564010354088520000319000070b000c1c0210395414007007810018201114401c040246402141510f00418010440798120010a11901c0c0150100010850516071181d005a0040c0140d03482c085280341410500000c0c2012101542d208000715603041d55140d02203918609903503c0400100d89940c203104040c2e004c0c3c070b005402581518a402300b05d00c1160710f107440303008034070003000b0f010000e00c000c00000030007018141c0000d0000e00007120f80886214602014800d220402c1d0f40010b40c600e1510703914900700d83c0e8500487e604113044c5d02e410070302e151825505000b0f464902e040241041c114810025000b0803023607504241c07a40907250800e403510202c2d12110f0503071400d000c1d103030300c400f13a0901d03210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 737209109 1250 737207859 737207879
    0xc030d09031b03050619090c0609090516080106050a0201090b1806010905040f110409022d0105030903091210050109140c09010906110a02030106080f0c01110c090406090b07080103030e0d0c 83
    0x1440140300b2102041c80ca0b8980c80d05603040003240c101400003440010248048032f42c602449801c2104489017101050001c8802020a10180102410024005101c0400310320075003101800c150001e0b001202c80c1400b045030204400301203400902c600444000091040781e0340b00b514442c1c0d8001c0561400603000380e5520310521050044d05601641e950111000350322804149990f110350342c841c4405d00b40301e01700e0720800d03185120011030401c0b008008104220340301100340c60803404281c5075a032065440103440c50903c040700300c60041d4603240c280000b5001354035401244154484010f02c800a4070748031300d90a170030700c50f00440d14041a51504200203052140811071444c44480007aa180801d00d0350020f42500c001e41d225010031303440f040303d0030070000e024007084410074800d0810107102500340e01402e4a458910313007a40c3c40703080310400160901c28103800075031106a0244000000d45403a66010342003031020702055000450300000c2804d00d007000414a40e01981040044280c0781c030704078100c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 737210359 1250 737209109 737209141
    0x402100c0b090307210f1404080d0810120201050706020a030b060d0204052b14031603030e0c0a0608040311010906020c06071805060d021b0a050a030810031a090c030d09031b030506 79
    0x104440c1f081200041000b4207100f032040c0a0820b550f02031150503e892111a500000e40040030b110fa0003041d5180140c0c0c0100c101c40109a1054000d600d42d000594280c00a2510340342494000d1350006000809101a0b4024420764104035182c0d9070303400b03500d1007440398170a183e0310800307008bc0300e440401c01184194032074901000005080780d18142100c802070004d03441104040340442d440d40c400001d000e43c20300060700d100600f0380d850b9010510b001c000400410014001806001d58900d030f6422204d820b401181c0415048003080d0341e50070b00981080d540f250122549000102c10ba0512180c0c000d8038058041203074001058a401c01842c096400c00a512a149581081058904000301400e09016148002d4000d401400c0741081c00d0801410048005003c1589064000000d20020b040e0549040035100c5544149616507500c400c0d66142851912609034141b1644500183d0290f015149400356446800e400a840010b4071240c001d6045c81c4c000240390341c12030400220481c412014075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 737211609 1250 737210359 737210387
    0x1802070c08120d110306101d03032b0501081e030d050901020703120e07030609021215090106270c09090c0507020108070e03060402100c0b090307210f 66
    0x1a60039035500e000140c5809490808042c02907400304070740d2454600c0344101d86802051044032461131405000203420700004801ea0428014401c550340307600b00c80600350302e99901000d021203558646070740718240c02c10304408040120041c0c0c2024081d2250762801500e0480c1c500e100203011070b0031119465410440c10b00729064491006000d8505140181d006280c043e40e01d40000603683c502d5800c004200030303003424840c000c0f20b0030b200b001080908000b503039008403078101c240080c0260b4144002102d041c43c04a001072a4400d083c403150300b020324000745034050300305030008000f1140d544140c0b00341001015180b5400040040d045c071443c0304907070000100004189003070a11642c0b201d00c818104c40401a001000440109008045513008180150040c0040c1460000200310900096450303030010002802004040d110040f039501400d0340d1125250b011010003150718014804559a03001041c040d0345060f80c0744405200c0090100480502820a0769580c0d00702c1401d00c42654441008418 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 737212859 1250 737211609 737211623
    0x60a0e0a03090b210c070204110f070803250e010206100e010b030c0c0304030b22080712021911030c060301080d080613020703030c120e0c0d020a0305150f01060306180207 75
    0x4004d880003100b08200c0c420b541c003014150301c9480e01d005001c00c4540340c100000d00c047c010000d00d040170f4444d50607103c901ea84000c0455495030b038040305c005c00c041a8110901d0805408902644164010040c0c603040c0c442079080754403654402107210310090080c0700e0b11a0344008400144102e00359603006652091310043c80c14a488002001540303194040c0c5c1c0203884000381641840b640c064a40c1000307451030400c0b06412801003490300d50240038418880e0042c0340d900c4101c2050f0644c6d0083c0940000b11b0901485900c1100349802c00c4496000c1000380b13188640514035420181e4507104064905070f440b2900145000c1c0115202500c1d190360280042ea0300200c41c19175400780300b10754002412554880d66000c120f0030000080901000c1c49404940302440c101381c520b41d6040030000e6090f09408045803c200881270a0005c02e25118180c2c0025010b40151031810320201c543c84101402686101e40000850381d0b05c0034218100d4100340200394901061704040f0140803802d4000c1d0000c507001e204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 737214109 1250 737212859 737212897
    0x100b070219030b1806060307061d0f1e03011803020d0f111204090f200706060503030a030501061803050c0f061c0c0e0301050c030721020c060a0e0a03090b 68
    0x850380c026a02c1154490280036100210140d013100070702940da00648150000c01009045c11400303031440c80701c22a0f10a0300c1c0b10002c5068103130b0341c43e511250000440030702a4100d07005080d503a49040072803490098065130074807003031540300180c240390480c42c80c0c0c01d40c0c0030b0159405178820450b01c1c105c50b001928100a20745e900b18258220071b0103417181c0300c81e102494564940ca0a44c42c001620020880400c4145c582009900e510400c0080c80e0960700400015994071981c1d131600030000d15003504903035014800400d013205d0003501944454103842c0b00d500c80c0032070f815a010101d030007108140002401600044200215070030484510080c5090041401d800e0450a1481c403c02c4050b2405030783c059134440040e180c00c2e0760085000e00070500150700a00540c500302c812203480d440082c0c002c1c81000b0780204945884400c800c2c4071000964a100155940c1200000b0656103000699040c0c501c54505014000b2002000896050050785a02c2d071841035480e01044240300d400001b0529039040c0810 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 737215359 1250 737214109 737214113
    0x906100c060f0212010b070b1f0801060e010305070f030c060c03050c0105070c0b160203030f04021801180609020c0a03030c03020d06080a060c090e1303091203050c06100b07021903 79
    0x4002d00da0868011080140c5900711030030762407400181039001d480f56142c00c21a020208141e0408030754070002a801701600c607011400d01008942455001e03610f00d51810001144c2400404030080c1224085c40888128070b80310100308181071002d1100801e00445140200410f0340035811100e2801d00030709046007800701210103a800d654013211840c00007001009502d042003001807809400a800103c240188060340038040e60700e100280507411640c0b0034000107400c41d520240070440000c1404070f002c0103135030741e001030000c10380240380000d03003d5080640c0429005418420b1305c0d09801c0c0d9000030800f442c0b0541f0198000c11210140000301a000c05c40311800024900681e03000302600801030a29200600740901212121a1190304000d500b402c108503030444480b10300d4100c0000c00304040680c6091034151a211000ea0100c95400701c48a0420181074025000d07090307118002099807d255103c40303500195002d103015602011800307010340b5015003403510348028984608141941d60544036 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 737216609 1250 737215359 737215361
    0x10909110f19080f090304030611040503070806070e0f01050a0516060e100b040c0e100c1e1101080103170915030906040c060e06030c0c010b130213140906100c06 71
    0x20b03211105011aa41620b041d200350b210081550116100f01007190f2410070b64006500ca2103148030240c061a00c1d82142d00344501d80000703d0340100001022110010303590340c03450b529404100c5105012401d80d64081e40507090a44282011481c141d407168a4400019000d480c1500452415804558141203600008085114003e140c0354004000c1c01250f145a07003c0041d1420000d0540c080c5051050441d100d5420071599821845c0450708580c80c902d240000303c1d200d0704a0708011302000e0b40b00d520488040708030111012a140550b0b0054212091480150390340c00081c480203110040251030145e031050f40c14003601c5054801010410000340040000c41d840e0000d403104103864100310240030030024240440d0000301140e091502e80c2070b8001c3c000816a010041c428200c8503400661172560364000e41c84080e0b0b0450041024941c4002c0d884090025000750032105021030002c000403580c002c5403c0c4000380120700529096070b03680e424081c414281c240008420038071000303070201c200080c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 737217859 1250 737216609 737216617
    0x7031509060e0304050f0103090c0302010806061207030903090b0c121602030322080f0304060516021903150e0307020402071b090506100504080c120f0d080103051506010909110f 78
    0x60400941e204d50502081001c01d0300d44030015814545000c2e11038001540c0307015030004803502400c05611175942d13203001c42c5440c46910710540135483c01c003040044064059210749031441c06565a07405084c2c0b1169a110a0700c15844110025808207d6100d58070810070020107001054003040d4608450a60119283d40c01c400d10303010090110700f41580d29022b44c6941c480041581d0402000018000c4500c607860f40715a020b42020000000390000146011201b1001c0065000d04468018a0388174020034040f10f0700d020448030240303949444e00b2440c046001d05000c43c50030300085c41c64482590b0800c0300a6108103801c0740c0c020104030000750341112000c2540c2c0100100c06c0302040624006041102079010000310a090010a100c10310500a00160507041b41e0000c1d00c1114024400240881c44d10981c115000128401c02c3c1c1084040380d0f0180306241224410001c850250001d01aa0310310400d040f12158000340310f10704108903100c2c840d000a0070300705294200e24540341c240d401c0e06050303501c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 737219109 1250 737217859 737217881
    0x50319052a1c0804200901090b030607180e040c082506020715031d0303280903050f1c060b12090714040902011101021b0f0606030703150906 62
    0x808076601c000d4103509018220000444001e0020503000c0b419000d000355001030001381480c07060125901225540e208411485640203083c8891980e40d03e5150000e4000c48400a0180c06008040f810240c0210180b00c403400c2c1e01d0000050090030090a1110580004c1085d181861036100010b104007080c028803c06a18815000c10b460300c403a0785d070044041c0268840e00466101c004100310040e140c6500c6000c0012500d008120341e01d20b6104441c0c0d43c6072542c44c0e08034500000041c0151000d2411000007185981580000009901c035906400c4071074110014000c280100852080c5112403c0207025180070301c490300d15800d0401141c10b04075607113900203100380d140010300c40c909440c0001100c0d41c000c1150004081403410030645a101c2240711011500650b16058550116070180f0603010000c54900001c41d240c40d45001e0401c1c5107100c0c412412480d02600841d050010800705d85244511070140041c0317052869940c821036480088068502002c0c0c0d50402c1c240020f0180c0500b080d100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 737220359 1250 737219109 737219167
    0x1090504050f030a2c040c081009020c030a03050712110430031101060e0f18030a080c0a26010f050a050d1202010b1908060703050405031905 62
    0x480c0c035240880c904a01181800b400760b10900c105442c0b50791101c40e180782400a001242c0110004104444032002007000081d8080d0800031080c08080d80000035501c514280c04001c030090f03554001080c00c0b4400c040400311650010001c11040d60301035044641c210b00c181c9851100307107c64854000407a00558990000d41c4000182003064003409411484049101004071a919040c01d51481071f0702c0d00024005c00b400070380d40c40ca956a480a600a0004128401d2012450710b040d00240d060140110350b0b5940c40700c014401c4040314040002922a002c0842c0c5401c01141c6607024204010341141c50001c0401080c0c0b01c28850f14124003000c0007090300302001c2c000c2e1550409141100032001608014040d000340c40d4104a9a61340320895150560006441d03079640079821400ca025050804209070051a00310728004120345a08944007101c2e00c1c0d5050b40c01d01d440e005030482c10b50300255800380070340e441032040030b000024990b000da422040b1350901e245005024103201d481c100040c41c2c17440c003203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 737221609 1250 737220359 737220361
    0x90d170d1407094b060807110d0f02071502010e0f0303060a0b030a06030c080109052e0509030f0406020a050c010c0b370b030606062d0c1b100e0a050609010201090b010905 75
    0x164001d46e2440d0402502d040c4090030649003455950b890300201010010441a80c584500b424004e2191101400c951101260340c2d18448501030b02130510310281c54158441c07110000d0318a4800301c2aa8022100100160760725864120540101e030070180c03074504800c0e61448000005000c04c103020006003004000480c200900b4102141010740c40c0841c025000300d03040d0f045150074882e402030941c0d0820b6440018294039540003182c614017400a10348041c190008010072000e03000648031404034030890445001510078030046420300703085800241010080f602181c040d042e5030710f034011b291811640c007442c1d482c090081c1d898400604242800859035a04c8140a81d0601740042a403140c002d4516500e49103405c0f101c5e102e4548001c5481849894000700d13194072140e00011546c0440d4004203c9070709600a80040410603c44480d40c0e119001e089540d140d040c0c09134290007028100100340d00111482c01c3c0a04c6420b5101a0780305046543c0c9080100004179203038005400390000078000211 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 737222859 1250 737221609 737221619
    0x705070c05030604030e1f080109020706020c15091c0801051003090c090506030d020c0315060a030c270b0a090c0309020406030503030f010b0f090d170d1407094b 71
    0x26805903124400c6002115011088207d0f8000181c1d504681d05244016501c00b03c13818030000030f000740f112200850040c103107280150a06a0300041c00744c0043c1c0e090301d500f9460704c01c0902000a01440724004211990010040e510f0980e14901c4038013820f05020491b040c4035a02c91071480e4241d0040c0841c1551001032004d2414200710140001c000f41c00145070f24040803000036070f00e42910210400084a210001d0b400742c40f044ea4880045038802c1d040741d0b065440303012180a44010504049000c104072040100c483c82034029008281c001820314071616050070207003405048400d0a04041c10b03140d1004c10b006840e07a1207a580194000d40c0690b0f100d0400600c908280300e410382c80421120428419400c005400000703d5141000454100014516038034100108032110f02c08024030440129144000d00440c2d0492100c2c140d01c22021069036403030000c240c86481450003181080821541155843c2d02c402004a01803070307074130340042d20b280d08200007004650242415091043d00100d01000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 737224109 1250 737222859 737222869
    0x1b04060e13030e0f0102070905090a050a0503030405100501050d23070609050406080a0305040b2d18061905090622091a060a0320040602010e060f09060705070c05030604030e 76
    0x4020300102c900c42000351145000039036070a000d0048c0d284460f901c8010416490040000038074981d8441e00741d401c2010300d4146643c690300107d60964003400760020b848890034441c40b555043e144011f1002c12040003507110718a112951002e201205410071544407030200003007106500400f100e07a90140c48a042006000030359805a200d46c107142d0041e94034034006504441603509881d000141103444601941c0c1003501c802c11210000381c006054505042c02c00c84010003482d03030f00c1c500c60b2000b40111101050114074407840e0618541001e5540ba18580346104900600b42110020029400c0c0070000c00c000040c01d5100f01c000300d050740712400401203078400b409100d620a00c0303000c103050040482000300e00144120140c207010940c3e0780362540b519482c92300c040d007041c140407140151501c2e110040a8001c00603074030b0354076062041c4400030709000000100248900f04c4400a84229110b054056540340c20244040741e0407189250040b403291020880310b44500e010307a0301e04040800da8400c2c06 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 737225359 1250 737224109 737224127
    0x150415090f0b10361b0c15020d02030a050601020601060509040f14090102120901091a04020117010305010b0a050f03030430061409030c1c0302040909150b030d021b04060e1303 77
    0x84c401c600b0b0a070038140311640940801360300304090502204d81030561030614050200800c1310f00c0124408501e006150030b6503806903100c1d1a4464007000310345c590000590361703400240300351400100e04004580d000d05041c4c00c109000007242c44007050606807242c02011740384003101c1030680c90394081030401d102e12070010302941102141d00204988035080d1202080080a050742021824a43c808101164482d10104a4113010021280c0d40381d6103a141140c003a1680d82070161181d40e0b0650046101d1500b101e00111050700100114509460110a581e90700500e102040d0307503412040c00950304c030b09000c50010889200d090001a012040581051804400380c00c907442e41e4000e00c1012141800001c40b0362104c500794951900b08410001e003140a441203400108040703003009603040c20440c8001595a42819040d0284895000001855540c0302c4004680d00107034022106102e030010442c41103c070702c190141c00410fa50342c42d200f110000500c15240c0103007010995006a09269007c0104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 737226609 1250 737225359 737225459
    0x5030c0f150f040204021b102004061d01050717031012031d0f0a2c060a033f02070509090309011101020903150415090f0b10 55
    0x200700d450408031181e401428000304000d020f079500007a0300a6810060942c4000402c001d0b08480440b401c0c160500007406030040d01c28107248000d043c290300904000242d400780c03111941c0d660358208445181d54064802c98448a042c8202001824041180b100500c04030200e810502d59481c140300c114141c4040c09540035880c0581552170400000b584148030104840003841c150f890105001c2c0020a002506020300d58041d080c0030340001d82d00c0911450042003149139145950320b480801c1d000d401e250007119250b9001040e4042400021051032084000c06020150160b0300b0440111030b149035182c1d02207800e042104501c0c41c2a50359410000c030b00140c40152400c1900d41842104550303030780101401513052000340c0d8143d01040809505484039180003c04031a0020310b0000608080001941c0613070344c03404821000100e40f58a801500d0499600c50240c00c0e5450040d00d0382c2d0901e01018181c214101e00c840c00c005602c0f02030448404500081c0301d400b81c0380307506400044200468450786 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 737227859 1250 737226609 737226643
    0xa080109080c21070b1b03090a030315120222021206120a122d081605070f080702060702030d080618040b01171608030d0b01051c020f0705030c0f 64
    0x107000b10512007002d44404079031108a01c0c00d50345604083c1014200c0703070180018031000101c108044210006154200ca5010b624208a400c44c07010714556110014061801cdd070b05148000400142486900031300350100c0d9400c1150048000c070194402d9034040350440c0c411402c200d0600242d07203885054100294100e4008001b5203500b0754909000c082104200c5007809684041005860106a248a0143d4044030804200d01c003500000d0400d501c156440c05800c000f42001603400d81c0148112500103410145800815a49548080480d4441a41240c101c00203001184c01a03c08100c0c81e02e8100b8152140f801910300b0f24280007004020740c207034400e89441001400042101c0c0345259041d43d0030165208200413031170504519180c1c00d00400d0404154403d800100c80c0804005014800c9444505100e0700c0303c030100440d0300740202c410084205680040c0c150401000c0ea008098900c01c4540a608080036070322224115040508003c1468228002002d10007000b03003c800909509948 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 737229109 1250 737227859 737227903
    0x30d0c02060f0f0603070e1e060901030f24020c0109050606060702130b011e0e1305040818030c03030d090605181504020d2001020f1c05090a080109080c 67
    0x480c2d080908406840f4001c8407074440081480303601e041c45400040d06500340003400d1810038414460000080b82285aa0004010041001807030310307495040c1200d0b04101040b0954a0a03143c03004800c40b448403e190841540280b6013000c0c0c00c50001d400329810140001440c1c00c01401e00794200390008181c1d030310405040200c0c0e0700580d100b5102e0818010b00030f100141c003441040041c0c80110b490500324208003060b1070341c04456076001c07002c00c904a0068900004410007a04040166035050710010840d490a1040c1c51445005001103644204010211222600b210002c2419540817030a5a040d40d600c40030500f003070012600030304e0342050305150182c92610f1010f58043d103940050380b000d0340003020300010509560764504904410b0390009a8201480c15400c0e05504200392451100c0c0540105400020300030404183c2408090204010030040c2c1c03c000e81c00c46060780084d811507800800c9074030206001c20b003440350401603842124080d41d03030f07070032202c52518080040e001c650803251140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 737230215 1106 737229109 737229121
    0x40605041418010e090d0201051909050a0804060201240e040305030a06032405090d200a060e010506011106040c050d0609020d12090e0c03070f0212030108030d0c0206 73
    0x17001c951302c00010007401c0e4240c410898004940700346007440c81c0d00051103900454119445142900d0501c4600c1e42c8840050700950003410060395034818448040d50481e8842c170392010350030080404503140003560764407a00020001810080d010011998006141d005000a9035000d00d00800c0b1010401106081c10544c214100d8494203200c0401c0101c41e010540021900c52541c841e4464118000d000c18031011101000d411031060540c142e004c80c6583c420404640e581c8000442e041c24940c00050141600300d0592181da00650107100008248841200843d807055546645900315810200010070f9003140c06500310841924502c2080501e991085040b15683c9505aa01d5103858200310700500c00c81d080300b40c014081010a5034180034400e030f80c540000a1040380d950b1814030308040e00703e41080c1e000c40c50652010a4500b8480101e0240070151940da20040420b85008 = true := by decide +kernel

theorem cover : BRFrame.Cov 737050359 737230215 := by
  have h0 := BRFrame.cov_init 737050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 737050359 ≤ n) (h2 : n < 737230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
