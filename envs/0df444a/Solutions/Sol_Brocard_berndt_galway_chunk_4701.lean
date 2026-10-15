-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4701
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:27:38.272677+00:00
-- url     : https://prove2.me/submissions/1249dcb4-c031-43ec-9503-b00563071670

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 845323741 ≤ n < 845503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 845324991 1250 845323741 845323747
    0x60406090c1e050a0b091c0323041d130b04050a020607060f050c160204090809031e0609030a0507060207020f100210050a140117010e0d030203060319020102070605070215030c 77
    0x4020000c030243c15070010392224004202821140d55011680003d070412102c5c5886c10b030352107040549c1c3d0882d01c03034414803207403904a040c40344e10120540184140d82480490803403400104055505901c000c85592210216405407400031591440c17499600510070001c0790740e007501690210b6440e4008580c21550543c40f01000022100c0034024507600802e501d600500b8001600d40f455407103114848003901a6503610010310511000d202100c00c800000740446000c104034040a012103444204050124012038000c111003001c08022103400310946e030303240c40c01c000d40c0c1d4641000941c07100504a07070020016005816607101c5490342c00d13240407550060100d071008003110341c09680004000403a4607140400307480d01408040c1d40b0343d06542400310f540c040340201d4104540181601c10181c1c000380b0644150401d80e551603001035124040580503151550526803001c240482c5100c80240035820120083c045e0511401c090300c0c60500091602d01d406092024241c001c5d84240c440c000358842c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 845326241 1250 845324991 845324999
    0x151306030e10050402011d030304170703120f0c1101020307050706020c04060e040c030b06030a30180509060f0603010b0a031107080904020a03020c060f100f0602060406090c1e 77
    0x62007070030501d0301e201c4000d11507440c1c245d0000b0403e998070001180344e81c0ca030002e040a02d4404005035030140c528140c3c0c0c00341208024804982c4c8200d40c3c84121040b0304007074004001c1c288504034000ca12406520b58090030f0300b0365601d0707840a2018450303050444c402030000002264040084400816142c0c02900041e1040307024441566025000b0301010030b107500034000090001c0400d6001c0b0794004200d0140343c0c407031400090510315120009400301c1c500d0b0300550898500915a09110311642540105100350ba0310180d45160810b1a020506c103504c020422041c149050302c40e50202d001005140821350550000d07803590800c1e0441003141d1004038212a407103030544580e640100e05068001d007400402d40d103606403446001d000b50302039038002c11b00385602c50098050b51030100074a8203880541c5080094a1000d8004490154040440c45400a92a4503854a030f40660b900c0340d024007815580c9403981c03005000108400c542c40c140d01100002c01622031a4800c1440c0705542d80b4248803450 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 845327491 1250 845326241 845326243
    0xc09040f080d060618051c11090405062d15150406030b0f0a0312030b0a0b0406020a1109090714190b03180601060801030f060b1002030d06170c151306030e 68
    0x8881c020010742d50107003000c6c409075a0300b008015001c07140f01c051509010782450003e400e425200c0925400c607011405010812101146143c8540c03154000401900500d02c6c0424070100036081105c01e101e0408081011002d4101c2401261080038090040310000e10f010120340c0c2d4496409000060f5071000016800e29219000b4100558220748445085c0d04603160541140f110b1400841419a80c0da0104016251460030764004d00711120301c0b9031516035540000e07440303c01910301182c3c102c0d5000e0500c5800c0c5061603589016a00c000f0040c6201d80c1841c6e04034011041c10300c0038030f61110400030640b00340031a0107111400b60544244c1c8988034104101300200d085040545142c03a0b07008000144200342e481002141101c0e005685284003401c203060040040050500003500314140da001101c00640000041200c40c0e02e41c90108a19561490b40c0c01100302c40a0b00030040e0380103000076542901c0d001c4090260791100d9a00b452802030010b407a030701d840200b03500003070210303844104c24800c0e100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 845328741 1250 845327491 845327507
    0x130603110405010512090703020604090b0108180c060d0f02030a090b070c080a1d1302030106180e15010513063603080a2a02040516020c09040f080d0606 67
    0x3840150505040c14070001030024002e10107a2000e100c180030024025610800c4035400850f0080d1400b9a103540f5001c4003005030600308400c07804200d4020224050380400e4029090002684000d881010b14031402c12007140e201080088001b51a0146694100540e00c0250f00851500100103061401890300c6465004002c20403414810003402d40d1003c0752034403044480c80300042c0b41900d009030b20b510802071030486e0070803001d030003214000611542c229103900460685040ba2550100c540440e615104140300e0fa0040c0b09a5240394404500e91035005030383d002c00602c050604070708040706802c0889400d6215400b030b40010b2103482440d81801b0701034061118814403400d143c2c4140d104651000c20b00c2101d4400102206000140c18003100c5c03245640d0184010080e07085408108090351602c000030215206922603071030007021401d8010641800b010524050b0041c00c021150f07030041088400f402081a00e5002901641d0720020f001c4000515132500d00c0c400001c1c0303c0e8144a80104108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 845329991 1250 845328741 845328761
    0xa031b2102060c0705060103110a090c02070e0117031804060305030307020106140111060415110a020708010c020f0a1b05040504050a050f0706090b0304061113150504030b190908130603 81
    0x24004c101d0ba40103c1c102203840c2c1e0640e80c000d1100d5410301d1120010900f81a100c2d44480c00903031030b01400303818042d408138525045032195034040790f80c0d9072100c0300c8a08407058690401c1c6940c0c0108a41c0b00d2069041c441006501c0d4010701c0011a10340e40c0d1509800c5600c200da40c0e40050750741d0001800802c25054510341004402e18000c2d182000740043c4503620000508007a0220380010a040c003004442d4004508a0101204140d1030785094907000e503445941e4081c4c0d10b025400c01900d1745580c2d100007a01d03644250350300020300f0f20503040e0721440141c2c0c84021141541301200c80c40400c2e035840754007826000c0e51003500240901b03056800c01c642080107225880585410200f41005807075403000c10700c8259035007040d10b40d45d00c1d180c614029005040500c5201045035000c59414511465010f404007200e042c1200400351f08808603044034103100380e0000420038205000410340b945050254940d100c200f01d40006081005900c4d901d1540e001088010810300000c0030900c20a036060147c0818030b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 845331241 1250 845329991 845330011
    0xf0d14150408180310020d0603050601080303070f23030c0403020f030607020606041a030a0b041401050115031d12130603050420031e01140609090a031b210206 70
    0x5050550340d00031248503516803503d0010200701d0f840282d940500a1090050045000711342d15504a41840042c2070fa034401a180c074042c0398000600010048100c03445035802da03440b010f1039045d1070420b481403100c2c1075094084008000402a2081100d0015401180e0007468251214914070400ca0031114800010780240c1118062080e4503400040241e004481107078085a541907010202038860f00c0c0b120155072500c01e0081120900290020300c0d40164003542d1088a0110b461150034280c6200303206103007210300e29422410a00b8826072112066404c0c43c0d0861090b9525000c80c06e1400c4500e0914040f40d51002039802d02041341d014402c070040070141802e01062425450388800801c04000c1102080d25004c0000b0b0159010300c01d094010140e9076003842e002007081c0c0d030f260023090300502c081078080c41040070400310704d0403c0c490713441100c4e1103000b00040d4819030f8048039007000c00204c03110844e10a49041e4005007200f00d5003800c202d007021074011a5032007a10001e1401c0c0004e000c41c048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 845332491 1250 845331241 845331283
    0xb0f01021507050c120d0b060301030b070548010603110409050115061101201e090d06090b0a050609150102030405060304111f0215060f0d14 62
    0x1640c001c07411020514504003000d40d2665400400d40703040c4240005014540149440d02c5405810030010740100610301500300b2442e1183c50a001d0341d0b11080c0005020705000d100013400080c402d01c01480c0c82d5526405c0e09244011150741480f60503002142c4048034042005090450b000395006d641e002c100660007030001314550307165244c00010401030607004a40f5410400d013401025001308000303d1160028000c050b40d10300c40103052602040c005060b9500b000f042d074064990340d01040424001c00807140f4504080f9501c40c0101912030020200760302e8080c003c040d00d40d0b4980a180041d240511000f00703140005d03140c89151480020402c054440c030380001d0045580f03401c0316159002c1c0800c89da41041c86003074401030f80b450045134041644500e0000070002040f402c1100071010703108c2910150b20516140c0c0203210002e88503a0040b0050740401107014000765030700c1c1a2500311101404001c258070910b008101424604041682c052540e401e800c13103c07180811031440c000208600310741d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 845333741 1250 845332491 845332519
    0x411030304062015010303091e0303080106201c110f030913090203120438160b09010606080109020a050702010507030215160e010507020913151e0b 65
    0x412810080c00607002810440c0100d00301e03104210180c3e200007581071041346582d50f407800500c51310300c034010304c058000314402201a4062041c0c0d1036040c1e03640b580303800403660b00b0880b01702e400c214030144656054000d81c0351200d03100700a00040d00d1401e01441c111565546070790002d4514450300c0341d410380682c0446000342c0365a20100a90380c0f400030446541000034013a4200d50044c10030800d01135810b0141c145140c80b0020310702e000b00304403000480540c800d181a4408144401f01421410451243c10740003980f0004c06200140002d030480103004242d102107454072200008101c07201c03129695180b4003840000d030000825401004221000e500c1c1041c1290010301500079540c2c02418002c1c0440c4540815000303001107440c1424024070203401d4a8000403646901042d00ba42c100403814030645680c071544900b08440f9140d030050b004480c0c035110000d4418511190150681c0e901c6958104074a410496004220a19402840c1003c58489081000c8202e074038070300007648100796040070b0311 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 845334991 1250 845333741 845333747
    0x2031c0f14031b160302072c07261006030c0309112101060b030402040e0706020c040203102706050105041d090a05060c09090f01030f0b0a0216050102030108010f06120803070c0f0605041103030406 86
    0x260340b02010b0314041c00030140ae00d851407026501c2541d480c00c500794641c100301108034100740c80802c43e41c40765414021001110416402c40d9030744000a03060005c01c140e011f02da07080900c0c101d108400a600100080d0960180b03c41c2115031310b401c1410360440000a200c158178080c0124451000c00b40060000c8524160b4080e5640b1031042e181d038000c1d80c000c00052602081c11040200030301010a0b880c05c1c5c004503410110b0380c1441c400e450754606181102c041640e51086041c1e9003910240105111102030661881d229541c00401780d155610501c60800001201400010b000e0002c14025036207842c0c1c1a010441d03840710003842030401e02c26070001003002c151900003880c60070b5080174000d41c0c0e54803070b455008041e10500c07298034000c4415103410410003005500550490b0440c40080103400d658900c0309042c2d844034030034410b042180c0700c50000400c82e000010b58000000d030030f050344c0245440e9112240244a403500307444c030365502e008101c1404202c0d801e128000204a0196250a092136405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 845336241 1250 845334991 845335079
    0x2030f040b040804270608010509030a1809090803090c090c030403030902150c070905010f030210050a020c150307030c020c01021b01090302031c0f14031b16030207 72
    0xa000d070400d000100e010300015800b03d4010f005031002d503c3c1c2c006801c60011201c02d41161610800c50701c5d04000060310141841070364002e61a0030041d620b00f40d00301c3d608440c91409000c10640401e00c007040000d107829544248402d040c45440c0c2c0baa240d14004025505220030440c52900560750781c001c000d500384400d01165485549401d0000300080c05001040d201c00a40745106150b110014040701701e441c00060303100888885140a21075031303803110403440c0d51854a01c002500a15104480714099010f2800b40a11100500c11180d2503075000001035000c001d8800407610b0400300000340194030340e0500640d214040c4500040c0040290480001d698204460404080c2d040c48a140c100740da118032900c50003541c0050485014500001e0862602001440030201040d00c00e1048554280121040c004148140340c41a045646160ba4501040300c002c0444200400c10000c00301140f18164129060305e001c0c1c0d00a20546042c642e84050300c110180580140203580d5045002d055001549 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 845337491 1250 845336241 845336243
    0x31d07051201111b0f0a030809011805030a081b0a0e0423060f0d06050903042408150a0b0c06190212041202010b030f010b0a0b28020f070303180902030f04 68
    0x80041c042007004e0700d41c0c00d00f0401100d00c491405040341c2c0c007040c0755001701414081c80241e002002038045c030750a01d183d803041c0303d80010516081403001c5c1c036080f030094120a9001c0660f4418641d00d51801c5607101007540184600e030045485429000b10728141881040250400d2181209006001d1010b8124660001304128070542e0740e40c50b0800b50746c94420340c150040e50301aa080c085030800d10805900ca070058004e20000c1c00d6a05008140701d45603040d41c0800310304270b860343c0f42c8a131501d6622040300000c8905c22030700170034040070008180001c00e0041180d88043c6020340003034100030b407603800c9104420315804003080c01481302035000356201c4159600715510103504c102c1503d070894280e0140c070094090300d50500660420141c080410340080c43e402c1c50440e081031b285900c80310b12440307030700071146005450248200070608107170210f00c821120321142d00403a9031311409207003198507082c19078104030001018084000410941e1155450203400c500c4010760070362504408100c4480e200403c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 845338741 1250 845337491 845337517
    0xa290a090305091e0f04140a0c140304030c0c05040e0309040b0411040e16140d05040c15051231060b0604060903150504020a05010f031d0705120111 65
    0x200d030800c05026804031a5180805060070541d62144000c00c901d81c0d038010041401459141031a40303061034036100f2a4458660320113a80c58a03154046414014944294203106000c401c240000c1040390b04030145109520a9440340320801461a240800c80c615500440c0940d040404c1120a420040281d51060b00103a034000f0b0f130f400003440042c0140000110580040100203000b10f070803a01c003203180d8890466031fa00d0f40d80c002e800308000c540010b400387c2d0305400c140e0705200702c4000c0c0400341c0005030018000e0240301c0b4015200c0c0c904901040c0419150300104100007907000814140080080d44051901210020350041082c81c01d4400c03503491000c00b40110700300c454030030414554841d2011820250420380c0382e42e100c0001901c00301c800e01040d60000c080c5940200c25107038038000c4034070a590190030760019518003001940c4006a4000340010705807100f4808480b4105092403240c0c0341c10744002009014613110a0000402d2012f40c14213159060510184405107084115100548204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 845339991 1250 845338741 845338751
    0x115050901051306090509030a1b261e0306030d0c0804091512050615043809040609030e0307141306080f01141f031e0b04050a290a 58
    0x1640c114004d10300b680004050078a040e0030b1000400c0c000000c2c240403005c944500c0e161160b4456500d180c0283d1010042c28154001202c240510441c6400400c1c0e0481000c11420500ca070380300803040c0200b41c03011824110011003000103516080101074010409802e06000f1407449480341c1d065403140d0300640d0501900c500b110b071031030b24410703001c04002d00211f40c2c01110304d040d914201d52030341c606440000029006a51003080c601d400e2089405501d1031201511080044020704988000702c048990b90540006014402d40e0b241c09460520441c8140fa000030309000714a40941407041c00b10086001e54000d18091202444a46d4400400c4000302c0d50401d8001008003e000035101c41c3e00086010300401003009070140054003e08226400d211440c096966801180f0b2004e40c903489030035403010444401000031130600000208400260110409030144907200c5280ba24802e0720100e8503503020300003d6003441808481c0030803202c3c002c4030042540404030704043c0706080c040c10400c9542d540d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 845341241 1250 845339991 845340019
    0x3a0c05100e060c19060e012d0507091806090c08160305041502120708070f09030b100b072003010b09060603180601140a05060c03041214010518011505090105 69
    0x822059207205141c1e016011388482e9460f280003d000103000040440d820b20041c1c0b5200d58002c0614010281210002230895600c2490310740a0800903000c1001d0218640c00402e112003008039000300011110404141540f600e10184110b8150a04580410008406110000014001030b190740c0501e03180200d855220344c10040c00b42c01303407401c071091000d10004089050100313550072103210340156121140d00d65105d02c07054038205100c003001000a008440148002511404050f4004041c801c3d000e2010ba1502c503d4152580015000d68910980c45011001d1100540a01018040560080c4260f80c545001300342d040f4400390000c6d100d4280070001442d070380000400c21079400107000031541296514401c110069100c040114019140b1410100d04c5013081000c17260102c5071840194581446c00c075420171010311710002202e041d0410104145021001d00959019055010b01d03100c0807404c062031035003125071003040d4044051091a00b040b060b554400e000341140e2003a6901e0110f00c2c60 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 845342491 1250 845341241 845341243
    0x3041e050409031733030c090402060301180902100c0b07210f09120305011d04120f021c0305060405090109030e10032415090e01053a0c05100e060c 65
    0xe450307206403042a4910090714403a4103400d10170310040d01641a01c05580b1407a080c4103004030b0803030340a50440030800040212254100420096a10400f000645450551b000848041e00c81940d800007032025024641805056803006c1e0308a10a4100500100400041224036942071100c60820740d036200704040700f440c03c5400ca51303152580050503029119880a014005103003c0c007a0902100640c4221140741d0351203244580901d80001c1c0e00e605100c40071408454510160000c00c0460081d42e224081d04030000e04801c022000d651030202e201d14144040c48111040100710520780d0307050602143c0425004404032110f544151810b005e48101c611098002e05800c2010076000100400b41c0c5040141034030048090724500b440310303412065004001c58a812646c022070795580c4580004010324070304881c800018071512080c02450303044840500d200700002d000800d00201d46840002d0030460041c041201030b010803643c25905005d44000113180c1218145443d00803100090000c1c58010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 845343741 1250 845342491 845342521
    0x20901030f1b030e011104030221030706020d0b060f03060904020111120d0e0606010906050a020703060c0c12111b03030403020909030712030c210e03041e0504090317 73
    0x2041c4600340041ca88040c0a1400c6116001c450b000192500007204e0200e101030107143c081402524906d401d06003184c00b000b0b03070052000141ca04420f00e100b2259520f003000e101825100c5d028100068031181c1d00c19000095a0b189480c140c0b04050411107030303010410010960350444002d59000c040c940ea107100507140300781c0350f441c10312061081e03510354130040820400034030320b403400c030242031110030b84030001c841c1e5920054603401c1c0820340400341400000e101f94043d144151992044030b03401c0340c3e40d80301c802c12125251800ba000440d00c0c01104103010318420982c0300507000340752164500c0302241000748c0b00c05002c1912540304443c0400da0101d03070790070803d031390145800522010050804814040d680c0c0d0094104513001407403103c4410031a4006e201d1030040140ca038a03a036851800310312084035401c1003508e0401c2d04690311025421030441c1040580041d280d00c00e580c1c80011a91080116000326581c403040c85941080700020010794043c141411a90096802c0900ca4540d0700c81c89031b03501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 845344991 1250 845343741 845343761
    0x100e06100e030f0318030111090f09042108010344040305010e07210312050c130308090a1413151223010e0d12060513141f030602090103 60
    0xc070021404805c501c001103800351011604a00801c141301038941400c050b401103c10559004111340645201414890400ba40c89481007000e03000154501d01c8203045804a000a0400607424000510030400207405601042460301720f028180c1401d03105010540c4180c0f01074011510001c03240c048481004020b0741c0103143d215000340440c80c10580015501c841500c91000c50000d400000840c800740040c2d15215184c0550302c0c1c14110340103048403c05010060000071228400300051424180d041c502d50001d18803a90035150360b000c181041010360b13080340e000824140741c0b86a800400756140c2202003807101c40d068010940c00d401c401c00f608006030950040c3c6070051021501c80400145551095010946003031151429040b00405d9080f50741204401a440d0b0040c22000305641c011071850020400c120340101e00c0507219004141e20080c2041c400d0301c1d894440c2c004908c24101c20441c25402940070030015960707000549502904035941c400501000e6000034884510f900c2a00f25070525 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 845346241 1250 845344991 845344993
    0x6130c09030c09050702060711030d18020d06061433040b0313051c170a061d0a0c020105280b0a12140303010f0e060315090303100e06100e030f 63
    0xd43c0d41d9103441d400b070801182c1039401070084c01c00150b0b8940c0200b0412060b6445c010045080042c10070b1030000070508000c140e0040302a6200c0320f001030703440b50b02d62a08940b00f002c0c0820705a1800f80c6504d40d480741c03203040b540b0813000384540002c41d01808407580b8081855008070f9a105540b019080224480e0390403095682a00004020a8262480d0005901485801110300303110300144103a032082e040201010010340b02075401b42040d060340c02016040300300401d0010310702d6511010005081c4009105401350020f240422480540700d00c60882c07210b506000900c101d10b007a42c0c42c10b07031404006403403002a24228004002d04031135640314400124010707080f00c00a948900c03402d19840b1070040f00301d8a101100004180351080441900d0403a01c0446c000310110342400d0718540710f904d0043c82550035125030410150002e0b07250104c0f900078505140a1a500d05015070108000306184c1c0000e00b903410880140229134603100b10220307001640d446e00c240207007080c200203414188400c400b0101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 845347491 1250 845346241 845346263
    0x906070f0c0e0a0606210b130b12030310061808120712020106180207080c03041202030d0201020408060609040302012d060611030d021e070b041a06130c0903 69
    0x10003034003510401c01d846000b140001a07550740c12242040d92143d02404000400004a440e18600140495511402401c1022501004000216449001300030b0104203851300c0310700036841030401d948c0c05045403108802643c030310314200c50b6951444410b48a49020000c640110108105060f51807401410100095402511242880388030079000000c090360a00d600c003185030380c07160052203100211000004844010205080310500039001128107681c121010003080715410020700041c8040c281119180d456506030307006251500403607081c1d98003035a1041106010080d4000b44580e840001111120704580e103615080f0302400400400660040e0000611002001d02c041074030011300e54100100590f03591003000b1034144c0303400c045452007030b04200080e9441c0d501075001045200c8181035113034000b0482ca2012041607000c40300c19034581002409001c10404074a8901e0019803804806141034100040050001040c0d140e800000c1d50341c5003255180d080c060ba100d4001140c01400c8210 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 845348741 1250 845347491 845347493
    0x8061513061407110f01050f1b12070f080904060503010c03050403020607020a0b130c080d0507030e0d03052215030f05060607050312060d0f03030c02210904020906070f 74
    0x3505060040d2804a940070005882041d9400140c03070056070020703450008441268103008400e10b042d03464a0401c03000300b15188080d51070070b00400c81600d03100340c034141c04900d030b00ca02da00304000d046480b220070710204400c0d00814040600c601001c2d030081211076449500c940007600600c0643d00085c1c055081c07065944e00340d41c06030300a6101c2d13030280c5c0130b1718600e0307440d940100e0b11071a81080041425800b900414960040c600c142c055003441518007280d00c64503019114034024001141d0000034000050503410940c1c860312071006142d09640d20b150100c0c403030340c000c3c000d8059581c2c10950811928003042840305042d0081700240155805071642441d0b200d0001c01802c03c0c5104000700509100119201341040e00c01c44400780d401502450030141901020545a00d014014a230701c07002c608a00c00100340b86d80604c0e00c03168800d4034001030f200441d05000c0c0c00c00c030311140c948407104581d00f5a02c504440003030071503036542421103005a40d0004500040c0d1130340220f0030003610fa1000c00790300d0341c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 845349991 1250 845348741 845348767
    0x10b070309091104031b030c1806080102030709090b040f0515030114060315070e0307060c0b07020607140702030703080313200d0b04020f04090c05041d030901080615 73
    0x200686000c0e944044600303854440840640349807441103455944104020000329600440d1300482a00b03001d10815000d607a605e5503500320050390040f1404596512102c0c0c00d41e0420f100e9034008040310340c0294154905050041c041003420701c21126281e4803201d03c90b4403a903566100c40032030b040200b002c204505214641d40b0006001083e01400781d8a000f0a22400c1c041c0b0074141c0303100704401001031840911800e903103000010003401c0321080c40800c82e00340e81d00e41d80501c894000b8201c290f484044a5660f0306100301950030207080342003550080418890071560103024103610010306848141e84d00c20b03902c0440d10b4440c0c00e51000d46040000320030301c05858400640408400e00401e5500170381000c2d00d84502c0b045001c5000d160b0300c20102011000007603040026036030312a0004043c0c41d0181410004102030381c090103408caa942004040a000c245000c0c89a414410790070800782846400d00c0f08460364034440c64040300e040c001c071480091995680c034080d000020102c1c0d90850340318000c41c4454 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 845351241 1250 845349991 845349997
    0x31507050d062718080702060d0f0212060f1003020c030f1801021204120b19020313120203070201020622080a0c0507090902030309010305040302010b040213031e03120f020d05010b 79
    0x1425081c103c10002150940c0b40c0211400c01c806000040125941c0e60fa400c4002d0780880c400326040101440300d030600325444d10900721448401c0d0800f681d18480a0ba0030540c800000700000e02c070381060324603500c907512a100da0340e9011a0a040060760780120056440c03450141c0440c400c1305e1500010310201d0950748005036801d81c0001e8003221040c50412010203c5030185000da001151601d5440c0c2000c21010280160010102ca81c4507140c82c001e06540d0081e84d1080b2600304170b0301440c2d01448100424203540b500c00c00390f2072000d54141074a0703a00007519644054801031010744d010030038003000e06110211a00320342d400350034140e41c0d20040c60040c106080c0400c1c207441a000d02c40002442c10120b024180c007090303000780a58607004640d40158010040a40164110b40d6114403d01036610b80c1d20040002c00741d94800550401e00d50b14000040c603002074400030109440303004440c002500b20301c010400403a100000b140c0502078000313060080c011500b031802258180310000640703681140007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 845352491 1250 845351241 845351279
    0x1061403070807180207020a0f0902090909030c3307020703050c03030a091205011d030702030f0114040b1f0b0301060807020715031512061d070302031507050d06 71
    0x29034114507501d80e4543c1d01c4019901c580a880c00101650700f403002d01c40c0d4000c26407644000c0c0864000c2c2e03221b2a07042889419608800300e900d81c0051000200d1400d500e880b90701041c0480110300d00405010700300d494260b11400104194604d4204060882003043c0400410410300001c985528114030020b545035414231050b51107000d100c2c410b40841c1004811242c800134292a580390003440c2c2495000d40e8041c0200c107440f95581c4078206413603407900c01046070507403003050000c6888004600416060090308908600b040e0b15142180111080542c042544540c020122440c25035402c0c0d0401070004c07a000e0209241c1460600204082c41d655003c2c1d816134555903070b03015880e542c69030242da541d4260300482d000000e00130b41d014403a900c81d4100315100b07030003d501550202d645030b42d41e083c0d5130401182194000d484010359801d256211908182414580008000e8940713150003194540303a89200041012514800046410340208202c4940c20004e1104010072541e44038804500402c10349 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 845353741 1250 845352491 845352493
    0x12150504111207051f02010e0a120e030a0209150a180c0f020a020a0e0c0408031b0c2b14061303020606060c031903151203080c0a02061501050c01061403 67
    0x210110b1088000601c1c0044e030b1030180001d25200c40740710002090781c0024107420304642d21900813010812050105040e8503210300d0b0784109240054401400306001c0c5200603000b03601080c0c0d0740300541d036040302d000c0e00405603924074281c000056020424030000c1e83c008698202080c5940391000085501001000507107995005032450790a0040f80c85081e50030780070b544811350100620060b4400c6030240d421520b064003551070300b0b07a00c0c0030b401e0554201e0f05403c1d04042000350308403030a42091040000a40c0129601841104007000b02508004403a180400c0d01d0035041c82881017080340c4402e43c01030700d0520102c0300f580c40c2902c0302441607070945404034018003c0402141031400c20740280c0d02150070102c082c40c10544078000058241d90383d00005001c00d5100d50300440385075003112890015200c01c41c4a82d0552285040140203800040c018030800c01082022404690303010880580080c01e000321040d600e803242004984a0207a8600040b543d46850380000343c005100c01c108803002001d030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 845354991 1250 845353741 845353759
    0x40b1c0c0f0602060f1f06021501120f0b04021503040602090406050609030a0209090304120b070801060504030b06131d0c09060d03080c0f1201090e16030305041215050411 75
    0x40020340782009031040202580c08203020500c038800e5031a6240e400000d030071341e00140c4140b110104840c80025401320025802c80140903148202c0c01181e2800743c0664036556000840c2c40da90416111810103024080600304030100d0211354442046085414003a81d809840307041ca81841802036000d2b851052080345400c4001400d81000d0302603d8003100018050305c0500059000e00c6552500140f050b0201c0c0020400403070524143c00c01c1e5404c0714015881034101d864103c1c4042d24042060b04443e0520405100c100001815141d040b0b42c4108c041c2e8505143d15000c46249001d0035002c4080c00344141c11268030b507594070f0300080d85605000110f80180f510f81b07411050012040d0204000340005604c0d00008019aa82d0f10040c110045005182e628080e507290070312480f01c2c030a8019100558480c0c3c40711001000c02c1082042034950040940009413465070050801d06c2213204148904024800366001d11607810850340d00c01c18000300920182ca800d1603d405001c2c2105881481040c0d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 845356241 1250 845354991 845354999
    0xd060614030a0c090b0f090414120f0a030b01021006030605070306120c060c03050f030f0f1e01050f12030705030403030305010b040b25021f2c040b040b1c0c 69
    0x380aa0301c20340050f44581200c0c100301c140d0001c3c05152020641214040b08221407540780c500e0304c2031045000d00c1406004114200c6114180f82c140264018030020134822000100c0700c00701118105012424009420f1011000503805d0106041c00701d83e60500c0c20f0340000a22600b608114403ea8083e503082000c0c07070b100c903110000000f06100c00f82c428100480d0501c245400f40c0700c110700c00f85c082d080c04ca06091010380340d03600705ea00454040d80d1808030300041c4005a0036204800c0d401105015260020b100d080c4280e03248440c05118103440b850f4030b00381c0030003c1d0b100d80c040d030741207003000360162941c40f055400d003540d996010344412170019107402c00014000e606c2109a4013075589100c2c400303252511202e4a1600b4400729158013040310031800082005a45401a403090600075010300302d8200c0207217002600c143d403508100c104441d107010300c910420a8440046108a41c101c81c005860032121011800415141d60031503003040c101540304d156007942d41e9005e4045489104a030340c4554031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 845357491 1250 845356241 845356243
    0x1d030a050d02030703110f0a143109060803031008070501020a0f03030f05090a03080619180e01150305010b0102030f120613020d020d06210f08090d06061403 69
    0x4119025002500a02541034600e03101d0700110307003103411454081590100107459180507402001c501d4400030340016001000f40d000280c0f024181c9a02c289982483c04650300c80540d10066a500d6680c1040107862200c0d070860070020070040c040740c4100b0080c003619054020b5580e4030603a11600c9000007280b00041190000501c4010f030740040c1c4c00744c24580502e564020701c2c00d0040e4170403401e2544503a01810140d001c0e116031031007840b101d00101184c520368180a440301d030019003000d000d043c42944550707040d00aa2148000c680e07079a0150130211a40b059080000c091302c21040e5407035400d02c030603900c0b0b100034508000207403400b5900030003ca00c50200160b86d2449160380c0001019024082c00c0702a03005589056400503000d406201054140d1168200300e0340249030b00c1001641c08550f4074140b07501c0d44030b030328041c1c241029000341c2c1c0e4450341c061041c1115680300090031501050791400c1000003d00a46121490140c9082d00d20484d519080e4080c16040c001d580c0400ea42c19044089454 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 845358741 1250 845357491 845357497
    0xc090903040e13060c03060e18061914070c02030607170a0c1e02100b0a08250e010609060f020613080a03060f0b1308210d09080a031d03 60
    0x540000035441c1626020010388001001403241060006140042010500f580110314000c60182d82c0010503a041c0b00d4044611035000e400c2002c1d035030300220110114400081e01da43c0240d0606810741020b20b629940304060154002d0a503641400300d01446100c58005044140f071902c2201030ba0f005944010381102c410119000c200742b49121000403519061196000044002140c82c0c00c0103080c03607810046528003401010100141e21040b500b254101c5548900a01a90111014050039107405a89560303441c11084198441c0792401000b00000007125001000344a01034901c01150f80d80d800290803400ca502c10b400100c1c000300c2035148510302c040b810a100e0810303840c00710081d120076156001e881c3c010184d11001d05580301c1000c1039500507043c1100050036410310070383d80c40040c0f00080034645c4456009040c00d070b004080003900140314907180e81c030000840c1e4603a07441d00400c400c1240641410320001c2c1c01d03040e00081380181254590880718202070304800301003801c1c42e01c41c1c4c0203950b88 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 845359991 1250 845358741 845358751
    0x50105031513030509030f07090c05070201090e100806041104050f22020102030d0e01020408070f0f06080939150a1103130b0c0c0a030308060d051513050c09 69
    0x40501c0780042c040c0b08030204884440c034068501141001c00107400309251607800c58540722190300c848410020207540380919600000709182090a010480c1d001800c10641c07801a40707064000c84d80010000001c2030040c01c01024501708030307407482c149414001c1c41e480b002d0b250a4011814140000c02400404124a00481e030040d04070700905108504181c11a00100301241140020072018005c50040d00850841042c010300059031246007004081c50b0035069880340040c404001010001d1050801205080320310b0350401c10300310303a0340a035000d0420a000035049004600a008400301290b075903140015080c007100200410b54402003000380382290740350305c496112001c00640103020310403a0044000c0440804580c2040c08100100c1c1c2d010f0340706c2c0c010720741c8040c01154100c65001c04002c0403288030320603214600c0c0c50f402c513100202990745c0200108e0203129400b290b903007040000c00218003004580301040d00d050a05c2d406041824542c00710903035503481252601c0c1c2052400c4c08200d8018 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 845361241 1250 845359991 845360023
    0xa05120c18060313080a1d03060f0106050c0c10080604150e0a0e030d11120c04060519020c0a090501261c090806190608210f0f0706020d05010503 64
    0x703a12a0410003006600051641407441102500341000525040140c244100300e503c40c502c40026031802d10078800c40d400e0119100e40d01040a00c0100c00510071100d06540f070030f01d0210364510207610418600b08240c815a904440d03a03114440056601540c0c1034020312084400340032195511403201d0100d4018001c2d5a20a078100d404034600c44034036400070000803001e00a0304d0912904c10f000d81c00f11103041010703000e603650010304945a2032450030a02d40c041032440703216081a0603c40b00070102d0040051040900900126058140f402085030081d41c210041c0080c20300ca4440c87c00d440a82803c0c4214170255132401c45405200c1141c8a5a0641180400080c040000380707944112104800022040034800c02c14004181d940043c0002807007a20000c071445000040007800400325030740c0d5070100651350400740311400c140955918908a5004d417800c1643c4900144210304443d1140964500000c0c00004018041080c2074015010303108595004205580c0e8450501d41c0747c3c00012031600790303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 845362491 1250 845361241 845361277
    0x1f15030f020c060a0c0c020a030f1406100302150409050a06051003180809180c0909070804050303040b1f0306090c05010e0112050a0b04020714120c031206040e01020a05120c 76
    0x42c403e1a9800903605c1d80c0700d403820481ca00c0c5c0c2034000c03903503182c4182c00130360710281d1030329a48060100e508114502118a8401050246003c0fa01f0a0502d10382d0b010013407081c0e1a0051220101c5100e10944000d04180d4074100054149150300308000c103018810710740906020040301c50000d00038440d8510342000390341d2074a00c203000f1341c0e9182d1440c0d104840381039215010f0381b00650b00513800020035100b803840a1100340d4601c42c55080101e186c90080c401000c00092004000003d90b000c0150390b0466448900003c0c0c5880340c00341e5034111008150040c201c400040000011b10045400412002d40124a0441c1464503403004648014490806501181f05444402a540007687c0080c1d03008a8521001807446803035400101642c1c000303041566a40f008003081c0850450910000305203096041c034442c40c0c000c844101a480780100c0300d042c80140000400181c0c0d0f07441d40d8112100404880c40210354070a8101d10280440c2c10135042809418800c00003d800c212403e000c071800c0c2290810f010071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 845363741 1250 845362491 845362501
    0x506030c0a050d110a090e0109021e0705013c0c0905060c0f06010b0304140703030e010c0c0f060503040b0c0315090901020d0f1a04090b0106081f15030f020c06 70
    0x103096405a40e0341c00301d0564820801624101902c044e002c141880e5403106c0c0c84070301d0180381030070000d0180c10100102e0b01c1040010a14140d034140b050f081c0362070555041d21044e0340d0a00500410034000aa22301e0181d0041c20b030402c1802100c0f8a211601d092814071014044584c00c02c211002641c1200115601000901c81c515000019042d002d503500c08490080401c1e40c007c0d41402c40030303880349805802c08414041000072000c44804200f8418000b00318207031664600404841c1407290741e03810300420300c00440502014007101b1000c1e08414400032141592000c00800c2648201e03010f0f9402c508810114407a00503031411240030301844807480001030080400c0056403c0050310312840c0d0740d420052300044800e613001d50030785000c00200020b112081924880d0000c0d4a0403138541c0f06920740820480014034039880581500d6503840c1601c0741d9179414100000000741c00c052101400310800c0d00040350f030001038200c0300c0711819070340034801ca51908007400d042c0c1c01078403c511200e40000c00022 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 845364991 1250 845363741 845363747
    0x130e010507050a321c0e0d0f0e010e0f061303080d060f0821280f0f120b010201020403050a08180a080a0318050406080303010e0f01030c12020102030f12100506030c0a 73
    0x518810301022050100e944045e4400c1121985116040c058100c1c80c1c001d45000c1c2c2011ba42c000c848213a080c90301020b035006e8002031a070100b048100344103001000c52240b040c0c84881c10b4520075030284130540e1504e6280e00b842c41058000180003515503040c2940480c10300d100340c444c5001c6904c808010008040494005940444103c645c80e07c0014180424401020003051309454030300d265414000501040c03a0041c11085604010406e0001980c1c440780040d60060621030344240c0c00f28001200c0480350b0040340a071059500180141c4103540341c901c141300008004107040c01c1d5944010400424a82c10b009071003d280c858401c06400414503c2c0c04203000b0616000d480c032000034042070007600c8400243c01c8030a0340e08100015440800144408101c0c2d40305507401002e00c0750030040941c5150b40d0106480c416005025a4000741c4040c8030840e4000c105644410f05014201611007032000407050100d002212080e160000317a040006032410440216401404180146840d1003400c25040e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 845366241 1250 845364991 845364997
    0x7080703030b040209041407020d0f022e05070504090e0703110d02030114270304240504030b010e07020606090c190c0501050c0c0607140306130e010507050a32 70
    0xb190030a808008034911036179184101d454610040980700120b052904000340b03031150801c0084144100c0d80c85140120b60001209240c4116036054103580498010206017100c0c0c01c0c842c00400141407505100b05182c1090140c4281e0305014000c00484c070307801d2112540c0f5041803002600e00d104c1c070f9010307101508100340714008090019001140c0700c110b0401780010034a048426500c840c622420014120210365118003180c40818011810a0705080040400700d800c8498003c2c201d411503400b101c041d0050007585e000b907400071100d11403981e444008640e00380301100d0080c0140603c00001f42145401303090b0f00c1c041c00459442900308a0302c20140004908081c462100380900c080d0210300240702406041c1c8202c0e051006151100350008070f0343e00d801b101615440c00d2224001c03101100001e01020303a50311410480300041e2160b0500074010080000602d6030091394200000c000c05690000c00400e0030070707135950300c80000d034014030020300c00c4451032601e100b0382d41c1410f0a07581030b580b400406 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 845367491 1250 845366241 845366261
    0x5030118091a131a091e0d03020a091a07020405160c0b07050c0610080705090f070302180d0c0302010206010609030f060e010e0609010b090609070e040504080912010f0506060708070303 81
    0xa000300c19059403130304044d090420406a01d0a2904c0c0c041044110041c81014006003401d070001d419900c00318501504d03031041c0440714040550124444803104e1044181400804590a1203040c021400c0e4014016078060881a4051410003010035104010b185d0960f140701c0041e5030b40703441c6490966580b140c40e8800b5010340100300c0c0600071080548010301185004080e01c07008038440d4ac2c40c20b4101414a483c5502c4140b00c2c86020040003009400190b5043c0e0100541c034005980d4105d1980701c03401c140c0100360480d004018140300c041006107111108040e60b000341c01300c803126aa0740380201c450343c083c9d0000030079501c4803030f01020010f0302541100d8109070f4500008201d03448501c15491a04408503032012070b0740c1d1070f8814003031a418010b00360750f0000d07c1550741c21910324024801030700205104105030700031651500060103100524090b01c100c0400200034086080c41145011b01804451100c1c0107400d00d4103012440c0c0b032415070210348a05a02041442c10500b603a01c06800074088150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 845368741 1250 845367491 845367511
    0x1e0f1a1621021b1603020108130f38010524070803280b0a06110c0307080327030c0121090b0a0c030504020102060c0d021905030118091a 60
    0x4015421219540058243ca001060460450080310407042d86000051002507202100032031003840541d0f80074a0300c0798000445501c003c402d0550b80740007425101e00340000b50400bc210091203600509804803041282071200c0007041c9510003c640c034045400038420250b00194003d00411303c00d1405484100035182c616026050102684440a80e039008940c1f80d0306800500440500b0b0410001203c982128130b00010004101d0000100792240640e0140c9003e000b04c0c03910804100070100450354105901a00303031280c09940b0403110355280c208040071810007160001c0e0207e0000f09807403560b00d00000500800101e190400191001150f4142560003842d051400101c15016800b07004c40d664490502c440721131400c0600c100c112115901d01c401054207007800d0001603070b0b002440980000700070400c00e07074030516409140003d103c1c4088520340d19801079070a0014070742244c0654100c43d0b1b00d14001000800d13005a140894014010040c14141c00c4423441442181200c103413076215414035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 845369991 1250 845368741 845368787
    0x50f040c020c060a0c0317010303080103240f02040f0501051306031107050a0b062707261e0105060a080f13080304050703110f1c1e0f1a16 61
    0x1e0b0104602d13030b108030f503103a02113954541002c08041e40000e440391426034203800012103504560b00105180d1040c0b10251848000142c6c110b09039441d840540d80400750320404000802003804030b140650014416582801e0f016140001e01d135000b18119001202d05180496006d81450b0042e001840326884107000d1040501507580025001c1224201143c080d9078604518030b092010444040409080a414198044859014500d9030050700303401038100e0501c000d1003408100c0000381c84030480d0b5100689603c8000384281c840610141e0740c1d0707080707603229200501e80c0ca0b10140040d40c0f00d494000b000040d02c480004103450ac007409443d4001a108100001c180d000f500c0e10307030607a0016241501c0f940c00440342001002080a441c1200010950340c0c40441d80401c030001d51000392500c99410301800080042c000c11000d0042c074007480c2041942d50b07407691010305104c0115000d020b022141d074180c0040b03941d00c051000d400d69101e00e01303844003420f005200103c00c03155546100000030205000c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 845371241 1250 845369991 845370013
    0x80f0a020717031c06060f080601030f021303020f060910081f09020c06070323041403031009051e01050607171902120c15091507110d09050f040c02 65
    0x10000c201e00707031400095450341307100358070001010140e05420f01e146103484402c01601c0d403c407040d2209401d96082c0a80240d68100040e0050032070001850755840c40021031401800040100da801e8a00235603100049424040c180440c510400803002e92004484651510192290f032a06902001054003090103c0c1080b0303010748a80c1c500d40003801c80b1034010401100c1d00108101403580042d443c41c082c084428160070701c03d110074001d407090038010101400207090020f99000785002003528000c0360350341c2c03402c600748119181083c00348011150401007c151051002c0e041d580061044400f400420391030b01d010082c0b00c1d40034010071900d161603000c81d40e02d2070000d000070b8049141d1328400c0d6040100080d400034200b501c03100308441c041c0018442103002410010703050f00400714a0302581003948503504014a0507145c840001c0031001c4d143c040002865004c034030b49103a0303040f803401c69014540380403040d80c85800c1d60107500d4104181302d00400e201c0c60660400c120803030141c01580d80100c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 845372491 1250 845371241 845371259
    0x6140d080d110d14040c06200313050a140312160203010c020c031203040804290313170a0206071206031b030314121918060b04060f03080f0a0207 64
    0xa1045000c182400100301c03211000c034203000f101303007446085180d2240c515042d9207a6000c289107015500401c50700040c403840f15589540240d96031004102182e032a0104202300d03c00070003050144500a0901220000f8200301041301c2c254004d00040141509404d80b03814000c09800900e031040409002ca0030f4640540c4084c0708100c1451850350241030900d00341c0c2c060500c5d2041695000c040d02d03004100f0440407403201000d4034151600038040d0b0f0710b100d01c84640d000c1034500e000202c080e400070010901000b06a04100e840481d48206005480240e11049000c10340c0030301104403000d60415000107600e02d00c01c28940c4000c0441e0107001491a8591b10b64401c0c1c40c100b02422505e80038100001d20038503410864082c0c0350144480e03141d10b0610102042c426401000d0020b2406902e01e400b0b56030300d030590790010b0150344021469880410801c0c14100081c3c110340b10074500407480e040c000b190501c0030b8580c441c10b403508a200b140c5001869041d8100e698080f06003103086019000c004910414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 845373741 1250 845372491 845372501
    0x3090d0c0b0c0f0d0e0f09071124060609010c0201030c090f09020d0b0a0812071a0703020702040b090105030a110d120c11010c150518010c0504061206140d080d 70
    0x65010043c55880d808510551030500c04007094418004461070701e45413903036030314551b91060509130703402e04558a94071003c1d208004081000c1c519801080c5400701e0200d80080035181d90084110079000d82d48564041c0400c1c5e126040107180083c0da4101403001550213900640040c0030180f408008056458403595001d00f905e410151302c2c10740006120803055494095520525412600c20700c21a1030000955600c1d200c002c006000b4080116010060185841c0b00d02e40c03c030100001c0c0030aa25102d07500800951051804900c5286428011201405c040c41c5e0981aa0b50160041401462a4591309080107180c0410b541c02402c19514100196885000041449458a0350b4211038141e01d40322140c0b00180050604001e09135440c000881c0e10009d000214180075000081c0503201d03400100751440020161740400d40c00d01c0d40d07107030041e94054001c0080700d0196450300c90840811502c0020748030244030b10400f02020a110307000600c1c00a96600400740b250400906d0541c8200c2a2001c1d10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 845374991 1250 845373741 845373757
    0x70c06051b04121a06030705120111030a060806090106030503160809030f0a021e090103120e0901031407090b0a091d1605100816051e0d0c090f0803090d0c0b 69
    0x9104040c1c02c1081140c002c2004401c038141400d04d050702e40200401e80e60342661240b43d2140220480c10004248294880004201e10184050fa80e140840c2c582c4007a15040c460140284144030000341e0301c0006105d002c098a07404809140340040c082e41404c05171103411410703220804100310801c2d083e981000105603006000c809004200014010024004911051007102403200d40e0002c0d4140e4680c852141500e500c07228041080c4000642140c06802903124260003859035000801403040b09913241c050300160740120341415844440100c01d8030b00080c4415084220340c5030602452019801080d4030604032070080c00e03180c610014203890b259180075040c0078417403003070310a2102d400c007401c0c1c8400600700782c10854580d00303080e21b480250300c03080441441046170104000174805800e0902000e0f8500b000d001e84d0300d8454003c01000100100841080422848000020302d10032980109044079410000785003400580801d02c94078084100e801c640f01e185503040403d6691104020700500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 845376241 1250 845374991 845375009
    0x221040b030a06080f120307050f1c200a020606121c05030108070b09010e010e1c080d0501080d051603090e010801021e042610181703070c06051b04 65
    0x45413601c00d24900b025510004141150414100a009512000c00700c86d005070302c07444d01941c1d450b207480b4643e10074010203103400d900d501e8070050606106941d03004040034044841d10020581d00220000400e84035003a044009608004000b405e10b1502d02e51805480b001a400d981e05010800e05081112207000c07010008100c2c04001409000402c10480c4068a1240c2c1d10501e468150000608036002c501c0515042003414000d1740195122100411000302002c0440441e41b412880d02031840d0308076000c520710b05440c0c00b000140381c41300000c42c04546003241d01d0f09450110441d4400ca041011144141e007444404036001614400c0c0d01c14950081001c1000180ca820303c4c003850100300d1840c10403003200791005100520581e0082c2854803c0044c54000441c061182050b18034100340d1601103c0c03000030b2400c07003010700c104c0e4a0703681044541c0c031810780395902c100e403100b0000342804180c50300e50010b1803501c1d010380001e0156001c03a402007600070090308000c140300741c40c210b10351243c2c001c400d107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 845377491 1250 845376241 845376251
    0x5160803010e070e01030606050f03070207090c0314150108070c05150709060201141b090d0f0606082103040f03202505031b0d15061404020a0221040b030a 68
    0x82c3c80d0f4810700da41c6420b4400d00e400d005262620500030294000c0002211a0040001c0440c0708175000b0040c0100800d0400c50621801081c4140a0020801c0103c80c0b1001c501c9100024070300703e5540050308031502e0584400382c1c40c1d1039400044031440b0040204031002e224260450440344c1c000c50800d44580c2441e51058580c81c04c1c500d0003400e42e5041c0140803440700700b0b141440035203440000c1068030404280c0c1950f4842541d0800200012862030001d4146412a00719100303010f070030380115098400900803501284821f416807011100c02001001c0d48103c107001050009485800150000e8040e01e40030000030b07410050200c4d2440e4188006c034080d4000e9000c01c50350002c002c08803524a0300354084ce0340f40307450000840d4403a1412248000f0300011f5001e0480c0301e5941c50000048960819400044003a0695901c401006980201d5501407180036440340c0350324103070007202c070001070781e90251a11448030801c4c8074005500756646040d44806020200d1030101010240d403099a1107240490 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 845378741 1250 845377491 845377501
    0x706080c040806011401030c17070806040f06090203070e06132112020105160e0d1502040e0a060906051519051b070e100617070c0f030c02030c040e0c0105160803010e 73
    0x1f0440c0c90f0380308044280504038258561143c00181c0c1298130001e40c1c1082ca0303079561001c0c0002d004060301c44044245078a4140081450000f0354082c51080d0304503103801d241d409a90080064a0007808146500d003c401002404800000c0c80c03000001101142c0c1c0405040f0540d481007041d034441d04008006070740d41c100300169103404400010020907141498128400aa400306a420314810b9019010000e948444405e1181f0383d411603008080a800310503541c10b040f00004040c00d114030403150485d0800901181a140900d10b0040904501c0249480c000841e411540840e004071043e4042c4001800103100d1441130034100f140c00311070b0001a080c468100035507410030140292062a40e01400c140c180300c1ea98000003c403401d00120102c0041c06d0355521412202c502c05690001c02804070031490400f010b810002d00480b4034809c03029200d004d0818000d00040700e41c00004008581d001021815081d40510010410305001d40c0205c0121383c2c06403288500d40d0b00c280d0025440031098400c00c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 845379991 1250 845378741 845378747
    0x1602032d0f0a18050f0d0201110f010e1c08060a050f0d0503040603090b0c04080604020118051809010513051209040b0901080a0302060106030b010822050f0106260706080c040806011401 81
    0x16003d8601110141c005c545240045141601c10f07000c000d043c884100d6900d2401101000303101c40c680d09480c0244102c4191001d05501c45043d0804111182050004c030701005003d80c0e04180301d0324000d040301030b8652400b4104541076055107840c58101d100a007080d40480c2c0c0034402040948440d403404661007055141503812214008c10503003a40d20180014401101c001c5900c940040d02460003003020b01008440540b62841540b01941c00000034407000480030360007031428401c0482000030030040ea5034000070b54600e040900000c11541100c003168015a0200025243c030304801303400040c8501010003c00c1503408207800100c160343c41040f11000b0142e04000c1e140c05000310340b400b402420150400600400009051000034003590380c2c041c0c92506114014a2805801408903103124040017030b01030080c6028055107401c882d010b00000303c02064001e0102403980080000c10311030b85003142c12280b2410251070f10300f001004000005903208100000c5020300f40003003402901c5c0022070005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 845381241 1250 845379991 845380037
    0x2401030219020f1e100902151612020616050a020c06030a0b04150e0c0906070f03090e16080a0b030f07091e05041a060102160306051602032d0f0a 64
    0x28611841c5130003030312989880c0840c8901c46000c4100c804103e072440c03440060307900032200039030101000d4045040c00244a85030444400d01e0b000302504810280141012038036003404440400c80208040a2503c1080c443c8005144038801ea106541188502d1400641d16910548102550b19120f207254001d07440c1c2446030301e00641d65607000880c1c403407802c041111006d000901000701d50101045503481c640f182000c41e040b580d4002c4151070131a80618000d04108403d020b0484c96203000d0000072962051101820a610b0301ca40350801c0a5032802c0c1c0740000ba0118015240d014041d20f9001c0b03142c68010030000c009460006004515000b44031064074250200902c00a400c5040805000105004c8079100e000c1c80c0c81c440c0c194020f03a0b907090044c0d141040202c1c0c00c040e440600d100000a003d6543e0200c0c0c01031f50710700900765450851140c106d949000d410f00d400c210501041001e408449580000c44c2d0f12680d22400d00d040644001001440740c005448001c04540408015660341c40b40041c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 845382491 1250 845381241 845381263
    0x80601031a010f150e06070803040b10050d0b060d05060c04030627060e150c0d0608060403080f040309031209050418080919030501150312082401030219020f 69
    0x6589040d80f5020503004105150712803000c0c000001181c92080521400301c5500c0b1920260030b0660300c031b10f1880c150800380e00440e0f0070303586140010701007a03600030440f0405044035030052103030021010944130384034a82000b40c1050f80c03103030014001100180c01800641c0c4900f19400780c5584551441c140441070300c0060313540c035400c290391032001c0c20001d04004209043c4d6410110024294951861071031815062001101c0645003160410440d0107002d80100204011040144140d40e61800919612801550002c020900ca040091800e110b1003070456407081c040e01e030a28603d6501c3e1502a600034000703003072400003811150240f101d82441e0250a500441407590488030043c540c80d17520041c014613120600c141f140d1801000c1c000c00e4006036002450300f2034000c001c204840202800d44641511049420380c000c02a140c0406006101e0b552161038060701d03400e140f142e40040c200c003a0b4004855541071513428420b00b00d80f520b4121942c040d00c142e80d0000c00c0c04c01500c40849203081390b040303c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 845383741 1250 845382491 845382533
    0x31506190923090c06030703051e01090204081006050d020906031e15090d080718081902180c0904021b0105040b091002040f050906120a03050703080f0702150c09040608060103 77
    0x2031101c4e503641301c0d03404882d0b010b5250302d03000480f42c55800409141e607902640780740c080b001402c0041503441190703000700700f1168006c0483c0d41086c3c6015a0f68251001071140c140c0c4014000307404005410007125032640b241c0002c0070b55074582c1c0700c00100010350022040f903958952141842c03545130101010b109411452400041440d0241064003e0845400500c541c0c100100e00070f181102080e81d40402d0083c1038020b00b540d58241c010515211241c071410800d1344075608540c5007045580341d001c0000d0080b0f03100100d40d4600311041041c0310182d8010b03000010b022014040c59500448280b0038203010f1403281c009880c403420502c45051400081801c0503200c10320401042080c0700d008194035084884c01d4500c10703019900c681c000782000600c1c4041c4541406803000c0c2c9020117030f002c0024030b1054440c1e100c40b8a07a80354448144882001190100003513802820200795084c040c01500b0b5001818401e1a8079041074900407030151a02540a400d2540c40340c0014410411460080850008007203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 845384991 1250 845383741 845383753
    0x60c04150306080303074a0d0c0605090d06060b12150303040909110406181107152d060305010b1c170708121503150619092309 56
    0x101a02d80300d21000e4008130600c01d40d00c800094031402c034030000358a041b134003045000c10030003001c00c40c615480c400c050080541001c4070540c02c2d8540230780c031700440c46d41000190b9803c504000703041d2015032042c124103900c0b940c0c0387c0c0c0540c0018403d005080c0500001c0e400c20f9222a01017000034041d00019102050062001580383c2c0551800810f4030201d03402d0000c0810079a2070740c14900d8464019503001c82d0403505080000c0307428102d0180050380040c0c140020003034613889540300e5400c0d015040c0000d082c00c464000c440e401651030740040c140d451080c0da902031007807042145034000c480c86480400701507482e22001c00c00d2001c00e20408289610907034000400180341c80c0c507044410311b124001010500c988800951100d440815a9007032588040391035079030f24030340302c0c26002890111030b4282509603c88544d04507080106d0f810000b00c2001000688984640c0e04004450704104d055828507980004002a261124000c0500407170320089282c01008115082c1c6083c00401054080907602403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 845386241 1250 845384991 845384999
    0x131a040809030d0c080910030b060309030310060819021c1529090d030c0812060f01020d020d050c0f190b10080a030309080d14090f0c091602010905060c04150306 71
    0x5d80304580c1d0000080707a1028034003446a800354001c0c079019552540103d00401042000140000250301031750710190002842075851404407280352040764065403030425580324008841070381e005001c0300800106c030751803005c007440c403110308640247d03d0100d442840f4032010401003018039800f414071030381d03030403081241c0c0c25610751310481d80302e02030794031307002e910101c41e544241803180b03e84150b625482296142d40b59011401c0c440340721010349601c3d00c10060700c42034680b15800010449500c0c0c2158024084118040380140d0321074114030365000c2c0300e004903244e04907207200903c2000490685010b40c8400140c580c2050111104020a503550380100200c0c00c1c07000100000d48241815414980401c440d000c0703280a0f409801400c00d1050000c1c20802001000410b02c481a4840c100e010100d598000013500b10711b507a05080c8840340d4000d9868000b01d0b1126201c1042012040d4090001060f142020703030b221464070a0442e502c5412a0000c80c3c144804d00200302c0480c0410000d142c140312071410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 845387491 1250 845386241 845386253
    0xd140a061a030c04030b0405060417070203060f10050a030303051501090303080a11070b0406050f0a06061b0606150c1e080301090914010606020102090a0f0e131a040809030d0c 77
    0x1140007107070801d60340480050076100d43c210454010719404141ca9030303d0b007000c3c50900d5503000113480842e644c5c004032240c070708600100800d8509490300103004121130740311502c280d40d00050140c2100800303c0c64100c0843c0c0c80d00ca24415900543c42aa400911441c0c11101c150f1000507010650303040080c008010004294813284c0243c11507001480000d880389a492008003030301c64028000d000000c0c41d020002030154907032050b8400d45400849203105d944d8002c0c0e0300100e8009015071004142406102d185200441d0b940f40e440c0d500c12940092200e4484104006183c0840202d90001d220400e00070100b101540502c28006000f012111002d5959583c012460005000b070a81050341d0700041c100b030040c0c0894021243c00f040b802000310544500d0000c3c0030f94840e41d4030328003030902210001b40d201140504039044495291040c007054440201e601c0e4003e400a50980c2e43c1202c0012114421a241896900591080b4001640d0301a242c05150030000e290803004103001c40b0140310800300788 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 845388741 1250 845387491 845387519
    0x80c13060f030e0a140c240a020a1b1508090709050601170a0b04110903100207080408070f030303110309100e01140a020306030c0d1709150d140a06 65
    0x2480d424101d07802001020210000d002c18245142e041c400c1c8540d05003804903525000101c06084000c1e52a003144681c00d00144100b0038054000d000302d001304c0109000501e0018150002003481551100d01f0151242104440740b1118000c1061554000b0030010400d006803507580a40750030902c000d481e200d401561a41460710440361020384810010b403060f03218016650007242400084601303030802d000158000d00b9075112483c020340c60401285018820002503c0c1306900040040100b20340d0520b00101039001082c0444400600344004640d860090040b50045d140c8105640c051901c2e50400500341d4440b400c0c6046070742420001d000715000c02003600845481d070400c0208807080c02e400d0301c500401400000c02821007000060001c2c1144540080d8069031044044031005a108000c200001e5000c42c00141b1060911005520b0b420a58000e4803220b00c0c020072811740b0100506002d007442d4480685d54140603611020341c442c502c5200180c64014034500c0341008462700700814003424503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 845389991 1250 845388741 845388749
    0x1140126070c031724041119090e0414011a010f0f0908010c021b0a0806150609060f0a0f0f050409090c0f12060f02090604050f120d0f080c13 62
    0x2c164100c0c11028103006441c5a04006085040c41c100344c640190030705051641c600e8030800d01d90008400c106985458000d180403070388007800b01407624130058060f20340100110300503070a10042603070008007211080030461085000e48401c40005c28245210b501712600c43d0f405030415220181100d0b91030364402e801c1203050b0340740d040040a01b4207004040d2800f0034154000191036003088120031505078042401c100f140d58042000112050352801c00c01941d003140142041540050006040d0588072288140c480a01070103052510b145103000c58420340c41035100c002070500009010b50029805405203000c035030b15103084c00d07400c150020024464802c0d4883d56442c240c03104445014040046020383c014298580d01c20001c6943d40428552100c2c00d04c0c0584120f89400c0040c1541c441031300071509000d000800c03c6d440c040c1060f0403c940c0302d91a040068109801a842210500003085054281c04058a03001c0d1402d4404c0d00040001000034804581c01409115001c030030850480c901044c0c0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 845391241 1250 845389991 845389997
    0xe0d1b0c06030c030f0608011d030f0316170a050411030c0906040b0f0907020703050f30130603060f0501020111070201030509150c2a1b180114012607 66
    0xd0002000c013103002e007000010080c0042d280581c0001c00030815800b201145030002003640d103000f500d2561075142c2c01884e19003c01c4181c02c01c0054403003183c3d26145800490355041c54503003140c1002d0340e0b11030b811b81210280d030079544e21424001030001d1140c48500d0000102c2c01098407003180004070305c401d200035103201d000e540c403051510600d65400e0100050490040c0c40e0010510b03281700020355800040c8025261400340400c2c184540340c0124144856984a41d2092099440320280c4800036400c1e2841400c440c00911944108043c182e802c10f0042c00150340200300c007810301441000c120410b80c029410358ec503010940044031401810380c0d004940900300000c4581d106280c10703091041c1c600413803041303a50030010000e2408888001d011407811091420129980764140f501203240c0ca2001e002c0a640320482003890150105050406090040c100d140c10415104100d01c1b41d61081c0c0082e40ac2d110f117410b03205040d5910811600070791000002a00c2da074009080310f02c0c075040c0084c02503010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 845392491 1250 845391241 845391251
    0xf0310150e040f060302040e15090a051b04060b1308010b0a0e010e060303090d050d032007021002010e01151a0306061903230414160b1c0e0d1b0c0603 66
    0x10312801ea44c011001160050010300591a030303183c0d002e884820840b044040340c0010b0011908890300051007400c459884402010302e10043c00d074803002014441c59103548140c47d810b012407844945409495040a210907440c0c1d86070400d803800d42503030300a009180c0140c02d890410044462442d60550444107a89024065034440340c000c00d0a42c4905c12303c05400c04d0b500721a6208024000401c050445880d60301088a0405003a404a841d00303024811128030109003c02c601510f804604e40004c41d02c1c0d4000015401085d50481d4255140e44502215200d00c04030108541c0d0084504500a8100d54600616600c3d0000000e0074500a5860301c1010108804114274014040d40c015400c000c8c2c00b0406c0305003400b100c030309228140c40c1150b0444030003414820200e86940001a0a24070364000d808101d030305814840c00c940642c020041c15051103a11210030340142d03501d4490301c0c100b50f000d480a080c5503c00701c603000e00f0141d074508071060806401d641e107070040f40e442e00c0f60700b050b5485481d000c0390b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 845393741 1250 845392491 845392511
    0xc25020301330e150f04270303050f0106021f09051203041208060f01110a14030a090b0a020c090403120e0303010f050d0b1305120f0310150e04 63
    0x1006000c070708402e02125a0507110301c80c4072070318001c11440302d400c81c40c030b00c40c5440e89540d00c0403200f8609030703200d000b91100351041c8042031800009002e407501c0c0240000030b507000e8280110302840444d00101d084001c640e411001419854018554412007002101206500d0140b0013075681e50722080d21401c10b49514511010000c1b29040110843d401c60121609107050100f800180c0d8030a0f00d044402c52100f0800d1001d990040418602c21040100010b070b80c140d01200565a0010152010301240106006440020910000d4060129a140007036480d545075040240044d051070300101d4610740c0c24422110034035070028125122290607102e10b40f4907141c034178040c0c80d680c00340d00120b409a420507204410b5110000061030403220408081c7c011903580d8030601c44030011100e13001c0d05c10720503a000500740341d0036952070402d014480c138110344803000300d200000343c1500034180c00200e4041c00414081c032445032403d405c0182c81007011070a10076007801c43c05441154901c000a000d191560020a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 845394991 1250 845393741 845393743
    0xc1b0c05060702120f071701201b010e030d0510080a120e030105132105040e04080f0f0a200a031101110406020f1905120c0109080c010506090c250203 66
    0x100028140b202110300308441143c070f00d91115501d000c1e035641c487e1104408210107005024020f42c2a0104000400071007117044104042e5105011b8070b03005202015940b260f03d0000d00c28004215140c8000c0e503156008403001da002d0b9031000c0c00b429110451420305000850340854982d41841e4031100c00d95014040f2481030b01c920401d807003016419441c081c10405150032580c002044280308450051b0384c1144108441160400c12041c4000200b0a0000344039a1035203035440758019004071368050400444010020030b0354801c00d40314101010210f1042070954114984001400f281004c2c080078500c0c80c003141d40d89000e00d020103000c0200244031403030752400a43c4408046410360b45015901d0f511400b010795501c80c00c42c2c01e8005440340d200e5640101605a20845049500c40054082c0b01d8007550224801e170041d82080126550300c484400c00584003000602c07090342550b0002c2a0f0780b0b0624100701440c5002002e107440000108038070005040c00d80c1780b007580b074103101c00e660712240c625001203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 845396241 1250 845394991 845395009
    0xf0904210903290a0510030f3e0402071e0c0b0c1b03061b1e031501020118030503070f110304030602130602030715020f090d060c1b0c05060702 63
    0x40c140e00c0603000e0f01581c081d2000c002008005400c240800c803a1144c59402048400c101c03034070041c2c03400b01041480080c1da000c0481001328003078008a42030005014901041e60132050b05241d90541001d1085060800560085a41c060480d011401c051494840d0810340c0060b810410003040c04c84440b108014864803150054461080002d407a1042e0484895485410004400166415001400380c6142c00100b0030b103e8010016a0b00c100c1082081d59909a00450201340c04d0240f103522002d2100c01040184d8450035483c1e14080140780440000790840c2c1504403803440320300b10700300c11502003500703c001c40740c200e41e09207012404040c41c0e21046504203202d294401560000040010034011980c003e0702c0100c038210403040c42a42d81d448282c0c3e40384241c100041c05413025441141d5012800e50140030007101d4003070040c0c03620f1340c420700059221020700e10844003942c0e600b41007010298002065030340f0721a040c00207142d00c0520f8031050006150392080c1446071030001500c10454a5104927 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 845397491 1250 845396241 845396243
    0x60b0a030f1401090b03011416050f0c01022a0d170a0902030613020f03030309100c0c05030a09080c0402040b120c16050c0102191a0403140c07050f0904210903 70
    0x3990110b540c403580940085e0030014000c511941c02c029400600c01030903020a8040c000b180d03400c901056814078191401e40103078144620141c014400455194000c1c001000605410301c0c098941c034004894a904000031510b00312501c1e4040300316501900e42110b900c13044d00100790320019036540c41d01e010398040c0c00c1008009402d03005000501a0800b108242100b0080c400c03560080d09500c0c0c178013450b543c0e0008490040709907000704003503e43d18041d40c1c0035140100707092601c0c6c2c0420315240c99007482c41d8045030400000890355902000303a0101400310100080080310154907141c03515010003e94041c03400d00113008461030012808441c0a20112485080703003007181c8034114118109161079070000c24405d80980130b2985400d01001e075008024080725800002011450005a000024070100400c01c400b0311020000103103100542e2405489019500301c0107291322410f1400f4010f08042e110492030055540000b488001071034088010030040c4035074204d038982042c01c030044030f002805900c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 845398741 1250 845397491 845397521
    0x9040b120106060903050d082404200d1512063207030b01080f04030f0c0c090e01150e130c05060a050c010c020703030f050c030c010606030207021003060b0a030f 71
    0xc800111190024200d0301117074003c2c0c054407040b187c014020380d25240202e411651030381c4419682c25042540810300f200d600700107400091519910a203900100280d142e00582e81707500443c0d03c040e44461030003180c010395090982c0f000340d1407500e00695900340c48030200031308498840d506941c5143d0362102d4011300411301d85080c451001d0380c42c5c2c0c5104c4440161040d1300001c4c10b19009040650007012140d005c0c9801507146103403540c9031b440440d0030344104150b20301048550a0124082010680c8040240400c242c000460350807014603682180c4e61040000031001c40708000704203185605000c1c0c0e61040c408162902c1c452000d162203006011141c100a40c0b0810103c0d9030809603502002503e2407080040c003c03c5050401c03082642e58052a10004000600e40207904420a101e50081c01904c05400126414401008003031030070368480d90002c1e03001a5011400301d040d0b160940c5100d6041056040410029082ca404030310244103454030941490b0b124041d0000707554640d401a50300c0e80c0381d91 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 845399991 1250 845398741 845398751
    0x307050c190609150b0604090c0203091305180f25030f0803060907110d03020a031d0d0917120a05091e12011812020c0a1202130606020309040b1201 65
    0x2c03400c80014840000203554810411401410040b52071085203050840102014141072900c81d0000c060031423840c0d00703000c601041c00f03049013540701c4842d60340e1704c2180140301050300c1c640b444100e800110015004c40c00c640c00303108032092104000c140403610a0050300344010703c00303c40b030341039121346202d07403005111512403a07680b02880100c00296000f0070044a00310740e00d0315030b08011900f441800c1c20000c101e411411203090320740e020780d004100008050030302144858003003849001000903400b00c80540e403c004400460968803012800107461080c48002d604500f030151203540c0c0001021520012000107070700070456000b441905c0401d40018251070060804101000c0c21811200c40c25010b26414440d200e440c000c18020804811b4010031407500f80d035110b8a858081892408290003980506500b0111540f101c1244801034480c0760203010205e50f8620601c190340319044040c00c8072515011080c030440340e0100c1101c9000008940106612000e040080c1c03000030701c40080905e641c038007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 845401241 1250 845399991 845399993
    0x20603070c0f0f1b0333090c05041b081302010e04020c100f0605060f03130c060818060103030c08090a080319110a110603190203010e040209090c060307050c19 70
    0xd51600303c03091058a2800789080c6030009101003080c1404024811302607145001a2883d0034414404540500c66191a0b5042c1c00c8100c402110b24203001540c00700b010000c00d000c51b06107801a214084058415043d801c9011b00005190b5131018001d034402038148541d100540e84141c0303446c0501a0300901c21503842e01d454541654445501241e0072546051002481071500d00780b25110441e50040c0c2240e00c0c0281c240c0340090700d9131000f011110341d03a1004100c000800c0c41c0400041c050640754994440e04e09040032000000500528a005943d01ca4001400003d5010201d441055800700c14580c0704d454200c001941d4070030b40c0d0404040b0780310100c2c030031424039114020380103808559110000480d0005d500c80d41c488001036805003108406840c1d0900d5410184001d50b403100c4001c1000b030341d480410008030280ea1081e0b21400744014480148030540c0340403039002c1d07040705080000b0071160018201051950100400310f0050203004603280d400320360300703100e036540103580c0d0007600314034000d5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 845402491 1250 845401241 845401253
    0x7020301020a050d0c020703081b19060510230105070206190918060b03060607080d14010302011b05060103080a0207050306011d07051608091815040b0418020603070c0f 74
    0xc002e44d090100e09060500c1c003214008140c46042e40e4005e41d800b494500c00500d03c08001c005082000401c1c403540500d02c1c094000c04400c000745074403c00000c00c40e0306040860b1040b014994008251402c448c6a80a07150104850010740c0c0c00c1e02030038882c0e141c04003400010154010303038507116a91004001d11038803956010a150050b01c401c44494104d84010624103800c80b01c2a000314682c50f80200080b4040e8907290010703182e07107840344181d14a803640c5c0c5000714040d5001c003a0508005070a0000510171980c2000c0010140e0062000c80000d00c0e140c1d032100382d40d4641c1032001500b00a030009031580842d1080c0614009040060126241565075002c2420014120486110079900310b0307011501440c4141708403100d40c1d41c01001407164901940704c480b61540207035481079010720b0b12043c01042000d5001240c0c481c41d40360891001080c25a03003070109484085242030b03c140d141802403030840700001c0e5840061382e01603c16a840740e45000c0c0640f04411040d4019200c640300c02044000c02074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 845403741 1250 845402491 845402497
    0x3310e040b01090c031a0906210106061407050319030e03040b04030b0702010219080a14090a030909050610080a0948030f0515010807050a05030604081e07020301020a05 74
    0x140ca44400c11a10709402005c40c11520302e03051a8a9174440490150014a03040c0c800c641c0011001305440c60700c0b2211040c03540300c48034908810083da5140c600400c90345401c5001c4240b0520724a040601d030103055610b11f80c881c882c0c808007415464045150842140c81307540300d80c0b0340340750000c01c81e035440b43c0701c840846183d00030307200c106c42801c0c4032000602c05034410b009a605d45c0040b020f095107144601d040a83d82c110300100040c059681d9a04040703e540440ea5000d80181000e40142c11081e01307504009101000c540c1105040d682408103003c080d03221580a500301e04a68503040b91030b61140485840030303010b140c8020b04500700c850b0100b840c2c500350070b00700d00041588c00d00007001d143c0d0002900380e21000b20200d0090700034030741c0020400302d480440e02c8028180b080080d1020300d00d02142101040000785c12144640c1d02c0b2490500c40b0f0305200650b40c0181c03000302c004005e9403410383d985440c648211800c230b14980403244409464030106505071178016900800030354441e9801c0900500c260 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 845404991 1250 845403741 845403749
    0x5121c02033d05150901080711241e06010f050c07031109010e09060406020a1b0305130906210201020703060c0e0406120f110a0b0c01051803310e040b01 67
    0x1d018140c00141450f000c00c00500d2403440c0c924445c140513503a801500c40c1c90004080e001401189044411000010b0200070680303245030b0315282c80010902109105030381c004240c034540c071400c551003980c115903101c0540d5100b1360074600962503031003075031007114a409440d111345954032504401000300b2011281c441d860040685407080180e90b01c0c0b00b1306019110541e001501504060007050201e0314940082c00391822904103c5004000b0b00b00c0310703d40141e011f00c01c1e00060303c003143d0741543da072010743ea03075006044100080c4542410300707103603d00c02c082d9042d507401d0002f43c811a04046900170301c0800019600310504000640d02a40040e04042d41482c2d164800da15041011031b40220050005400540043d002c091040d810f0303545d0003201a416030444d030700210481000401031780802c0144a600b00240003c0350a080c485500c8042480b02d1600081c141c00901c801c28020040219007031410b000c0001e5142d08004209804406d901c5a402c4481c036000d003481000203002120109a04a03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 845406241 1250 845404991 845405101
    0x1a0405060d06080d21091a151f020c24030f010602010c0f08070e0f030304120b0f040f0b070e0604060c0b220212030d090f05121c0203 59
    0x1144020b9012150110b00174050301170418045180c1d40019902c4e446816030a00c6000c410000c40101a122801400226211078401643c24239045050400b14008030680403107102d0200d04010702e0700003030b440c0c3d1424181240110b000350fa2554500701c256030044003446040100580e00d0510100044880d2824002e0f04055824005038408052040618101d0200195502c0402e912084802c903100a90303003009603400000c003250700c21190303003d1008000030440d449844040005510700180315400081141d0b0503074500104201c089649070b0a40d81c4440e0b44116080c40d107075074440742a6080401205115040000854041030254118025001d11030044108000d0345d580d010301c401291003060510500502240d519000505040c84001e0b08040542d0689082c140c50310822001c1b641c1c620740c2035032070b10700284144041c480b003404403590b202c011005a516050300400c0c06400034609203603404a49a0000006e0150886651025040c00000e54058140940050800103030903100c01d2007105 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 845407491 1250 845406241 845406253
    0x1104180206092b031b031b14070f0504060902041d4501050705040b0c0c1306170102030402030a0f061b050a0f0206150f220c11161a0405060d0608 64
    0x21405038445140039074143d6408001e104140811380c107d8482c00302c11500b070107108421500301042400b00d0b0020380311b00b2841034035035480c001c100002c1d540507a101400d514810801800700d04001036003084905a015501030700307921100c0c4580000300e0741645212030a0103400c0c4074910390328840b40c0009007034120745549502c1e01541d00c3c1142203903400c0d600c1070042101000100100d9404201410880412100741c80c04420701c1c40104004085102e65518060350301d071010702c22041c1c1c51024060b962403000c001c504514040c0c0c042982c4210f003003000742000f0222414082080340381d4200d58a5545614500e110203179403814050700540203a0440b03004240d0f2011404c90b100d20005800740b1882020740c620b910240510b05104440c84507000c1c154100c990070955082821524503585281c05200da00090030800840c8002d00060b140c1c0c00d02c1d506500030700f04e500e4420003011141e9040d42c1e80030301149000c0c2007080000103580320300da10032a00490302080a0f10723208010760086082380e4610080d601 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 845408741 1250 845407491 845407517
    0x1505060603072703230706050f030f0a23060909010b030604120e06030c04050310141b04051801050909030901050304150f0f02071104180206092b03 65
    0x300c030302048540d0400540011031002002070742c0c4040d5503101d40a82d21003894251a5291746280305c51290b08070001c507040d4612401c1d50102040380304020255860194285490340200020902c405042003d0400f00040800c03500c42c815480500c000c0e0903914500340030001c0e0003003035880750f07012504141f069480d100040c00320241070041480007080240942026034442d41d0701c07001000c1c070146a004000300c1c40503220150319010b0066001d07100f0005515241d502d0042050700d0002c004604a403414202038201c04209411400160095030f820034480c503402d42c2000d0111140243e9020940c00400004554a20b44441c0301c3c060585070240c403458070a42c0c2d40c40b040c030764910844180030300141040000070045550801080041c15200101264100c402d0b40c00700265034800410001d03540d0300007284000c000c0d000c48882942002500c0c1844100c1e403280038440d00c00000301d03001c0c1c000d1000080d02d1643ea9203d40400c880d00c0000e2481c5203414a006c0104400041c90000840100c0c0181c01040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 845409991 1250 845408741 845408749
    0x1020c040f2306060a080406060f1e081501180f06090603021516141501170607020d0e01120f09060e061302060405010f05090d0602031005060c030a030207021c150506 73
    0x1031042001400151510315491411500003100400c217131102552030340045410a0003252100040a00c103500b19061810791003100801d0312f49a00009081d40300000c0c40d8228400034121a04460000c0304200e903080002c0c40c004041c218581d0044035407071800c0404107072001950300020641b030007510039503a51612541084424801d5401800f05090281649000a04a01c2c03413039a24900000030b6030880340501c00450100e080a0b0000b01d2022241c140c80300c504003040140ca41e00c55180d20003408030240740040500591010252181004102400000141c02ea138110480d0201100e40c02c00c4140c1c0503040030388c000c00c40071001d8100c03400b0704004108110181940300e101d8940082903945007510f8080103640e120281002082401424040c84d03481d66203403a01c0644140c06404096a04d180000c400118071100387c0241d4803944040c00b09000300301000065494401d46820300595662890000a2401c4400c0b0300480403611450301c24001c2162101d02c000d00e51450301c80602042d03d5050802c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 845411241 1250 845409991 845410061
    0x15090803090603060d0212010f050711010507120e390a0b16020a2117040b1902011d01020a03060e010e060d03140c07050906270601020c040f 62
    0x1e94070500910104d0301d24980410220450761009040c100d151401000c024255081e18140592455881041000e0260000d01402050320b10000800c020301e44041d000d4178138205148041c040c560b40b1000003d800c181042240350321960040c16194500004c020500c04a05840304003101c006603554800850502c40b00003000c3d1210040464140792484042c80c00808115070140d130301c821a01710000303800c1000c0d0b00c1d0a80082c01d04400602120b4541400364070700039040604910381d9410402042406114001c3d100801451200300741c85090b07201c1c08a02401c40f21001e29140540c034240c60aa0540540c01080110565202400100da175403040d41c480071000d1040014002c901000100039160250000c00018400e00344100c03416864841c4854075002503400740795560042a042c4030501d480c1e20a280d2007001201c80c0c05556414154100c9402165461000e0082e001d00206045a009100c4d0714060b0030064000c00c0004005013010b07000c4c1c030400704141c103564003201401903690b09030084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 845412491 1250 845411241 845411257
    0x303010f0b03010f120c0f03081b0c15070606050a0e15010e0a0303030b0a0e01090207020a090b0a120804150509040c0f02061501111c1107081209130615090803 70
    0x4e84040c0c145081400c050003a8018030131644586031100100e5005040380410300a5030043e65030300e8032040905820075200e0040e030108001940400301c4500241e5507903142d1b0315040300120301d141c0c582c2141d1810301d000d414980c003c80d40c4030b0361401012071a160403801b0184100d03602011020524518401903a180e2005103159800285c40c20043c4086806a0021064024090080d9589941e2504000302c14002a0040c4403a507400149080c158540912040041c0a1284080003643d05200c001618050769225456045501d044507809120506094400811000f40155408442070100030510b520100d80e492040789000d850b500d00d1845007890449502494000300b0041d100c1031008107041e05e514403422304110514010864185003403000754841c5100003035001d20a00390f200060b00a0400c0009000141c0c004101086580343c001140100f2503062450300390341c2c4220708082460351888074001c0e0400c0b070070440c00040d15110500c00341c051200554072491140d440740d994903220302ca0032034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 845413741 1250 845412491 845412509
    0xf0b090607140f1c050103030302190206101a0c030a09061403040b0f0901022101060e19060e0f041409122107200102041e030201050712020f07080303010f0b0301 71
    0x11018540f0840303200240088042404ca001d040061040c058081e20400d800c224006500404c12040e0700c00795401c5503210600700c1c0080d004601c0c2054400790410030300e00c1015400d00329140403041c4408000c0460b03007415043d0003920380d99041420044c11a4506104040c0060f03421110100340301d01d80020361740101e5010001640030340b154480740351900d10180100b0901d541c00c10140d1104506040c130300c413005080c0404418190b01d4080c0c086d012252007000f0b6409107807200c04098468aa08410100f59a205c0c2030104d080e058810115102190400721150490710f80700f00c2010008841d00e46034031600a0300119107840400003021142402114250941c0700c0b45a01c41629079068000056406403451412a151101c501f0480c2c3e07088880d100d8075940b5950001d020700c2052a40750007008500519005003d0052840e40020045c4c81250710142c001d0701290964080207100340949500c00400900b1a25540e46440e001510b036131003031043d54100003401e2000140e820b202000e5a04842c1032030313 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 845414991 1250 845413741 845413747
    0x30507060819090305032403030403050105090c01031503060207060216050a14030c0304050405040f050a030f03060501020309091f0e192403020d03110111030403180806130f0f0b09060714 82
    0x10070781c0200000c2408200c85080b90910701c2d8466803009c102500c000c60140002040c80e0802401c03090078402284421810182032285401030314403940741e00e030101c1c0e03840080140e0f80c201d1400d1040090241c1072110074050030303d01e0040103001d000034030780b51601d024000580300e20048444465881c401c404400c080c5800601c01003195250a51000ba441401028200312903030140c2d441c0350602c440004118007180300e10025661180d0315200e2a40a01828002546030581d000002145035800514801e5a2a00c0e035200340350400340744040100521410000d03178a681468031440709002480310341e410009d440c00c160324450401000644003103004030b0100001c4d4604640030b00c041c0a4094005030180400b5010a19440009206007400311418103002d503280c2c2418a40240700700094145408000c01d1100c1c24004030300d010801d5500065080c0f0448004503281c50024003c4030020006080183c401d04c0740c10501c42d090a0140c40340c01d10030306a480340da4404200b40c43e01c40038030000840301c400c28 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 845416241 1250 845414991 845415001
    0x4060f0503060a150b07240c02070803030c0d0b010219030e2d01030b03150109050403080a1a01030b0d08070c03031e050a030c031814071d060607020a03050706081909030503 76
    0x49001821b10314000d80b40340d50000702400d13400115640d403e003240011a42e8400116a842e4140b00c42c2c4080e062501c05140785040c52203002c00c8600554245104059442000381c0407a8000c00004552005040c2c800c01d1a0065081c098074011100f1031003402030107003201ca0010551159074000b007a08030088012100a0303003400440090540350701721501845502c1c03a2007500350684080e03500034945d0903404180340c80d0602d0700400580c0c010300140c9031542002c0d400d110200d40b403d68200300d2002031900040700914800051104400a0800b41110000260520900040034054020b9034025250500001e440c00c80d15009050070107806c000144040c401d01180521940099112040500e00810502a5040d4400604490440c216165800c0b10310340c4401c2d5105000040c01003903210049500340c032201c0412080030345c00801c21071161000081d81d600310b5440c00c1c882c2e400303107030080c0c11034083d1038941c40041c0003005d01b07540200d0700505403c503000111110703014400c001c0d50b155481300c0c20f580710 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 845417491 1250 845416241 845416259
    0xc05041e110405060d0507030b0411090f0310020a0203130501020705090a0906060f29090d110a0816061209240e01110904060f14061804060f0503060a15 67
    0x30341c031561826800308001c002016610744024141e1007204110003c0c81c0e06090070058101c905c0d1004450040c1e05154114150160f4481074405030341c02070324000d00c07070003441000905080401a100442c14400315852015070b0b40000940f4100c080307080d200c1540743c0c4400c010399950601c1c0c450194040071040010710141c045070090025188038140c00314800e903c440e02034010700b50301e0300090000c40414030703014110600c0c69200489010515016441c144002c00030640e4010000c02c081c189401c240d004408507160b02c44804001c00404081d502440ca00359021410801c00b0300c984800144004003084084c1c80b103100b100310050744912200da10704421a0301c542a0000c0a000b02c0e000d80d0340b03502101c0903903002e002d80c0440201010000c0d66520881c0100300480304690000b1040d18075851050000ba001c0500389101007404460450700c508100c104400c51985400950780c00c1410606c0c00280c071000645801d0640c0d00880945185945003101c2d0030846e2030103003a0031800c100800080082c110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 845418741 1250 845417491 845417501
    0x19080403140109020d080d1a0307170a0b130c0f0e01050d0f170d0e01111e0d0c1715090402011b0803100312050a0507081b190c05041e 59
    0x1401c001280d5052541c00003000310492607415180080d0005108107048460f1080c085401900110b0850407450100800d40c5c40380300d4000c420502c4449060042078420810041e19100c3e4091400a85803412208a103561461400100c4290240810106804117100201400c1d0740d81d40078030b552141c4c81d003030400c91940c010040554000003040e001c3c5010900002590110300d23421031401e550788a03d054058122442341c900e40032280d14042507503040c040d502049848103c098021460720880040c0a60307a5031149810b010300c09071a0540d41e03480756400210400176030980302d8000c000c070f988080305079104c01500321043d603200440b41c1c0020010b41c0100302c0c00040c3c054500c07465038200c501c1e66a42102d03170b000355060961030860541c00c00801c000860024054a03083c0b401505006032a800a00700c2c4c0282e0750010072600d000304062005402c1400c0328039140e5901021030300070341440d14180d2941143c1990540c0c90300c90442000ca0786041c44e000c2d51031044400702c0102c40d90500c000103540244 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 845419991 1250 845418741 845418773
    0x41b3005070e0301050f09070803090901331d010f0e10050c070e04021201060303020307060f02210402090601020706050d05090f010c0f0f0c03140c0c0913020319080403 74
    0x1900704040e007140c40034031480344103100046d0181e0a1b8101414164540003482d400b94085034010010781609484e11540c2c503046900c1c0b4a94883c400050008110000742c0d9806803403a01022154001440b81d0b0190080001c155446240f5415030144401160781148024201c00401c01132005120b0604180b5682d00409140d4039040b41411000c54445042001950108a00a1004043c00150700c2c010340752140072400c4100030440c852540c0c4d0301075203074061486c1c040c1130595540d41c0784200300c1d25030701180c1808580d501882901946402c0840031804117440980c05090010005050b0b0750000455106072100c1b80c03201410003400150f40409000000c240c4070090040c044c0c0440c1d5000700740501000c03a8015101cbc420048100c5078010980071120740600c0420000100c90004039800c0f043c1c0b17420b1a210703010155626020010414907007800c8841e40b0341c01400c20f100304140302c140c0f6500390805da0701c00c0b400d4500c01603d0101c401c01350204c40001030045a410082000064124036041440c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 845421241 1250 845419991 845419997
    0x25051c0201120c02011d24070302090d03120b04051b0a030f111c061a0a0c05070e16020f1c260106081f0509090c041b300507 55
    0x35000c20040da00b80c54103043d9002c00b607034445140301e04600c203c03003200c0c1d03d49114000924124409042c0d205650007000701d452030800c06107000c81e081c0e6100390102d070f6107444094406400202c0e180742c0104002a00a0740003846031034494510158606130069a000d419580108004080710b00d003000e0300d540c0024910000e150392811031496034074442c0102e0b42101005001e60340c540304001111181d406910700003040701490180c0071700032415030101ea60f800001c0c1003003041d20b481c040320041c0e603800e10503c0090140e00c2004800514601c40b40e119900c40c10f04005808d0220041c05810fa0f41c41340715420107803268100e101115039003100c2401d20788610a403450f00c40d0000c1c601012811680308050f940c2c910301541d083c0103024041d000000b0b41e803c10302c0750202c0c0d82c2c4451103c105421000c0903000f00c92203000d403039000c1005103004101054604000810800503c0390fa643c18183c0414070002c10030200340e08042144801d41006c0b040f40391240d8403404010b16586520b82c0c200104002440d40080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 845422491 1250 845421241 845421257
    0x180914070e061303050715080103030c0b27060a11070209060f0a0e07080a150b070204050703020f0a0e03100c0503131509050a021e010c080d06080f25051c0201 70
    0x9650002c0c000303c011801400039041603070900f40050500c080f103003807110a002143e80100006980400806045500300b010740786a40c407030802281890b000000d100500d0400f020682202000c0031031010b000b0301a8100400045c181060002c009018480003c1d5000c44240001011420000d40b040190240141810348081d1180618021356400b901d415002074001d00800400a05c648115400319000d40c43c01c40c1181d1401c4100c1c6983d2007140c0000340283e1b00e03040400c1010340650185c4501d43d0101c1002c3d0303218254200000c26013180c02306010300c288928000c1e0702509802c0d106440450701155140361965442107a44d41e03c40849040440f07c0303242100c602981360707055101e0070607507a10036405000e002e20140100015044240000c03001000000321484403a0380141940001d2030784440401e0b00c0b40d100300000c1c0c00405480d07000c09514020441e045002c44030200340814120300c00b0114144182180b5460020700041340202508040b02480b1088620010501c94255034814500401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 845423741 1250 845422491 845422507
    0x90a050414070e0f10120b09010803090a1d04020d170d0209040c0f05180f12011d03030105060a110c040603121103090d06110c0d180914070e06 63
    0x101c48119415121508251040c002403660011810304000340031200303500c4420307543c0001418801c03480488401c2c044c40034428246400c0c25000300e038220704003c1079112650394030101c6d42e460740d02603c08144030384091000454032070915401c1281161200f038052079550b40341c0d8240300820103000002c0d50004030404090180d49c0e00f01001b4050000602d5002d61110400401d102c19200c003c1840c0003401206244490104da003c016209040500d4084003100344103000400c5101040380b00780303a00000c8800b04081605030541100030940f00b44200e07607455444078581241c4901080c06855403144042014086141c410200c81e20790381420350070b40301654900e40c0003500303c0e09207070320840758503040100007001140c00186079110104142d001e1407403c0039880000d1880b42c4c00c0c95009100c0c42c1d07a510600070710001c103416a696000550101d4036155001c1c0c1300a0160421541c001045100b00080070032035042c5030142c02c1c1c14100b0000302d4507407610369010594010300440c10550b000807092103040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 845424991 1250 845423741 845423749
    0x103110f060c01020d020a121406010509040b06030c03160c0b0f040c260706020a08030a020c01060b1305041b0804110135060904021503071b0b06130c0e06090a05 71
    0x1d8068105e00c030050b9504200d8201400c800100c0c181c0d03240c41480d090040280101e00c1c001c180d800002480c00ca907032941034000140062443c441d459420070408010403010001000c000c41c0160210302c0c280002030807500f41185d025510180051046400e1030100d180c3d203110250a54126201c4d180e9104090b845124000c90f0410130306405c1c0c1c2c500c0084102c580031036018170034540500400e2001e0003408090740c0314018944400b40c0202400d6034009840d821840d02940050040c018242925588419622490f01006000c2c01003d00c00d5103084590381101c000401e03200411001c42d11f03120901d64a946807a21401d0003108694107000400380c4a8106852220414080b00404040410a0840107000f003514040082c0018040c441880a010150780c3d405243c5401861000113650350781c0da07054046502880483c0c0004950b032078440a4410008107421041c8592001d503080b2041440d46515401560f1040d91210045100d00d44603119504010005202800015100d0f9100907a40c0b000700d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 845426241 1250 845424991 845424997
    0x40314011b0225230d2406050429220c1701030503161109010902090906010c2105160b010611030a1202070638090103110f060c0102 58
    0x3040180c00000300c0803040d0942c002041189a0314200001c1e6440c10242d844494000c1c41c4da0341c8402e040901d03807240e0300b503a030026141100c6900100c000102e1600039400d030000e0f8840d089150296080c04400b1409090074072440c4404403821011040f04006405460394030500a01c00f01e070001c0c0c00740c04088824120b0743c00d804036040300c2040041e20b40c0040b100207040745003842c0408140c400a00040001c59400019070310355903c4600c448003c0e4180d03103070010101c0c1e02c50702c1454026080100010f03200c1455805000443d4042d140c448842e5601001168000700c5581c0041036503120140015652510a4080700201c03942d081c0340b4500302c01d00c00b5109003103d005004072a12080000103001c1298407840c05e0401c03001c83c10080d0309104c2c10307903c09000c2c1d144090f5000c10003680400e4290511929402180350b01c020110b1501040c8400002d451003c061507540c041042d1000152061608220f917100f8101c0750801044020a280391040000d807519080546501c181c2c280000c42c03014500b0310007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 845427491 1250 845426241 845426291
    0x5040609050618070f030503040303032d0906242c040503030624040303030f240503071e0b070203030909011508060607030e0f03030d09060902090903070804031401 72
    0x43d00745444442c502c00f514110160b0407030b16502403a0a81040000c400200b5a020f5a07131506002c40d10801c0c00c0301e126040c4205205041031039100700035445296200b40c0c00115420300610081c001d6400740c0c40e101e13400d5401003040011034022241c0c20800d100048540c034051400c00c000403185100c4010810150880c01d48040ea015000001070054910f0180c1003180c1c0801600600c80c0408141c2614072100d00451101905143e124001900500c1d17031a80700c81c0c0081000b903010b0303076202c419410708140c40d00240102030003031041440104a00c04440104500440c4451143c039405d41000c07020903664004100490300362106000c0d40070a07540d000303202806800c0c80e040b41c0d21018248100107059a2000d0302d220700030b031820007102010a5000d144003c58400a48124034061121408280385204070380d0b540d6409032a04212000304407994000c4403045008a070014000e4035818101e40d228070400d10018443c601c02c100800c002441c40940c0e8241c030081400020b800d00011050028452500d04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 845428741 1250 845427491 845427511
    0x70305040f050a0501020a03050904060b071b0803040b0409020d0605060f031b07030801090e0f0303100915290c1f0f0606020d0e150a0201090c0b0319050406090506 72
    0x150074000d44039411011001401c0498079848403900d40f00000c0d40340c0c0490000501080b5000400c145140c0700d0341c210400600321088043d958410b681001c40443d02d01d000d0344040701000d450005040c400020580b016180940340d40c6203410300e4004108001e500c000041d214554440ca0b002459540c4d1002400480d00c0c0905066600e1030304100347d200708000c0c0c5c8000c21500c4810301c8068082a4072511075419203400b00000030701400300031501d0740782042203a0b1f8000c0d2440004100515088070311851811607000200c00d2081c090308910409a04041d4001c0b0120084c80c00c080d181c4000190707020f451000c051448491400d00e00b03229040c20110b40c0c001030010100d15041d521141d074a2403060701004107101404200290070200000c2d1101d00310107150042228202d1040600e0703443c1041845440040c1c50b04c999224000c0b0401f80c080c100807101500d401c143c042e0002441e48190045074442d82c0034812001ca42c4000c2c1c3c11800040c680500191620f039901c0302100c0004e04100312642c0280c120300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 845429991 1250 845428741 845428747
    0x60504030b01120b06040b0105160507060f020a0f0b0c0d110712030216030e030c030604060e1c17150409030305040b0c071a2a0403050709142406070305 67
    0x820301e0403041006030b11090019002d0450b21000c078208045240d0008411680450008000801202d05014104040b44060420a0808104600042d00c0d03405c0b1200341d1181c0c115200e20702c1080e41c5401c5c4543d03000c1c0503100c04102c03650000700119400e5a10a001401072410840721000c01c4044807000c425605003d5000904181130000c01e00c8803440555007403405610780b54140001e05255888241c0003003c0c00180b41c60301100340d0f828040b20701d61060203402c403809440d240c2044c202403d400010229076018005a21210b100d01518007000417060392520148480111030080c04e4090081c011183c03580641d110b008159070300e000e074030f080f01e000361740105a50809080c0a124410054904014510108405400919800e01082c8240303d20f140803921555035020f40ca407010034000c1d4040340155040e6005441491000250090b6809241240d848988440741081214142c211312050741042c1ca00251440d241045600518a030071000318140c146010003144041e081044100d0200e4004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 845431241 1250 845429991 845429993
    0x16150f0f1b0e011b0c1715252111070b1b18031912080603030918060d0611071505010501200a05010204061d09131707050706050c011802090a020d110406050403 70
    0x751405503007285148c81602c0b402e0000310150411000120440310a000c0ba210700c00c681039019100c1c04100d40e4003200244031308181941408841d0b4852107003201d0441040b07020541c0c1c0300d100c410302d000c0380ca46814202c0c03804005034211039500b04003404c419414810098280720008d202001100098860b8400988031a0b10b0780c0c014100a8004080c0341c02544284103400c401e548008810828420f402c1100783c0e140c50320000700e03105a800d0300c0040c145a040250003040c0e000c0600c0280101b5019031481d144805001d0b03152402d66000388160380c00640241034600100c1c80d03020310b040e8040840c3c0201d0310b12500a40d2010300baa001030780000c0106102c00c40c4440881d074214401102000d01300c40e015a00c1c5046988030415001c000341c0a00b08811441d803405a64142100b10341d00b994008049800141e518000141140d110003011105542003403481c0d808401c826800003511980140301c0302d0159108050803000390000031140c21104d8071007580c051800031a00c010310140c0000e9860f20340d00c40c11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 845432491 1250 845431241 845431273
    0x7030c020418150c0521070f032306040906050a05070e12030313080f0f0d060e090606191d0906010b16150f0f1b0e011b0c17 55
    0x282c1184140781034030080c0391900003446441002641c1580c040c0c005507800b10390004441500842a06003200d00d804880140d100e811201c0d030b94441e40752551103001c1d100c070301502102902c1d4060103402c4100a0030141190342820f004c040e03544206d004c3c1001401e02c0303181d212103095800c02d41b041210713581c0d03032014000100e5003c00d000711001340c15510349084420201c0e01607580e1000800301d8200882014104040050803c101c440c4902d111580c541c48d4401800500383c00c0c1e01401c45000050b2406d03000150b8450200d525030312071303070036074010b0002c964807941172200541c6800e210000c0b5000c0c1000200b00d1a1402d505014615822054003005203000e071a05032500d401a0022556850240204000042c0007001182d0741940000240d072101085800d400c05005110440d44501d810718010320b050464980c031003c0112030100310161118018030382035031501d02c44011140010248a032842070b41e02d051100c48071313442c4510002c41c50302c0d5070303005e03209450319948840d60078030b07002400c04410303e2030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 845433741 1250 845432491 845432501
    0x3020f0102030c060105090606042c13050c0114040902070303060533070f140616140403140705120d03060f2105010b060a0201090b0a1503240207030c0204 68
    0x602800154640190381034030719510641489940c4c4200d0407080011902d46414040d00c1c010181c001c514503045030074001c2549140c0d113007506039505010b2440014a42241824516800c540120140c00d0f0001e00a00440390042500315148403e0000c000c0001c1c1184c02d88001c3c0a4107000365000942203041c502003084e20b102404106490a12404507500c1080d142c2a441d00a030304194110b03591200c1618108865505c1da032409440c07000c00c130070001300505000c1044ea00c10041001409290710000c8070544800c41c1e010a14000c000b01440140002220440401c0c2c0c072503034030303411900b1940d40c0354000f0300040c01c0702e0461f0301903420990045000c40d425000e60350141c400c60120600003800c09200105418005246900561040b100c0b40700f441420360003401c1064002c2c111680d18000401c02038068090444112341c0022228001003100c15a88502d41c1e8070304010105000c0320346142c0310008540b03681c2080403400324000b41300340000f142c1d510081680e6482910383c0440d03030340c00340100b00c101ca03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 845434991 1250 845433741 845433769
    0x201020709020310060c030315090b0f03010e0c1201060302030a0609031704020d030e0f0307030c05010f05030609040f05030f030a06090608031c0c0306030215070c0f290d05100302 79
    0x50060040c00841c1642c51302d00d0b8161030080c03070410040d4015017030441c0582541c4130401078209124002003480566600120040340c800e031400150080908141400c031038400f84d40701d4035508200c031521030501d00040785100510178a0700120358a5200d07000a410100a070a04940d1603a513403040d403007019001004078190192200c0c21342d105103082c3c3c01080094012420003000c110a400d071804261342c1d582610201e00401608130b820054036403510800c001d6240c003880f030100d10100e13008290303107120310201c0b8131500b0003504e99116600c9a90f1404940040584102e0340e500061007000016000e05028511441c035045001c41d40518240d03141c0100c80240d000010070783c00130059203900449404500d00822500d010000304410070100c1140101141d4200030347c4004080550307044540316502403c032a42c0203030740300c00c0f1711036803807601c0c21000300c841c811110049009126030f820225440c40b07044159455410283c503149850541a0403940308a500e80180b03540c1c400c00b80309508005130000900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 845436241 1250 845434991 845435009
    0x5010e0c030c0d0309090f020c031c0b040c1b0f05060c031b0306060a110106170c04050603060f0420090c07030212031003021903020603040506041202160b0d062102010207 75
    0x664180c4c0300100002098041e00d84880c2d290b9042c0d00864030300e5411149141100400d40362960707841803510900701ca500360035000d014105000114949818841c8903100640d03511031209069460170750b00d040f900c104405455410005000101148007800b24a2048410400e450354901e4400a0f402c140d1200040400c040c0a0031b008200390307616001c044a8100441d803c1c00040c81c02d041000c2400f41c41c4907082880010004800800342000c005819524a58104c1c0c06100030b0b5a070806040d41e03a44211141c51040c0300440201c3c0210305000f070050425810b9000c04020340c007100d00494141c030000e440303406407140005116001d00d036041c400c03c50145d41181c005461400c0417804d1103480c0e82d480c0001fa05c80c0074000318a031406101c60042000031a8060851601ca03e06420540d4071900e04660990b0000d18100700107000d940f0101e24900c0840308150588902402c1044407000c0c0c1d0850862107508683d43d11000c03605c55000d000f4003c40011210144613500c0700751000a050070100c2d4022100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 845437491 1250 845436241 845436259
    0x506040c0e100e13062c0a020102031b07030b100611150105010f0504030b040602092b06020c0a052b03050402101b0b040c09050c03061e010c05010e0c030c 68
    0x3903251000c00340c008a4018100d8044140c0b01c1018480a40c08030740380041480346002c01403144121b82441ca003148100380325080c07011880ca80e078507d40fa0f2450080090042c0c108016440146c070002880c81c001c00c450b2400c1350200c940366500e080c3d2140c02525410003681390320f03004014031613020a00007000f0301e10901800d0241c1c86c01c0e400d2007203a40180a4a810f0041c13044403051550b01c200c06031001550025044540382c00c141c20840002c0d44074011590045070302a0070340c100143d605140341428500302010314910211500c0e00c0c3d00941014024161500070850024080b42c0d08101d42030b8260107216248140c03070a60050039405a401008035000d2501308000c000c090f07668800340d1070590100d4140b5021401400d0942151050710810081c03001d8050020710051000e1381d0044000c0d14a61203041040d500d41422010326808125150355003c01440c030103042d41c40c038500440101c520181000c02c00c2007800c0d0744607070075a01c8011400d001a40130101500700c83ca010010083c03160704c240da091407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 845438741 1250 845437491 845437501
    0x50f070c05061915090f11040b040315090f0615050d0c050d05030903070909050601092904021c020306090112030f0302030903090616020112230a020f070506040c0e 72
    0x1d1180310040c6440716030b80c3d581c00c800c1c540003030a42028a0074101010203001c030791344680c0c01c43c0c01040d40000c1c05200d24030b804200031900c44103c00b107c060303491074405142020b15603a1444030302d40010729080010741d2030b0044480003901e1011f650608030321031440426402c010010700d00300c00c2e4542d48100e109000f02500280803c0600301c0120550700c06a07200c080c078690701e0070a035141d4450426002c0d01032240f89000202200c2035413212003d03034412016180c10307903a540d10a40a0301c0e0b480000207140d00b00401181c4042102640c06181010060300160401010015a441407000004026030180e0000100609443c100c886140580351500c0003203141c00468800404241e036041d9001c06043c0d001000c6580510f08000741c8900703103401858250346089c0c1d02d01d4403034111000c2e4000c0307002c10400e004182080c0c1c200d00907000c629448460031003046210720a0641c00c8440501108140c950070030175018003101200007003001a009200601240c00c091074800d600c0445540100194005442401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 845439991 1250 845438741 845438743
    0x270a050901020a0c0b04050f0a0302030717031506090f09011e08060f0f131b2603160213050408040f1203020d031d010e010e100605090402090c0d090303050f070c05 72
    0x5043d054024013040004d46c0c0e03620302245040c245440300c14040c401c03403005004040e800001403441600c0f80c0360b030883c00c5032040c1e41002c090000395404403c20702401202d0b0954180707400a04401140180009140e00122000c01c001c95000e8000300501d45000d40028802210f000400e0010211500202184d00e04103140344045c09000d4102c44800c29a10040749940a0b52402e499815400043e4000000c00e0907100d0b400015040c401c0035402003200009aa44c5601a58168684900c0c0405035103021585160705212042c0280100da01036580c4c040e4520b04030b0b99100b41031041d442514647c2c3d0311401c0c5802c841d0742810b80c2d44140d5440803800203107000241d002c5a24141c0c4082c508010406030481509440e5614402c0e40d0311030f20750320702208102c000c0c1e01500310684514421095500001c00c0e90441c0050318402e000e42c07900100e074040482e0060500300a5030364050094142e090030308611100600c29a91609029000031783c0380d01c184202e0300da4002d402a000090343c10301c4044040155542 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 845441241 1250 845439991 845440007
    0x30f061003020906031f02030f07111510080a080c010e031303060f0921090b0c070311150a0e0a0f030b06040905010f060321180b0702270a050901020a 66
    0xa009000c4600419001c5d00d04210007010041c207080d08900800c02e0381103540094001315039418940d180f580216401e68001d2016504079004140544403510f2003554550115001401d1181801c548400000305407100b4840d40b480203205460742591900c5000c03240d425030b02500400f0556030400c00c82c29001316000089102200c1d4010004980d192501007590010310b80c20002030031300741c0b1080c0003103500001c06407640d054459907281c0f080401d0300c0e031000712060702500311088180d501001090000c14080117541981d10001850110411508680b03c041600303c19403400220315804158480d42c688220440060b00d20007011300111459901d40c8a5080f8028184602a6580f00e04590038403800f9005540c0511510005001c0c081e6685441131100c0e01003e411010010040d9102e4030b01b42c400d40050380446000c0015801e03542c100380381d03a0065400100c00720391111000313904105922050f40c041000400030050409507191182d006404d840c0006c1c00602c9503441000210740e865001422 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 845442491 1250 845441241 845441243
    0x10f03090201030f0f140c090d0803090c10050c01062709030c020a15020609060c07021c0f08040603050907030503160809060c071a03090c0f01180f05030f061003 71
    0x404580e0144a00040e80104440071424042c58104986001c0440d0150072044040300c007203004103010382c1c8030762080d9218010703c03849542c400481c0381034902045c620400f46402c544d010060702c010359400c03c0011006d0380c4050303c2c030020801c0402c502c55858020f00c80d100c0201190440040581d1040040e04605d100121491802994490b10031302070502c03401018409a030301804440d080380c3c035010500f1808552140303400041c840d40c80068440080843c040340140000d801c51403c0811640c2080341c80c221400071580603002040c041380100343c0303041800680901070320032140e845003002c000800350340700201300303032318a91020b4400c20001e00c0000c1290624108a0040c5038040041d20b00061a84220741003aa801000420180c000760004180c1e101250705481c0152490301210101440a010442d80d044454000080e01c0d4114200000001030300b143c14502501111b000c400105541110743d0440c08181907804000d000e241001c21039440055a104011704c032a107455048070382503103102c0c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 845443741 1250 845442491 845442497
    0x20a02040e0319120c020115030206030613110d0e0a02131802222406050d02250c0617130512030114090a0504020618060d06080a05070602010506010f 66
    0x181000c00c0321814000c3d201aa440403010081c400340c440001003103030807582e041052280c075103101002d52900500ca4500851250088446100e2642c3c00b0454613800c02000d0507080b0b0200400c140c2006c60a00c143d081003500c0d00541600e843c1074110b1a022540c4820310520181e02c1202d42c0405a80e50917280441d402c1c0300c01c80491500d07202010401e9a0100c1400207400c1080602ca080744000f03071090f2110602c0a0201c1001080080c20420640070480031004071000179202050003a24403580c010001300b640b003400585010540c0341c0601e0b0a4410442e50140510488140d0080080b1001c4c80c0340101410720340708907004810780c45035044035000b03026444281501c1c05050100725084c08408003442c040d16220b904d85d0f965a0138041500e452031101c0340b2606940002502c0c180c07040c40351b00d00440e00902101c0c10440007031128500d0100781c0502c03c0c0d001784140641c1c140d003102030240f1005030507190058240540340740703030140c984150b9401070380940e4140001c000700c80e44c0c4182480f0300500ea40c030b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 845444991 1250 845443741 845443751
    0x9061d0604050403021f050a0e070f0312140f0703020735070f230102070308030a020d0b120c0f030a02030c01051c020a0503010323070603150f03060905070f06020a0204 74
    0x129090b0301c1c001490044031b030311980e50b50914517251410b9001c50700c5460290420302282040030507460700c4540034010a01d035207450b40c109101040140100343c0002501c0c0c10300d94026640340101900c150040c99852401c58000910325003016414491200144120200d46240001c4e40386540c11082200e048080050310081e0514542841084900c0080c00e183c80702c82480f075190300c40b215146061000c0b03e18050780041010000794030014001c008c581d040007003682540c07105034584010f5071244001454060316100d544546590341d464220011114000410f6015010402d1241400c440b040b158400e400030034400016072408030f4030301c40444003440c00705e50f9007140705000307800c03058590b9410b40d17854804a031401801c0c0d0030000840c141c0e40600a401640e0019a420154000c02500e1551554015400400c02c00c0e01940040020b180945803080e01103890740304c242d003403083d26031081c3c1e0503540b104652018032409000e818040e01400001102060134490b02030b5135600b20075402405160f880d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 845446241 1250 845444991 845444993
    0x60e040903021507030501030308180303010611030d150501090e090a2901090b010e030102030907150311130e01050d031409010329210a0206070606080a03030609061d06040504 77
    0xb0f1101d0552840d102002c10200e00304100c00400400b400d010460110303011102048101d50f00e0483d890400700c02c1e2000310725583c00d0107002c494012200d0a00c41c05488280034040030b4210b1400740c43e03890b16224140160691900c000140b1520301076201e819182000c030305010720081d01003a14080355400c044504552610603c2003080581c0d04010702d030800044000115241460381c01100c007103d800d988074884070400200b01400c0340300aa501c040ea03948060401c010f5a6482c1c02006902446403c00240556481010510b6940480700554807003555004c14001241004942405480251068826a0110340d4003800da200c00000c8030743c0c00e00c00405d50444036132007070f0004052000c0c2409041c04041000c0d655148415034030380450700c01e810680c02880c0c0308401e13103140201800c80200524094240d80c0034400301e0b602c584000e0701c07010340300e150100354800e04005c036080d400c0c8241d500259440c03500540000300d81881d00702d0054044d420040301d501210142000381c000d4800c840010f202c0d125 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 845447491 1250 845446241 845446243
    0x111071a0909010308030610080708040209040305090310020409050a0e03160204180503030601030c03021806030612010c1e020105100b0d0b041d010e070e13050c040612150501060e04090302 83
    0xe41e54001d6100e242e4200201c00c020251000d98020f440a03108000c88000310001560300c00e10450311100010b12882c00a005071804080c815007060080c10164508012840464200744011005084840c0c00040810110301513100340c41d0700500e10b940030003034407d21523516a203a02c502c0510a0f0b402408a15403000c0d0b548540c0809481020200d0b5020301c0c004520f0095100c6d0401c0790203d01092401e6007003d8101c0c003a008a401c4600b4008881e4185c02d098400c000b61230300003802c096003148031403d49658440c0300340301d00c200c7c1c842203856525949181031480005029511811021641082c061008200c8085405c4080d01c0e401d00362191203420080c00030004014400c03456a2150401c030f50490203c907580d00e150000c034141c500a00c044052060301c0b5544011074400e0820340400d80000a540e0540100814529031041007641d0380d481034800010181c455039004904801e14035610b01c1c2c204040352041c02e0401c1c040980610480d07241000261080c07400210132801147c0b030350004010148 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 845448741 1250 845447491 845447497
    0x302040f0e0c22241d03062a03180601080304060e130e0a03092c0c0a0207090912030f0c0906031104050d0c03050106170c01180b21060111071a 63
    0x72220201d220298109601c005080e0300c0b0040d2400324104c402c0840c5c0c00d441011583c03d50307000140c01080180c8605644000c0680d00e0301c1c180c01c1034446040c001c5000c200071001103000d4021035003034903070103e0360070f06680c14054180d001942660082004125031a005105058822001c4507501d02035800c0e401d842c000f420301001e40700d4850242c1c41400c0b08161300701c00070806032940034100350b200c10205001c1d1203541041803840c0f95041b80d04000106003060030402440008000d10664025541d120112000c1e584001c40481705801c1c8645150b0b0007503418400c0d6172400504034820720184a000c20042c0c443c540301c0c040c103002c25271907452003d002d420b01001c4800800014151000da0100c90903c0c4161078210b0104036202c0d42010720000d06608041c010210300d0141e400503100d140c502200558442e0342c001446840055a01c0000506003001c0c0d004d4040e48040da030302e044645a54a0010b0002100209210305028610070517504042000460401361102c080b1031042d50040032030728000747c1c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 845449991 1250 845448741 845448749
    0x806190b0628120905060c0702150f04060e0604150c03020102042630031005091302030c040e1e0c09040302100608120f0313120302040f0e0c22 63
    0x404080361010010945580c09951150b9481003d8140b07010700c008155024048040d0050f03000d10040b0b0041038000b002086002d1004140c43c4003400e841201c0c400da500020000518640c0100b000c2001640021000700c408070110f521500d06810428a4075240181c007141004220300114940d0406000b54102d07000341401040c032806881c0c441060910110003002864070724041d0035108080c0d0342900c4201e01c919240340c105406549810092111780783c0005022401500c3c06540004d031a8a07034021203402240048070400b40003995005152a101d01480c0040c003c03490300c484d00307003014804901c1041c84882c2c0c524048040004080b95031502d840038100542c8030700c8010611041580026560180321421581484072075650380c40d60342c841c0c41c90f62400d4045041006440d0307400100740011940080c08a00b0312103010303001d88400480e45101240345003c690b000a0500100d103e00c040700c030083c107841d0f08a451380d262190b50a45540100c0b01c8807410300a082c0344001c4031603180c8900c40060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 845451241 1250 845449991 845450017
    0x409050303150f0a030308131509060b1e06180402041a090a080606031f09050601180b040b030a2d1b0602030a090501050f090a0803030105030105010806190b06 70
    0x3400c0444940b008180d0035521244910400303a00082030741002c440d010b0449825031a03174074440ea01d81000345030305c2107890411100c500780035060011180035841458001402148001041c0300c010060100c402160000100c400900c90f0142e031650b502e0000300c1c1c09051028100300322040200f030120300a0b0295402000100014840c041e070604c000b8405880116004c889a040503a903909020740c8650050380c1c1550181c00108007030001050709252007600311000c00000031400307003a440700350a10b00c003070700520f1504102500c01d0301034004901038200c03101c004803000c008002d01200029610503a0640080c050468880c546403d00e982c1c0350821928a9600036260b4100c2d40f82c68060700b4911080c40e03001c50008507035404601c01d48008242c07003031124607880f0015480d003060015280d94200c0424011310f100c04101c00000d035101c5803151001030034060000c507200c1d4101804c02d82900c0c07050b000300c0308540c082c0d010811802c05000b00c0520403942c94600080c1d24410f04082406441003c0b03a092034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 845452491 1250 845451241 845451247
    0xc05040b031302211510170d0f020d09052803060b011b030c0b0408270906060708040306020f04120b090c0603064509011a090a0b04090503 61
    0x190212001a01e45a188201c48144c08010840c0354010124201811181654450520200000c02c40d1200b2604500c01c1c04114401954510a10002085807151040c907a00021300b581c60b000d400c0300d42d250f00422070380050214034a003002d00416025952080d80d10a82c03012240200c020150300003404024826400030741d0032912810004040e003440d04041e4000b82100076152192801060114900741e0f1594a044d07601c050b907195401c02b8200503006440b800010040c2c44503401c05482c1510b1220000306030b41003410301100810046c100020100c5000d16000c020200000d401201240c043d070764040f20058440c401802c0484540c01150002d0b0342d0442200e0b01d0f54180300151114600c200e800d04200c030f41111180c020b00019000c00d80c2e800340c0004012410403c0d602055503100c4a2a0b03108402c0e50b18441104a000c1c0300c02030226400c6118002d820900120580038015070700303047c01e0400790840911410005c6409080000d09000320705646442540c4250b565404c8405120b410408480e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 845453741 1250 845452491 845452501
    0xd1b08070f1b0f0f2904020904030e190e0c090a030201050a03230121050606040c141b070803032802090d08040504061a070605040314070b060108070e0d03030c05040b03 74
    0x10807070b0360010580c0d40d841071a020034180801050480d05c40e1111200f0100b607902c031507082c040c034660003500171010f0000840400071662641d90100d0110364001030b0004c0020b14004071080c2d44c040284c01b40f03071464030410039515140c840c1e103041d0040b241c0c2864400d540c0c94200744114010005440c440c0e121074042c1c054600c2d202e00c400701c02d605940f0a503110b900704c12822a0411500c903032400004085400440000b0300619207503200c07500da11102c0c20000040300010050150396400090101e0079185000c070004101d030400c02072100a07001c0600110300e9030030b10060701c0c484440c0c048860f500b41c00131421013000404841c1c068030030701403003e003903a101048c181ca010503e0760003500500b0700861615a00282403a000c0c00315516650b505542545400c40c00c0c6ca075071024180007081a000d025104501f069410740c070784000c00c10305000d46110071040c100321b40010aa5140548064208030b01c3c40d80c0c41043e1b0b62544070440303034036a0500b000680d80301c20742002e0b1800d01681d80311011400000c01004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 845454991 1250 845453741 845453753
    0xc04090f0203040c120b0a05100321020d0807050913020d231003031e4515080901060503120706050f0f0127020d1b08070f1b0f 56
    0x35008138070401c0880b0103d0340303690b400300002c1c15100c00502aa00e842004c20007a000b164805031b0050089010030280325180d4490304030500c006061790590000b441040c420417941030045d10641482864203540c1424040d0b001002c90107240c41992081200368214101100c603941119111401391005000e00c09520441004034402d102e04000c0c802038980010f00d2110040400c103050740c0d07264072107406010a119030441c100c1240811141402600098101411014030800c0706080c1a547c4100c0d000c1013256245451080c0c426041c2103c445180d8140000ca07048002d0702c12400140c54241070756a0b80b110501e02611956110300e03014050320060701c0017007100031b004200300b902070705082c00640c40b00011110440c10403114075448002c0320005000c1c4401c541004d00034031a20880c440102e10075086102d080f41d218081c2841307000e65800c100000004042d041d44004010b6041140700b518154030050b0100c5500074214041121000200080b5001c03170059103111604544040070302c00c4149803603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 845456241 1250 845454991 845454997
    0x1d031b0a140d090e19020f04120b09070f180506032506020115050a0312051309020c0f010902060d0b0604030503191101150303050a0c02031b0f040e070e0c04090f02 72
    0x10070005500220046a28511084014040d0b00501540b85c034625082c420035000303420000e50305074201c0c1c040000242102c0701c00f8800144502952160981d810031190300d070314208c2d03958042da0f503080100b0030401580c09101e0551503441c149000c003203038aa4540e00000d00b055000c14132405002030007078079407080e2140700c44c0100c192101c0d07400030002d81c030301800c1240d010650742c03240c035501191040e01031002910100c00300900b006141421802d05100f216a450010103980141d505d10f07602140c103080715101040001c1460720044000c0042e115150041241807280381490340159407030701031007a52911003c2c111001940c00409480c2c89811700e00c0014690003a18071b18100141c0d00c03551b01d6020010612030340c4e032122a80c061161801e40b81d940d054540790003050b18141800f510301c40000168a090004c038602c0750b0f0b041c200c2c2d040c0c050810100802040c240c0c251900462a00b91200c0c0c400304005000025122000342c0d188482d034402850704603612440c1c0008050300d04200704610782400a4010b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 845457491 1250 845456241 845456263
    0x60c0c010b01090b09012001020703020d0e01080f1f0302180f010519140f180702071d220f05010504020a0501050c0d03050c0c0f0a061d031b0a14 64
    0x280007002103a8011240300030035002d042a003010401100300d643d8041c01840031840130540e100f80a44204041c074a089030040782058000d038003c00c1c04205610f46c0490300840f00701090070640c285051422011660300710007000701d6014001c06103030803204002900c010005581c01880000f5070b540040300c1d4040d05005484039031040c140030b0008205440d005460000c01001c012564840300d1500005105240c400102e1076007040c9a902500d0050312007540310b4803103101d80f2051043e181001c1900a16101d015484212040c450b4100c502a94000c40b0766203070840301e4410422240802010036000d40b04c80d9400c000c0c90220180c100d04100881900914811402203c000c0c5c4540d60351401501c051146189160003030700142503da849a0080d48801d07003011101c00003d06000d80e079a1310902e001c80d10044900d083c0d010040d400c08220041c0180307100440c49a4020b0032040360002c416540340a40c1c42c46601b0b480030301c00c042c0707500300007000801c501e5504001c0c588000c04103d0501c0b0385503400303d10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 845458741 1250 845457491 845457493
    0x406091407120b0912181c060e06060103110a111608150f15041a030d03061a0906040e04081e030603061006020c011803080d02091f0c0b06060c060c0c 66
    0x3001548100c800b0a90800324658824560301e070950301d0f80800c03400300c01d460080d47d008921030505240a070009800000841c803071000082c50b1001c440340d180c9401402801c1604041c10805900154001002039034451b062904100707a0507074401c0e0600c0d00304050210810b65410500400140100d030020341e0810f400034402d030b14502d60b100c00c0c80c00980204115085076000303914085000003420301c0e600c0010282d8a503040c1c86002101f0341e000a08256110058a000949403032007131108244660100750200004800c092510800002041d014095481060758141c0c1780d0000a00b4040c18804803000000d032800032040c25210a80c100310709070010386156019202e1240060513550034540e0305415581650000e000104082c001117400d1805c545840b01c3c911001e0b03070f00000191442c0040c18855940001c09a140c0c0c502000780300c0c440701c420210f101340d62a0a90602c00460300304007124512604103d400c40c440c0d5070340f0040348442c419000c9400d0584130780380811900c0c90060000d8044003281030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 845459991 1250 845458741 845458763
    0xd020909010e071b030c12030b031b0d230d08042a180e0105090c0909031306030b0f090a1e02121f080714090109060e040609140712 58
    0x804001850402c90b880c8010407015200c40700c44203101100d000d0124803a02c6c000c80101e00ca0365484003032503030790300c00400480e072222461510340c40c1c140840d013040020403010b20000d01884000507009130010401070f001d019940c0309440c810111002442c12030002d90210b4801d004050b4004152a03401c440c1910440b5107030f000701808180c00e400c400e0140c0da0303004031074482c0c07410000b508036030f105001000c0840030740e0344407038001d281000c1c041c0c5403040712148017034110307001b88405012034000018514010307a00208160250061903c541e03006030740c4180341c0041c4041601d07021401010040c202641e000c8500d40c00c21549808640019000d40d402ca0905220106050400020381c0138036201d0b80482d510020003c0c9030060280c1c8041c07a50b9030f50320b94105041d035490162504020281c1c0058010318141c0c540a80981010a521030041800d900d0802c22545080c0e40441c001401410044ca295110b024a9003032010705c01e1440703007095201098614140e500c1441e805c000404010481d4075400d40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 845461241 1250 845459991 845459999
    0xb07080a0510034407061107021c0305090a030b0604200d091a040b07030c1d0d020a030c0b0c010f0608062a0d0c08130c0603020c030409020d02090901 66
    0x2e840c2d45030441c0c2d4400e200c0f80d00d800c403c4400000b070180c00705201c440301886180b4500035411004948003180350440e005580d03081c4505040c002c0d80c2801000c408611743c10013424006071601d6500b1501c0d44c420100142030b040c00c0d45030451b0b180c807034080010f43c003004014000c17061020316038246010b088100c408100b07107941c03d18961000090000c041e881c1e01800d125034683c0c8002a00543d80e0544580740340000d81c0d0320100944003c00301943d003a80c55001050420290720340511a80e50300c28994204139a007440103004900401115205450151400803080d40440d2a10f000f80400345501048540100343c41d0038100903143c00030a01e207082c40d82007600c01c2c565803415104210543e45c07294041c2034a070759030341050201c501002114181001c84820071080745481d1502800480c0504907010800c010413900052030008050000d68a03c4a102403074000203603a01c2c2c03c9012103006d81000741c1c991100c0c1500a0035801707964081c070071590000610807208038069000700364841c0105d070301c14501e98031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 845462491 1250 845461241 845461261
    0x3080717190e100915050d0603060902010807030b090a020f120f19020403150e07090e01020720011d0117010803032a180604050628111f06030b07080a05 67
    0x1181c400c0f100403c1c0946130a10003003030b141c50721100c50322460500f24a03151681e014041101c28680c02601d51030b40c1c0703400b200e00319a07104500b1500040f15140500010110300d0005040b00b07006000c0c00c000359070008000c2ca0201e956000c1d01d580d5460f01049080038a01990580b000148c03c944400e20244a02c4a054202046200b0b41e803e61390800d00505c0c0d0f130301e0380305c1c516001000b003e11010b10600c1040301c0001c141215020380303c00c00074614005a21100941742c2804640c10b8521007142410072024042240d0764000001b0308049400c2c1201105598070200594400d40030345000c940703030182c00c1d00120300840300000a42c06226401c681100c1d644810f0350000b50300c40711450202d60ac410821840c0d01e41d41a4901c40000c102009181c3d9191a6440001070b400360700420525251510070b012940d030034000c282a5144220540c1070002c00140580086500d5088400c56a00b0078084041d0800c02d043c419400000a10b500c0b42210340d5034189000c0180800302c085501d8240366080400080a81710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 845463741 1250 845462491 845462509
    0xc020613030b010b27030f030c011b050f0a120e0d0e030d08040b010e04020a09140601020c030c10050706181401240308031b03240402040f03080717190e 67
    0xc030302e580000c081c000e00d45c00c103c42c001c1c030400e95458072880051901924050000b4054031184400002d940e05404803010541200320551406200c0284804481c8002d501c0440b00d0040c12460022680c00b4001902d07001841120204041d5100d030200d80345080c0c7c0c0242076041d00e02022070407288050450142101c0040048074002c10210b114001004064a540c90842d0020b20041078680c6103900c901202003180c10810391a000c110480040c4820f950b01802620f690340300560242c10f1368000d00000c101002c900d00f00c80810000700003424410b02042e984610b480041c1c102200c0010062401c016110721a5202d00078095440d15945120346e1058901c90243c911000035800c205510315100c41c0c0c0c031b03500000c000804440440b030f04108980340b104015845658010a913a4016501901c0d1010b808e90720204a801140304100500c1001100c0c3c2900040b06d41c0403001e29a91411480c1c24440004210f92165400c0b801040703c8409030710704416104561019580c03c0e400c006100100051a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 845464991 1250 845463741 845463757
    0x1101110414010804050a0807030804030f110303270102030a2a020705010c0602070b010b04150806090426071a060105070b0a020d140115080c04060207060806010c020613030b010b 78
    0x50180089181c0c40d4001d0004076441401034055480742c10190300c641510360b20842044000501c0c8004000c101500500fa1103003c03d200d10340307030210340c00105005650b4400074001480e00c8000d07411070400c050600c01c0c610100c040c0c4800a54503418041c03032100c080c0a1825044041400041d6541350701264801443c004035016401080c41c0c0c0c0c50702c0d00540b081d091400c02991140e400300070741d034081161031032090f00800d030141403982e5852401c2d075003043e002e1480002030100001e41c000c2c008142d451546080e002500007044c581c1352002190032031001c2c0c1e1548180682c082020034090240540800b05003d180c0c041000414199500e200446880c49015070003043c0d1920344c8007044c4045601d50240c0101401090000340214864011441c450707402d0f845101400d1226801440b5194800c0d1101d8200014240c41410a4148000a5200d40d5540509410423580c2000150240e110342e0520a0b87c0740c002d03042a40c0e078400000100d011f860030703000558044a80600001d107044200080b90f05031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 845466241 1250 845464991 845465009
    0x506010f0b0712080a18050d020d0203040e0f070903050f0a110906100827030c0c150307080a0f061d070e0a23040c020703060b06040e0c0a020a0501020a11011104 71
    0x40c42c80c00030f0540b041040a850010307100e90b1802c0c03000507110380e10b0040f1101b602030002010300000000009180203085694402150002d000810000d01c0d000411900b102e01190340c2e008940e40c1400c1201c01182590000d0724502c01c244c092020075002103100da2026028940354407106e4440c0e020301c11641401e44085070001c00008401c000301d4400c43c02c15800082c0781c0703911101140300c1886035801c08041c0b10450b085400016504070140d004200d984081401910110300c1c03103041da1581c01311804000e00e907506106c80e13400000c0c06402d241e4030515a51303061120811190b0b403102d185452081140c80903d0420001c070000c1030f1502e00401c021240d049009119542c0c1074101220800101507900300c03441d1034801c180c3c245115589a010700101c048040e40280420780c95800c012090307880b5000401c6c050001048180410078110400c16800780c0e8030601240c0d43e02100804910700849158060410751001c20003024640d84107803000701000130503000380710400c8001440103413482207100b18074203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 845467491 1250 845466241 845466263
    0x3160b1609050f0f1003020901120e030a05031306090f061a06031807081b03070902120c22230303091c1b08150708090c012007030506010f0b07 63
    0x42c43d001d00c00f100310001c09025124618800008500c0c83c0030204000d1000c42e03000300e00708545580c8100c59510740c40d039128051002c1c4e0f0100d081e40e0303264494100d403003080040020000f04151915184050010f44c495400c00084501d403c265480c0070071608202d804034101000c5000e0125034002100381c211008104a207541c03a031500521306010f64100310f003214003c1140010ba801c509000311490803081418070b00b139888600d4101420a900d541041a401d4418000e0750405081040d940d903120038645000380d943c80030702c4202102c114100107039030b91000d104540403801d8030400c0d10024084030424403501d81e940b0607100700b644901a1807903003034000b41400c401d924a00e10415500203144c8c002c110803c0c45103004008a400a1101d40080d41c0355807050300210322100c05540001d40c0a9210b107007540050030108000e17138844200003811810420200b00076404c00c403a072140c0d01e90328810f0204481d092039a0b0b02e00703d5100d1409101d40131405031340a40010718022540d0480b00059480304c0b285d05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 845468741 1250 845467491 845467499
    0x207020f010807200f06090303100f030506060603061c0f05010c0908060a020a0e130605011b15110f1b0706050301050102102c1b0a05210f03160b1609 66
    0x40c0c044220713070f0303240d40714070580d1864160340400f40406401402c42c103020315600e14200110340c0c0086d07100d5100d0740f11004400000c00210f00c4c08606190840011034619540303465500014042000051124142250303080d4500100b24080149405103031260000b4001d030103001c83c00b510003001310300c5014400d402081c00a100b444080e8000c081c1c152060902c0ca1142d50904c000c2108815481c8030940d9842c0d984906018541c1c01020328a90580c41310050442d02200c2e0791035103078421041d045241042d4855074103a0b003008000341558051001c254a039500c1d145040006d500c004022200c4038460b000e168408501c55124108980c1079483c180c0041804070a10213042c0003c0040b03c441c543c0304505500f80060208000d20000f043e01504401020b52000b51910003d46c0302c41c0700d8046100d2140b505003000745071624020f51030f10104000d02591000c440340f1803242880252280c510490000251a0080b142c91200902d1400c0c02511760310391564038040c102c404e001d01515050081101440200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 845469991 1250 845468741 845468777
    0x906090c060d200c060906010b0703111c03020d110315090405071508090f0d0207051201060509010e0117010b0a0e09031e180a050604090903050f0a030207020f010807 73
    0x81d11000d0300c0030004180f000030002804a4000020210400800003024141584100022034110350407502900302541742c03040c41c100500c41c9290040500071a004090b03001841400311150480d650080c002c0c00c5891184000c000750b00113044d040c9414508001d56030042008001e8911500d0390012443d0310901340c40800403141e000078001c40d060b100d45000030035070314650a460350420340d0b29101c00c9600c0c00d041042d02d040005c4114810000c1c3d01040b50f882c600c581c0002c10100700c0328141c4451445107140003d080c050320494210907084910807000046030140301c00064102d5454086020807080249021401d803058a400300c0d9109010b5002031010b085040603158000100e40216460f024200c8400c2e01c1544808110400d0350301c000c0351000408600100182004800b101d07844501402d041c00a00240110302800300801e0303a0b9401c000405019030112909a08516143d940340d050210000b0701035841040c0c120700504060300f80482a501454100b4043c1905894214008080d101d9403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 845471241 1250 845469991 845469997
    0x30112050a15020d0b03010c1e030608060c0a020c1503150d0b040c0e0603150406180c120302010609140403030509252610020721020303040b0906090c06 67
    0xd95150140d07000e18000a01c04240701900107445400141c0c44120580c0039204403206034001c80e0080c0d060042d40c0c0700041d03000d02e10001c0c1102c0d2181254401c5001c1d40210010034213600016071030f10651040c09403508400d40502740e01d000c01c0c1e00300c1d502e090952041c00300d692104003034a100c525050010030189031103070802414802000e80080186a480d880e9542c84000c00c0e5070940b042c44a14405200c10311002c000070360b001d0f50540041850b011681100f601280008101078482996880c003804000000075042d64400d41125042c650707207032506c0d00c000d10034045400850140d8070380840003409100c41d00802640c203203000317151810350396a51029405041c00400100b0300d4001c602c500700208030080d1205120354501c0004640d21814004465184074100010410b06440b07048008494000064486c03485154004003684800c01803800500a05048800b4040c5a042d80010080c180d8000b000e18411400782031000802c1d11280420341c0c5810054405405540102c03041d000079003000c00007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 845472491 1250 845471241 845471243
    0x50a0f030f05010617011a0702120c0a0303050406090e16052b09150e19140a0803070e19061d0d1202120c0d120f110301170f03030112 59
    0x82040c0311440c01050072564241c0061012441504440c4080b80c6010907460241c0200c140c510001c00080c001c91095000d50782c03009201c2d031309881500103c050144083cbc5045540a49404c0080e91070307142c0078015801a00034400003030310322100041c1d2507403c0903607240a20080c04000e004898040b00c1140d5a6214806c1c41c1c1940c1e200e008411169104501e4026440d40b91404c0002d40004500d8095078001c420710003000200e05140204420880100f40411825035103074442c0c43c00300c0140b0b8500345c03050342000c03007171018001c0e0040d2006000c6032900031071242400f035642500302041402000000c1000b2090b03045400360003481407204038021200c45216548000e541c054905103080080e4050485020894282400104100c56682c0411417010064845060581004080b5641c241e65086442c89131080040802c0000d07c4d42c035003607202c407540d461180f0041c0030014801e0392003449039100b8800e0a600b0548030b0b01104100201003080c950000f900707809145941d1825a42c07081420501038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 845473741 1250 845472491 845472497
    0x203040809090c04060e01080130050607020a060b0907090303051804023411010c0222091e0804090e12070302010603151a130e15010e070f050a0f 64
    0x10541c2041d80d80c1e007141c588a020202c403440c1d0794905052004040482c1c03e080d56040c4985a801030084c188510b10010a090b80290701035251510741c540b00107030b020301c950041c0107405102c040c001040e501160b1458414003d400070310900c46140b05220148108491110006618060a0000a118000034081d101102e1684100d6000b8270300058201e070f224441143d002d40943c902e5500c6910000c03007444e8503604404650115410b1030b00c03800e070400e000c1c4614604010300e0800c214219641c540d000135184601c1c170422a0031600121600c0c0040c8001c036010360700003d0480300003500c104104540d90840e58024135980c00d1174501703010900607000310101c220240c0904403000e5a0b0103007400141600754000d03400070901c9451800c20664150403900384130005401e00c4101101249800700031155440c083c1c0d0141900852a400c0e47c00401c1c1000c2804081c3c0141410030030109843e40e44203050760080108410a41c0b40d07000151090000c0031031120104006100d00840b103805014804000070980c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 845474991 1250 845473741 845473747
    0x2130c090810090b01091104031b0f170f0c010f03050603150702030a0806030313030201080601171e06040b01141b16140f060319020c010501060804050f0604080d02030408 75
    0x8480701d41400404010094101d43e50034095090004600c0058010720080704100041c80d249405004a40305071f000c040d007500600059082d0312904040780340010003450741100d161a071078100449906241208480d9503118201480414a0000c25004000041611000c0361380a40e0b080950140c50010071035039150056824100c5010072046003207105000903400fa65a40c40d038600d000d44084005000f041c004e60091010200c0d0034540e00e4580d09885d02420200b00c1ca59903100101e076400340384540c04240c0d203411821b120b10414038690f545180c0614020301045580c0d140d080c842150b04000b41c207400543ca8a4130000c5081912009204c14600d40c541215543d58812002d454201c60080400102c905070200f00003455075074a600070b2540007200c1b0401d0100380c810000d00c40d400b01411183d41c0c090341c80f131041428080c5034100d804000f02d80b0000c2c0301c1c56940d254081c1800750115010780383c4d40a85010104d6441d0040b6407035200b82d0b40580e03054100b90109103a50300a400c014400c55480c2020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 845476241 1250 845474991 845474999
    0x270301150f0513061d0f0106080103030801032004091419020603220b09150a090b150f04090503090a05220b0607062a0e060f0d0603081804150302130c09 67
    0x20403440440100c1c28480145040c102c3c800d101b01c000580c010320812400c0401400042e070312400a90440350080300d89118810700140383c0002c0b50307465085070343c46840c001d0300c1404c10030510a200c5c04000030100b42d41850055125401da0540c042e4030003507014408000140d0220560b050440c03040c10701c0a60f8a403030b12010746d641800c280f41601e02621a6010343c0342c004031000c8d081c1d0880c1d400740d4004402c0c0030440862f0b4900404420107070407050210015035203590981c03030b02a041c201c00d00008006214001d5035040580d101d91000d401540103078184500803402c7c3c2082245000101410004420040b8250b10f01400420071424440e0348900c04218003004281075000701031403800c200e007070b03181c003d501444d401c00702410741d081d01802d1016000c184d10895440005079010700f0440102c19540701d0040f6181c3c0014182a000142911701c049026408440706c1800590040010f8904001d0100c44981c0c44840c08101e11000b903002c00091600c05030b8136034507003181d010b580190038850303103841e26 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 845477491 1250 845476241 845476259
    0xc02031209030906180f04111218030a0905040b01020706021c1e170907050d020f040615120c02120301060509030708010c0309110a0305030901080903270301150f051306 74
    0xc15201c20118500317203180c4043d1400c117080300c02c00c41e8115410420103000d044100d4290081461011000345023130000b80b00100d00b1807080d01b006403507000b0340750f84034140c42c1c001c0c001e000140605400f461070111055001e50001036034800b41e03449034004000c401d1013440140180c6815144002c10840031150700403042281c1d03d113044680d28582c03140144170000580705103292000620582c100e43c400e00e010004c1d500d40ca40703184c45458041d00d00d1490349500c1c00c08200600030590001584001c4a90750741c1d11280e212140100d401e041100034000e08440b15412a911004150303ca62144010401000302500440c014203692801a0036110703a40d55401001c3d003100d02082e400404640c80310031220420082c8100d1000c400380c11902e480f421801c40e01d40e5540c80c098051440d05010b619004504245020002d440000144003400c41035000c0392a0140c00100402205602940c20810b203180d100801d60340200c2911381e120044d90b007640c0b1b000c0401130505003000300200c02e1a07888101142c5000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 845478741 1250 845477491 845477497
    0x218060306180c0d0216050c090103080a050f0702060313170403150c03090c0e100504020304080306010f110d0e0a060302031312030204090213150f050a03091703090d030f0c02031209030906 83
    0xb01082d8142141b2401e81801d42c200400310f9603161060101000610019038040c0a035600d44005241c9262612480c41510084d031007a0600658400c0c1c02000700209600b181d2581442c1e00d01c901038413000780c1000200c00d003141c0280d0000800d10a1040c0d985810000786900c240b48a0500b0310b008555007031240c45004403012246c00808112107088100164134920101d810000c010a80c2c0441c80c600d4151913440103400b01900f607a041045e860043d60040b8490000039a00c0013010064940c82405031001410945c00e0401d480d00680d47e2600000d000b038040e1094070721481258500c08805c25080d50356041c0510080045410b0503403e000209007605680b02414000840c11075202a880c101040d0940e90740700744400d0410441040c0300c00d0f05007540201500d00303114203814045a2402c0303524183c0301070316074211140751205010040005010700000c011400f20f0040d10308001c100c0000c42420103a40c9101c000d080540d104205034014041c000c2c41c0c4c240c0c00390721101900e0404d440741000600d030340c2c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 845479991 1250 845478741 845478757
    0x81308160c06030b010c020105120711030c010e06060f1014190e130513030e0d061e14070f1d1c031202070b150103060305100218060306180c0d02 64
    0x8000300144811601441044413481c400d0a00004074540c03a400203003540b00d5410000240341044c000704001a00078003142c41020300b02801ea0b030300d820708407040341c2c003d00c541068140540302d4070b4045281410181234400c800140946400c0c2c22038008001681da040e00c00d1005040c00c64100090b84000d129041c4031555070241d555003444440d11030081010b41403026600c003061a01e800207101e500441300e41501503080e8142040d0002c43e07401000210000c442c14405070490f403c0c00b000c00e10380100410b00384a0304103c260104203005030403102e050381c000c003121050045a221080c91594a02030454506000206541203c81d5200c0c84007184c00004042e4020100800c0900348070101a000f45a01080b60158442141080072649544d1481c50340a0140d515032003200c0a042c00d43d034400d8024070040c0d50850100c1d000d045580c02d0010081d40000307085a284d43d03120340242100d2070a44100d0340150401000074800c003100e900306000442c800382119103250310402c43c20103101c65500180184c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 845481241 1250 845479991 845480003
    0x3060d0b10030b09120a120204150305040b16091404150b13061e05070218040b011d01120602131215050903070507090513140c041b08130816 62
    0x55256152103010340c1000340c524405a0003440e0710704010306011090746e9445800380303400b81120001c0450b80e0300070b11940e003002021280540ca4091640e4043c0c00490241d8031500b000c40d2103990301d14400f000800f800070103000140c0d480320100511311b152070003058002002440006e0400340741c9424000d000b55684007001070440070403e007251103252000b6500074505030401d040e110703002da0901110710180c203031284140240411309205648440030440700392812210008401e0410b401c041240700402d2290441101040c0300ca40c54100d19010340d03074100c0e510b0441c14802454182e4440029400400000c40000582c480c00100a1002400c0d540041d00402c8905540070310b00380a6410381e04020003040c00e0303520410080c00002e1000510b00102d4038804000034164484500c00c1c16503095071030000d03040028590701500410001700b0305c0002d4090895040015200c0c0400164000c0151703000003010400c00c400003000c000350504042c2d01d075032150003064070f0910300301c0712581100b003129403c2d100703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 845482491 1250 845481241 845481271
    0x203090a03030b0306011401080c070b0f100807050d0807061503080307080109331a1c0c0c060c02070306050403020307030306171b0402070606170d0509060a0503060d0b 74
    0x7031641500c0b5448605034290040d060a40c1001c0c000307a443e00c1116802c50401c50120700094060103070100341c5640d580e200044082d0f40c28000c3e015417400e402500e19251180e201100000c0110000424404076000903143c1c440340002c54494004e103400c0100251240f50310351039482541206542c10001540c81400c0213034507410301241c0142071040580001030807034a4030100100b40c40844503502e926107008000340302441c040281042d1520841d40c8040d005c60b1503111f0058043d00258037509441e032121000000401d2041500b00540c1c0a0960f46030205030045103080104407541c00000d008a040d00440d4481070760b940d03646048a100712030940c01a000803c0c0c90741019894010b0000520361518509842d0038a03414440e01c9400c988002d4202c16060701c0581d0365505c803030f01510b184607082101080b02e11f035101c0d00d82000a102c611405194092140c14900043c010307401e981d001702c400740180e800c1070b4180e030050300c0990010781010f512048079003400d000101c80700c0d000c9108241810380120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 845483741 1250 845482491 845482493
    0x160e0a05090405151f18060515070605090c010e1014130e0f0103020105090d1713080607110c010c0203030706050c19390605010801021903020a080109051503010203090a 74
    0x1000f0030243c060600340600500c0e203003081c040c1c00d072003c5c150f921916180d0144080c01601c44020000c651056400c9961094001d44409035040500780b8140181c1c800c2c080c03542c0300c0782c0464a451711641078034003041c6100210010b03130805c0704040e24010b50a0515105100c0204801a010b0f081002c0b021000c400326482400b00440c141040b41c1c100303124110804155042d40d0001c1d16a0044006280c02214040302410038419440d2410001c0704030100356540d1500040d00c00c80054441e4081c40c4428860341001ca00d49610400001041d0846d68002c1c044d400c10301e0004403079012004105030380c075100600085012401c64811f46010303d268040040d0f030b5880711001000b010f9600d0b030522043c4840c0d88003509215000d101c03240300145514680a20100e0390b020220391400b180800a0040351424001041c0d01e40c055006190030078000440d182c101c400031f10101e06034418041140000b03035001004000000441d04120703081014080f4201d81d11081030b02090072a0400c9411207119446049071038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 845484991 1250 845483741 845483773
    0x20703030c0f0903080310210218070c020103020d06050303130905010b0f430201031b0c0b092103011406132709110901060503160e0a05090405 63
    0xc1c4452060904060034450b410010380341c43c0c0a40f00190400c1c0c000000950102405251200a4141e5400200e1503841600c40d410524520f068100e028080d880706501000d02c100c4032552061447c1d5690084280143e40111701039000020341042c11038031864041665941880640342c00d0322868010800c241c9400c101c801074500607409000001020400040500418401c035058940c0245c2241c9060000d00c0c89486064140c1c410415820305c400103010900b55104a0388401d14000d0740c06001401103040a00d440d00040f11240000c40c800e0400c0d00000351804c2c4019622035101801d90b41c0f980d0110b510441d0070700c108200d50151100c008010310107651420f0004690701415200541001401b44503406621000d000b03421a980c21442c03a01a001421080741842543c070001c28898000c80b403402000e00082421504e228001c80000441c1c0c81d840b51017541d03c9022410014034004180d51820799404948000c429040010520045a036446003503415008600c10030082104558400f414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 845486241 1250 845484991 845485001
    0x1804050d030c0f050d110412030801140916080403090b0a020f060109050403051e16120f020622080d053301120f02071424060d170c030c0102070303 65
    0x2c8024811418443e0042d568040141d659010039a0800983c0c0b150350074204090340503c0d40284400c48000c00c19108056101d90b1190407101010761a10f0b03003c115504000d400718048610304c05030441001d41c0541030340701d210200d030424042d007464941c45480c0d400e001c840340d00c1803c4030405640103041c09002d10004000041c01040740c04403c008a086c680d030001d100b4420314208284811a0124092400e03403800121074410250ba940c3c1c072490b40c002d1804000030b8002e9140038000c80d54a241c42070042e030011404030320600e0383e00c0d43d1000e014814040d00d40d05540344103056a18800920021400c80514030031140904100341141c1d00350003400100100350032801003049484998002c0707446e01c41e60441c100600807915000e0104541a41d0f03811007000307020b11400035110008800440b9480305010954901450412100810300d101c5402c40c040c5e20401659200e8000c50320244a0010890201406810034007640b04140717030003030480c43ca070300d9500440c0c4843c507640d40c0010b901c000c01d038041c403078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 845487491 1250 845486241 845486261
    0x90d030e1c0c03022803050d110a2307031704050306090313090c051c050f0a0603080f071103030d0501050f090906130809190504061e030f021804050d03 67
    0x1a11040040c10b6480ba04195203c2c40300178000c2154904d40040c100e180401180556040b00d04801403a5803030900030707a0750314801003040200780340e442400e8020b107012581400c002e402c10a1010003030a2250101c41c3c1406602c2407000d00d000d0040d0110000c0c40c205888035640700550031403500c6074240020181099070140c00034045074410403400300d24089e0035440c10b0495801c8240010301142551081d076641c40340506c02c0d001801020304014060340903520440c0605010124809107950f901e5452080b06c3d0140000351128400740405003182c1d40c08030080100c14406d80f0800780902034903010a1540d0020948482410b458000522503803d0804008040c60001c5841c40340c5410070b240010340321080030b400814400c00100d20381060012180403a1094000078040e4000c00d071840741c540e2102c41950240c0c0d0b210311301b40140054592002071010b070b031282d41e01084040c1c1a1035540d441c42d018400341001c0740c2181c01d0301302c030700d92070302d8825003903403203540150041e0030100c40c2504018103d0b010600d07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 845488741 1250 845487491 845487529
    0x504050c0922020312030412030b06160b0603280b06010305060604031e0c06050a030b100f0c0311030301030b07111c050702060d0203181002040e0601050906090d030e 73
    0x10401c26150410307049089180d02ca044484100d0529001190601a441c103d01070842000018081085002c1143c001203810300d03a81000b15150100406c0300c14803580c180c401d200d1405042082c0452454020700717821440003011240100d07450110700c144580302002c5810400340e2600d41109001e0160310071680003c0900c2d080143d0301d070100000d80c03180104e0001401030018070014000740300040f03200307102690f08984aa6201591850002c01a5000d61400c03400641801092a1141411540701c4465902038035032103000010040203c2d0804501c61003581089000300d1900a520390500055000c1c501802c0c803d111440c010001a20005140c0041150359100c860040c81301c00d1070342d605561941a6142c0650f0b81d00c8030740009044c42c0114240800c034903100200380840d6620168810280b000411305a4840b2410a08500304900591181007801403040c800110781d0f6200d00002e04200c1d400400390b5040625200200e07051a10102c030403804a88003c100603000d2420140c00750907a0b03240b030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 845489991 1250 845488741 845488759
    0x20106050a12021210020903010c0206091203060a0b121501080423010e010213030c05030706021513061a01030e0a020d080d2d1506052209020d0504050c 67
    0x10011034914600c521802240005081442c42155a82e4201500081c9a03604035102c0e81c400c01042c4000b540801c001c103102c0c4d0301c3c0c004054441400860914070810b1100301034960900c441c03036181f07001e41c40102010342c040d01c0f29030003086092001c006040c42c0c01c91601c2007101840c04403141c00904541c505820f050000040030400010103040303481c2c2d000e20807a1005c03a28048807809450242c48800005c1990703500200d0300b120508020000d08040301e00603c80d010b1165035803030a05480d80c0d00d502540d40140c108080c81031002083c4815035801c0b00b43d4500c0d00c0300089640e103860040760341c5000c1c080c1d9900310320803043d4815039041c01048041001d1001034000c100041c0d00143c070a400540b0024002e44001c00c901c411186c03541c1c403d505000c3c1800341020001d244114982003008641900d00c4058502000b540e1001d84054010099840984130790b450302d100d1f01c04100c00c141d29014020201c0c030f030000c80820a40b0290014103030780b00880700003081504051030000d0800a031000814025207690b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 845491241 1250 845489991 845489999
    0x90c0905040c091817161406072d050702120d02010b04060f05150708030c190e090f2815080a02090403081e070e0405070e0102070501110f0d050a080106020106 70
    0x518031071118258013001041511070b002882c400e40c0d0240452407240b80301040d86c4030045c084182c5204040031480f00070390300141c0e1881c0c07003a507803410b038415000c80305202184c40340702c800403546000010340e60604005040114a030700280c400700d804211080c540e042404500c1805809010301880ca1004450601c0110308041e00b160703940c4c5141c45094403c10345400706880400300141207812072030b0829072240d43d91500e00d6015013240e0004600d21000c05a5658a00030b60b807003260503d07108a0018010314103a03d0380d00030740c4400c3c1c2c1c0c06081d541006900c42c07004442c40c140e001d1648079000000c0404255003075110013900100f08582d00c054469042200c2030390050790741501e220f9200d507050070010803d884128800c880d0040c410400841920003d0502c01107680001003441e20510840d0144850b9603003920032103c1c000c1880c40540564003208080c08190700506500c211000752004440c040d004a04009150840d40552840400c000003000c4103403a41c010f05260161800740004e210107890 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 845492491 1250 845491241 845491271
    0x1d010c0801060822050307081210050303030a0b01110d020c150418180f03360306020f1608030105010311030c090f06090607060501090e0c0f040c03090c0905040c09 72
    0x3c010204664412038071000400391061a400e1810150440212030700d942c1e951078010b55550000142112041c00da20008132503206401603078042c0c82010380a1411905e4a041520191240c2d110705414000c0b680b1b20100c500d1020040b07084c1a010940c01420f6a0441409006010707400c4199a00a44c00c00c0109000c0d10400c0700c0c1c07544042421b10070002d00780415a9812040799000301005008800c94091942403691007042c814180064000130035245c00100d030b0150b044000350020b1050100703140c80030804034034564060050310032001b00c040d15094462140800756020a20100c1da9401c02100501880d40c1c94807945e003c6400203e210741c55410b03d800c1850b114019000c51a100f0013001c01c0c8003203280c54080648407214409460a901d9114901d0a400584000d025040c0d4051600306464110b00d0001404400442c000e41240005800d28050001500251026400749902c1e401a200052514600d600050201031400507803410145460310546046a000d500e2050511010188440d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 845493741 1250 845492491 845492507
    0x5090a120e06090f0a0b030a1e0c0c0219090603030503091e0703081614010c022a010c080415020d020105090a0201080a02030415020d020d0b030105100510121d010c080106 75
    0x403c80c0d604c180245000c002a0b2400060380120910303001c040280200740c1a0794000d031100c03d8800b04c0700c041d10502c460b21402241d602c1640c02001400c009250005030a0020312060002c83c8001035224080d1940e4403d8183c81c40b0342c2c030840004400004000d131190f4144608490352035405920105171070190b4001d80e03680301902000d89924000101440c0c1104e559010700d4070a0791007600741030069480c084650003444041003910142c0220440400d030304000b00c3c031420980d80301d00416904443c41200454503100b0b1725004407081141044041812003218000d41919042940100100e10f28904020f0030f581e4013411070721695002043c220010b030703005400d05a111b95029001038132070b5114180342214109155004458600c002600e408061154004010300d290058080c441e0100d01e10a00d4200c55088401ea900c44001000a2140d4548038854905040286c80d0018519400207201e104640ca0b40e08660f1415011500d48501500c0c00e0003052140c0c1801d08102d00c140d03242c8440509811 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 845494991 1250 845493741 845493757
    0x4030c0b04150818011a03102702150d0603020109090c0512150904030504150509060315152101090902010c03050a03060e040b1807030507030303051003020405090a120e06 75
    0x10454000103021a005003613041180b0006400a1000c0c290b1140031400072090345400a00034004c3d0a142e1031503501030f01500301d40811054603841000d0440480355401100c22408a84c0403180c0e00c141030065203040068400c49158101c001203483c6184000b40485280c1d42c070016040d82007000d001032154005c000d8803c032030a2022594801d40e10b0179071424861003d0507625034000e42a40610081c1035101026009a5602410311000310440840c191254000c01c00c54581c024802c000041c000342c2840c80c819003402000d401410070003e40c00280200b034001e00c994ad54080000c01c03d03001d0740158a40ca09004015400040202c151203400090600800e02d40240034070000080100045110341c3c0305d00010031082c4042a501c1c103281c41c0010703400c003090303072141c041e040601a24440d0041c00b20b99001200d901200501c004c928650b01075000d01703001007010354180d004210010240e01c89019031486606445e018082019051814100071042d00c80064208880e55013061019210041218000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 845496241 1250 845494991 845494997
    0x708070909080c0f011a03010b0a0513020c1009050d0e060a08040c080a06091a070503040f1110020f120a0509060702040f020a090303081609030b060406050406080304030c0b0415 78
    0xc5614201580703248103040343c4024901c160840a04854010362000d591000700064480d13144409200b0142680d01d482a159805400e0300c00c100101e00e441c00d1000001300e061030002d030500c0c1590410301d060588070402520110348824034813041210622860107204194100b0540245c21301d00499980e0044040440900a204d00406c040c0705600307040000501200381141d01019541c58100007a09406400302c4010449195060003808280e80701e9224000582d1080d00310b80d03c50700c07103420f0030074030300302c00c0c0c641a0302d04010081c83e444d540d01c3d1000600c0d682d0014a0811142c409580c50100026080010b401060082c4003413164441d0880d04210070844209440b0700c0517000181c001d00003450f840c400c4904c00104544c03155000301160084a020ba03c51104541d1140e14070340d480449000008000740c5186000e0000440b0580c0d41038005d5006030000a400b526803020900b102c0752030708a03c4540d80041000c2042040c0041220f000d0182d8402440c10107181040707040c22020000401024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 845497491 1250 845496241 845496251
    0x201c112d0721020105010f140102100c020703110d0203030a050a050403050601031a16090501050a0908060f0417030903030402040c03090c0609090c09050a0512151003210e010f090305070f1707080709 87
    0x11682b00b00a007000700f0002100c1002035205080c0060b544100c24071080300c0108004282440b01d1504603012024660081c000d5407500c2000d000481d4198050034040c01408024480032000c5641044050301031882076060703520303840c0c5d070101907a84143c00030101114440f40070108400203522013803410481300203090035519804001d006583c415100d40041440780b203110100034005a0035500700d8040d50140985425030900d91001d1078280c8011a0150341540c02080410b00600786a1702110042c0054900001d8000d9150b0740c1c2c040030b522581c41070001802d02c103814407449030b0910440038948410308010201c28540000718034036070810b2090902c035281d042052075080409000380c4003210381d41801580c0710701e00074050014500070303400152a0030306150095000b81c01c440070541a10062500d8070400c8016400046030a01c1440189004000c012100000004d0b02003140e00d01625810311303000c808500f031008800200080090412195002d400304009100000c1060002e44282507c0895 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 845498741 1250 845497491 845497529
    0x203040f02101116050a060216140d12031a030106210302010b15040306050a020f2208150123090406050a201c112d0721020105010f 58
    0x1040300203840c4070080f034000ca00401050b0001c00310b0500a0350300440b03000781301c9901c2e948120394484000b480170200303181601d003d20160000e036140d0f210f0031000030806000e00c02d00c0d42e100c03000c0d00d0303140799401c1c04651035a02c54290200c00d070b24401c030b41d22000d070001c0100f585001d8035034551a04203035141d282001d052500c038052510030f4000d029211070140402820940780000003e60794003034802a5541440c3c0404208801024005c90704da03d209168924144842d80400042d40000300049041e134800c03414002401e5881800050040300400701403450719850720400a000d01a454244801c00314032110325003050384c03140d00783ca800075013058000407683c0d00d0703580000c002c0209a9400e069080707201c08044401d0714400051290000f503540000700508a1100a410b4a00c3c4803130000c83d4427401e205a00101444036031f460350710b140001071060200c9a10200d51016400307804181d443c0d8005d1001c0b070591240c2954120542920f0f44001c100542c0f400302452b64040a07030085055405400c2401d030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 845499991 1250 845498741 845498747
    0x9120e041b021b0310090c030c0e012312060a060812030105010206041b1206050a0e060402060d0216020a0815070807080406051314061501020a020f0f0111060c07150203040f0210 78
    0x1184c81d85c00541001a5900e504221903510303214403045400d0f000c6244080394610f0402106d070304035000340b150b03903015002200420b0900b00c3e4140074560010800c036014048040200107050140800c05000215581410522400d201c8520103c0c8810802040100300c1039a000484075400703900202441840640001040c10205071584000c240c2c10700c001700c0006000140c1e0060740500c004010400c5090260b902294482e4411200a07620480c00e1000c84641d121540051508009060300c02c5040000750340090102601a0059111170307000301501d500500182c03506c1c3e07811081c0740c20030b0f204a241551004040600c02031006040316101c9010902c40d80c600d503982003842d64058008884803d81072010381e80d43c282103071a038a9801000103c4031140d40041011100c5a401610320030306644130b182800306c0f0400007110740c0c0c10407107a0340402c610070205010407801030f03406000c41640c0301c9075418844c0c0c1000b60013002d01000ca10401c280b00c009074103070035441441c56050761034420f85503071241c0c26 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 845501241 1250 845499991 845500003
    0x3080d0e0a05010627140604020f1c0207060c050418092301290102060c160210050913020909040b07110a03020718141909120e041b021b03 61
    0xb0000d600340130000c41c00103082c1c0000141e0290314003441d12400351070303907140084d50666018031024000c60f5000c42e03201e0820ba001000a00140054030780381c8940d8603120700e0b1501c010181c0d4060700d5404260041002820b00030303c1c2c0d5401451600c20f04150070114400c10a50004a001c80c10b665070b08036040400c00841c80c0d0341032012451548050b550405900700e400b038600100d03030039504200045d640802e0341400c0820342d040340c1d069000b03003000e661b05100d40550b80d10016106031507100825a00005a81c2d0703001e07101c2e40101d0b550381c1e141c032110244240101001820400c004050041c0701c604130949403000d10030761094009806d6610394a44901c151050f44a0320f51410b00c034011170342c2003420f06400240110481d40305090101d00482d0000240c0d040b13440c0e194440320110010b001282070a2034a4038440d02c14000e600d0002425203a95840c0e0102252034844400402c41d000b400c0b800c030f450944100e00e84151340181000c80030301841002522881650041010920038109110300c6450403c54 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 845502491 1250 845501241 845501243
    0x1b030206011a19121b0309020a150e01120b0904080a0806030303010614181e13020f07021002030c10140a140c070c17010209031212010b03040f0c062703080d0e0a 71
    0x880c09580c04441c0006d010f41400071050f030180c0b8843c14001101c0c560340b001500304003255540c488884006600440d0190100100d009865032140e0f0810380c80d50720b900c0c2c030354007482c4102d252a0b40e820000364058890240148418030981082c00100406c0340c20945040307800c400504515a40c011601c800c0180840101d03200380c01506404150000c4000880220000001294200d006d5181d0350080c030264440c4008206038441c1c14040c00b001418851000d13002000180150b030b0030a40020400c0d0f18201d510701c8240201034440301121508400c4105180d080311031244d050000a00c1d0164503590008040d02100c15100005034560901c842036110702c015102c00c0c0b20010f07640f195a030b4218040c1d00300590040c401d0080080b082c258090708404c80708c0003180319a108445a19002034a150fa80008000391030701220b842c40f490000e0142c0051a001d007445840d5501040180c061180c20700012814015000f05007801c24070105140c1e40c25103001d10080c8001246202010140c0b50034200c03d404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 845503597 1106 845502491 845502521
    0x6050f061902030c06090714120607051605070803030f010b040e010e0604020c011b020601090603080319151d0c03011508071b030206011a1912 63
    0x7900741101c00103005a034105042c0d4080300d400d1110444860000c3d80000c401408031302c086004450f000001039606000d041e4614104581d40c1c080581240c06100c004070381c88042551607100840b070036500c501a41e9820390748002c244d50b207400640784030781301030103801c000300386c22010744140d40c100c0390208180d441c02e0f445c150b806110110054009508190200310b141c110b207009002d240801c5905100401c202c07800c0140080c10510181c210114032810036000b0000b188200040d40c0d0400b20195410102c0340e81c1c03908010050040c8000c18040b552002c50024070100e4080124840700e105950900c0ca9550b00c030140165444240148040d0f10000000d619040f84120b0100340d0008007418140c1c4984c0f951210f80002852210701100144c1c008801805151810700030140c011000c20440342c00d00c4880c1d0003001020074000910302c01c0000101490072902c5030b40d0086d09020f2100d072 = true := by decide +kernel

theorem cover : BRFrame.Cov 845323741 845503597 := by
  have h0 := BRFrame.cov_init 845323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 845323741 ≤ n) (h2 : n < 845503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
