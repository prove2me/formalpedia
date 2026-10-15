-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4840
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:54:20.201258+00:00
-- url     : https://prove2.me/submissions/55a01f96-2d50-4245-b0bc-25616d2d8b76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 870323741 ≤ n < 870503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 870324991 1250 870323741 870323813
    0x2070b090d0f140c0f0d0f0e061902030c01050f070906091805100b0406020d09050f2b140c011407031b0311030d0605040b041104090203150a06020703 66
    0x80781c0d510b031400c0a0303000c2d4003000102002c50207402c2034841103008070100d8104d0104d02191100104202e62103a149040900400303c40a0303291885035500050204006007014010342c1a03c0e516107110700c100e03031a00e01400b5074242550400c0d58602c1e0b030740100d0020f02c0341c0c540c0c10a1020025000c40d152990415240c0818801e40c1e0500400ca0781400e5070318030214807040c0c1c004010711301074952256455a12079460034001d5a805400b241c800010740b40c000082000d01d81814071448101000340101d40c648811000c000480c2c3e18200c200c105640040b100e01d00103141c50f00d0300031844000b40b002c1c0030125000340001d007a60300410444810f170b603001c009210010703400001844220900c10288091800f0074070b4183d03042f452240847c00340b8800132845d0300c441340185d000181903032070075201440301d0007100c01440140c481c0c1e09045040004184000d00800010b40c0c09035900641c036105007285d403003a01011850b1030031103030000001a0059403040c000d2003400b01407010901c00c8402c000031030514100360340c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 870326241 1250 870324991 870325007
    0x40c020a02040213030b01030c1a0405011e0509191d040308040308060d021513050330070206131d01050108060120061f050904052104090f02070b090d 66
    0x2403181d9408070350b44c2d0740010240da200000e554026001450355850f4140080c0e40c003c2c500c00c422140c8890105080090614415601103405c181c5603461040070b01113a900c0f652128464400402006210341400d590364051603085a44d0707208401c0c0041e03400e00700280d540880f070380c1040820510300303810300000a5102017043d90183d05490300a81503103510300040d48444014502075407081850303070011040c1c50410000c1c610a03242416146455644030103041c1c5880415000595005442e89204241c158002d032400c071752107607060882d2400301654001040c0c1c4d040440000c0c002140008148a1815098403040c20281440400032041d85403800080c83e0710001880c0e24100204e08690080c00010100c203402c00c5903101007600d003a40b400d403150001e240796650303683c044138082c0e0f2000a01800e00f03c4400c0c0c0200d400c0005840f114850780030340214080c0e10520304a11714000c10002036200414814585038403072840f809652482c15062109442c035000e8140719a0380c1229140c4d2907030395048119 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 870327491 1250 870326241 870326243
    0x14506050409030c0b041e0b09160812090f10030204051e0f04020a03090f062c21071505100b12010303030e0703050a12020f0607020706121803030506030705040c020a 73
    0x211095640d07607032503c10030708443d403041a2105800c1f01480c1041000900308103209000c80000c0300e40e50b8807441e0280c4c1414a0511400c10345170842614400709840e00c200a0003184800b0304040301c1000580085200e841c03210800d400045d5010a080c48586001d2440e1260000c10001c908401d5020500181a542c80b22400c4d81c4204e074002860140680070790410000d9070741103101c10f03404120900b0940d015013141daa031200c4040202c400c40c42120410500500c000040e4801002d9021034101240140d483c02610103011010601220b4001280360380703082250f80d41c0035030100701ca0810000c1d4502e00411038018a2010b1400e0090200b1030b841180d03598116501032901190200e0200c049074105111a003011344580641c2c0a5403090140500d220903000c0d20300d03401ca4846060b0008043c1d11050305680150060300a000c0c100042407080c0c000204a01030704800180b0080d00f911200083c00f607000046002c030752186c0030000c50385000d009410082905403401d02482c140300c4002500c1d0096204 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 870328741 1250 870327491 870327503
    0xb060c03180d111905090411030708010c0503010312020307021003060612020f0304030309060e07030f02090604020a0914041b03050a0b1e091e090a0b09070509014506050409030c 78
    0x10702d020fa0300030402004c0024980034090440700d00342410010100140a000103000e440303000e4002074991014800c51640c07180c542c3c3d4582c25039080d0381d035401a034006200c2078002c52009200349800369481d08200c0c0c4140700705032400110185410b20103000c0291480c82d41d0f61182c030507c00310719240b004800b00c90f0300c540c0c540350000303c0c40c180307181c050020481001d642a8034801c0305004810080358030701c0d5600c4507000300c840f1000c0c0d0f42c59601b0401648a00d83c1c4a10000715448402c005880b090043d000d400b030401000031600303c0040c1906030900b203250904a0009495400b07100c00e014051050003940c000c2a20966082c03292600c8054400b000141c0c2c450080c3c080350700048160000e42000c8503184070036108910036050a6680d03590311007242c0e00556100d030f4143d0105140f1840002d0041c11100b0143c118462a031038000e170ba0400d060f1030004405010017034510812072010142140c1445d0002c2e01e404590703035840c01e980000300d0366650046401946030072950380220fa0010030015540398064 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 870329991 1250 870328741 870328759
    0x50708071e020f0706020c01180518070309060c0e0f030f071707032909010b09060409020f030f07090e010212010306111c060e07030903080402130b060c03180d11 71
    0x2001240380032403580358034009004401002c581160701240440c0c811f0026610820b10f402c10000e0010a102e8a219413035101a070318403001c26100340e000d2060ba04c005603040c002a50f0140d92515015074010300b0a940010b50310000c400703918640003040306074055003035006110024183e070b4034641e208507501981c0c0d03628450318141d01c801c1c0c03000c2001102966204041070000006051100101c10418582c2d4050414000000da8444014822140c101500501c00540750703c54030140300051a4071013060343c00c120344040c620010b403010050340002004500080c81414a0210300c80c00f110b2842e00c0e4032149900410070103d0310564940000e040d41e401820000f030941c003c100c02c036058805d0700000850400d080d15090b40c4048103034072030700440e20325240d0546140c1c0d4418045040380c0700254024041050a80894054181036100150714243d1100019428a2040010340d441d0000485100c840e400028180000d854a80b024901d03490160781c02915502c595444884a4503c00503c0b07011319070f61 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 870331241 1250 870329991 870330047
    0x30f040b0c0903030d1a100525140705010201110a090e100e0f0a110703080a110c01020c0309030705150f07210e03010c08190207050703121205070807 66
    0x800c0c00c40e020304a00404581d50303032001160303620103491901c0348201c8003546c04a5000f01c82c10300c0200d041000c03007156501d07031600e454030140e24026000e0815a80d0341e5810040c0b01ea0018008042131094045110001c0081d0703480d00c0002400e561241040b00030314074081c015500c0554210351200282e0b0110150300d80a540d0355420303030580a48582c03104002c01c0c078410600100b50182c503051030007112141c80c103100c00b0660760600303540c134400c000d4014002201980000d4a41c10700398801c0800c2d2080b10001481e00340c16560711820390b0002104408903401c001070240b82c61400300101c00003400c050729014840071142a8590740343c0285280700e000301500048074420014000c0e00d5001c403040f1420200b03140303500710340005d01d000d001c0a4594000d40c40c000020b001c50b0f02504809100c0c032062000301c0d0000d000180c2000c042d4010003401ca40d2445040ba01100103002c2101080320703003c071580c070031800c01803008408040c0d0b00c000d04100c01744103140e0140601307a640241c4d0400409408107482d08002c2039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 870332491 1250 870331241 870331261
    0x1b0a0504050604020c150f0c03040c09020705010b0406081e072418120209150a050118050310021e0315010e0f03060a0c020d0801050d0b1f120201080c030f040b 70
    0x1100c410b24101d015030600e8080309100e05140798010462480305010b555208600c101231840b06581c080c004860580e02048024070940042c00c60702d100e40300125064800748003107010340b032498100b20703810707008140059102c009002c205160002002c008040c050b24083c0d003080440008040e808954090301d41d404160342c040c0f2100050000142e600b6440c09949a0f04030b0902d03144070108921464200780422490083c41641e0340845000a00280307400340360500640d000d41504850301d0300050842000140d940e8103008022400104070800340c3c0e00e002a0342200c103c103070f10f1041040c1c68003080c418408281c1c20465039420412080c02c1c0300d140d40404000182c40038244041059151040400704801120310390002e0030800940e0302118a20035490b1000d484410007400341981154070032001602145407185a070381c11003441221844004101400d119100c82190001004503c1d100c07020400c55902c210300e1548041c0c000003c0c1c0c19800c0c1f81000084182c4068409080c65034600040341d11078103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 870333741 1250 870332491 870332497
    0x130509060a0f06050406080903091509030a1401050403030605150d110903011d101116030513060c050d090311040c020c190e070c02030640051b0a050405060402 70
    0x100d81c54150a425607110401070460740175024841c005040c030000f0a50848000007951000c0400915540c040042c840304d40c000c0da0462000c0d281e0510680d51b031040441c80000703030014140300c0e417000892076241c5418043c0c15070b9621340c031260181c500025002c0304040132400f0340ba0018401c1300003140c00141c40500d802d80380182070109500d946054002c03408164001040c1821350500c206480074402800c603c06c1c2114040140303c40801006c02c03800010348940c103203c0c007180d40719003005410512074501c080e841c005146c110074086030140d4042024040100700c0c0884800d003d2030030b028200e08681d11841100554010385024646616107900d81c14000d00000107400d03800761600b200034001d100c2c10704600805201d0710201ca050480880c170514811444d40030181c3c1c01800130540d5440c2c000403140c0a1520403086910720030f03690301c0c5c00a00300b03401405031259105190062900600c604100d810b0001903080804910010f01c20100750341c42d801800000c6032011200042d042e0ba650000c10040c0c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 870334991 1250 870333741 870333749
    0x60a02010b21070b0c1c0e0f0319030e03100e06040309080304061b03020a1b17010b090c030411090c03072c0411040329070e01020a0b0718060201020d11130509060a 72
    0x21050034413040d46660307c80d00e80c103401b4208680102c1106c00c04d40c00e0548a864100d21074400c4d03020035103ca0082802a1034440c00f414001d01102c0070006040d41c0c013000c482c010113030500f160300312109010a0640c4400c03200042c015120240d45050b2505c8805001d03105045018004400b00b8006082454028086203070140e4216000814511948001d0071404030240500c6041601c050346420000005100c1c10881c850040c000c00c1007501c2d80c00c5008001d030002002217a6242415103084a2912450700441c0a49103103060f0a0712420000b030094204450500a1a54038005d0403003414050001800300184420980d80020045059144013195229076000544101d4407000002800010300d600401c030a80b020f5004a019211840300311801c0c2c50105040d070069000c0c10340c60010030325103409640c014130303d41000c0300800c4000c50f0751002e107840e5a0148000d170350b0110f105c18900e00580204581d0b0100124003d00e040c182c1c8010400d4803c450017420b0007a4104000100c90351902c5005030050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 870336241 1250 870334991 870335023
    0x906041713240c0b040303180501020a0507060c030e060a1d0f07090506031f11040e100f1710020904061a0306010e04022a0c060a02010b21070b0c 64
    0xe40c442048602c00d003410214403545410110b14125014421000840d15650082103c03440751190348044000d000000c1a1000c400703020003031940000c000b44018280030f032050715110385030700c000d050410132201c1d4500510241400c041407481c0800c2c0101d2810780c050481140000c509140d4041c4501c20140021561240c0c071815007810342c4148001141c0d001c0311141d540501581d5200000d041d100e0300c1481040d024181011301d03428074461182c10030b5444401d00350642c0e0415654000041c0c01c1041500c95003040c0401c1c4509100d115000c2d96001c0141110039a42c600060041c48844d589010602c89454041d078003040401e0207a403181c222070000d194110700d0754099031480303540ba00143e0007030351f91740d000c90700e40d2403003034900d052034000d0b0740c0149004880d0180041080041407030a103030746c4010404d00e00500c4030480c00b594840001e801c279442c09900015401700c0110600c1510078403103e4000c09410700c560710252381e00d00018040251340342032200b076465641020384180391000c03c091030300030307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 870337491 1250 870336241 870336277
    0x8030307200f060108060c0406020a0f0203152703091c020a080a05100e01060b070602030a0f0f020a0e151b03040f031103011a010e010516080409050103021809060417 73
    0x5020300150160690f94010250703a41d5440b2540c02c100c55204a00c2089c0c056001204900301080d903400300c115406001400741c031b810011000e05101c810740100c5802034140100851020f281741c4c0c202d10010500c10703d20007540703043d48440c0040d501120a061071181028a00c5101003103445045400004001c05402c0f164a40c4080c40c001da200c640f000307035160600d4600600c0c403100d8403050291004441c035090b14546001800c0e140c0101950004208580090315102d60216a00782d034858022412340b081401602c2d84a081001000000701a4407a0b2064134000c0746c6111000c2201c041707030b1041c078087c1c4548079516a443c210798190301560303000107040c1e800c0010001c207101110101c3c0c1c040d4003040f00200301c0c891046c5180c0030b80e201f4043c80980058601801814254003c4004107148140341c6848a107030580c541c0c80d1410350303026030030101031980c0b113034010011030800002e455442070402c01e0160a501c0d04440c043e84c0d03000000c0c0090b01e42d0700d12840d4440903220641c126610304aa85400c1e002c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 870338741 1250 870337491 870337513
    0xa032c09010909121d060a050909011503062702070f0f030c110d0b040b0c160c0905060d111c14071a040303080a0e07080a1a0109060803030720 63
    0x402403050700c00030796012103400c51010102d4400c089805800c09000382140c0b8641c2d170b202c2481015003200301b0030790601c4410000c04c13160745d80d0b4a020301c2c02017403141001441070001d0396004042c0c51690b408059003407441e101c0c408040c500005480c1222140c014016244e8402c3c1c2000440da00c03691002038840600346c1c50300410b26520582e800501801080642c40ca480c0701414801240c44e04140500a20646400b2070b00052404140c6600403d150f103009080048c4868030000c1e0181100003203c40441407101009034110354012994000402c4a2001c511116911002d8141d803d2001d035600c10108100c1410354590111415070016810900320181442c11494844e0b86000500481a5010f42e07901554004d000f0301007210b00742c95256458004030380720030f48030745c2c06840007040c0482240a480070101d0655400c0280318032031801540c6004042d42c01240001c40341c44180c01c5001d0040c00c00b001440350440000c2201d800c405c0c145010890603140182c85400045101c0c0400c802c2d00803070460503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 870339991 1250 870338741 870338759
    0x4090f0602092106180c0a09090b0c07080d05190216020103141302090603100c05041401032a0903020909010b090a18030f050c030d09030f020a032c0901 67
    0x320030881d0582d03400f00000703011a414580032040c4003085a2039440b040c002000c5440300a1048030304140b520460302064114800181c1440882d04260304155940b83d000c02400301e0a40403540124020410625000310350b100ca401608c14100c420040c1c0741c1b9070f80850703120342a04200c2c141a034003501c2e045444101c2d441c1c1c1e01c14920b0001c00140d0001c2c0c201800700c045e100780d429800d0f01540f20303005803110f002c4182c0d00b4032a5800c8020b010750f906025a03100d60300395034000d000d4410b040105035289566607044c880703180d01c00300d0400103041c1090700c2c040340344c03d054698503000424a00464940b48006181190495006442c4e4000a40180d00c0109000200c00150001101071400311340d92403841d550807075000d044400a444000c028121020840701003406412040c4140c076041c0740061825000400d06441c5a1007042c1c14189a40e807a14020b05160f17006032258040f04c25403000d85401d40a0303850080080380142e020290300c5031800096078660708400c030443c00d240c201400100a80d81d6540d07290b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 870341241 1250 870339991 870339997
    0x1815030b030d020606010509040c03060306020d0e15090615120106140a140f090402182802072105070204111305030a08041e170f0d030c1b0204090f0602 67
    0x40c0244103001c0302d4162980007150003885040180c0d00e203405d041e160010400500401030704c00040c1995441c02001103010b80c0001e200c802e01444022403003845102080e480d008284c500c1c540201c02a80501601050101d06141c200c0c0040d60224003803896080040c100d100d0100200d0b1079503190210000d10fa540840b40c40c211040202c4101c0000e550300d9130b840c250003400e060324552080c0a0481642d05203030100341c0d60b4002d4000340007030a2091000c1085d039150081500d00c1291344540072081072025194005441c00000c50030404d508200e07590344c84000008444580c0301c00c4001420f218480f451140c803e0b140c26503001071040c0003010302500d02c055107500c0100221811800b103400070449050024110a0781517002031000d1910b80340441001c0813164008680d0380086040d1000602d180f014040300c40842100c03000307040b21402d40c000091501c1400d5064505040c2444c1c0c2c98034185401555041da002047e062640b58010148002030050501400050081881140410910440ba406 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 870342491 1250 870341241 870341261
    0x18040c03050705010e0a18060b0c0106030b0123010e031c09090f0207081204060f02190f090f0605030603031207080a1107150b0a03150c1b0203070303181503 69
    0x2034420190f1110300440354407000c1041245c20034034044c400c2044141007a00c8030071a88404000055107500c03080c02440380e9001c240414210ba4403000107009000740712042d9801407010a112410700c20034100201081113000340801d061115500181040c0d0f241030044100b01800154682e1400e000c40b140600400050b014400090b807070a40713030090f190b0551080350703446908000560300349800c0d0000d07080480d0307006004640d0701c0c0c3c40707540c0c14150801900203008800b0700c1b84042440801c0d041002000156202204002c11843c10810461001c0301c40080d019140c4500d0030036500e41d10f80010a14621070264807550310380c0081e08004150350b1001d6810300440c0030450a0100184880565010b40103c91002c5d0801d04580031302d00d080302c20307a4041807142e080541400d000d15a80c1c3c03641207032615004144000c0c030340c0b545080950769500011401c4801c0603a101507804640075008aa5112014000241440040c0c098594081900500e03200144101960640c141c506c02c0b030010064075902036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 870343741 1250 870342491 870342493
    0x509010e270717071a0f090a2301080103111005120906191a0d0201020f1b0a0b03100905060307080a150e0303090d0e0f18160c0b07050918040c0305 65
    0x251a064040d00410040221085c108801c0c41489117800b51131600d0b132000361b10500155013004140307520b841e8000c0c1d01c03005100503030b0300c0e0262407203c09200c0c1c2014820b24056040013540c400610000b03008907003001c00c1600036a84228205030030101610140307d135448032401013100c1d004024851000185c098441e1502030600307101c030340741d820084054510f900005020140e606c00040200d0812150307501c2260700520490340c9500066400508100300a420b03207210f01c805020f64202030a240400d10000c0c46061032180c41d52900c00c0180303800702c040b0f003e03c40c080c0303485801043e542d64040024602030950081598440042882c0030310a00d101d4030405580d250501c9070107107212070040309407031040c1c01d00d030302800d50215100700480d480750070480141e901a038202150328141d100c030100891400c0391280c280d03195050050060706000280081c3d94100042011070600040350000300680040c2ca40c18600d840704401c00000e10003440a1040100159101c6e040000b44a9004c0f801c01c00c42740210 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 870344991 1250 870343741 870343769
    0x30e04090b15011b080405040b0a0314011406010c080d0f020c0d0c0b061c0210121d070f210f060c0507150b01020a0b0406140702160902040509010e2707 67
    0x481000c0c09208180007605c074402c1403001700043d08107500718485440d001028403e007030b501c90392400d80c40341100c1c5050301169500d102901ca20402e0600c00e50300042c0900b040220032006640c0c000c007130701c00c807501004400e4860b100d14800c200c40d9010740308025008410303164030b0201518000d25441460800b621230b003821002041c42c42c00c2101071341c01c070850b010901c90404030203038080c0300c1d00c05c0300c1c203440100300200804103c5805400307206006003401d898404d0780721103401d00702c2c143c60040190001d0cc40414000d004201c40c079980b09207440c181e460710280b400075035400d003090790f406480c00e00d02030010390510080c40b50065001c80141446840360b00080104030704111f141d0b0440719000c0020380980d2100b03d903540442e4504410a038090712940300441d81074608406c51100b6941524400d000d40e00500c03003030900c00020501030001e06110036003142010300d44030004003e40018800c2aa81890110114521246220201d412180c5001b100703900103043da02015a03445d5140309c1c1c100700326420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 870346241 1250 870344991 870345017
    0x70305010923070c06020a20030f0909070203090d03030501170d0917010e070308070302060906071b05030723121606020901110a030903030806120a030e04090b1501 72
    0x82d00c0b0700104515601402c6240c1c07031880401c400b210360064503403018004495514400506103000a01c0005a00d40d1600c07448071001400618040148580c080140c006108409502d03111605a9440320300888807903201341c40d940d105030304501c10903a03419009502d20a4580906d0b806400003070484030381e030416010710225610f541b0380b0b911442002d140040c148900410820210340c1101481160141c00041c005c0314000c4070740e103031055a5000301c50380d240120300c1714107168040c8a482d51082c400070140100f440d0031f0400a2a100300c0c000000e000e1041904000e0510004000f034a50061b44640c14200102880210300040240c8003172807030303541c80361a151081401060054400c0d54007d1401c940f400c04080e921a400703900203001050410203403008102c001c950400a80f0345241c000e0700d4100005066080c010000c4000404507801030940c100748000c1048005581580180c151a01910188a440001d0082d1107200005080d208950003405450045125032042c80740090720790100c45480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 870347491 1250 870346241 870346259
    0x406031a0f100305100e10150813031b06020c0c0f01020307020d11040b1f031406010203070b0910020d061e0b1b010603080d020702040c050405060f0c0c0d03020607030501 75
    0x51500c1aa0300300d0800c582c481c501c030380070b504a903410040d0343d03420392201a12900503000707445044170320408855180c1c0c2c04110020b1010310044513100d4a2421400910700f03010f08909000103500c00401300500764148401100403100244145503006a0a541d503070114400e00f40e40705602d0b01500c0c0714410314410018550b000000321180303150302030010405042c2c507881d21303520341c0000c15080d0f070015103d0309415441c0da24030484180c441501c540111018a007050001e045410700d41c03401c3c2034034040f8002d000f05a80c00005030340807a0f50011900b1015607034140a207040a451041044140d0f0000c1651141107441d600104180c03040790000301e4042081c800c1403c40da01701d0744500070b1940f0f02040307840c6d8a401c00940041100c5512000410059940c0d529a0055449151f58003140340d80070030071408514007400b851020041c82d1a110b810a414040000c000d44244141c000710480009406004108240a00da508120040846151100905029444030741c01c503590000245042d00108001d01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 870348741 1250 870347491 870347509
    0x7141905011d01020a090e1f0303120509030406050306130f05070c26030c0f041509031b050306150f09090106180203040f0305030a090c03080a1706060702040c140406031a 75
    0x5017036510711440c6454000310207a2000d01074800700e2100e8801d0680c010341c0110043d03440084d4440c4d0740320513032007408044ca03008440c8060f07c841080e40040008200b940e51040640f80c20030403c440a0720f4202140b14810010410124816030050510080014003500103a00d816407d000e98402a10003024207400701a890100800090491040c4041404072200801618005020000103454191101c11060703815843c54030000004109980074020001d9001c02d0704001c1e6030b0451140001c5090900003a04c600c4003c240038581203012501d803440d55100444c0580140000e0030718100750402c4120300d03028024500480140d80c904076282c5203512407901c00c5034440e6030403c411801159103541e080700c083c4e001502c940c00b001e4032400214003250329012040000c51042500303507511450810003130040464942c0701c80020841001300142070700c80a007107c0c0f280343e0403500054007080b04002074941c00c3d101b9041c4105c01c607001c600402c0040e05a4006207201c01400403200c0c40d0982e050400c40259 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 870349991 1250 870348741 870348757
    0x71707350f060a0f09050a0c0c030e1212070807050c03160e0c0d0218120d080c0a02121b060f0c190e0d050a0611070807141905011d0102 60
    0x3240c0c0016000e500d01980498010700001d0010f600e8980d90740c1a4080320032207800c02060240e0350014850a04e00a10031121490303800c0c10441d40043d420744005d041c0244102400e070096261041c14040d000c424000c100e2400c1c4000d0501c2d494450038140688543c110f0039080701c07903210b040c265030080d2030005000e00b1903000c40f06600301000e0408c2d407400301c100c0b00606407441c03101c014890241100d0080c0050034200b0181d68000b14400000020130000101c80306c02e1a02e80d402c03841c02c42c1d40080e480480342c8e501c05400c59840d59a1303107004604a150020f18a02010724100100e01c400000001031804c941010b0040c003124501d8541101080282d00140c034031103070310b05041042d072001c030000c4103600e6048070443c1030051410200030046503001c00685811103080e0091b601c0ca808021062080e0310200c045078002c6814116035540c0c4400500c20344002800000014a200d51080c00401400c400c00480580c5002400040d1804a02903c00d00040200d82d05208100a05504c014401d07541c504c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 870351241 1250 870349991 870350087
    0x1f03050303191415040c0908100213051c060f11090405060d08040902070303200a1103040302060f0403050c030d020d18080a1b0b0702060909071707 65
    0x1640318501803948580390800d0700303000d4548803d92400320049640302c0c079200c2c056102c038003807492a5070010041165404480c600604c40d15010070700054000140303c08009004100060b9180801c51b249080c6008a1384403d40c090110810304070034a20210800003050b00c214800e014000612052100750b4414100803030b140e043c140042401ea1034680c0280c0d42020700030300301161000d09916460150390050300a18407560b0000b41170000c00d5454400e203140151880a41c0e40900e0000a4000a611606104004000a2001c0700501c15400e000311001158020542d80d41c460000255642c1c9810522064446d0f01444140318000d080120716030713022150a9000d446414250101560249040d8003891842d000492010500741000c02c0200350260244400e40080721008109128501c102d811124541406200c45c0c4010384900d4140c4a8a01040ba444516543c5032102224960031100c3c5d4a0440031301a002e010541750400e900110700d403040703420300d40500045098035a071000480411100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 870352491 1250 870351241 870351247
    0x90c171006171006030809061c050f07020c01020a020306040227100f080c01080609090a0510020301031103160b032509080705010e06030f0403021203010602060702060a112209020d051f030503 84
    0x424030b03041d0018042003a22507000b8540d4009c440d914000c175602201c0d50840445000d040c4029180c040158818070b0000348020000c0c00c8141c0d001c0703501c1d00c202800007402071980a001c1c40f0902c4064840c461034030400000c11300140f41016000015481521070b603e80e01e00c0d0030750302007165a4081000092608180c43d1780c0040d440f40400e00c818001c0003880100703140618481040040e13401d000050765004044005a140d504508104807810240188107100c2d5010b140c000b1405800250a0011110b1000c03026440b175071018405d00424800340000300e550201040b22030300d600e40014020094541500c11650216201d00065aa0010403032010307030311290910010b090210307203a00d203ea11601c6032064403c0c040c1c1820302d000700341c0c20030b802c60740240e04500c00300084a641040303107035400310302d0100501c02642080c1d17008890b485600c04104000c00d0b500040c1c03548840030840071000781080f981c2155210035500d90107000745815507a189003048001820310001c01000d000d00e0681c0c0e045806149 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 870353741 1250 870352491 870352507
    0xa0209040c23130203010e070f03020d020f09040b03010204050d030c02031c171501050d021804090c03150b06070605061801060e0a1d0106120f05010e0603060901090c1710061710060308 81
    0x9004000310640f0410107800b000331020019242c00a440190180c1408036101c0d140c2d401000141e4803503c0031940242c0c4180810082603842c41c280e28012074140c24140807084d000d00109041000321628405003038a00400e91200d02d0f804105248020060615210b15480340c03401c8c5644106048182d86c0080c0d82480fa0086800781035004260b0001114041041800c2d01000b2501f50360004c0d800395503001e01d0007001c0050106000b4000ea518078004d4041015005980024140d80283c010140c0401d68900003d0110b8403210708a036014640680d1145066942c0c6a0090960380404c82250180c0c3c0040400035841031242c0d803c1d0103249210354a20443d038200300040355001c8454600080c480c0d2910001014450140314a601a1040d151004014900700703061514101c000782c00300703030b640c0c1c50100340c14080307611030341c0c090180d91005000780787c0100340041081c80c101880100d1003d0b42c0c64810002041c0402000f51589482c189041c1d80324000b450181004440203480040e00399030b1b00300aa40c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 870354991 1250 870353741 870353747
    0x303050405060c0f1b1903020a030f11040e0d090f030c0603020309070909050a061d0c1c050318010f08040507121401051e1302030a0209040c23130203010e07 69
    0xe0f0600403c41d600180d04242484c504904881245049000d54190864500b04401c4104100300040580310110380380d0f50100c0c0b0041500d00c005803039483c109010718100000c44800b2030440c03170f00400a01c4081c0006181a44070140a24a00c0c0400c4a81c0400254817803000104030450381c1090f6501045440e08509501030342c40244508240d0060107000f090081c0c0c81d10844158030700a40003030048016525140084841c8820a200140992810071001c1c2c1c0000440700b81c040c1007a10b050000842e100c22800304c0a000210040a80c0008180d0b1a50004051980603405009a8130452591900e0409989800d425103001d440c603006044180328070f80960080d42e010510a0503030b100c0d5003c080c505182110003c0d01c0400c0624103950f01000305c05024580d0300d40004210303c10340d221501c1c960020307550300300c1801c2c001c0c01040400001010700c44102060310040031502c2601c40007a04143c501c3c815101d00600303851040c01c21546000f1001e0f290300c00e480c140c4104410551658960203016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 870356241 1250 870354991 870354997
    0xf0b0f03060d021c0c05041a040c0e0d0501230603061803070c03120207091a0f040e0f071d01060f120603080d02210903090904110303030c0912010501030305040506 72
    0x4103412202440240d00140c40350f2a101c084106101386045100c4458500302503455260f0780024070450400c00d07800307101c41d03071580000d44511301203900050400caa4102a41d4030702c0f2400400d0f501804002c1c14005000041d00a03141d840c0356802d980c60720040c01d540f0344204041c02e0760b8060701540700c2c00c00990356031407035811203c18025030750440382415a00c2d41c030050340400d45c6d081120314880031003c5000c0c8036010000c420181c08806801d10100326207a200400b102903500174244911400034244141c1c0e11542d0060508450368000d8a02c911070300e01445540301703154440c080e0100000c1c003640c990507013403100300c0d4107039500c5941c1d808074044580340496180700092480c50380e00d55a000b00100040f44803008007080c824450002d030b2136103040c04002900c0c2600c1900c051642d440c0f2010415220004002c58040000880702c49650380c59505104107680760154420342c1500c000001d0005260048006e0b0400140845240c50b81004100880d400d8641c28400100070600500040c010b03480c00300c000e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 870357491 1250 870356241 870356251
    0xb04030c0501090305071412030a1109060c0309100513030605060f10030605120a1e050a0503040906030204050115090501031e05041a0708130303091a0f09070f0b0f03 73
    0x1240c8000001511042e00b156507250044002c1280060700c5810000300e100f6403c00c56140034094002500712603280c9400d444002e1026035165991040240a10484402e403401e064001d4019600c85540e060829501e40c48006031030f00c501003850000c00c80710320920440c0c0d0a01e0310480038514051556a94001600340070b00440d5002000c0c80e010b62060b22050075248004020b6a404241d95141000780101c10b041e0081c13a440781c2c0c0040c50500042151216103090382141c000440388140d00508142e410090303000ca0081031408002340c0098040400e030803140c1928022903040141e0790f40d80d0090a4090020000702c0b010400c0303544100101d6000398000c490307010710f030b0b000d5400c040710005400d8120b640071142202c03036050540c541e40b4185029450552701042d81e00700200c560805a051000761809150001e040640301e84900c1e08001040800d442d07412628150380d2460300700481040400e15041714088580d00c14024000f40c0a820f041e000021511120769141c40c00702c1400b020b07119544001c00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 870358741 1250 870357491 870357497
    0xc070c0b03070e091f0b07111002070b0403060e010b013f0207030908010c0c05061b040b030c09011205270304120b240f130e03030106030e060907030f0b0403 69
    0x45260f607140c072010140707441071110b155241c1c040510102050148450342d040301641d52400c0c07041d117002451044143c0780108013102c0182118141c034008901d40500c9421201d8440008507001003040101c5c0c004d290316104a1b0002d002600401004403030100070000007410604e0f9410240e1a031440485410807200480300c0c02429051001440c070701030368003605049000412000003084061028407500304401094644420b4080c503540700c0903a02c090250107911038000040f600404071311003c0840307000789124400c0300c0c0c0782e10346401510400c0d000107081901281922081400d0301c14644504c911850017150f4220440c00e0f156407e001e0304400031200c40b01440200700c0801d20300d001c000d8000c840b5214a481010520348400003151001042c2d40c041e44000d80c511180185a50b040301000c0d0002d400d0303a00d60f080041c800181009090180e030050014007000002017505503051f080001041030000480e0f0042d00d9442d2025070340c0e0094440a000c0302071152440000402c0c1c401d485421600030701e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 870359991 1250 870358741 870358757
    0x50c0c061908250c0b0105040204150807050702130b01081b03220c09061d010605070b06130911040c050f030c1308070e0105120109121107030803041a0c070c0b0307 72
    0x300040c00c1d03c0c0510b02960000c1000d2258003400c001a460f10710f800340c0030545055090915002c0031000060f440d042040a1294102c001651307640710300d01b0754500d41c3c4c00501d2210740380c1484064500914850300d5040c0001c6856001030140005c14012600c5a12641506807079543e5a01d0082c2494400c0180f81640e01c1240c09050003081071000703800c001d40400c84c000540d0034900301581c3c0700d100e5503a04030703030301c801c03d09004112203074206c0c0c147c90820360403640c2c0d0443c50b40d4180000ba410910041d4400e400c51403d1400001c0c02115500140184020703101005108520300080d41c50b4090078942800341901000041c1e041034648010701850300d00204417505041d101c25080d810f000d50b84c4c02064140200000402142c40d060b0300a182c1209858002c105a41d041e0300c441d000c00b004002107505000c81045881e0781c0207000c12901c002140c1141c036654a0342414030384000d64402c5182c4001c140075000c004038440710401012074013415400500c80d01d00d54a86180039506420003040300703081c45007107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 870361241 1250 870359991 870360031
    0xb0103140304090e010e0c100503130c05030109050d110307021f0201110408031801091d040203070f0e040203070e0705030403031505090c07030f05090618040b040c050c0c061908 78
    0x203401011180c813108400459150301403007040c0d240680e1700e410244140070404400001030b030001c080b2600800c00c00030800404c1d0260600c2400c0f5181a40700030b40641c608650708050240c00304204400e072070160f40c1c940070507500741c5003d540c0340200c0401075404000001102c007021000940c040c0480002e000200701003e400e003000300c2681082e8003042c1b90703800c0010102c2e4055032003c0c0040042e0024202000701340e00300700220014030343c50b811840c3c070131000501080a40d50308000c11001003002e25241500d254035082c4d150031030b28007960100d0091240c81004605080042c0a0910410b200c1d0fa81d1811503907070741c904030b018020070381c3c16001041001d0004900341e190040b5091251542a140940d11410340c44c3c01480380c4216158201008401cac0044904e5a0703403502242c00010044610405682c03261000a00810030038546560003403030119803115485e00440a882c0f915180800e0700c000c5c0313142c00c00307100161003481c000501140c00c0440510590f0f001d001d203582c0050240c281c2c0011a0300c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 870362491 1250 870361241 870361259
    0x317060f061c0c1d060301060f08091c21060825090513121d0d0606050303070c05120303011508041b03031d0102030f162f18040b0103140304 62
    0x1512240303c00007058040007040244141c030b9858406281500c04500d150724010009002503000410b110400907400046100888100704070400c034041a83d815440c010300481c040c14a9030b0f0030045c400c40011040d100303010180c0c540f0402d8200c0701c40c9405044c902e04034a080c0da40c12170b80300c00402c84c54106c0000100c0e401c111441400e104543c0040c24071401182c90800c0001190f5007080c039410060204140c0c04078041c4007400c20f1600708140c030007031088207291078120041c00c181e404c0b003501440080b90340b806010008040e0345c11280c01b034440e000e403102441202a240d10090003180300c482c0c89120b01c00ba031144a010400c2d80700c0d00403600c0200100b0202841e0584100ba507000b50002941080e40c00c0e4444440310b00781421a400b40002e62410901180204c81c0340170740801e001182c0041c80c01d00090100407502402100103580105943d61441014016a0701040f80c00034051a003038114440b0103000d149119020315007082040d84c2d180e2840c0c2c0c0b04811504810030007206030100b84400a94140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 870363741 1250 870362491 870362501
    0x4091b060e010e0f031b010302070512071412070803061f020c0405010603090f02091e010f092909061c050f0c030c10120207080c0a0317060f061c 64
    0x9959180c1e2001a03064000600f8400d66001480c07090f49400c801d10075503540052903003414101001d1005401404100680080c028080090102e008188a040d0711000300300042c54058410440d01c0d0008004108040c0d03501a141c155a08204040110001090358440512b91104006101c014180e030716901045020540d08800c0015030311211892959103458050035000d4451440c04008001081c1c440e50305003584214044c0c081c0440e400458224030710024081e1841040202440d25035940c0c1006540c02d4445208500d2401d01e07003204000f10000e400842c10500200740381c0b12030445c588200b00301c1c0040c800340030503901a0a021003a0001401d211001c10824040d0000c1c00012200413446804c01001c0f60701c10f4400e4000b03200083d160366400b50001600210b07454100c0460b00403074107100c004d108440000c3d02801002c1840d00c91a500059010030043c0709641d480c81c810085041c8000c61041a1140c9500c040d001c04070700c50301e0400034041d00d5103802d4418034480c0d6407000c9403a001258 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 870364991 1250 870363741 870363749
    0xb1b030403082202060f0904050c03100504020c01091a070306091a0111010b28080a021c03020c06030123030610120c0b07110307140a120302030d0501060807030f0b06070204091b 78
    0x80100b0405c01f2031a0521840e580715821003a04c52451420200d50031810200d405154801d642c04240da041d840320940c2300903001988020360591190808034503081207071049400c4000030313060071000f0038aa42079002d1050421088032106d24030b40d808030010748a409100e035104c4104c0d9078441c0350142541e60b0301e010020403044580c0688440d00d00e54201450304c503080d000400a5804840043e005803503c80e00500e01c02042c0000d00d0605c4070300e160072800d1481081c0140c0d48a00048000300ba00c80402c542c000e52240640e0b0700015080ca52000c2c1503c4081c12141d40e250042a1a004c00a61603810b000481d02841b5041c105003242d2901d441800d103400c4114165282c4004000070754250904201c0303803018000c28041c0034048041000003031190392490154411011004640c03074100350003002500d2423004076800c20300082da161440100310070012030b20000002c0c04c00a80040c003001e40c1c03182c08180031015040d540ba00d1700940134800a0602d4035000c40d102c0c04040c6c4894000d00030015220054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 870366241 1250 870364991 870365017
    0x15060e01021f1b03090807080c0a050f060f070e0f040f0e01020408070501080108061b18030a03080a1104051e0a2403060f05030c010f0509030106030b1b03040308220206 74
    0x405104070700343c0c003044541c0d10038000341443d00e10340a0110b030082042c0c903280f96001e40d449959020042103181021940c0782e008020780304224041020110128030144540c646031210100d55880791012241860002e03d0150404d403607000e94100c40c02c20350000d41c078000c81104041040103e0024540c2203a10507031102c2c1b07958018400c24002980e205c0950360040046100402407410700c80d60b403001c0050038104865202c2c000245c1000e0300340c44008864031050006050394031015003030402900e100ba007224000f0380d9614181e40c20350f451112209903410381b00054007044108241400b0f810031407408000d200d510907001c0c140061301e000e4020200100b48512500459280c0f50080041c0070394585801140c145603550300c090099840025842d00703582004d180c8204d00c400d90100c107076418803512506580550a040010080c88074003414540109040e1000f8030512107600d01d41c1d0000d004c2640c00800050190003c140131200700c2400c1e0020402507940c0c64038012250340012120360001c0181110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 870367491 1250 870366241 870366251
    0x220302030d030e1b0102010b0904030c1703070e010e031606110c0402272b0b0603060c07020d050709091a090d32030106050304140115060e01021f 64
    0x450506104a403124900d81c141482110125000f20f034480c1c00008103104a190b80940c02c481c581c1c801d41040390f910201030204c4030345080c00d0500030200001c000080d215254164801517107603c9040440744560303000e42d207000240e040c0074011103d90714003c01f40796052043c9881d0464040c0243c0607000200041d807680308103280c1c00440b039801c00d5a480c95241c400c0d4418000305080390034005440c8000e030a000444144020100c0008a000340b911098000d40c010500e001c50225410003030140d4080d0280c441d6102c0c0f95288001c069441c1412610f10706108070610082d80181400d491000089204a0584101d581c070341c0301c40d00458441f02030a07036000004079415407800310032003d4240c211403180050410010390140241050090445000c810039050441908400c801d9900340c1d5408490703010583d40c3c0d40e46d024010882c0c3c00540e0150b0f00000056100c1911003014813a03007441c40820150401014503011080d42d0050901603481e041d400758404005509520350940358525505041c0011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 870368741 1250 870367491 870367493
    0xf040b0106020c01080a2309160b070816030504090c0305160f09060810091a09060d050a03121b03060608061504180209030304081b060f0a0c03052203 66
    0xa20010680c80002503420200001c40310340d90203103003603074440400762000c1036010341d1802d4a80a0056040b681c80c040c2104000d014003c003000c10a6a1b0300c0e611b1004004d034641d120685238145110341000145100410800d08100200b10701031441054000c3c2420380c202943d0b02c1c084d00580d400c2c1089000026640e50070850f291254910280d15200c6910f000441d80074101c1001e0080308845c000e0100b8400d6070000038088d50101015000605100302003409070307135148041d4000340450144514451384200d03000170340c24100384200090039a0407000401c0c0d01d0b8074540f015110108144542c040d850f403941c0a415068201c01600400a03d4a0341e0003d2144d20300040240b0022000d06024458a40071101d6180b60000d541030300e0a564000c1c0350729641c4001140c45800034420180342c16090b000c042000aaa101c1c0850390700300c02225000c00d4640018805d003001214800c070341c6212002c802c103000b8800224800c00f9030104040c860309110b490484a490585102d01caa1011116607003a2250b040c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 870369991 1250 870368741 870368753
    0xc0408191a011d1503030d0e1204060815040b0d0b1003020a0e10060f020d03151d071202070201410711030d020c060d0204090c080103051504030210230f04 68
    0x44c0d1101e2038035064074102000c1c03c006a241d104090109206584442c002a841c02c8240000e001c00f0f105c000502d580c4540ea2070002d07001034800c64000c10020080d0751041514203003070043c2c00031540c004149001c40f80307160742c6603000d01c00b02800c014041d288070080400141c4038000603001410025003180c255103080b0016444058168003d8030410100410441201c2e40000e00030200d048503080c04103d000101c451518070550b0741c1d02000d40c4401241840c182c1c0480144c03000d020b001203a848080d46011442d81500340e1103071200090000c0c290540300150069180404d6110015605101d003032a01c04000810561010301c54101c1440b00010300801004600380d9404480e5074160041d00e081c48110741c02948500b000f04c0d01d24001c0701c000078800c07415142ca40c1201c002d424000f03010040b1541882006180c0b80302404125128400e94130b200b00040d401943c0300e88900d50590007400748024110228000d000c02c100c189610341f0701800c0300c1c0c1083c1380c1d444a0501c0f8000d800949011072074241400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 870371241 1250 870369991 870370049
    0xc140307030230161b02060d0f020c071205030a121508011a010914091906090c111b040b03010b15031e070f0305070e030d0c06050c0408191a01 63
    0x4140139020280e070418485810003110b400f40300c3d00c070b1140f180d41c4a060010504921807600d10a410310710307041c0a51401d40c0c866000e00f40200505003110075054136440304020640035498054070316401401480b8409104a40100d51600c070070001040803155224408546101c680000c4001c0c1d4403400b50540030103550f00300f6400041d00b444d10401261805145807002d01c080c114407409003480a0001c0c04048411400341044c01c0c141d0000c01c01c403550751510000500300c0414038000580310701e03069945080e0015100410104240c203920300c06254004001c010480007007007a8040d52200d11100041c0c1c1c84550069040714110051640c1c1e10740f00d08910590303029256074036445540326052103906648100e48003407030b050780d0074000358035110b503541542c1c0c480391040029031601c5030039041c40e015640101e00c1c00d10b5510540c001c1c40b550b103d8081107035041c0900d0081207202d40c052040c2c502828a00502541c00301d0080d220190001c105281d40740541400360085c1c90b00c81b80300304503804030003000052 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 870372491 1250 870371241 870371251
    0x140a03110a110603221b060305150120100b040b0a08030703030f0209040f0f050603010204121b0b1909080102090d0f05010e0d030b130c140307030230 66
    0x980080c0c2800d5540340b403048040c0e1030345402468040001000c0200e040c440001c0d080d003860070103490300c8851524020895030503241e90519483c040001803018060b0051600800d03402d8074001404540c00d00448103003040b28818050300d5448400141c001c2401d101c68040c01c01009404900015400148015076002091413401180340310010020a103010040c0c444691b490302d804286255810200e002038051003402c0703948948ec0142d16281240194001c42100d0340b001c1040c4038135a00c0c901054200e010302c0c807a180315145186095000203100c480c3c41c0030340461364021811956155184a03081380c01c03030340c1c4400302c200260b210300603e04c1d00704000c00000c20008c00254941815a40800c00c0c418410800801c5c610789030140d032041010a42000703000798044411070340e05100c2c090b8014080c20320528400d015512030303045020b54010b580140c407020481600e0b11080401c51048005096100500f02410541d080c130207003101414030b0058084401c003a20801c0080001c3c1980e40c00c01500c0909 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 870373741 1250 870372491 870372493
    0x1506030304060f051303081c0510180c050c010903170a0515040c20071d090a02011b05060702030310060e0d110409020d140610060228140a0311 63
    0x100800601d0b0344a03480c407189800c986807007521503142d4505e4034000119504007e021010119004158000304c04d12030f140810780c420248080d8690f5100003004c00e83c3c2d8054101c54501c070b00102d0034031002070740094108505510b403040c5048002c01ca11401c4410094080f00058184c082491808540074038030f42c0c0103007860b00d04000c107040640403c1c1415100703075000c41c0115140c42900c00094007030034580721252140b00280c215005040c101e6a00d54102e402900c0103502c03034004443c42c0d000010b0201d0f22030b02201000701401e5400340c0041d141001031003841c4900407040004540091000e002042c080e07003442e0021030700ca09148941300d1441106401078800c1010310a8405d4070750781c83c4151400c03080c2d000000c2d844521a03000101c0d000e00102c0c50082e411182d00300c00c032401c1000e41a002901d0804030401d40300c2d03035100c066803124185114842ca5005038855141c45400d21803107001c02c408041504111511512140d5905000f0302e0b07038408049540e001100d0100906070007044080310900c00c0f00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 870374991 1250 870373741 870373747
    0xf09020408010c0809100c0e101211070c05060d150e0a0c08040f020d02060c030c0a1101080105010207030803190903020109020a050f0d0b040516030c060f0302070803040609050a021215060303 84
    0x4e0300955440030a5403441b20056140c2d2150114540101080003054402808003464003580b403001816515200d40100422481c00488020298a46041d40c4100350301c0310f941c2159620341001c00c24960014a0846c01007550b884000b1a81d4021600e120002e2813000b001840d02e1130400481d0085401c103902c6603003401120003c0000042c42d0301130380303c1074030b034100d0300444031002d00d0020810324058405070501030300c40007a1040040c10002012102d0078170907100c4e88030384c004038001190408028030a02d40541d200000c20302c000340070f02d4041d6030710038a41c2a8686a11804210382806d41d00c8a620070b401603590764a16600b0b606081040601034103082c0d4449a00340d007400d0114010045d0610040d101045003070200c0c1c20060300344002c10b0311390a10710043c0c94060f100e01f00440c8480c0070b80b00e8080031414600ca0b0a07081800307030003a580760030f400031205802d65450f522070714081c2124440803100c0e40112100c16006a5986d040c400c408400e1200412194008079040060707260050b0a45110307074018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 870376241 1250 870374991 870375001
    0x1203090b030415091b0f081c17070c06020708040302040f0e0c010c050c0306010b120a050f15060c10150f03050d18211203020705070608100f09020408010c08 69
    0x43c40c035016000c40460000301c8842030f0406800c83c1540c841c410722082911400002d0400100d9100800c1d58020003c1d9000c3e8003010313210182114000549202003445000c4524041d141c0d80e0506600c40c0360390a01c04c503007102c55513a08089034880d92048444c114082000c0c0190b041034410150a560103e03001c11401c1000321080e0364034101013050034100101581c2000400900b03100041900502a007103410950b1584000200d0303403c40c45261000b141c0f00c10014401180368040d203405040000c0941707040b501d40380f02020200d00d4000001c2d800880400c002c40d151802004084180d282c4020002480c60384414402c0c042c400c035511401010f5941407040c00820004200b49141010609002c2114031981440c40401c0046901c00009401c04d500000c403803034001c042540c0483d10488141e01e4120b52104194124040c0a0014090b984034910030300a15004181e09034010301001107622a0541e242c2094009070369640000034103540101302040707010300c00d00803800000d1617818140390603e41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 870377491 1250 870376241 870376253
    0x20f010c1d060a12110403020904050d0224070c02220912050c1002031305070b1306030e0606090901020c010608010e060106092403060512010509071517060f0402041203090b0304 78
    0x1c12001e10342420741c3c1d09144041505d410341181d0007180d020380321036981d03c1c0905107036807589180403a401c054001e56051400b2041245950103c01c5813000a100540d00c030780c03800b1140300d032600c03204036049000030805401451103101021417610084502160610062410114508400c040302c5c003400b40a00a1001206d40459400800f0001d4a0010b80341d9032001900d42050b440000041e005001d0b42c580452070960320f030000c00f101e04042c10320640703d5035500c1080b0222640c0b4074204c00b03150440360111b1114035154200940150b0200009401c042110620710308544840e8480b480d60ba540700030104040105129140c010600ba0512409440c500310100516801012102e000c00c54a2064160100d0207540b007040070389805480c000002c0502c00046000702400d8035884110f1244442c0003400190461882011450654650a0728034101c0a440800c690141c02035600995000900340e090f1264400b510040180e184203261400e0745003005020030410b600710001c025401c00400010401e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 870378741 1250 870377491 870377507
    0x13110a0f05090901150b07061b09060503040228050a08060c0723150604050f01081b01091d180601051c020d0f050102040515090d030e01020f010c1d060a 67
    0x120a5030110341e1556280f0080d80140b011510700002005407940203e020550003001d065100d200e41020040440c401c0d008a540c003051082500c0003620b80f02c01409042d1081e800746812500c050b1450038907130542004240741c1c03d04699000682c03c0402410441442e000016800400c1c00901820b440d00700030841000302d00c43c2c900058409141029080c00782a03c400d42107001c0114070044d500d004407401c01194000105541c491b11950402022032021018420600c0c101c860800040070311081c1d1506d40b2005c0281189085d06203d50540c5c0021002010380d0b0b001810203041055140c10b00e082014400030f0a036403040c458103940554010300c0142c8031210b13680d560a0203080403070007084061000801e00d5240c584003e00202009014800700b1405402800541e030b41241c041c0030030300700745c0001807050040b0440f05a20103419280324000c41d005883c540d12138801071042d18064030303c5019030b900750b803d40711140000035454181032504902418119035118800c550b240d180844461005011b02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 870379991 1250 870378741 870378749
    0x3060105010e011e0806010e030607090e0c0708070b091e0309042c0a0308060315150123091504080a1b081207060c0c1a07030b060313110a0f 62
    0x110b0605800090750303004a040358544102d50800c0440540e0400005102c01004d50720140490840d06140040d86400b1842911560300c569800c05040d1901000003124007010b80000074204041280d080410004801840344501505c0c07040b44c241466000c50340303018007c1c0f04080001102c41c200d200c40703520100c1200c1c0e00304000c031004101b1542c01003655084460200040c1c0c40004080c003c07401818000c0f50040d182e5001e84c540140e545c0d183d0081c56192045120301c84803501c00c0301d00090190030045003c02d0004818503004441003180903280d089214026001104000085401c0c0d1561904041e0403000c006900000783c2080c0c982000c0d2a9140e8082800810194940f1074181d00a0403404075000281440b070104d0791030740380c21048000709501200d41558050f0030540048210b80c0a04c0b103e18446501c208400518140c00d40341e002186400b074080310401d0327101c0c480c81ca40b0f87d449801441c040c2181c4400210404050710706100700421a04595001d68000c2404109465426156600b15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 870381241 1250 870379991 870379997
    0x20105031305030d09050607021e0c1c0204090b011517070e04090219030c14150307021006090c12111819030507051e13020d0f050a020c1504020306010501 68
    0x281d54685031141c2076005081c3d402c8101494003004006000740050760500800f000d400307552810b41c0100c8010045030801d440b0355425481400c1198440c205245a699401441050a076440301d86900084c10344803041d006689825a800c0140541c0c10003000070b82d2082071a04010000c2024001c2070304005030003c1107141404040c4400428030303150b80e0407040c03046a004143d203808100110803060640c06c20b000c20f8802c2c400d100700201e03001e5202c0031311000714a0300404601900c6007001070403100303500091500b021409a02c441f05050409030203a603000d0500c00c00049041002c0e014002e1110141c01c0c42100c245080844160021f240581202c1d151103420a041e0a50550340000c00c4842c0c8031000c142001403802080042031003000329405040d100201d646455800280714201e5400c5803c07109160701045048070242d9141ca5130780200880031710008042800c0c40403905000890740c0840741c40c0b07022500001c01040300c2d0b00500200c5100302e40007034040f001d1f05051b00881d60340d0751305020b000d040c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 870382491 1250 870381241 870381271
    0x3050a060504020607050a03080a060905010e0a02131206020a081f0306050c0f07111507051b0d080703090e060a03050a112805150c0615130905011a030105010302010503 74
    0xf90f440c1c00040312086a000821501d01c3c00302032400404103102203462080d06840e005001c42c0320417080c0030300d0741200c1c5061911100e40d103e40c215240250300c54800f419840e20444e500290301060300c1c41604000c0c2c0206070060303c454075003d002e40f00f440000e04201e507400010100c64400140d41c049241a203812500004060382c0d5420700ca00070703126814110009101c0030070801c003003003200841e0780450b08041d2040d500b10a4040c512412078080c1d030f54020425002480c620710711460207c1e0700711502000401168411a103511081d025500800c1c040c3c00140a43c0c0040c0850416580f5441d0031603020f41d0b0350100e291840e00c9068541c01e03203d000138002a0f880349100c246584000481d03010711151154080650b551192144400ca010f1149a02400c1c21a5200884241082c01c1d507904030390301d20180c00a9502d030030044181324010300841f40c2c406090001d9420002c82c1d4414407914505c10340c00080e10000300030486407240c05a8500034404e0381080014001030340d2100036a40c0180c0c0c0444c9a41c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 870383741 1250 870382491 870382493
    0x9101104050d08040518010e040803130b09061510050909040f0c080d0e0d0c1203020a081c06090c020d1404050603042001030b0a140102070902121f03050a060504 71
    0x2900e10480c0d000d03039840701c0102041d10500070540010411241308480302c1001c294a1454070541440034070400030300c4903580e00084c020400e014019588030b0a101c2102101d61016a0b600740414000e941b8541190700580030071000d09080560031480394030071149030030403070a81c0b20001c20910403040224042e800c5034004c6010018141520040d16038482101d594080d155040340b540c4502d07a480d140c0000c2d000b5407070080c0c0d03410220009040326803c45504a04e481c02c0101c03840210109407000c90031489580041d00114481d440a88a164070b442c000003140c018000b00e00b81940e609403c0b0131805450305030100d00745e0340c0018440c4940d081a0400103e0800c00c104c1a200f68003c41d0303c81c940148002003000f040010b03520f0755000c112103070000d6001c1e02840c800110100c803079850080d074000345008410700c1a205041407003000c0701c1d01441140d00254403a5540001e80e0044170703003d03c034201350301c060180161006266200110225406600d26031035616059030302c0900900c060700090fa40e0011030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 870384991 1250 870383741 870383771
    0x60402220b060c031c0203040309090c0507022805011707140c0a050c090f060d20040e0c0306010602030a0906050d020403140d09050f012015010621050910 68
    0x44a2103400400603a25100c11543c2e242c3c40354000d010044c0d20060381c4440440082c1d481c0b007503034010354050fa100010241082d11480050072030f1200d400603c4030910000c40140d8a04960281c509030f100b9580361001800001245100400d801070350602c520354400d0b2803d07412070642130364403031070b149005182e02c24640140403c40c401c0034010407503030041300741080c180000001d01480e00c20003036841e121700e551040d02c09000f401c825959168040c40c2c2c10740140208103807001110440040403c01d11207206848001421204a0507040b062a0420586000c0503d07003402614010705250000d103182452011000700001a00d005210900038049002e00c108402a81501d01969012103070085400000020f40c2c0d030340c1c003480c020718002440c2c4100842c05090400400700085010307121070031026110500c01050401c500001c110500c0340701514034121460302d40d114001c28460f02c41d14511444181038000900000302000a61418817050080c44080011607206880180100180101c0d43d00002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 870386241 1250 870384991 870385001
    0x908060a180b070215010f030201320c0f0d080618070516150e030901021203150a030b0411010c03081612020a09090605120304030f170703050a08070206040222 70
    0x60b00c040c4140041000d000d40004544090815520020300c5503039aa03600d51003411020300000f8005100270030602d8035501031100000c100f103600711594044005510b0381a1040e005041140182e03070082144003d80c4a041c00030202c0703051279191428691030220042500c141e0300300400b0701269004400960154840c009079900c0e508001f5011540c40224100410100140480780e140e681c0390912211081d03800204685ea11401a0003821a01b0707200d1728404c0d0340c3d800c01030813041106412422003a460b41c917030600c04003840c4243c0c042c0701b840c1440d04009481c1480c5404480c10b226000440501103a00301d41c4156001d0100d003c45221210740d000200c1e05007405090291101d40041210100706070003840c203c0c1990142c1d00200040382e600c0c410410498213110b02c5003920f420401043c40416551810300583c00e0003074030003c665240304c045040f82548001025800508040350500203254040c0c0c00c1a04141d40384001c07c007a050070b400141100c0300321886242d1a91040c0380300040d54003941c1107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 870387491 1250 870386241 870386243
    0xb010828140102120a05060904021f05040b0a03061d090307120e040e0f0c03061519030c0602070303170906010501030213090501030b010f06020601080c010302090d02030613120908060a18 82
    0xf50340702e25412458242d01c81050340c00c2203c0c03070704100004605d800d02240b000d1245800130454030320455012021960071103032000d1581044002c00000c11447c081c80010035a4651b03556000804c18500416840c580d0452800c10040380950020710100b02d200006582e800760f00440f41c41e05201554000381c5582c940c04907615002810a003445c0200e81021840d4440c0c815441c05031003004802404060302c0f0318044500c1c0014201c0450f0300c55040c00c00342003031400000c1004014401d00c0d10b07a20384401121055002000503401814180105940601e044440001c070619001305802d01e6401142c403640140130b464101940030501480c4a2101a0864014000c07460100840c1d610ba04001c255500709000b1210240c44c9410b00141d0740e4400180103040b1504200a08406084d4800440c040c4d440280c00642c000b40700d500da80050303581484031502030820a5104509603649180001120b10700d4140c84007403002c44001045088000304600742d2041d21007500048000842101c40a05189504 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 870388741 1250 870387491 870387493
    0x1202130f1406010201110c0615060c0a061a060412020d020a0f0f0e0609011508091c0c030e06190e030102071e03180303090b0a030e030d06030b01082814 67
    0x16500310020300015500b4050442039009100c01c0c41640194419031050b81c80c200c0d81580311000103903800c018040307090304c500760040056284c8281209402e02c0c2c0f201a04d4192a880e60700c2114a400d00d5054502145403501945c5140c1814500f58001da03502c4a407000113400f035034500300d082e0304640d100440701000d0051702c0c3c82c4a00068a642c692a04000280200d01941c006078002c00d400b880e201e495541203800c46100c0b100d0707405070704070125940031019107141050301c02d80c880208200713103403031203020b1700e00c0c0c590344102e98203515050080000003440100d50040404200400f06c84207102c000240741030503410a01c036421034410200b4020b21500030040c0841e00040c0007080000c0d10802241d0b100380c003079600c060a106c01c603001070125241e80d01c001404981401c00810105100030060810180c481c200015100ba10322440f82c1594000380303a80000e0f580c2c0f5102802041103c140580c0500501d400420b100e8458114218910254061040016030668030020410400f0411024020490b40c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 870389991 1250 870388741 870388751
    0x150e1617040f320322120f03020f1c0e040507020705011d03030d0519060f030b091507090f0905060907140408100501150e0f060a03060302090c0a02070f1202130f 71
    0xc524107449405c1040d01040301a80c95188540c1c00704820419010742e00d40c50003406580d511990b070804030396000380c000c40a60113191007403001e101d0309100348000d0101d11207a05a5100007072000074001407081d5401c61269181105000c003503940000c040c2d003a500c00f030901c18012000004c092003040950041d507641031000040520005000303400050003210035144854044500700c41e0700094031118060b070882e4031590f590070408501c00480741504404954150382004400c041108410307402101c03050007044081c24100990702c20100e001c0000c01d1010700421407424628009403030010050034030400c001071902c8100384030004038115001800d4031003c4500101ca94914540588030921886181046465808441c1c5000e880d0101000c20010000703039021002030704005181d007101001404160341d1f444040010385446040c14016628152060f44505250000078603080040d00052510070003c03100b0450791407000ca22640e81641117070620700e104500880a00142440800010034038142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 870391241 1250 870389991 870390083
    0x6020d0e0c0307080a260d091704060914040204150e030d0e100804061805010e06070c02090c0307120606030f060f18150e1617040f 58
    0x158821502a9103030000e40d901c15203850101501d8440034442c08140d500310315482d500051b900d4429010030350040c2c40295448040a1901026802c0220142000c5680715a140f0902c501c500400501c0440a003003140780c14188800140b42500f540705048002e10f06101d020b04a660f5501070740d000e018000c00700c00c920000c2e030f80700424568022900a000e0300400715950380003032080f00506640312010f02254020402c0304030868548800800c00c2d80c04c690381d204403c5200d2044c081161280e4050380010416680201000341400e401038040d8082c00558080be10050312403070b44140e40690040c0c9082d441c0d031f44008054603540811498645068940000468495055840580807000003c801c200c240e4a401400e0100c0e801070144104458612844504000841d08050780390b42581403040201ca035610207249034410117071290300300c201d1008807003454070380e224048000c00248485201300030304040c0ca810ac4c001d80450f0024281c5007403508918101c42c040c206580c1c6052010000078050205 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 870392491 1250 870391241 870391267
    0x3061403030a450905010b0a111204060512090601060c020d0f1704030b0a050601051e07020d0b1819020405090c0307060306170105150f1504080c040f0905061f030602 73
    0xf0000002c040e0800305000490801000d1141030306860425054074a4400304950940b4125070040c00290303d8801d10400c102080c64450240c0b0003002213494550300c0d03141c04000c40d002120000d0020340c8981c011001000140c0e409520f40550a07015a065100080281000a195070b145c0e0000f0b0101e098041e07000e03400d40049401001142d00440080406458058185040c0d40c010780f00a400035505001c40d10780710241d8280d0030021000035502d580b034010b41e540420b50300c1440060542c0c1d0b42c0007a004001003080002400444000c000c8081c4c40c008004100091600d1180b14001c0e01495460000900d180c008200b8968549c0009044a03102c0750381e0003006014000b24052403020311407203c0a0300c1317444014010300d0b00958000070849138001482003070241d0a41d00d800000d600040b803440c440012440c440090014019200c05440502108018401518003284804d94000d18005800003c920b001c10602d401007124100002d4540703000d5444480200e240e08080c2c00380d480040c0300e541e1076907 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 870393741 1250 870392491 870392597
    0xf05030a120506030604020f011809051005040c020f060c1803030d0c0e040902010503010315021213060c05030f13111009030c0b0c0607032d0c03061403030a 69
    0x39184505010342c1d07a400091648071702c02914000e4020842c83d140c0030166000d02c03080e544040f04090881c2656644280c3d0806503a0190340d44203929003040003c1c091030415003d4543c4102c554001031044a089600c04c079903a0f0350050400304468404203009848503864166084502c0740101200d0715642400490002054403008000101c0c018800b03400c1c2c6420203000f01d2281580507110319046a1940c0c5401c001c2c14200c2801011240c1d00304043c044001c04410000d000e0044221342c40e1405a070386c0b0b0070208036071004002d07030f042c007209204010044a01040c4070703902042501d13001d075540c68185441e03001580800c5100394803901d0045440101c0d40d010380c103001100e0150180c002e00c2c51380d400207150f03a1b1054044020154201400103107046000c0d402290452050804181c944100898161030b0b10726088184103405480d074180d03e042c147d040c01140003621072109a00340c204c0035440081d40da442048a00010301a04a8040740e0f0a102000f11080903440303521031020443c0200c0c05900080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 870394991 1250 870393741 870393767
    0x807140c1f0f03020f04030c030c03140c060403120c0606090e060f010803090d170307030c120606021e1009060e10020a0507020f0d060606020c0406050f0604120f05030a 74
    0x6459000d41c581080a40092400510064482c40d5040c1c0015000700c0280d03005044400c449101044000001189410039038010b5006d20706801315141185841100114141955041c80e40528400c00031030b0350795400c59007180e0f03110080e04a00713501540e00352642c00c0722200203404a0300c4e20000045820f4950011004000400150303400342c0d403401000c01e21214280668200ba50080c00380e4141760070315881c024031030390040700b40300140c5403114401809580211040000a0746504546018541103011000e0000c00d504041c08060704203c00259512501441c2401c0809040700c484c040c03c45c03e018114407100440e1091180b00703080d042c050040e0456a107006243d03c10500702c0c1c8400381311407007174032000001580d840785489519020040b60120b510640c0f42c0c030410280c0c03503200140c1c45203c0c880c001c0c504e81c0c025007036030261034082104440450b4015401644070800e00000d554a440840f01071320500301001e049010503007442c0f00103040d00d6100a00c548000a60702c2590307500001172510403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 870396241 1250 870394991 870394999
    0xf020d171f06031e0207050304090b15180f030a02100f03200a1403040308010308030c090607030201060f0f0b041a0405120106050a09060e0403030c051303031d09010602060f040807140c 81
    0x44c40e89070710030300d089114100c00502160070030b0005100d0580c00c1d400041d11040001e12003001421244403030b040650204a028140c0c283d60b1809040d0303800c040400b1504854214081c1c00194205d802203411560010403000802456502c401e040501070b0344206a4114000300e41450071805202621142d440741c0303e4038000c00c00540c000008146610f04813486683d041e0b0311040164038542d03071000180c10151103000700c484144001c100a44920020749162400b0ba800415428544003043c040342d1034941090b50142a5840700b8021480a00c0407036088402542c00c200c0d448a503011082c1c054011030f000141e10158200382000c1c60081500904241c0f0422240a54903641c0c0d445080c04440b2944103061811401000080220f8001d82c010400303580c481c101a031038908003c800c2c81c10308005400c02c80119240f521903e042130f03060002089182c50544101c07107070754102140a035880c01c00420b41091030391203a000408001040041e201003a9010400c0028102c1c0490040d4507406000c0301c09000e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 870397491 1250 870396241 870396281
    0x21e0304051209011b030905100509041a01050f090411030408040906090203070906030f090b011509171e10050a0e010b01020a1e031808010b010f020d171f0603 70
    0x103070742c84603011a910204161501422100054015801c0c25003030781080d001c3c000182c00014507615007264800d1264829070382c0c1942e0340829000c01088480c90024600200c04586003d106a40c06c07808803030f18880c0303130343c2111746a42600d0002000350400c2500c1d061101c0c00070040c8030030460504041c000f981c1d00302c0c03014014191101b020070100e0008a410394001803501e1803c000030343c025800361544070310549001c60711030481d8944a50300d941c2070b4003150361144041d0600c11481c4d84040044040d01c1c2d01c1a15000c01c4c00a20002c569840c10200015000741000d260706840a000300000454040719a03c00d01503407070710380b100000404020311055815401c0c03405000380f0358404203981c164180e011500c100f440c04190592403040000780800c030141f1052806440c0c0c4176a01d42940310042c9403010000c21184001d1000610000c1076044040070340d488000070b120001c2d0008140c180310605403a0f0a0010341d030b000344200092260310418031809060381e001040450740b40e0080c4044650b06051521 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 870398741 1250 870397491 870397513
    0x81005010b04270f1e09050c06210c1b0c0d0b060a08100506010e010e01020601090b040b040e031e040f0603021c1d070f030b010509040c051206072c04050a021e030405 73
    0x700352200e446c0000c4c210780005100d010546020300246c0b0141c454100780070291441541408029007040d5400168080040b800c50007541c880543c0276080841d00c800350420102000101e1148104050010718100c40c3d00700084003611081030840040ca0880101c0300700c404c0704504a40180340c1a6201400545000b02401d071f9540109000c1100c113070181c0c010506a8644407001c00288140303000c0c1795000d511010218010350300c0f801001d5002c54500c014590f140021681c4100e0521440580115040144802c11450910081600848005017001f5a681c01c43c3d841da0f0100c1c0300103917000603529251039540e0182c0c3c0010410340b81560103d00c200c58500c6c0c0c031b50762840d0b03640c141c9d80301c010f1544101c84014050342c200140100e4109110f860344508507600c400024052201004100040d41d00803801c01413456445640c00300e9440d00308078000741c4130603442c026280350780d05108603a00843e00c0e040411440c0d4203650403109110f241c1c03408200c5d040003036066240564000e480c19203041c0300c0d0040c82a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 870399991 1250 870398741 870398801
    0x4110d0212010510050d1a030d080a0516122304061505060f2704021b0105070c020d030f0e0913030201050a05150909010f020a0504081005010b04270f 66
    0x102c0304c0c00391203c0342440e4030110140d001e4004020080750416115200b5940b40d182000200004503032522a4010b5182822454040f142c0082244180d001c6003414040050b400a20361194006002c801050840a421103a036131548842004644611500100800e10915a01031b070308803015032424800f81607071142000f04501412180580410f01008449030000c2215006468084440360f00c01c1d0782d404c03d00004040707800c460b02c100d0400713001d11a81c03030b0412000e110316507000c4020f0a082e01c0c4810160041030040b61100001000d02181c5201c011203c1d0040019680030f84000300986050300d420031800b13407418400141200598200700c04901c800c50180138a40c42400c000c00c14070420307001340d400c01402c5240944055420b5503511080e41140009000a04030a030290301c07202d50311468140c8040c80c20740c110b401a80013a26104c018040800c054040b201190710020100701c0c001420310801076061558a07103c91600d03c1e09540d440613038801e401485001581081061050050705404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 870401241 1250 870399991 870400009
    0x60403030c05060906061302090a050d050f0d2d050921070603090803040206030c0d02070c050a06020d091a04080105090d23070215070204140f070207080703060b04110d02120105 78
    0x440c2c1d20114100c087ca144030304a9010700a5240020030000300c203aa00c174003241e460300c04800162061b030450340f680d5500c14410006401c5417904c1c0d1074401514102c180611000040060a050716000c03140d0b620021070344035400341d4418102c0200403006454182c140044280403500441c082c6000744d5600056050181c824100c00d035400c114002d14503566a4204003280d440100390300c034154006d004140034505c2503c09005514410010010494100710800c92341c0070069202d9004c650140110000c116884401d0700c0442c0c141c1c1348017110721200c06030400411b003d560012140d81d8030f0041000104200060091190301d81521a06c2c01800101c0034005000d2000c04400b03000c00c0100144001401c00210804032024409031882c02c0440e5a0300081c08c0e24010031036580c59031000014040d5581c0b02d4401c59400040900003403155626000701c007074440e4124840a482142d444000743c00588a0360010894142c619502ca680d0f82c0e00080d1450094000003c14500c0e0119140003003510b0800000c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 870402491 1250 870401241 870401251
    0x181905010b1914180901060518191515080105040b10020d05090103021209030a0e010e010c0f050f0102041701060605090a1710061d0a0506060f03070905060403030c05060906 76
    0x100716142e00380f401a003524070103050710603002040b119904c0e04003100c507003420380030365898800825410714200030440040c00c0381440c03051088007801405814420030890561004240c0e0000c5449403440300b040c0c2c0e550032140c0c0b0810702d035801c0a5601a5240d03200c1021410b0b0345040b903040001c00c2e81d02c4107205460414842480c0941d00c51038105421174081c4c1c01810001405140251030700107800c0d01e9145004042d50700e1001c540c00420007640007500040e17521035002003841c2c41190030f2407040000b040b03043e00314409090000300980c1c21003132003811310000d4440a000c1c4029990782e5600c403c0781c118480300507525240c075481c001c0003160a0303101744216120039500802554001d400d00054280300c1c07080845511080c0305494203600ca286150140030010714050016400c4044060340780c104600d4028070110030249003004009040d903a22081d11075400482401640300c3e518030101b5122042c180d0003640d4000700c0810000304042e8462820707048036114005440b810b89880c00140c0d52240c05480c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 870403741 1250 870402491 870402529
    0x40806040305030a110f0c1e10020c0f070f0303022e02180a0608060415120b062409121902040c03090b0a270b06010503181905010b 58
    0x10034003182c4507001554100002c0040040c010803c10100c2560b40c0c0500c03a030303140e5610042020401381d00180031500340965420300c020340300e01440b8100790b01c4d802c040a01c0c040d000c5e808100c5d40e1500c1010446039001c0d00b000c2c01219001502c1b154690f080032980c2c40118018441d0030440392003000701079098440b001c003d41045441408640100019400c0502c640080c10030601c4401c0341681e0b9080104003c00c0107460b0540141002c0041c00151014902113242a0b44045000c0183c100381c1e020404840b60400480c100c80d407560000a101e4070b084e402d154000020300560405a600880002e082c0e002e030403145003900041c0c0544158480c141084c000040404050300800541800d03042804651074a14000410000c145d41c0d1000189040d1071a81c04a40e40c1d0702000e840f00c071081070031078102504152002c851040c80d52444c240302401403007281040310100108404004000307a11600c03030f411100756100548505401c00a00020b0710081c0c0d0320b9030030b0518055660401c05140e00c04500c81c1d01c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 870404991 1250 870403741 870403753
    0x6030f2d130f050d170703020705071511100c021e0c0d0305040f0b030a0c0c0f15110706021801030b0d021207050603090d0f02030a30020a051e0408 65
    0x1140c40c0704440600d200982e071150380700000070001881403010045500290301d40030a0310150280c2802c80000050a4000b858030400150021807400264001110069004806e9090f2a40d1048480010402c040300751449501700442c1e078103442e600800084d89180d0308a41100c064408820700000c100b80305025036030810052803980b410014401d60503140282070603441c241e07858031520607203001e90f4002440c509000c418401e00300224010a242c14100d49000d180212942e129894001c0c2c035518020824200308228000024941e0800001d00307112507401900c4560500b8007801070b5000d40140ca15900600400d808a903000c0d204144450034003404100c0070149903800e10150000b918041c0c08240b1486000290a9940380f00451048007c0406480300715040440500041500c07100c440964100344000c205a0b40d0000100d101c2a02880703d0351100384801c0380c030441905154201489941c0002003101046c0e070803800800c156501180310aa111445c0c8407070b20030038055801140a607170400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 870406241 1250 870404991 870405001
    0x50a022107032a2d091409011d13050a03080402120106030302060a1e11040510021c03020d1e05150306090d050a1b0b010306110703090b0c0c06030f2d 66
    0x1081042d03907030356414135201c0d141483c1d2401010a8400c50318103c002420b58881031168007050040340141e148146ca069511f035041c90b000b2031100030b91490f40340308170ba01c00000070401c005008005164541000035140200c00600340209845403c6800b41d0141e008000c1520f1100814400d010480340c01d9806815540c030354880d0351014040240c85a4801014048816101005407043e44800d9500400c0c00d580c0c1e074900818001c015040010120641d000440441f8041540c0e842c6510320010b14a00140d0f40d40c02c0002000041200c2c480140e03000300c5410880840c9a01a03000764016170703c210103003080f20350703407401c0540c0d8140440f014010b5810840c08201c4080c0200d01a006e10015810400c07070702c43d01410000b041e071003a1602501c5007110000101306204103841f270f501c0c40011040f1023510349801a1001340c10503041d482208a4400006198071179124144004201007000510b60f03640c070308010203c03980900041d609140320104041d04111030742c1540071408140200e20039100d40d81e64a0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 870407491 1250 870406241 870406247
    0x50a1a1503151605041e08010b0909060402090c122701020c030f0d18031e1d010f3f091707030302040902030a09050607020607020709050a022107032a 66
    0x740821000502000741700100d000e5900801c41024074000d0703c180d1102c6440c0442071420756a03900d072007900580c03054040c800c1600001c01c0c41c42c0c3c46034050301c4018107500c4d2820780803690f05c07440000d80c808907e40c0c818080a603181d140c0086c00040c50b43d241083c0305030b076020740038200e10682d80200b08603402040b03503842e880e54140152141105000340001d07044006211043c012a1605085000a00004861648880740040e5520b641c40915000c0900e40310154a030215003801020641400110654001513501c9820300b03034140840c1c0c0c1d10a10048954100c82001000380d00a01500d0080c0c40410003038503400c40c403841810940003c203c9401010303c071100c540c1a488500140c040503005c210125812189000460082c10201f00000b061000c6080203030502901501c1c072411504150207100b507069001410400b6a05102000201a00e030b0800f14002803094200c0400b82001c0c801803254014458000684107511a0300c050200d00c4082c0d00b034443d58081c80c01c00410a00c1c980c0c55512030144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 870408741 1250 870407491 870407521
    0x705120603070815071206030201212a0201110f07170d0203010b0c0c010e010f110a021002030c070b0f07173f060d0f050a1a150315 58
    0x1402405507440759449030300c80c50034400c002005641803840813082c4881c080d4401c1d2110744001900d142003080d2819035000030002c03505130302c40c80340f250000c8400041044d556885502101c45114403c4186980b89000c4103400c0324243d00300c0050f5203401003036402d043e0583c0890300c9000007003000c24900161a55519900d043c0219606140c1c00e00f80030040e0042c00c030b40b0096005e01070b07447d20241c031103a10b103464600d407040800e515410400030002202069820010b01c044001b90390600500c5591610310340c81c40e00603149000b9502ca0040149100125004001041c202d070380c481c15109181c3e102d020020306446a0000c1042c20b840421070400890040000a440301c840404061b25262656442c00c0781d0001c1c240d2085400822414114110340c40031650251040c2c01c14000811850140c002030455400410003401540e0040c40c1002005020f0122018240c0d210704000d081c0955401006846101203803071713107504540d049802c42035250001d0516261040f0b00003089845c0d5070210017506843c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 870409991 1250 870408741 870408751
    0x50f1902030c151b100f0b1509030a020a090506040507080114010f110639031308070807031107050a03080a030c050f0a0e0f0f06030f0408070206160b0f070512 70
    0x3d1420b100c0c55002480203c1e00c040c2502c4140f008040e0721015440102c1103400c92030b202400c540c5454100c100d16141d0f05c08980e490720000c0d444545855640c0e01003030030000110070003981300c80c20780c03408101707909540d00241c090030b01074604000321b585d001c1c0195902c1c48203001c1c15111241c40304505c0040d601c2141603103e80b0405280480d00803111050301494040b00b07480c5d143e13202d10140980040c0442e980c500388190010142d452189101d01300407445148001340180601e1765044981a090000301000c031038070b103036211031080d03907940c000d007402480010600c4d000340d0a401565800a10303031034506410010741e03070000005441c0c0314603140c2c158014120210a1030603c2414042c1000780e6400301d0260401d0100c580394100c4c00c01c0c00a0800941c9000e0485051064083d022840419220130041e80d6100012020203040d07601c8074203203910a4061900000e601200008200d000d100301c140404003424032450354009952194503412240002c1254000300084060084001e81054690115000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 870411241 1250 870409991 870410029
    0x11040902010c1104200706050c03010b0703112508010c0203280908070f0303021006080a0b0a0b06161406040210031104031a01241e1b050f1902030c 65
    0x400312084251000c500100d8591700b080d000b003210340038006d140c003035540d200484545e801c0c90742d13040046034803007401a02000307803c00c0301c0761418581c0001c00b0442c00d40e05400f0501e030f08d0020203042443c580289214080c0d0368040d402c0685016140e400001034980c40041e0040c040c209a040c01f070131300d20320841055400200070202c3c0b000607107c1303030902000300a81110300c5258052400c500340640751000948521400c90324040c010015040042a480c4925030302c141c2e4640d07241c90f188001d4000d4140740820742d41c411400110342498180c08210011150310907644184c12001c1c0d01d40e02da84605c02268081c0d000114684080c0410f4030aa0204c51175030501e007820381c20603450b61607149030011032680000403a400724005001a0280307a5022405107118a84038017090742c521002010050301100100e901d14110480110306800350007a4015403079a100f0850b660480d03130800b543e0700c41944911681a00859403503660680c101d046841300b454014000f0b1400c0041081401007042d128034040c040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 870412491 1250 870411241 870411251
    0x40501030b041d03090f01141b0f0304091401150c11041d0c1f09090b0f0315061c08031306240501080601110606190503070f0311040902010c1104 64
    0x140f540b00040b40981d0490400454846460406000b04030a56000310f906100000403400d0350103224000b160301400504140102070f10109949605e40881840282e400d40400b140206035203159078000f1030522a0840b42c80c60130390b03035107484803109488461795a00003010940240041445c2c8601840040c1000e0300014140590074909040c880e0300608003001d5803c6001c0e11050703803500c3c02500d0400d4611110903032101c01850806030100810340b045011031074861100c110165a803a410343c150240103015940404200c0007a0816048210f882d50720412810038801b014010807010401a9640013600d00d10f143c8900008480f40440f040044035041c1d143c2d40d42000c00007084d20400025000040e0108103281440d0016002c528010300050404c000d020105040842c005050354021605544031010341025180c299190030140d001590148547d0300005083d1005c5400441200d000d8414480c0d0150040f003080185d5040c0c01c0060700051244025001099200b001c3c03240c1100010710000ea = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 870413741 1250 870412491 870412511
    0x10b030903270402041d01081c0305220303020c1c0912080d0603050a1106070f06090c0f080d0210090c03030513050d030305010e07030b21100525090803040501030b04 73
    0x3c02d82e031041d00178107594200d5808258080e400001a20b0140850380c01421b41207a41078054108900b02041e10030801d903c603000710740021400f8035400c140000e1078880c0f4a20403558140640a98011001b0b04070b58882c140115800002c185582008444640e41d40c41e415407030102e071000d184c2c50070316041e101040704022a80a02c2541d1240c072004500ca10050440c504080c2080c200080b18040d199003d03450421005000400340c3d5640c84000f58401c5001841509a05080504075102d801070b0b0a003000c1c0c2400461784503000a03e0f8008035400d40d00322801200c04520540598040700c400030249002d1007424800a400745000d0080420b03107420395002c00c0d81d1800061013581d00c4203001c3d40070a59903001400004078020186038000c0e26030070240894000440401c129003c00002d0141c07480d40b8201c1102200000e009502c0c0b80c1901460a1043e42040d40040b2403440c0500a25610030300030442d08200c1d28040e40042c2c013200c407494091030500d443c003001900036009010010b80c1c4141c0da046030f14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 870414991 1250 870413741 870413749
    0xa110c03030304061d010216060c030b03011d010b031c0f0c051213050f09160302073017010605030406140a060501090b1201141f0e09010b03090327 65
    0x243c4218042e84004c24a414410012035643c4100200c02490380d00420440c00a0704941c0044412140d110100240100802c00d00f20300400c108058075500d54208514880d10300581030100d1075229005008010010b503600030540c0d100b0300000c2884150040c9001066a607020311108440c030070241c244010806c0496130f034a0300348865040da411801d00e0100300d401116059030402c202800080e140c82042600b40000500074910040800c0aaa01c03801c0c1c0c0c0780c408a100380c068480b25540003801000500c550500580b10480090b418201007180c2c11a45002c00e01c115001e45501c0c2e101045021241d00f052011112540010020b440742c5448a030100d1a0300007400d0518454000000001030690608000400721051940000700240382445500c01440040341c0060440348804102d0200e038540070040b4242d480a07081030006a0442803e8400c0903070002005104000120740d029032580c2c80e2015081360340000e03261030341503500c02e100e5841c240f4860500350345d003805010b4411003220303101c0c0002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 870416241 1250 870414991 870414997
    0x8031008030f0406090e040f0228090b030c09061f05070c09020d060f050609091803030112060506010206010e0412180b090a05030601060e0105070c0302060a05031e0103080a110c0303 80
    0xc0b20485000041c1084100c3d80a0701d1a000362000d074107020080d04103926500100c0900b0703130f17029215910500340d541c3c28030405080061050ba2040344145015030b1040e1031350090580d0b0500e14024061001580128540300749581d115881c01400c07032445c00504480342160940941c000020b10908024007000325020110804c002e000391140565143ca005070720100b520301c2c0da403142080708a62201400700d9a9945d0581d007261809540c080990758806020329001c488010070849540400000455500c01c4200303c0002c4a00800007404280c450f6001285d4450782403182040407005000820b001400b5090ba10080c2c2c84030340350010010b014040c050000a680b548588000306000640c140c0a0410f042d2400060100310b0250940d03601d0144054a406130b000044c40c10060009616400c020446440c44065038000e00242e0701c43e04000f1010b0107640c000d482000e02e0680101d030511300d51940610070f605a9a11011490401c48800b0058851185409500c5940d0080304540b01c91620b0400c06 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 870417491 1250 870416241 870416257
    0x40305010f0f0b030c13020a02030d0e0706090b0414040b190905090f1b01030c0908010c0503010303030f090f08030601170405070303141219090210030905060108190803100803 77
    0x8202d107150b114001152103070300205000e40c2020440705000c3d40d40c0d00304203000d030b0140d03840580d503100741980032800d40c490002404111450030400c03442e20103000580c0d009a400c5500e8450b8100d4540301808014041c0d8400e00c8615001c80c1a541c45070f0605400c103200701400a84064003a0004101c1c2c0c55014085410114100d0380c0d81e4200403d040c0104010406225210050501020b0080b42c43d0014648101014141525410001c118038403403400e4400801c8008020450350102c9000180039600a11003a00043d0401c09010200d020034484c610034154450700c1280000b010340e5a598844c0c0008007060b06018001c06a80d1001e0b050480c050b01c9a48030f0806807031098158a8041e00300d036101d1040e210f9040c41409007a840300d0381d014185410606004400340f00004c00c420408c0038000101000f074002c410866003410f41605900b1034104c00b8031890a50320140c1e01ca0f40a00d544c0e054483d5082c00d6000011780150100309104020b581000c00c17803400c024495100d114a62440c5c0c01114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 870418741 1250 870417491 870417521
    0x2a100c060e060a050711100506060714010203070e060405010509040f0e0d031d0706021e1c031b210506120f0f100605060f0a030e07140112151a04030501 67
    0x410441100f0191046944c080902e09000c9000440354a0095031402c01981c1d982032980d8500100706699200400e03641500d03440103c1c1e0780420741044040f4042d400030f4640c0c40100d840c81100e4100740c42c25409442c10354006a40303d03400c0c00068010800a0904d00c408031942c1680c403460420200303c05d102954002e1080d0710302007400003a11046c41d40301c0070b200c81400340e82d400108003030000300d50104802422140d0a11101c080c0c00f031454080741032403540e04030224200100741940c082550107400280e0043c51100010110038100001170f208100c0c3c07000c0e100102c40017050758002c11201030b84140d8000a003d0030342d5584d030700b01100e16841c00c405001c8150481c3d00448010400380c030204401340c1c041c41c0e0304006200e4289464085840d41c001c22603044100140401c8004406119030312407041200300394103d44000e5500c83c3c9145022030005c600785c1c005a00040c101d06014403c0c00b039602c0310b0003240b00b00d052032441d00d010750700c1c800307691036000450302003c10000002c10024003542041502c514 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 870419991 1250 870418741 870418753
    0x10905070f030c0e09191a060a180c02010902030a0807020a1a0f07050313351b03071a090405010e04050604020603070c0b0c0c2a100c060e 61
    0x420954a405200d40c451000c4001415080c000519841c0028040b5000510080207035101c4421180c245401c0c0400c0c40c4141c542c64030b0038411f112484140398102a44080c040c84141c82d1201840b075065070300e0260248248008801d086c42c0340c842d500000100140d4070001400040f1640004c0c2001c15858041e901e81402080d140203619000c03281100800c0048001015044001c4060300907018840b21000b80e11750225801007401018411078070390507403030f00c0b01ca1344c0a80c40303050340340300ca03419900fa01500070400440e00c2d4003070107607000e03507194409d20314000c112a410101184401743c0115200ca900b50107142400600703851103420000d00300303004c2d070aa542c6517030251080c8011030381c1c168400380d070010058040c031011901c0420300c3d98005405444540d6250766002c4151040d901e9008010150b482820801c10105c0425000e0011603d241003030f80c60701da82541103844450400c1203a1401c43c4030303804101e4024940541c21411806440c02c2418114920b030300e0340750480c0c8080407011a540c2000b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 870421241 1250 870419991 870419993
    0x606141f0e0a030b090f060c0c061b091f0e03030a0e360130060b0f0a03080306031902010503011211280b03010b180f04050c0726250c06020109 63
    0x7c1c07281c15440300c07110b4510390038810307204442551094080c04500051003810203020110014074100c0d81150001342908280410040320b84454001e4000c0240000d8071702d4400e410140b40100468140e40c00b26500e2038200d030b040e04200007490b1462102503410705200c1401c0b410390407010f8002518108611082d000941c98059864030a0806504030705a07100c01c4041c20a04118036000d2134580380c0c00c5903000500251035004a161030a061042562243c400500002080100c80027180f1800082c1d007a18005c50703607080350342403000c400b0400034003199091005009601e91490b21000650141c815002110031240c00301d04d50403102c85035440e1f1a0045c1c0c0041d5030461140d68110f00902d03000405901c0e541c5040c110a903107000b082c1b51310003000b0030b410700d254040e81c468106203c02c0310014801c02031414109809855179220a004a074040c40d04e161844400e0441e0150400000c4044501032424001402c40e80c10710601c00a80c03c0b5091000750f039070020681c40c4c1c00080140500703400000312480c1d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 870422491 1250 870421241 870421243
    0xf06080d18030c06080a0e120d060b1905131e230303031603020409021218070b2514030301060201140103050a1101050d02070606141f0e0a030b090f 65
    0x20307981040305041282142080010181d0116004940a5141804103074440c2c0c0c030104060988942920804e00c1603d480f00090502e4000500c10301c000410304110a0707075240400b00c0203003e400c0520742001010b011500c00113004800400e40c0b40f1810600f04146a00c82c440e031109140c00b441c5e0b1031611646000309202c03800d00310405442d841203a00340043c42900c0302c0002030381ca10005007000c400c80018910801c1d43e5001c0d0b011765002d443d84080654840e001030b04200307105003044400c10060f070b200d140b144018039400700d641d1094441041d10640380202d4054030b103c4002a0008440c1c542c50303500756900c0030910040c4100c0c09400c0800185035203500d00400242135a175030b03c24050030400914010400600005900304020741d2103103100742c8007050b075001a41c1c2070081d240004011030001468000b0001c85a111105450401d02c000c01c00b10060401d1020407440c15040e54081c000400c003504485010701401d900003c002855950855143e590b01350b644035082d11980f0311640944001280804 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 870423741 1250 870422491 870422507
    0x503070204141003080d2306030c011d041104080303090d2604060c05040509040302010e070609030320030c030a020102030a1119050d060b1224130b040f06080d 70
    0x2d03642500c10814101492030002810191000500b185030008000701d01110641011280350042a42e01c00034a9002d2040e015101c001c440312071080c0500c01030f010481d0300612041013810032018034940409141c00038400100381005802d40e040c0c4050200041e1910204011352241c25110090007401601c104050107031700c0b805485101c00641d0112080d068100c1045290b4080e030044400b00b800340b0402010fa503544195001141c0060b00d0608200a164054111150041403c0102c0700e0050b516a001c49180300d242c000103001506003510700403155a0302441118511410301601c1c46d08010340e130381a156512074140d00780580d4010081020011180c0b00d80044007004a18940c0740c1540c1c66080307000880281f038904148800441c680618201903400040600181601181e80e054070400489072054102d40c001c852811091050369001410f4982c02044d40010709091011000700381190041c24490350850303005a80c5044c02e80440200340240c1000b00400303805840d1648020b14000c080034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 870424991 1250 870423741 870423761
    0x1140406050901171902211003120216031506080118021221070302011401061e0c030e010f020a0c270212061c05010c0e2d041e090503070204 62
    0x2c00c04c0c8080010000031181310140d401e110480c010fa0f03800c421101300740c2c01000180b040403500740500410114001880900c81500d0180c0b01c404000d0941c03840490307aa132203400700c1c140004030711030b410400180f04003105949492060070104816480301040760031190300e00160311015007824603c80641c28a045e40a1000d0348590251559107014010008920301c1c0d0401e401180703200003005414140300f0350004a80502040800c0503651351000014000c0038900307030100c6812440301400450301d015464000003141d064403142c2e040302503c0700554070100c10003040740a5020711680301c00000c00b55501b082c017a05024041c40039203c100745000b00e49060310404103600717030b00c104031080500010006969000c0c100f141c2c030350140401d5148800c0d1409040704020b00035800d00d00340400c1c503504080303c2c1c4a08036017912241200400c00f21a0340c0c02c2c40e00100748002c000c9050304040c010303041ca03070464017112040c0e682e01565440c900c5580b00c100c400140040d141c0e03070008203c030002c528150003250006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 870426241 1250 870424991 870425027
    0x1b12020d0f1107120213020a020d030c110c09091207080705010e0303010b0304240f05061c020a03110d020a0e090607030b2d100327080a03090201140406050901 70
    0x103000202d42d501e40c0c6440700d004004418010055960465503000c0f000c4400c408018019034a613a0307054400b03503966190141a05c0801e040c5001802964480c2c80b841c050200004010308901520005018002001402e1070085010301402034500400e020300801a05120742c2c0c040744c1d100400d050045c03c583c10b4521700142c0790070030401000b560309400142c80d0816000345c030000b40800d8010701d0146900e1a072290100031824a0002c04450300c42d075110787e1060b0740a8072142a445150045889000481040254041d403110740a00c0403c100e0507202e4403070080a4040785100c40142c0000c3c082c0c00055014062000d031040400611101c04e01ca0a42c01c1541030805010b00c04400303000a84c402c486402c1f110b02414085071024140c42030f044d0160b40350384044e005a06000c4402c07401000703007007114960070125600800c180801c02e4000e403c586641e800400c0c031400c24208110440140103195000e03030400080c0308983c0d80b00c405200c020700081c031007500c40790b0b9a081910005407000e03011001e40040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 870427491 1250 870426241 870426257
    0xc0411030f0c090307030b01061d01080606120402041d0f0d0201060303090303120f150e0105030d0f200d0e091003120e04090506010306061d0105101b12020d0f 70
    0x8100d24059107810003541d8800316182e02c00c000201c0c0c40c1820301d92001e01f9049100000054060b0000c20b042d14080400c48441c4038072840d8401541c0d203d00a40d1a41c0d08400200402d0034201d00c40003000790440d00c0240b0204440399803014288040c49441c0d0500d00d00d070018003212003903e20400140701d40d6400780c0001c1c070480f4a161009414100750b0f200203030a001084c100c40e221100554003040740500910400c1090341d50b03110400c00146081d0151000c1c4000080004c5510320300003070700d458107049940c0c4e41660081c42c0602110190303044110010586000c003032034419440709000b4480090031030340c1d81001010880b020000c4000002d0710002194002c44400e001182e08032102e1100e6002d18185500e201005001140003400c110380050b2050003070000203c100030464001c00212680b200e96101c5031500007040d44070043c42845060750150b0b00314601c030f02150040c6140d070303a450b96204105000325055140c1c49000b0301c29400b018010781000c41611000d94101c0e60341070b5256124a010b0300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 870428741 1250 870427491 870427501
    0x6020601050d0b0405010b0306090106053309031f090b010b03070c0b061203160b180c0103110c032206020a030e091518010504050c03130b180d020c041103 68
    0x4a862180345014040a02c43c1c40040d0500100350803040c00050054211642460488500c50003800c0030f00902d4400da01c0b091080b4504007400c41400e84400b160302440c00a03c8451b5084030041c1d1010240e43c0d003501a80c1404c064811000c003e201518400040c0800d28204502d051200b468050308486120042070040c040c030298024503a010b00c6a1003012001c441e1241000102004035502d00503540b03100000700c07084440030b143c40118945102c0c15003070b001c1e41c64003c02d0710044040900030204c281d000c00c10081d0190711941101034810072180840e0324160f030168cd00c030b0131a80310749400402e89100e00000f129203000c201c1210001d121074405080c440425540052111022060b540d1080d11040042000180d1507800e40c01862401411003050a04039145100005800d2141501ca68075201c0011340740788180c81101d200d18044a030101d005159591188410304000e0205405408008174191200104201c0522020001d40042c940203404904100580e0708040418640e5401070040c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 870429991 1250 870428741 870428749
    0xf07021506041104060c0605060d05030f0a03061701020a021c020723030601030c090b0f0d06090309030213061e0f06051b0706030204081504050c0103150506031806010602060105 78
    0x10031501020000110a07150200041c000e001c002c1142c0d12a41e100090000b4443d41081d021a000c5100d04001e1140da81c400f01040203020095030f0107081074000300003110b0b960b0b8000004120031196401c000420b03030303242c139013416145050000d040c805a5000a2160358150108208020907220155035040200290390094603055075219200508100c2444000c0f040c500526062080c1c2026049464540c0d41c0d0031315060400d01485115141d51400502c00003a0524030003c4250030b0020b00311142001e480e6a0301401446941d000790f040014600004c40107a4034500c0580390000082000314400e4146240e1000081c1103030b84886c504101c0410403c5255542c1d40d1107000c40740c190801c0e036101c00020660748001514012003030800e014a1b0703004030710103825601800035100c0c100200e40340100400c0d0340c0f001400e001d5070064069070060203030f800f442d80300381c11001d410441c480c8070610782da58440c0855002c0c1c01c26240c1280c2c8100340004a00e4020003000766a004100a1008110551401003c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 870431241 1250 870429991 870430003
    0x50a0b06250f0f0b0108190803090a1506090f06150503060d14010603111905060c010f060b04061e0c03050a090302030613020a0603060b03150307030206030712050f0702 74
    0x205a10004041c6590040300400c2100c00900e600100c4500c00c1510510b00082001000d500448a00441d00d0000c50140760014012002c0d12102940045894040e00d60340c4840c1c00040c02c40000d449440307160700c001880c841400b844c000b46a000450b106080c89000c400340c03145c1502c08100755240000c1002201001c0360f03001d02401c00307404c06599039103500d0046000c100c507a81d0098400021140c40d981d900b10154000411a40522606424620b03100d04020b4074000354001c6030801100e40006102c80e2920b900148044001c000000540f6602c0044500a403082c55124400c0a40081010414150081a02e044040d081c80b00c0e03140e580784000001e04920341c002c8015081050204030713520414090134691004d9500201120041d29220404003c00070180700e00700d001c0e0307a4251002a80038024000c034419225440000780c1156286000c1440200c0d448020540c540306045000000d40c44040065004000903039504d80c090140401900a0318006071841080c401d4450130000780a80c04204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 870432491 1250 870431241 870431257
    0x3070818010203040e0408030402100309080a08071b1b0527060f09090d032a080c12070f0314010501050406081f06051222030f11031309050a0b06 64
    0x240c244041034610040b4618081c0e030f000001c0c02d500c400c080c4802d201b0800059032040e8401c035805900c001c030346030341182030381e50320b00000308040310038441c04003507034018241994880d02c1c62030200f0603058140d102000d89450203000b9950b42414111150f072007900c0b0303080540504015210f414007403821981d00d0030000380071800d89880031402c40105545680c0c4858007000c25100900200380b50038081e440315143ca0303041e402d14010038580740b880e1411000d4141c440000141c03001d52440300e0749501e0b205945451006100d003160306410400e10b00c26042258800780108095900e410102d18420405422290689000800600385400400c40e0340c0c1d002084401b903890624017005107441e9144d031400703c5184c041000403485410200401d0140d03002c40a0200c2c026141a5070f0002d8441c07440c0031003000d480c0040e40f944c0300304105141e40031078050381c0b1801030b08501b880c1c40c9100d007808100036811074000741c1038100e448140c06010041107400d40105508403258200401c100080000040c80c988a00d100c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 870433741 1250 870432491 870432517
    0x604030f0b071b080309011508190203010e060f040309061404260708100f05090303072001050c0909010b0c0604030f0e03070b07020411030403141605030c0d030608030708 75
    0x182c04680316400d0340505541c030341a1500303458080c4c900b80510b60401c850310700d5150310b008a605c211803546a8481c1c200c2d40428064035101a8209030141500c844080907600742d0340303403403008400800c1006210310502c02c07040646181d013001d240003090002154006c00c10440c1000c4554004c080e0541100d04480b1080003240c4400c1c100301d0703101440c032128140003150380075035a00040c1a0310301188104036107511060070030607543e80510260480e001550200c4070ba600900c0022506402060355041520062038400f51300c560f18a8910709440c0f0844201800314404146901d00d81447e81c152405003032003104141c10f00011071030143d51344400800240070001140e00313000c8450301038140d034600c1ca04040d042e200f0a9807603000c103d109510520003280031303078603006141882c9503541059900540d4980d5400300500f020398252045500144045170707403089140a00c000052040000306042c00e060400303061004010b120140484101d41d1198101e9041088050700084900088513545c9182c29 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 870434991 1250 870433741 870433763
    0x7060215070f0e0d060b040510062a02030a120e0a141009170303091c0c0809040f0c200d02070306150915030c050d17030912030c04050901050604030f 66
    0xb1400c45806803a0004a40c01240302e80c484411720401d40c0042001200070760b800c1c04545c40700c69042001c11130511a0100143d44149060b02428039011108800d951017440140c003240c0070b0300003e0501042c400c00312085017020501c2050b0b207400030790a681e6003400722140704105103400782903022511401440b91003500c84204031903c0901801420000e017059021300760030104800300450b41ca41c01a14823207050311510310a003015103200340080ad0340c0d08040d6144070120806039544940b60f005810700ca544a07485440c1c075140c0140503c00c0840c200b030300e13580d10303800030002c46001c80130b0203005001445c807038000302e203c2400d00c0e0f00050543c085a03449000010381c00c841004050046d080e542001c0181070030103921000c039205038844481524000c0511203009a134450400c0040040d0b48401003281208404c60321240250202442c0d20400341001d0305c0840404809508180d4001c640e000107804d0040f40c240820306111812901512080d2a018501810354039802c2d02030700d540e20001e022803040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 870436241 1250 870434991 870435017
    0x70c02031507110c04051e0901060801381e010201180c05271b132c0910020a02070305060a053405090a0b030109020a020706021507 58
    0x2000441080351a1508100c2030b0b0800000c020000a0b10310482c080901c02c400381d0700c0b281d24081c41514010002100702c401c035802407001264003058010300120080d540e61600107500c100a0080f030302c00c2100b066610042c09400e0240003984440d12502c03c03441401103102da02c0907100c0041c41c041407040c146108a035001d00800403405024800802d01201540005280c1040001411842600e4040700d00b003e14110404100f00c001541034083c40c1d01501940c0880c07011328000030003078000b01005480502e40400c2c40c520381c0d289242a400181000108260684210418034502101055541d1210b00e0b9060100d03045d55145514110102d400381c2c006240c4000038002c0000310000c55000d01900c0462030b2400d800c0d001458200c0304e918095012620301d42c0b000c1680d208900142c5c014038904005040c0040d000c81c0c1640200000c250414403046010980c201342c80082c5008003080500546d840f5150318009040c080d0561141085d580401c80b032441c1e401310540c046500c50080d01e0022085030341 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 870437491 1250 870436241 870436243
    0xf02010b220603021801090c05030f0c0a0c051509100905121b060412020601090c05070b1504020c100e03040609150509091302010305060a060212131716060c0803070c0203 75
    0x3c0c1d00007580802e4603044110001c401d1034009040f550078050070490340b60b0420b030a940e503103c100c0c2c0c50344070f0030b0506c0300003114400c00d0000782c8080c0b509485d0038901541c09a13911894413080319104c0c405403500c001003125440c0100400d9003d965100403c2c00703218501d50b03030140d48a0001c00e0a490b521004140040f82c0340c868405040920705400440790142000d003440421300c001004054014040c84002040c40c03001d500520419000c1a96000d01c1e14006441e050085040904584041005c800b04903480d542c0d140042c042c00c5082e00301502c0000071221207501114003a4a0100483c1c10601c800c01646400440081c00c40c0c541820a000c107103078401c801c54241c894a440035034011824010700c400321207000c15501c480780c0700b03032020040c07030b00c0d00c00421807205503511903076005a001700c5c41000034000d5103001d0621080042c01d200300c0991601e08414220f5908101214164054006809030114400d901d000030201c600742007180203d43d441d02e51542c80000d04001c00e01c80403030b20540071510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 870438741 1250 870437491 870437501
    0x140609120d051f030b181b01031a221407050a140405100c060c080903190c020913050d0c0c050114070b04120207171b010903170a0f02010b22 62
    0x10760b4580f03204160348a19110584802c1130310044084141071000300545c0c1c0c03000507010100c1d02005603c10381c9a8003800118090144911b65240803c201c5c001b42c14543c58060001200d1301d0420000da80981e0904884c0d82114000015034241810000a10900036001070440da41600c0d070f464001001120680c6035480c620540c0c0c1704540089020805c024055807040751645d100307120303031030501c41c00f240c018080340c0824003514110015001080126a80c800e603600500e1402a070f420103070417402080d00012100f00d004c980c8a41c0b42c070040e1540d03c040040c2030141605030703182410060140507060b121000e410310340380522418041c200c240600c0901c2d01c00e003542c1c8001c0c0d2206583d2000d01d0689030000f44c25042c05d0b81c000261181400114040710544002041c070300441d07000300054103000c401c0c2e454146070052514140041c0d01804000f01d88a88c0000c54101400240a40d441e040042d00800d00c01c2d02d400c000b0304591400c070719a085540d41d2541080016002881c20031044030603015840282 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 870439991 1250 870438741 870438781
    0x203120403110f030d0911030d08242205090607090905151903020f0105040e0402150c0303070e09010f23010e10020f01050606030c0307140d09140609120d05 69
    0x704c00420044a0440503410000380c1c1c520030300e0352290518410040c103607102e07012000c0c100407403038200002d0000100c844210001c08030000c1080f0307014950102080320041400d1400151000c0c000c0201200e031580d004058014840100604141c90142002085000680980e081164440c0042080c2c45905100403061b03083c002d0000f1000c0e00c1c9920a8000c68007070784001c03802100c1803038550900758040c10aa800702c807203403003944185a865a0811440c40100103210410103c14403401004600c20000380d445000162115a03100030250104000c0d400168484541e031801ca180030703c0030795001d5400001e01259400102d1b548609800142d5078508286030b80c9030889005000303400840da00080344249900d1407002000191281014441d00384011620400000000c0010820992141c0541035102106910450505410b00180c100303845200b581618144c1d4050141c0b100b002017844144d4212080030000d12482d91034500c0e564440c06400e509405607507803540050580da592907440340a01d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 870441241 1250 870439991 870439993
    0x501090e06030a1406040b01141c0203070e070909060938090a020418050c040618270f0b010801150e04050f2208040b0d09060c0801080d0203120403110f 67
    0x4c003040b00c09503900e00702150165180b11050000003950454045004000000500b944134ad118048107803542031542d40000300c0e0544140003001410441c0c204000380aa00e80355a03220906180040325401c0e909a9089a009680b1385084041e51204107113800f4120403848003441080d80541c084100e600d1131103e0342640141c0410208092020680d00900c04d885c000f142c1c00349824140314058040300e00840352140030b0141040309003d541c3c021000c0b10030381404d11a000f6480c44e00c3c3c2ca00c05441c0f40078000d07406080b030180f40d000b110720720160003285e0340050b040000700003000f01100005d01200d818420300c1c00001040a1a4002902c2802180c0020300060024045810812070000440d8001c841d0000b060f90320403000da1084801c807030441801d541101445e410141080c0700c0d40150f40c05408201c503210b94501d0080d0010310a8080c0c2c075184500d548079044298500203103142070a091800300c1c01190810400003c2c000301c0011015001901458000d084144240c5c0d0700303151103109000001c031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 870442491 1250 870441241 870441263
    0x80a031e080109091110032705210d0609091a1905060d0506040f060b180a0b01050705011b030b0103060e0411060c070f180606170603280611040501090e06030a 70
    0x340e0340d0075401806140c1d00702e404080303100100084052342c1060303042c00100780c0c0d003001845142509802c541c43d042c0641624140d490910108011001c40e086a8051150a030311240c03482c042c0041c203144911a44008642c0344450301d00360043d400700101d03c0840c95102540d84c00407450b15100e4041c4652042c1d4003500300c4190303003814101401c1401010504440080c00c00b60b003112142000d4400010300e501d04040b54485445004019020f080344041d03407810032205210700000304500f4010700c1081c03140403142803014100003100a00369800c0156040c1854104070003080ba00d40c208a240341d02c160429104183c450300440050361a01c40c1c1c0c20346141c18450700c5004170b90381c0c1c0110411001c851298008c0000321544034424000d43e1428403035400030403211800802d50b225410006070f4880001000d5440d4071314902c1e843c07159503007045803d0100b00608504541001080d120756800d100400c5146400d20b890080000c04105081c01424005070300f00000ca1031944040100c5060240d1003050228 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 870443741 1250 870442491 870442519
    0x90f0d0611070308040b07020d1e02010b1f080604020c0c010309050304030803180c010f0e0d21182117040b030a02071101030c1e1701080a031e0801090911 68
    0x30081e41d0507202502c1c0555411b0200c4c60305400010340e43d64111040e29401260048410300001042c0c030b282d018019552a1a68082103588030016000282d1900f51400d10003401c0e00d400810504008050034065403040000c07400040001590300413201e001d2030007045030b4181e0300d4a24294082c545c001040000b000c801c0c000101d50b0b60b2208064140600200c6030300c001c0304001100e1720003200780400c011542c5040c40106a0401c070540f2800b080c021a48601c078248002c2d20000c00c0e404000345c4c8400205c80c560030501d460310301c06000004200c07070880030518009001e0350304032604140b100100303600d034040c11000504c0e0424040c0d42c002c0484180c1e480d20313490000c1580c4080c0d80041400c450403051071840216035030280c490280c4141043d40c80300c1140c10100050383e41240241f800005004255401030642ca080c0071245003c2c00c08070010b03001d011064078010f414132034843d01068804501d8030101d2401580400042d04540c070741c0320041200c00150800c1e8406440c031a80300c0d504405e8010b0101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 870444991 1250 870443741 870443747
    0x30b19020409110903210414011b030203030105120a020a17101e0609021306120b0301061d010e041a1b0c0c1e0306010302090c092211090f0d06110703 66
    0x10011300c1041d815100c40f144001020050341c849104442001c8600344010f0080d5010b42100f5282124181403526090816009024172a00a00030840059100100610840c10300d40310b032001c00100da0000300012003155000502800c0136024505140803000d120120075201000b13000701e8080100030800800200340000c003924400c82c0080c04240e07092040024000e49988220381c40196002c20310161a0b0034000c08940295803660440b4030b294a41c500d42d44e5a9a007841448020700c5580b03100e501c18204031558906400050340700400c504110410000418044519001841d00101d8054810303601e024414900c208040e07844508014049140c040035140010511a480021200c1102c000c01d840842d02c4e26912a09541e070701a00240010001418826030180e080039240e0452410450f242000c030b000360380c0c0c0302c41d010140c0503680c1140041200912a607665030032040820b501e00030710030011a4844501a40c92802060114000c02c28003241c1c6d4412030110410742c40e503540c2d07000c603403c0003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 870446241 1250 870444991 870444997
    0x6040609060f080910330905010501080705120702031314031e2a0316060e04050601080c03091006150e0d03140c030d060b0309010f0501030b1902040911 67
    0x2039000b04a002110a03071240c090142148603194100051050340d003d40c01d1040603000311a080c007800b1001070600c6420144114074603085010100c0d07038598452505003031100795941070f1f12840c18041e4003001e1180e444d07448411108005d081900c060b00549443c00700301c3c5148a00040000303161030305030340420006c01c1400c3e00010550114212005120041e000d2a64255040300c0b949143d44402c0100f02c09024004031a41c410a071050024045901c0718003090802c02990045100400c1c01c1c8001d102207a0841212152114251001c000301c0c0790900003e131a0900250030111105008000601e603800b0400540b5190804880300f80442d0365161096201d5900180c05140400c1401c00c48170703118140440102d032001d070540d4400342906911910880340ea4400810004c05005c02c2100504100660044c90001c00070100da03296a0304d450301e500b600b1a242ea45085481d40e04040040010a41580c0d10541000d0b699009500e80c40c10055080028840c2d6400040d00da810700c4601d44400c00c500002e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 870447491 1250 870446241 870446249
    0x1d06150c0d110d14190c06020f040806010e0603060601080a0b040905480102120a05040f050f10030509190f05010e0f0304090b120a0606031101020d02060c03040201020c06040609 78
    0x4482040201c580250b1360111014500728100005000a02d0000c020101410b0b20a0302e5003025441c8240e0742e01d132a0203991111483d5040c1460000b01000300800c01c00155004160781005045903003030503800a6210b55024045034100301516001c01c8004001d50f20110341101c0007032080011b10514600aa00c078045a40d6014110385500490b81540c040800d4250340030b01264558180c00c400c9041d0b800394442d845038110b04512406446130030640040006010041a90b00c6043d21903243c0801007250501d1500440c0c011120f98500d45025107450521031006012824042000e660303203401e851030101c4016088469400f041c00c02410701040381d40c10458640600300a120804014040d1540d0b581c95001c403424980c010001000091183d50001048650040c0003860461060080c1803806000910955265940345810010800c4403401403000e20700a002030040d0b62030804001c2c1d120800200280808000003000404681c4203002d000f0140340d00400c002e4035141c1f01c00b401011001075000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 870448741 1250 870447491 870447493
    0xf05160f0203060702120909220c051306050306072015043e3715091e15050c010609060e1311040e030a091d06150c0d11 53
    0x2c00704941302d2000c13030f84070300c0c0100301055540f40448140510524900041070380d40d01041020910001c520400030200d400b901031182000d0141c103017010420040348421120003103601d441c100700080d482c080f44865000c845030400200034000b00d080503902c080404455001c1303005808080c0015024004510300840c002c10740068514042d0348902d24654600c900e24180750682e80c40320a56003880348041e4401d010103044800c0e40c0410310300c450590004084144a00305d0400410580104098075101c020802c1c448d0384403d914280d0400742c020341c0d107801444120f000030301c41c084c526070421141e500101002103a6401c944814040106560008070515a06500300070f000030340401c02c1e000308003e42d40b211002903429200c40140360224240b80320211000c000310102d41c3e2060303407584141c0d1100030ba6000a0741d45d81240d80c000420b00b0195405c41920782c0ca40005080b80b2080f6a03900640c4a0b2081d52513004050100d00018007078000d00c0079aa4607031144484402040d07610038080e0010044d410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 870449991 1250 870448741 870448753
    0x3050307112e02090303040312031103010321030c200c060d0b18010501120c1b08030615042301120513020a080105072c061b06070c120f05160f0203 65
    0x21803010141c0c0704d4501d019074103034007d02c418000302d0080e4039041e241500700e0a000174160280160601d05800980c0103803490031a99501002440e07003505812620a007a1404101880b174030400a00341c0c54682d80340302124000261071200d080740400c60041000d4000342245c0d1901800084031010780001402c00b40602d90f1542e500c0d4900020070707041c0d41a0b0700140c440d00d0400320055034000081c072580c05844100100c20b900c8a02c5000c1d44182d00031600d000710480c0d990780c50020103001c10500b40440c2c1c0c54207010108070401844842c0d0074003017100c8410051440103000340303000484202d8444401c0c0500b040c54101840515645210f080340400e00c01c0c0c0342460030654410312103003220400c40c1d5110116292441204200c1001c258200300d05035030f010300c1991041c0481c08103003540c002c0142c41481c020603100c60040c10200b04042c4d6032007405440c0c01800c18034a9518142c01c00c480c02c00540030b0041556040b05281e010b68190390b921143c0b810100315041c1c45060110302069444010b0340280204c3c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 870451241 1250 870449991 870450073
    0x80303160c0809040c200a030e1002070e0703060f061e030203040515180109290601021f0b043305061b10090b0106170f040305030711 59
    0x2119038400031a004419a402c118003c4103100161080d401004104800707201e4400074034400e41d00c3c200c14a13001900800e2904180c0c58007030040500342454610403c41500a981c0c100c0c0d0003d072007410b0324290212251a0341301c01205802903e040c1d08441d6040c01410808100344e1351100c00028900c10070b05450000c0c105605080d0100d02c07050702d011f481900414040104031002000151308a03074101070038103204400c41d400c642140c0e07d02c0b101b1240500448070b030040402e04103a4415032141390700c4000301d103814840c001079918204200b08280d4a410700c81181e10700c3c01e40b036100040d80d0304050030a00130312401c1c03604019041441d20040b6019119400d0101418020400140540704084e1000746004007407400f03c0f410109000c1c020b000d9201e211032045121046000c0d440714a40301c1c025800c038950502401429204110404503180e11882041150f40d1000130012904141c150030000e07aa91140c0d2401c079401031206443d24280c1c854001d01c01001400302030b401828500e4841109840955 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 870452491 1250 870451241 870451247
    0x190b04020c0f0d14250219152a030c060f06170d0216170f161805090d0305131202100b09040c0308030c1209030a090b070b0718090608030316 62
    0x9142201440c41d01501c44441964490000302d00d8040c0000e10004440519501c003043d40f08643c3c10038400f170b480c923001e4000c110307820002c40c6d00310f6003035110b000c1180403014007142c601ea0781c104070240400c00d000d070000044c07004550101139003c00091040c050b140d1109201004c07003200e0349156100c1e20422421782003082c404140d00701030720002c0000544552410143c510ba44017a211221034034054800d8100a00030300700051550142c450486150540c030b0580d0000c02c1c1d005003450072550a04000c1046081800407544641021341c5040c009419117900c61003100f0244854001000c801c41c81c103801240980010f1075136001d81e40a1028015895400f013402107041007a90001d10399202240f050000540c0c403005958485000c140d241c0c101a10305031540e90640054550340b000d40c00000b03004010581c040500c501138003d000c0384501d0000c0320b54403d2a0000014104410003901d5520820360004c0b44111070b00400d41014240051a2078071040c075100d81c02511a4421807c12070046006180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 870453741 1250 870452491 870452497
    0x50319020c0c060c010e0304090c03060b12071202071e0b01050418140c0303040b0705010f020901051c06090e030405030c09040c0324020c03090102070b03190b04020c0f0d14 76
    0xc000002e05202c15401c1d00744402d07504600784245042d525003d8103c03400c071080001d413008001d6a0000b10b4148100140901101e090340c020703510641c0c080285580c4c402e5583c0d04190425014900a162152220300600007409032010007042018401d000901d202844e24804102500404021009982c1c42d410041190441d15644550308401c10908010a05055030307880b5446a5006442051035031200003030940c4e0103500524811200440c14105001091142d011482440d1000310f01d4110032000180003401205105180c00c0c1c102c2041900004440d08054020510041e05101e0a40c10400d000c0e244c1d0860301585009119821100805140100042e405290030100d00c448942c119141c000c400c6641d10346c0640501099440f40900d040e0350320003095500204400f03540c544d10044002420680940d00c448920700080c42481140030000d6803400c2600050302d0001502c03000c80001c40c000e4011401c41800c1406215218400f191020441d640c1034a680d56034000204141b1080f030100340 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 870454991 1250 870453741 870453757
    0x230606011404060c150603020406081005010e07090302061b0d031a030601030b0c25080711090103030f03230903040510022a0d170c0c120604020f01050c01090305031902 74
    0x500004c0d07080000c01d2942c60900f010401c61500818206d442c0c2d00403070700380e840c25845100b540e840980b00300d1003a20039110721409065051000d0260b4100440010228101e901020b03120708800940021781207100c1415030711000600c81964400d000c0014050018030660344d40740070428000c58000800e10b404107400f41600c2e8040c103202e00f00d0f00e5585038441070360003805410544049046010180640c03220f144440d43c1d21605035555215660320f012200740704681c08042c0908860b10050000980102e641c0d484441c032490f00040740d654204801d1401101002828086144001031021440000c8010003c0d248151446244100095412030740d402c03080d110031070303060070080104425008000d002607010900500401e41103106440c0c00c0c0c40706a03640103200240000041582c00b0420a120b18003040604803880420050791184040c3c1302c44009100a110300381c44540c0c056943c0c001c100f83c4442e150305a00070000480e96140107400c59006031504c02c0b004e50141c80d507a40c04c18041c021201c0c00e03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 870456241 1250 870454991 870454997
    0x3070c0c29120106180807080307030923090916090c14040f090504020607080307022104030201050d0507020708070303030608160305100f0e15040c06230723060601140406 75
    0x984c68010200c0d0b001c00101c000ca034000c194850000b03922201002207901400c21038015507070320707030703061a0281c000d000035442602c007051000d40d10450072a008098040c0888261040503207941c0380540241002d505e90124581d06c0c0348890041105082a1b100041c80d490a850f00c01c00c005450040f61700d01d000b54412046c9041c94000148850503458020581161014101e103003080a0b07a9240030082c2c10456000c03006078001a4240c1d0103100c946100e1002c10180180d5500d4903081da0002841445062144100f40f81c0307800c04284107500c20442c010040141d1400e541d84181c4924004024154038032502c2c6486c400d8044509441030080c901d10101d9502800524a021112445002818400445400e01541d48040f4001c0700703400c1c40260307092881d00101d800d00b8074141c034003094090601d0300310a0412807003c0d407080880390703c103411400c00c8031028560f40c2c44540d13034544401c09144000c1d0070212070800c1c03210304014000c0041e606016010980318042c82005c203002e00c44260040748501400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 870457491 1250 870456241 870456277
    0x2d0c02070f0303120204090507030f0501090b281509031b211113060f0e0405060609040c030210030e010c11030a1d040501141207030201020d0503070c0c29 68
    0x290291058084002c90344c01d001d8101613949840301c044510807103001f0046626048000100840c5108840c05000d10b124200040f00006000c40c1c0005d1043c100b600b0507070031340d0001004a409a014003402003400c003410000c011038000307001300456114401111448981c001010b43c64a200552009482038884070625030710510394103d00c5964000d106551410706200041c417641c5802940310010b03082d40c00080b60082c9400713405a00c2c1180340d0b00c00b4640c56100010322002400100e405038001d4402c07642c0c0c0000e61500c1c10705000c2041da44e40001d41c0290103040640d8a6601031b0800d020360802c49000300103441c19484140c82044054144444e0303a0010840030340401c0c040c0c06800d104803000070b80c8019a46001001c10112102030300060203c500504901c01e00e8680704c0c034104920780842014103130092031640042e41c0c9002d4081030400b40030011000605403403007040c04940c07003a00a44207a80f05952040c0312f0f08804026441c1d00051803107146101000d044403400c503030043c0c08944c15118 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 870458741 1250 870457491 870457493
    0x102091c0201021507170403020f0d050306090402060307261005010c05070b030a061d04020f12120a0309120806090604020406021902060705060c031e0c070f0302012d0c02070f03 78
    0x4046134010102000c3c04000c02044030b88004018620788500c2c801e800605071690319440c0d0920303200a408024041000410420005855118080750060f5041e510b075901c0780c940c26401d45001c9610300005500e859040e150080311449860894010410800e007403480035190780c01120314010511003d070460340303c0c6808000c2c80c1c0383c9100455014110071700000700d407074850000001ca48a01014214600880018081546800c682c8190900c0e0200d03a070503200c03454543c81a0f140c1000f82145a81b100000c05d0300c014070340c06034100c080c55940c0010400c0002d03506017800740440901380e40f60303405543d441d0300252460820380b08a40545840e90020040c5c10302001c1880e886040c2864109d8004d4824804100050020011680281020900103407a031030309402032a03240a420440750741401014091002c108060400c031800d40b44c01480702c20303000455040603030150003101101c0210903112054141d0781034148603400c010a4045030148010301150000700d03915000da000308241d050207960200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 870459991 1250 870458741 870458773
    0x1e03030c02011121040807090c09060806130204081506040c02211e0c010c03090f06090c0b03070905041b0206071101090b010f051c0c1a0702060c0102091c020102 71
    0x580b0f1502c40c80855940c5090080d01c0c60b42d505036246820a0b0040c0071500b07000c0c5100c24010300c40513011030b0904100f00e40c0c3c1103000a00c20700d2280302d00000d01403410b0100e066601c810918101000c44e41900355902c13941d607240300c1d503900d90011421100041c8100420791710314060041500e08909070b8000c0c401c1e0b88400302d00e00c1c05000c0f40c9205140365801081285140c1ca400c03103680302e01066040e41c15448200e0040120f0a54030700d07a081d9400c1504c0c2020304400202842400f00c01103400241c00212a049480c1400600e22680c21141c1c101601004000b441c82d440303210034065070400e035410300c0f190100c603406d04111811202e615000da0001301c00115814460824400021020400807c0554441d119010400020380003003480340500303e030520260908a8101d0301e4100c507840e41500b0394050341c0750702821140c0750254545081101d00d4250064814000b0f50320074540081059644444c4449842d00075440300307003001d000d0703a404a60260030303050407054007078105d4060b000303407008005050000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 870461241 1250 870459991 870460007
    0x702181b18091e09031c1a030a050304050a0905060f0402071a13290f06041d060103171e0703050d090b09120f160206040b030a061e03030c0201 63
    0x814040144006009003076840c01078080c0901079450710740070190f03400a01c8194801e40101100d9140d4010400e4080201011041882107001d09070000f440e6180008006009943c00c03825070b0b03051081000c040306024001c8001c008075a001c81c0d0760306c00603031b41d442142c1c00e0b81d20460f410340e8081521a0003500381d00300b41d001815020310495103141750003803e02e282c100030581961402c01c05400205800c080060b44a5030096610345411072a02481004180c850075042c020f084155200c410400300b41d403a02c89411884540ca44990500240700742c4210307080d030380e500074401a1a035590074000d02c44401132200850b115a4400c102d61041092205060700301940060411070420204000030b10305000a0300c504201107101d1460540c80381084041e007071414901c01c041c008030010800800000c400480c0c01c560246c10307010408034440725140001200c41c0500d900c81240400004100b001a803804e90001080d104500740d89070518000d140035080502081c0001000b1400071460280558007510032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 870462491 1250 870461241 870461257
    0xd0503070804030b040c050d0b040303150b0403061e06080303070e0f09070302070b070513050d15110a0215010302010503240a23030c0312030a140c0702181b 69
    0x890303140c000c0994440610b940268002e0307591280303910502040100750408a801840100d41c21004070f0029103980b03c801e0700143c001000d0590350015070b00c043d425070702074100a1030040c081d1502d8569074144980600703401e100c100c8070803d8030b80340c85107400755601c200f505032000c0c0380042d41150303501c0d64150340c00782440c1440e580c000190f4020101d16034480c80c089100b80520b0354050b8694510346860b0300084409840c03c4240082880501e091084509088045072821a40210003440038108100103003520320321650498200039145003c000c7c1e0307000500c0110700d19800c96280b84500000f8020000c02804001c0c00507404001103224400140d0300c801d01d04890303003541802d0184c07032000140070303021075413045442d020a002d031042e040e64050311003207101c8030070b0b406011010741c8d07100000d880c0d4410341c100210a100c0132010620208196204030740c0c40702c0308a03141546082440109005d60003d0780100c0c803030f151201d50f0707040051018a24070f0040c1000c654445900c03a8000c0d16070710640203054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 870463741 1250 870462491 870462493
    0x60c0a052703010c0c020108072a0602070212060402090c0f0307050f09040e01061d010305030d0903050403060608060a050c12060111030d051302240a0e0a03050307200f030a020d05 79
    0x7402030341c0b60b42c01e1040c0003100042d61a01c0d404c8007410302c000f51034200020090000d001c9181c104210b4811400010081000d290f0b11b81d1600403064a0034400900030305a010b50400c00da0b1402c0c407010400007c0c1d90340542d000b16a160365981c0c2d0a135816080c0d00c05c200c003084103000e0600115403080e0041c8080d203840f183e100d43e00c60521128402007000c0314200711000101d40e4403501c0801c1031040d41907488a1079052086204025810358403110b07540c2c0704101c444a0f4440c2d0f161161400d0600c96400d440203503078403010078012545d0305d00c21290307200020707290380400c185000e0104100003d068100c0d956503072445451580d40d948c400040d01c4034940f10443c0141c0d40410010344070400c4007803144030710035642e40060b40c510302218018000b100040d5501d2201a4620b000c600501401400a032003401c00c440c500075500c1440c103000300c0d6080c1d405500050480c800070440104000c44112019074545112800f0f0701d029840c082082424a040103940707030550071030b400001c0542001c2c5035400740a800b600c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 870464991 1250 870463741 870463807
    0x71a0411010c17030f01061b0b0c0a110610081509150a060b1308010617150619030f050607020d090308180607031d01020a03080a0513080d0608060c0a05 67
    0x28152903c540c000c075815035580d81e0b01c000600c0415002800340c150030740c0c0050000c0c05120f09a8507030b0340c0050b0242061070b0410002c149400c0d0a403042c008149840c01031000e560031402c000314400901c000340d0141220b54003440b5041907409c2c04d141006440303550600001c20040300c0300f94142100607001750041c0d10482d00e44c07401040350a001d9005207812035448440d030010519000d0340c0750031201181c100480b000010304010040490001c1d80700f09101d0030902c9004d10351030780340004030b0301550049440305818203090300005015102d445d070350701903000e501034921fa03607285942241c403101c0012400c000306119074010704c0800c1e60140988070704200d00c41c40b40340e40c0d040301380021402e07089070504900044d04010a5800c0380146020b03000300d40301c00e000070000305032666030162032540004d01e1a001140c0d550009030481d46803e181803002c1d904607041c02e0303480c1d80c81c0750400040d20031070040074a24402d4601141d07000d02c2d010211081c51015a681e103041010802c2403a00060707800c00e10418846240c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 870466241 1250 870464991 870465023
    0x31031b06020415020c0307060905010f021015030605100501081501020708160f080d020631060e01150317160b0f041203020a230d02040b071a0411010c 66
    0xa1004001804070741c04100d442030b02041c402850440b103200040d001f500200030812440c2e4202c2003034411344100342888210000b240c03200b01d14000e8003100d03143c07446003404050500c01044543c0c11058901804007480b140c0d6681035900160103140c030130701c0d0005d801d00001070007500e0580d54058151a051069a000640c1ca8049a140440340002a594031070382d1801009007403114a40d0100038140c850190a00b40707200c1c10040c3d01d4041c000c0050072100c000c0108201400112080a840032a282a1129500080e41060401082058005000d943c640010b03500c1d103000c40c031420070071603501c000012210706128802c1270158200c2c014020002c4000c00c014000520035100e42446014051034203003030f61400d030a140c030800700d40d00c02c003805051041001036811941320f00d241c1803c00c49800303010300350485103c0f00f0040340b02e615048403125201013400320300310141e071004000560007284601410038080c4110101540165002400d51011140c40380855019003029a281401100400702c0003102c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 870467491 1250 870466241 870466253
    0xb070c03080a1b080408061f12022d1c05280f030503040303060509010b0a200307051005010608011d09030d0e060f10080d110a080f0331031b 62
    0xf05021189140c01040511804104104040d0b00040c51807400b1070100441c05408400c405a01804c14a0000c40d0040380545d111002000762041c4401341241c2031000c508812104105020405480b9070764071190701d8013a0604505401b8543d403c20041e2008120390541040d200030b800004803500341e059103610011610041109160078003944031242e680c0b4061030010202d40b03843c0c20091080988500500c401840003054907000800d908190380746440b14501e00c807450074800d001581034171000868900300000420b80034080f08401e0018881030340c07500000e03038468109020340205482d500f6120300b00110100d4905800500000960f031802ca90340c08060152000c00d05010710b01d920140900c04c0c04400e6138040b070341c0100310845039018a030419200340e4a50310b25084100422401207412001d60005011815410b5030000300c691f80c40f800c0c40c034020031941044440d1307034804601c010710741035264011603000c41141c84910410b2881c201a03505441810401c07003450f0019045040300c5c030001c1c078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 870468741 1250 870467491 870467537
    0x102010c120f06050d23010908030c16060e1e120313060209090a052208030a0b01030b090f04050f0f070306180c080c030c0103020c03070f21030507090b070c03080a 72
    0xc010020011102e40400749003091188079031506c521a807510560801013000c2000740c0c0d400000210000d60740c4c0c222150100ba03550751141e005030003949040000010b21100003981003510103c00c030507580c4012140d10160b01c85051440d0b0180900f010000246d401f10318480c1d426807031b0b1280d44c0c0141440c5661001c42d1503000101caa0400031903641c0107100301401c01c2c5580c0c06c00041010030146502d1010703078800c003450101034580300a80c1e0b01c07041a1021a80130f13805c0b40c00e001201410200c1d07540303003240d820a60010161000c2d105409003108a00305c500f40440c01400c01c14030000180201e07440c558400c0e00500304c02011035842402d01c282100000c0c816100b580c0100001b400510365014080200342c1800580200305040c544100302003050400007005650380c1c0da4110800d10f84054039070a004071851001c185107002c0105c90700309003600035016408180a4005039454606013a180c40741105248941d0001a0011450701820000500c25100920703404200345040c0013070701e03003544c0744a29150b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 870469991 1250 870468741 870468743
    0x41512170a080a1109010e09270a02190b030402090c04080d090f060504030201080609040809090f070221030f09071802120a0b090a0c1704051b0102010c120f06050d 72
    0x154086040c0084002c3d94020900d203c6441e0880a140c00051000a03202001c98504035001d0301d156030020341c00a00402d28905001f8080a21118541401c21101d8550040c204100d10580070719036400c02000420010ba0151100100540d127140c546030200302c84110700400f21400080d0405c000304d46503505108441c0384a20b40d40b2400981814682000010315054218500304402840300f040980e0748001c0e00740e0000c03002d450b10302040d1510300344150307284925541c0981294007070050015805080b101e051180c00c042e401c1c4d07004051240c807840c42039441c00c00000480d140520104000307100701c01ca00c03a00509050116001da503581d0b0010f624650141000c002c6665021600714180b5001540f540d6008500090410074034a0f4080001e040200250081a2880d6101111610b1324001e4040b10f016410901032000c80b40b50604e49213540340c001414907039411800900b2140c0d254014007900001401c25101d11400c031021a07404c40050001c01c60b003090083c5c54100c0082c040c2c0f50f40310b081c2c07540c17 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 870471241 1250 870469991 870469997
    0xc051e0a0b010e07050a12020409140405070b040b090f040b12160f050a170c06162a0501210603061515080109020a0c051218041512170a 60
    0x1030416080003120781c1016400202c0343c80100d001c00440c141d1181c201e5081c4a42d0f42040c42405101c0360980c1c0003800b41d600b107140d03a80d141180201610b00c0c1071031050720580c0b1031002c071140c0320f032030314000b48241c002c81c0704641d2800320030b02641e0034600d452a00c0b4030040c100a4000175130810300c8000601d01d01304100c0d0000ba1500a0317500f4100c401c4906030380c54050030030f00301d010032424946004540b800e0003612801207200b191600014a641c400d01c016010b5100c010030880e100c0080b038082100071090b98008962240d0221841c1d2000d9030000c0944015116800c012408580f4000c01034913103400c80c4180310b008000c9280c100c14250b5291190314040c0d4005e1000240c0008404c0103c0b84c04c40e040d401002642e6074400e025118aa440040d06040d140c03845000f40c0c403608190000c0d1440d404850004150340034801074041c050007106c014000061520801100c80105c400a00c0202c50304203d181041c1c800c81e18041c041ca107518504660454440c10f188038050640711b500d042590000c03002d002c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 870472491 1250 870471241 870471253
    0x41806091202100b0303030604020705030d0501030305300414010b030303040807020a050901080607140f16050d0311120702190f1101080c0a0f140d0605090a02030105030304060c051e 80
    0x5056410040180b040c4883c400400000d4507201c0001d54a01000f05100e110310307000241c000401900344240c07201078210325001e02c859616440c02a200ba0088850501903032684009400c043c201501419821590800300095903101c076150400380c1e06081180460642d00d8010b10429a2000c000544c80b41e070181960035126400c510421002104590001d841110480014050600040b50183d0003803040c1c2030a03411076000a10101403400340c03c104910b00c1102141c0c00b03000284101c80b000c250b9100f407003540c2c00340035400d4046d02240c20405820134425010f00141c06e81c031105010303c40e00100366004032000340c040c45040510a624a00086901507a16007415040213203400d813100c40720f10709003482805031a102840940324010001c1d0365080140070842c0d241540d0013100403400700c0b01c40d20782842d40c820643c0da401015007054800c26000f400440002100070200c0d00c00d583c1a60030040c0510318140c5003000c00c0fa400c0c07048070301c15501030090950511130618a488141c0b07810b41c48501401d5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 870473741 1250 870472491 870472523
    0xa0b0a08190b071718280b060405040201081503070f03440c190f2001050d0504170a020c09010f060f0c0309050d0b0708070f0e130e030307180602010e0c04180609 71
    0xa1f90480207030115001d103080209002c0145c2e000060140c0c03140b80f0310503400044031881d001074580141c40c0d03c44040340c5801003010040c01080303040345040c104080142081c81084c100d0b50242c201c0d003c242541d440b000e0b0701784400b416110300001d00710350b09404102c9040111007841461012030540c41140e03c0c0c03c0303c40d41c02d030070412900e000140110a0b0250b00b0b1010001c2c2d0b001030180d2140c105950f42442d80c4400040400016003008242d2140d81440180c4580383c0e400081d40d10702480d000c41e03115444030f0000044429001003901c00342e17a401d9940c0c00313200390807407001d036941000c0f004220300340042e244021845458002010803214020001d2124600703000d0405040d440019204000300010b4100c642c91054001040010040d0191612004445841c940314018a1955201c080d83d01001007401407903a40024021191b504610749040402c0c0d0b5940c0503400c8031014184001d0036080346d5201d071403e160a90182c9560b44604011807258070745607407283c0407160710780822550340c841429446 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 870474991 1250 870473741 870473753
    0x10e0a02060f07030203221701051e04030314040b0a1a06071106041211040b040902030a03050309120301170f070e22021f0306050301020a080a0b0a08190b07171828 72
    0x740d10450030710700070481d1341040c8800d1340201c40c1c6601090300e0bc98410340841d0416100e603010348030040d07904200c2091381c105407418001005084e6180341c180c2d41024403c180d844100302c01c40c2c4154000605141c036100d00da03030b240f80958038503407011039110318203100c00030320782c010364603d02e0007140f041000910b1030700440f007080111030210b5525401145050002c00c01602d00003100c1c20b5168040c20030989998840118605d800481c168001c0000c03004800062100345006804014200680580b02140d002d00121503484075540b00f604611031250f03001c02e034002c0b801a44080c220207288128000d0426503004121040d00e40081c220704d080daa03020b8100300c9a894450780010704002c0b0000e5140c028050740040400101511200d03510342e56444c041000c3c3d40e8034081400414227042510320042100541d12484512808140ca0442c020400a01014417409080403100c44010704044207880305000c50101b04822501c2e03148074464001403003074081c3d0710209030108685c00100765165084521b004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 870476241 1250 870474991 870475019
    0x2070302030d03050f0f13020d0c0906080f0d0c022110021c05010b0c0c0f0613150822080d110c0f01061e120510050a02030702010e0a02060f0703020322 67
    0x10040c3c0c0507080c0500c07007101d810703111000030160112454401c27007156040c28142c0031620f501030000a0b10b0725600152142c008940400490004401d0700c1e120b0101400c1660714441c1c03a0f5000303500c1241c00c400864920400110310600c48140390880c3e250800c0944041c04a078481c10b10760002c07403803070300c01c195416100f4010f240c05440e2a00c50780b424084540d9000e6074403030546402c2072041c41400a2202c00741c8404040e01c0110050781c640c50000707a6149110101a21060034002c00120180c0001d42c040c0d01360840040da00408210381114184103440e244081d402c42c0d03400101c480c6d00c03409045107106408002e0302c40c0d21812000b40980203c030302080c1e400c41d02158030404800c00c250002040021480d0078040440d03d030070f4402d0300240ca040c58580e090900d00c41071201c4140c941001d00a44c040b49038042c5204143c55002000312040311a459035903004032100017544044100300c41003521114070040d1046034800c1c01180c2c00e1881c24130a864188502110145841502400400620042c0400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 870477491 1250 870476241 870476251
    0x5090f010908061501050c0d09030b10031703090c0a09050106020f0f0c01030c170a02070c0e04020307030219092316020d03091103011d0d0203040803090f0102070302030d03050f 78
    0x4120414039008901d03440d8800146808004c402c00844441c10307034020012142c1d1040110b00b5101c0c4100c0d2041d0280844a040c0426036924111000090000c02d5850559050340d03003010064200002148034a1400d0380010214a894094a20354040c0e60700e03001865805044144000300d810740c113042d0000d1815415441e8400076501100381c180c0c080341c000c07604002510007841d02003030154001000b555808100610305442494001c200031b42d050b01030b406420080d11940d05002100e90314451a01c60079003d64005e903268000c0c00040005241182c641d00406a01c100c3c2032520795590400f0030708a42c0e0301444042c12116010030301d5001c00010481c19401001a1604c1d1080803030010000e68540c1110044028940d403600440e0a00a8050b182245810014024421000307503441401c0900c42001c04900c862250300040c9010600200568081d281450000d50928540d102001b03030100300d0040d114150b000b40303203000c00542c806200c5103680103000d4402140e01e0070075900c034a29011005003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 870478741 1250 870477491 870477497
    0xf06070203070809041a1207050102010c0512130606080307030c060e161406070c15030606030b06090d060609140411090105010f0f141605011b050306062805090f01 72
    0x202d8600058040300a50350200c0043d14001080301040326884800f40907901490b80c07050404c05c0e00090705c400000c030403007a22420390003404142d0000342c09407400c3c0284940d84090744d40080000d0710752000c250b000116680103c0010a5040e40e965480d402d540c08010140c000960214840d018407030170f809014400302c0060300604441d4000e465025000345a4000c9505460350205040241c0c0c0c0c2d40c0701070700c03d02600005d0313070003c0c1075961580340c0880701e5085290b404242490000916a03009104800c2c2440024101c80c0c40c0c403440070100310032180390035021540d1a90b1050046443c980034401c6c02c40500e08501c250a0b5803c00d82801c16000104030341061050411500520a07640d00c55401304003103001e030800000300941c01d04141c40c24140700c01e128405980c0880c0d083e05111807044140c2c10f00380554001c000201d0290034010340307443c41c0d96903e800b00710200b02090207414840010034101288080810007524012541d80030000040e00220008002151890304c40c5040c0711300c0d11804600742 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 870479991 1250 870478741 870478747
    0x6130c030c4a03010218011130120c030615180114090904030e132a11061e06011d060a03060e0f07080f0c120402060d0e0f06070203 58
    0x3406080b20303400c0c6440700202081040110b14100302c00600c56210000020000c0d51500b56104110000c415001c2019001174000c240700b0b07407120408100380c0f01e00b9200c0c4040d8600508461000c141c00400b0342d940020403c01000184001103480d01028010401c440c44507581e424030b00f0400085000c24600540302480030081600101083e8080800884080c03c080490882c3c0381f604134800c0c0242c04032950800d4034002040200769010360340b20b500003c112542c203110050b142c8004205c0c1c024032203510400a84001c1d4940c4d41c44011030000c140b58840c50404543c8005500003424034005480301e50b00d03403070713001c0442c0f031003004400101d80d201c4801e18203201c031220240c041c81000001c0c55903a90103000e0014240080c07921a40000d400340c040c49400c022903040c03035440040103030f8003210200000340f001c0c008601003040030f44405008491200145051071b510340c45071007003080d016001301d074041c1c410811040f002250b8081d40700b88403204409880d01c8c1800c4042ca03070030100b00a2082d41190410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 870481241 1250 870479991 870480047
    0x307090c0921060b01111e01110703200f070e0403021203072c04020414040c03090503040e07120e010b0a060906140c0f060906100f05090a0506130c030c 67
    0x2c26000d842e840c2e0041c402141d01d40c80380c001a160208540e42c2d0f20814080d00ca407200b0700c0179000420a201da402a03008003c010300b090741b407203264050102c00070b001901510561014018079101001003911541c2560070f60700000740100d150010320760040030301080310410401410b070141300034440110801c012500c1d5240081004040e8844622015000100c51000030659034a03044849945407000d442155100e8450600c84061801d080c00184100d080c0104606913038443d016080f02294000000e5040c44c1c01c110015402107401400ca10030400a070244800352002400b50020300003428000103401e1054a09218251900c0c0d00b02c0002d01c03a6000c07040001c0c0f0341c070040600c60100281505529684c80707002c1c5500b05402100c242040d485407000707205074030f080800d4881c098150600c51100482e52852491045030262044580c04011000011031220003030300b11710b9001c00000c1080501c0c0e51401000030444807052210b200280d51001e4404029400448030340b15608200001c0080d4000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 870482491 1250 870481241 870481289
    0x120906090318010c0f0213021201051807080a0b1522050901091d0a1a0a0911040504051903050a1409060f070816060f0b06071203050705090307090c09 66
    0xb50070682410064800350410903c258001e21144641c0d00502e14000003800000b0f1602a40141000011211a2400009032460030121702c56403a0807620000c8400e40c0c81303031001d88010310002c0541c00003648401f044940f5960f0111408102c641d040e012503128140010482021a6034820f0012202c07028130b002d01c402d56466161a045444a80006c82c0c400d1800101156244103d0300592051244030101000c00809855548910b020b40a10102c242d5850798407400395119501c000c0d0481804a0300c0d04050308140c1c100e1940180920101e40e22404160390000d5618480c80701a400038002046040520794861040619000c85048141c10700103004009140d502c01c0d075503030703403002c130400194003007080060300684000d0283c080c4030010030515070a0410150410000700034030103141154450040c41d102c1f003510600c42c5c01211070b0000e0101328000b41e00030075000d002d440a0110074440b0140303682d020008140034101c2c45001154007141540d000e0000c01043d00035040400c200020311800b118 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 870483741 1250 870482491 870482527
    0xc0905060d1a06060c03030a020424090315090b070206100603090b060d06060b04081f090b190b04020a09050301060509010b07030509010302090a080c090709050a06050d0f021209060903 81
    0x20b182e500c0b030400c0ea101c000005001d84a010000220740c0400700c104000c2420701e0380504100c80e400c05040485607640c40610f90305c2000300c0c01910104010b0306050002c038204c00301c1d5802c901c15034030f4002050002900e4043c410202211481c00591201d020404070101981c039000003820941804c0c0441001d07039558003100d040041c049809600ba244641c014040581c0000000f460000b54496a460700c032550326450380c00842e0141500c0c8890036100014070f65900c40c0c601c450350007050740046034440405281d0980422040140119140c40c644001aa160300c02000210140c0d01d4071006185064181404e4a403281d10a078800d1340c2c00c000410a521954046030075003541850090756921035040180c0090244c403403d6500540c4003d000315070844005403405100c01c3c11900d40b241c0e035442440c00c50302c00c241806001e401c0140b8080070031449006101401042a280d9000301d08507070500442e070102d803c00c01c00e00c41148402024024502014490141c0050484001e10f01d490443c81c030044040d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 870484991 1250 870483741 870483773
    0x150a0801050619120807061b0504060237060b040204090e2103220f06020c010509010603020a060c05071a07170a0e010e060c0a030503011401030b030c011b050303040c0905060d 77
    0xc10009112007c2001c00e45c810880d41d48840080c00c03088c0201e01c001041500036000d444090300ca404001c5030151007441ea000c07007038900c00303118602d910746544014a0a5511200840d4801c0e01c2c2d5031246042d50b143d00180003e03141d504070015101590f10f4404c0e14003030310311300c0700c4449400c1d942c0c6405d08202d0101c1140da100294000540a084c0c0b4400210303c80c540000c0c01400301d1001d1411042008801d400031300002100200900181e10b074503000900302c1e8520320000794848004a8204905030085c0400510203000d0001d41c0c801980e124030311034150b40709075884900301000059000400603010040546866035a1600303040920600b0701a045901c80c00c0c0050502c000704450508964a81c130031610320311b41000980b06108038620300500290007c1c0030b5940d80f40310342003c01420b54842e01c0340124041004004000c00c20240c401500d00042c40720800700c41e0111f62a941002c82d0040000311300451052404040d2245040d1883c0c0407a04060962841400c407411180007141e5600d6581c4503070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 870486241 1250 870484991 870485003
    0x2310140d08070206070506010b07060f0c0c0b101206020702010f0504030c031e240c02210a031b08061005031501030b01030219030e0c091608150a080105061912 70
    0x51482c50000070140e000754400285648111000454004081c0c005440c24910030881030200c0030060050340241c418030400c2500062480c0300c0d0700d01040140d003189402000075003c00300c44645a58611a034280e284100b912104d400041480441d40d024081c000240614901141801d08680d280e9243c4242c3d480080e0440c11461020580e81285c0d501355000103a111900c031401410700120082840c152806c07460009207085c16054207940041a070041e84080f910000107078400c0c07203c1c4c0241ca5002092500d040503902c444889054030f20100b882d18402d41c90f141c00c400c6181c10b00800c0a400108042c2808211060040c4040b1a131585114841c02d80e09003004102c400c400c90048009025040e02c610440c100350118611164041d070200c4407200c5001e05039480c83d0f2041050003240c0c14199040d0ba020b1099a044484032032203107500c96003204114809034107006204e4002030081e0041c2d040010265540d01c02d0145528211551404903203002081031465460150a0815296255800361039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 870487491 1250 870486241 870486247
    0x3240306160e0607200901050f0105160b07020303090d0e15030a0b130c020f01090305120403180f05040c0201060b0a0f050f07030f020f070e04030f02012310140d08 72
    0x81c035004104111056501801d015140c081604206500048151901003440044000381c43c290519821147c140d80c000f40c20380d0441d16240c1c004441d60380c00424a00b058004140c284000500a02d51850140b03c2541c0119281c0c00d1581045050800e81c0c410341080c0301c07800b610741a841d02e40101c07614480d140880000e803296034400c2500301030300c04e143d0a20b6020b900000c814076245150780c040b0040d030403664200c80c80c00c0c40c0184200d00301e4160001c05000310340d05121020542e140104400d90040c0f09180000040c1541800e032490301442d83c0003a05100c54800062029042034407905248600b01c4c0b00a207c0c3c90310b001080f0407207105101c032100802241c11032041e04540120b08a07112b03d2030700c9031f10f26929021414002c14003000c2d039454400500801d405215122800901030301170310384070030000840c3c2c0c44598090310690303610071164066540f10901d0002002581c030b1500c9800c442c400c5840c003603241001301c5245445260300050000d41610101c0380003522400c00b400403440e030040046036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 870488741 1250 870487491 870487531
    0x30c02091e07110111040f050f0d05011406150712080c04031e0c0e010e0a0b0f0d060c0f090315020f1213020103050c0910030b2403240306 61
    0x240700514408524000e10381442440300442e071282100704a107a50000030004007140407002e40c0103105030704c00d48200b002006414002c0e4988080d15400d00304006004a000c0a1981c0ea00c9080d507680f440100180d05080003000442e0601c441c5a02c140c00003140f0040c41d0500d1a500c1e2504240000c1c601c1040052080015101440038012200550303040101907020310328414104450300d6924400f2248541034200c0003030b100e600460b045058a0101d00031301443d80d56010740700000c0200543c0190301c64090b0b101c00b80640ca0b408803c6c58464050000441c2c14441e90901030076407116010480104210140104040f944440c000c0d0b0000e4240341001da5a01180c610b000414060b000c42d8000c42141c80060000c40450314103640751091003a28140065a034070300c10b402640c05451910b41d00000d0340201c40007007620170390040c1e024040042070038250364000552000203004062150341c0d410740000074005c0307101e00e51020b80d00200710903500c0002e800e401d45c00319072111405043d80c01c410107200c00d03c0c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 870489991 1250 870488741 870488761
    0xb030f090106172a060d020903011d0313320d02031c020c06070b1302280504050c04080a080703210506010e030105060f0111010609060e06100309030c0209 68
    0x50007009402c0038004400341850781540c0321203040500445250105450320f044552400c40e80e144250000c0c4406c0c208070103200100c0184d4042c00c400c0f40c0c59580c0d140b48000102c1042d480c1c00c41d4040c030100868840c48403111040284001d60000c0d000700d280c0c450305807281011680d131400310400d5280700300c80508605000c1100100f010354003c0d07060044080c400e5a9069510316060f0191041c0d00312488005500c06001e054413845901a01c1004107c00141d01c200384640030092035131000e8048203014410900c854484115010f4200701c8002000b0308101520b0503010361f41e00b1042c24000c00f40307490304d0816a940c3c1c0b11074100300107001c0100820b0b03643c00e060144018182081d608044880d4031a20000a0001054200c940ea80401c100c00150000c038103051041c24401c80010307040c1101c45401d800113555040801903407040310340d02d8031400b041d81ca5076402180c00501a80c2ca5000807070410600300500c05102402d90410580f90409040109621188240304150143c54203456511040002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 870491241 1250 870489991 870490001
    0x30b06040515040e0915011d0c030c0d09030210060902040e06091f0f0e07020f0c0616020604030b0403030b121504020103090f05061b0f04051513030f06150b030f0901 73
    0x700b01150744c00c100105101103044e014030745404806038010303070301c070480040790300603035290060081a0000010002c0001c0c000440d0440c1000c00180c0c2049031492004003070702d00c0386000700c00503080740390407602004190080f00044e001d1414107504050900341c2043c1c6400d0000d159910540b0000c1c046100d01001c0c00011943c800c81d0180c48200701c0e12100481846015031040340300504070340300050609031001c14250700910780003000c2e00c220720440c0e0412003560801c025010142401705d21100050b0741d800018001184100700404943c030781070074050104e440011005000e0500110103a102d014003141e260071400f05c402004640d6101ca0004034010180410002c05816003903802d20107002000488901c103030f06104404100380c1d052840d101c0a40181040e8101c400c2c0300784010f00152801101c140714142d028121182040003424030045194503942c410740740b9920001c900030a002c410302070399208070189158840a45e203042451000c42c07100906403101a8402c50109a485e08203400c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 870492491 1250 870491241 870491249
    0x5060414010b1911030909075301061b020612151e0909030d06170c03060f06090411090a0c030506091303110c06130503010c030b0604051504 62
    0x5035030020760711500407094a901c0103010307072007034101502d040e01c045108403c1d020001c282c0c44084e5080401e010306002c4090700c054210f0b4180900d004200c00007804041081d4a0002509012010904160403404507100c2c15422600d140008800291182e90003030b0750309044070800d1615080c050500170400340f1018031480001d602020000f2007141940300103c4d9a401884000d40d00300c140b01200f01000069035400350000003502d00300300e000185141000c410b580c0004000700b501c1c03600740e000c3d4494084981940000c010200300004142034101c04010307104142400b03030f00130461070901f14400c1c1d941c800000c01144c801d01401e0300240400c40918900c405256016040910905003110440003800c006140e1b0b100080c9000001401460164166030203074441d500030b50b00803203094070202c3c7c103070000b2010b082e8107126031850240c80d500c901c4020044601d2100c0903d101c141004101405e4807104080a070030181060130000700c40d030307801044404541044030f01e10100c0303802070f03550000342c00b450340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 870493741 1250 870492491 870492521
    0x2113061d060f07050d1404200310020a0e04090b011701270305071203050a0b090f040f050a0f0b0a060b09030d050c0106091e0606080903190e0316091d10050604 70
    0x803150345010706d4186180c011480b50445c2030760400d4600c01c640700a488998071560660110b04d00302100e0150b98010320034040d03245003031044086002d003c50107507503020000f12800d46800c0010403c60307613401030b01c1440030b003484028009240c01520036010300b1086c01801703c00d80c0c089428a401c140c0180e0450746520360241e440f4070300f200c00400160092200f10b80c00502075081c0700c031246a0f45805040b162040c110405000765940f52510749058100400030111418494046c14002107100d5020419805220b418200410325049103108103070f5240703a10044110b00300b8000c165050340d01280d101c518100070303c2e0554031507005940c06400750525611511500e450701c924081107245110005a102d00c0010081c00441da65aa044402c0c00c03045a80340500e810511840104c45965a40c521750540180780610b5001f045d0400a814495824000300000c46540d13810010354505024240352021450302005003140c403d880305466036010616500210b555600080300b03641c46900080d00c624580b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 870494991 1250 870493741 870493751
    0xa110f0d05011505030d0914010c0c08032503021507050438040f0303031104050402041e2103080414060702100f06050a05062113061d060f07050d 64
    0x1c140030b030091081c9152400c000c04552030100c0d582c24006000003400144d03654080c2c01034070782202180141540641d250400c4050f4210030301090700a4901806001c2d8038002d1603551840540048040702140140f0000901000354440807a8002c600c80c0762049640118150a582d0030b07408440e640f140d034102e2102161808460030307000e5100150b4907003042c20200410401e45541400022501851040c0d0403000b104000c20310000748030303810444003041440e482c2400c090302d0f030300042c1c1030303811070741009118800360fa6040112501c900403901c000d0041e035021f103041c42d031800510070421041c6480a418402c540000c141040900c4200403114110303403041e60301b81d082500000391a0050b02070b60400303407030500311301403071035800c900c40c5a0851780c004145100d2545000184005608001020a8076034034200c440304205048a075024414024503024540920710307441c00c1c0040f150308006401084820344c01100c4454000600c040e005907404003e0001942e4460341100d41d44036075034595210508007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 870496241 1250 870494991 870494993
    0x1a0d0b0d021c030806031203190204050307030b0f0f040809041104051905030d110616020a050714120109080703050c1e0706030c031503060203100f0b0a0f0f020a110f0d 74
    0x28001c50030b0442d02c00d0ba03454540391070b50070416aa030b05440843d8a4010386c10004140401400700c401c100c4c01828000250600d44d8800000f400c008840c0d03c103654100346207040040c03050002e071049a01c450030902990700c80c00e0940710b5403064020407400364003407a81c0342c50300c2c103a82122200b07490083c140103018894203d8940c0040182504034402c00c4c3c007030710580b141d203c881030140e00150342c013026020080ca5295100c900c0381d0b0200050813480340660040c0b02c419004101c0521885002d041560703024007c070110171040c000341403560306c1e2040341382e4503045510002441d0102100d40442d014500b4a881d41280096941030a0f1004450b900b95001c20311184001e56010941c40110784180d1130400240b00c8425013070b416100003071841c2e22891542358040c0002100e6a01030764102201c0798640c2d802c0e0340c40b41c0c120f90000c406034000c500303031600c0030a808132000e82c0001074034080c503c00c0c5400c2030050186600a540c07200701340f90040000c04681c1980003c0d45400f034104080320350040201d02c4003409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 870497491 1250 870496241 870496279
    0x10210605041d0d0801030b0c030c12070903110a18051509040f020112062103030209031e010501090c1b080d0911010f110a0305130f030515011a0d0b0d02 67
    0x1800c2c40d9524600030701c1c20340c0c4403160003562068101c0f078005000000b160745e074031210740080e40000d100d20741000f0309101384805183d03003100c2c035841a04240c60b07581d185e40c114104542c14810000000d4031588405105012103400c219a0200080c0319650219031070b128419102c1c202c1e5aa42e50b101d401141400811043c4034641c44c00c0d400302c9000380c0325004188080701200b070a652080c015203007025020300200d070719850302007841d0000501900e0014207183c000c00000c0d060203003a4803411394030009840c0501c1c0e03200080c4280c900501d04c071f901c200721120005e1405003031143c160009040d030406002c900c1091004c544112441e000c000c9100b0040c20ac03072468010100c10084083c030380000c20740d220310705405006088ac24007141d11040208140c0360503903022107041d0302640642075442c5480500003446410a194500903500c00c0c0c0c0600401c29800500b0385002d00140c0c003460802d409074001c0e2000764840800c0720805040c103000403c003410040d0101b180c40024443c029001207200203040000700c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 870498741 1250 870497491 870497531
    0x1406030405100510180207020d02060d1b0f121404150204080303010b0415020604050303060f1503042402030705041203021905010b01121416170103201021060504 71
    0x61982c2d10b4140c0308405c80c400c0c124005c0410080d0030820040e10080035241420160021401c442c9022841e130030003294129000e00b9031441c01c800306000328071542c100b81d00a50f01d18100c0e03017000400c1002d495040c81221a45a000e00044c01320400310046031100566601200c1c054030361101100d5403540e440e80c0048056001d4411810540340958140c01c40ca071020841c24040c0350000d0055095841c0c82c000c0040d80080903003241d5000b88400c681201071000c50024611490260380491080c0007141c0c00710a0000c01c0800003030340796104108200800f5085003d9a055400400d81c4c41042d6800e49010382c80c0030398002a54010300c1d5840390600411005400908a4080a030703200c007900e0340d2810803442524090100110000700c4071000600b01d00712100600c003c503140e0710b00720500e098480c5141c2451802a0001d8030070440210300054143c0040003408c5508d0f0098581000b9401c030b148006204078941c0781005070089400e0300e50b00d01000c8982120014100041c0b042020307000c1c424250300114 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 870499991 1250 870498741 870498749
    0x3070c06050a271e17011505120319030b0618151612030b13020c160e0703050a020c01140103020f1c0305030408250b0108071406030405100510 63
    0x102140240001210f02160081d5107040f054200078a603030030444a0111580c4000f078260782000d140e080040c0c0130400c0110410f40404c490000203501c1e03003e6801380034141c0540c00a40c007410000d40741000100000007243d5000b92400c01144a0001c44542100079040c0040f110b5401140410103141c1e07044107614180c0807100407544085e03100001b9030348c00400e01540324520785665089041c0710104504e988001044460b40c50005900340c070b6500055410030411711090b15599010480f81d00c0705404100c00e0200d050700d01c00007003270945400242e451412000744142d0130141c94001141560600fa0103031420030364014001e12800300c60074201c01d011a001d01c816881000d505000200f00d0800d0404840038014414a04040001544007950598006442102c40000070044c40040381615500d82240c2c441c2c80382d01d642d121540e800c0a0380c85401c10b802c5092141c0103c401000600c00d50f10a201c0019800c3d14010b89a41d1141010350521500e055088402c41c00c2c0700c01c00c280440342401280a503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 870501241 1250 870499991 870499997
    0x1031407111506010504090b0a1203050c0c06040b0d090c05031e070b03071e050d050c0306042406141c1b0215011a0d0c11010b0103090c12030203070c06050a 69
    0x2031418040410702d0509490f824003181c01080188610741554008100180025044054803566500c5135089410030100a4000480c0456006101c10303007800340c01c58011003205d40d9400c1c81c0c24003203c91243d210360008ac1100b9941c4800e240c00f0010846886001048004c1c00d48030081181b9aa2034080b04414400c00703482c0c01040301c00b10b0200c04141c2076034007aa0740760b560200005540505413001303912145c2081e050240501c1070352040a0203000d5503100b0100d0403403540e02c03801e01206000c252925100704285110546550303040110a0015901c2107031110b00d441d52040680d0706030000d50b4411004007802400c21a941020340b603902e034001d01207814190b40b07a4084805242d0003261281079039442d02c1c4d040d91034400100f022042c5403640c3c8c8000a2440c00c01483c103001c0500e4079007140d1401c13401e1000704d409807140e00c008100c2032041d0466008203003010300926095685000520740707a8014209105d040c41d0f010b40616108105903034405034089503400506840c0d140242c05504001107074000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 870502491 1250 870501241 870501253
    0x912120c030608070605031017011a061c02090d1a100f0e16140c010c120b0a15050f0c06040213091e0206130e0a380103140711 56
    0x20992092061034201c0e8440c5000d0900c0c5030511108546030747c0042e25240043d0350030040801e111035905c2d001040d185005000040803221100c100e443d207100708817040d106900920641100001000c0441012080744d10016035400c44000069441c2c1c100f01c102801071003028403c05210021500328034003c0c40041e0b02038880da5520550751001e42400d02680100c4207070f21021a50426a0b040710002446460420060030381c03940781c01d01c02580044461140706c0c0c1d103c0d040c10307001c240c206c4031000421f00855424020062000045809050503200c0d5031180c480500070864010f00c40c45c1501c044480c00b01c940c666410a5002d001e544403416102039114041340300e64408440f8542c843d039110f41e580a0f0034080c604582207510180024107a1040ea00400100320780c0c0700242d0000002d00240c0f0711101c0410703041c100003003450216100b61350640211504100f04480800561041910006a800e513442429001c0b00c0100c000e00754143d4001010203519003030142d515049140009807000f10421924 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 870503597 1106 870502491 870502511
    0x807061a0d1506060305130f06090803090a0303050f100302040504050f0d0306090501050d020f06030c160609060c08041e02060f0c0313140f010302090301091212 71
    0x1a201d00b00c50746021180468480d102c0507060b02d142c108030511b80703418400a09001540090b103501c100a254004010060b080701c081c05600103680c580f281801d11007559100c107503210440102c0d00303100c002402c00946040e02e500c10840128002880c0f46550248001000081c1040d542c6004046900c080410b00300200c2804071403590f8006661440c140c05182100c40c1038200700d01c212410140352000da6298941e0a602480480381320380c2c2d03912016180a554401c0f440c0e1f41144070040103103042170001d9030340011860742c06100207100c4800c003540d0850742034070111030060210707400035181c07810050000c02e851074052003d4155440d040c110340c0c4005c5160089141c40e8102d910028940c0d00d00fa034501680b07001484c590000000891003c000120400c924007500341c100340d40410b6504240d0303400d410030600c2a4020801054007000d5800007009105010388075802c1a04003142c440e = true := by decide +kernel

theorem cover : BRFrame.Cov 870323741 870503597 := by
  have h0 := BRFrame.cov_init 870323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 870323741 ≤ n) (h2 : n < 870503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
