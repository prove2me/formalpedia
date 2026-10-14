-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1464
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:07:02.768045+00:00
-- url     : https://prove2.me/submissions/fc49846c-70d2-48a6-a39c-8fdb3e8c98a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 263129496 ≤ n < 263309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 263130746 1250 263129496 263129501
    0x90711060103062d2903100509070302030601060203030405100203190c021614030f0303070219151a040b010201060e0a0b1809030a2c010804030c0c06020303090d03110d 74
    0x1c00c4c44801c01c0062690785040443c002203e4a4004440e540ea044e041e050b044210803c03c5202c100255540c002c441c0c07410000395038400680014420680d5400810742501082042000030f540c00303000c0d9861036030340702800b07500ca8204580c00d45090080d501301d00907481d070038800c0b2403040e0b101c0c85c0f214501c00c65580c0203d0040810864000944c0b0981050303a1507004081c04081c01089100b80002c1d100c2404001c0c581091045049405c140e841841807105103034022801200c80b0080690303107034008070a814030300c14180404030079050240c074052412440696511020f0702c3c4000c10789040c00a0000b8100481c226403451140040404522020a6404409401c00c010005005260f0341020050001c800303c2d4000503965140164000070789401d2940c0c21116414501c104543d0a501012a540c44803454200c00030150b410048070b0b40020f400c1600840d139240d07041d07800841d40d2400d00d03180c0402075901e9000b0703070381b1001d80d20606940c40001d6100e4042e250448200101c02c2e410030f054050700802 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 263131996 1250 263130746 263130761
    0xb130203041a01030c0602070e04080f0309120706021908070207090e0a02060f09030c0d0b0106050307051603030504020111070b091e090930030601080a022709071106010306 76
    0x222516a9203a91160850781c410b828040c44c0030310b2440d40028500340d8080e00e41440744c0d020b030751100034500c00c02c40440c0100060b2034140042090140d903070f0390742400340c0d41410141c1050480484021030581d091180c0c40c0d0140070034400c0e40d070803098900503401d0244d600407000ca50040c010fa00c00c0c81e090224026582102c004541800304444103c10140c0c00258160410800726401810110b82c1c45090301d02048602c0b680002603400316100c00303440d111910000d00c140207640500500002150304580715404691128940c000c2c04100408903103001030160400340c0e016400075041d500380400024002c1180c1041318041d102e500d1402c040301d17050015010a45500c4403548049040c00c0841d910340c03403515880740d094070000e45541d06079500001c3e50403c903480c900d440c1180c100452050359044400f202d820541c01d0a050036183d44168600021b80300b04840914900943c0e145015403490780062100008012103404815589070035080b0756007907a0072013117015a070200c801000410200c1d8482803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 263133246 1250 263131996 263132003
    0x90c08062d0a080f06161e14030406150b0a0207140a0302061309051b0301420305061f0f020a12050c010b01020705060307030e1f0c020d030b13020304 66
    0x8640d0003010002030144102507100c02c0151300b180c0d4015007095030a1106641c007545481d6a070801024880e0003c050500030800700e1040d0318168401d40700d07180503a80944c2c1044104120316984d281a00d4150090144000349070441c5d40108008075104290300300b65240f049455000f401018546154016101aa0314415812071040000800503895010042014221a10103181c0c0c55150118404c100e40005240b4006406d54100801d065041c134802c50b8111101e5019140054008191200346d40001010070716040c098030303036150f013050080400905c1018058030104815640ea07800c1c00746e00200007800401024880310700743c4a9600504403420004018412100451202e0b41c0c2c01c0c079a103100c4c0c03018001007540402c46440c4140c0034050707444141c00a1015001e030620703013404138000e030002801d004141901c8420110007980304001002101501d0380000c00c00e20100003000d0000c0840b608004014040c00c1c1d200042d180c000d018002140c88041c004410401c0340d920321800a410181048 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 263134496 1250 263133246 263133319
    0x5030606070c09140702061506040b030612011a030709050f04030c0f0606060306030210032306030a050304031109090318011803020d0b16031116030509030303010f090c0806 76
    0x8261103c440c031a00d009040407001c985240c0c01d100c900070749441801010002c0d1003184110000094a440040e10f0446e40402d50294407600d0709000608202c580780780404c4079618040c14041e66003002250040d4901c006c1d0142d8000b41c3d201e26942e010344500300d42c0e003141d800010700494006849141c02c05c525500410811060400301c0e50340340142c45181d440b0100003600c40b0780500075450820a142080d0300da5082c10050405111f940c6802d2406010006006e44035102c0021035686041c072208400f180d0000583c1c1e61241c6a01e440b000140c1d1800c042801103501100084100308000210792803c42c1072168040b0010032400115001e07100c0411884903000005c81c00401616503003519551503100b0004a0890b19012040c2c2806d0345282d180141050706214841c951404606c046032070070702142381807010040040c20151690304c03503a0314450f0184400000020808940c10b88003099800c0e0b10814042c51440d030004403180f50064601551140e1058424003448150a81d030340340444255504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 263135746 1250 263134496 263134499
    0x1a0703020717070e060906130c0e0a1e0906120b1e090c03010b06090f011419090f080105040b070302180a1d09060103050a0305130504050c070506060f0105030606070c 73
    0x560410b5581c61150031050344044014882034501e611510b612420684d00c90b03080c0d1810000240d41403c0c8444201c41c220ba07510001a44240f181408004611020713000c4914190380d48170711021084d12a00481001c61802004a070504050103040c0c212007040c1031030002e20006840b4000340c2c1c9801303003600b0507401d4000300c1000703040c0825059910490114002c6e1000c2c80100040c142034032142c01a080c4100000c02c07030184940d0760040341d03540104080c6000d025801503548103003014450072600c0c074605001c6004e8016415445003040c4195525140c10307200c02c5039240d1405091b900160760062584d02c071507000a461600c2940604503500b07440a6030014104104007090030410079810495015050196600e903d458001100e0b8010040800030030507503266803180c50300e03070340743e03030001010403d001440041000300783c0c0c0b03518041d03d401001000241010080241e05a001c1e000072034103405100001809d614041d8514070035080107845e07003803859807002c04115590b031240008807401c080e001c80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 263136996 1250 263135746 263135759
    0xa0204030f0303051905091f02070203030c0604021302120f06010c150203010603060518040f03051908010303090e06010c1514040b06030c06250c1203021005090102041a07030207 78
    0x49400d29030094900003245d082c0180c90396640400c5995900b9040d0401040c001c20080004041000f0070407080303140c007074105051007000a44500c480107035142c800401c03085d05844000c2040c90045208603225010b220520308000207070300030703030740d0b40e840b1814500002860044411040d9503c181305242140c9411803690340c0c540d402030710310302500d80594040b0050114540600c55000507040803078440402d0103500c602d020742020001e000518944074036888a04150160303042c3c030300240180200111000d4680c03c0105101c0c030074070041e40050380c0443c000843d100001c0c900c0d4092070741039480394070000030303511041030086884401703001403a52806110030401030b005405004601ca012150340e28140f00041510f4190035124651048408200010301074407002c81e0600b2941011110440040080c1443c1e110404291700800065000a4204040550102d00303100400b80162040105485400c0294202c0c0947d0242244004a03142000855418180a040c20328820f204944c0304a44030b41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 263138246 1250 263136996 263137013
    0x7110d050607030c021b03070b0708040b0d091e02100809030c0708010204140103050907090f020403080705011e0612061d07060906170402060702090702011409030a021e150a020403 79
    0x2601100003035510040808802d1781480520f0f07005291110a46155400304000b98403004248980325005000003119010018210240e40040081c0e00d02c85403101050501c0501034405000110b8240e42181002d120b410380d0040c200c0143c64010b406608031256080042d51001c501405407900c0e80f106004408004400b0024000a8121503001580f00c92400540d6400003a4202a240c14141002c08008190500103505c800b1100e0744800440c0741c0b20340507040380092240303401c06804003800088130405e004054000d90100d142800d010103d0005070080c00d0101e0700d81d8001c002104400c1d10b0910042030240d0031880360200030006410041c5030821009240800d29400b21001c10040e0f28104520368011441c8128009071000c1030b001403500c1c1e4000380c5035120748007000b40701b01c10b01c0c40881d143c40d200b50300903520302c3c0c8594915601d5081c461030080d5207400108148005100d804149400c144c43e2805441d00c0c3c5410a000785a594081081c84001070b40050482103034035070903c8004040f942d4803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 263139496 1250 263138246 263138251
    0x5090c041506021011190509030a0f02090a0506060f0a030b040c0c050706020d0519030f09030905040c020f12030402010212120a061e090216020a080c040c0f0507110d0506 75
    0x4041c00403968030700031001e03042c41002448800050f250000c20039422020a084450b03c00e8805801d0340ca5207810b05040d2050301a5018403601881426008000c01a01c4a41107107658000c0780c0c100d2642c0c0c2c0346e000590658004032022900404103000e0408100d424001401d06001503040200c0c0c00c3c40758030003140c203e4104081ea40000381035405c82c0b60902c1428000769000c2d00d030740d1018144416079140d014110b0701c9000500c101c0850207401940c1e100c1c0c1300c3d52104e4244a06d40c20184802c00315414014030403a640d00a0901c910310b400c2105050078000100032900f0304008010340103018200040130469000100700380c0c10750041d8230400390050190f400501d04440307a0070615000342020a92a000c444807074200b4158002c030203000d40d110100d04905401150880b00000da41c840c0c01707140e42a42e03400f450b00000d4226003010701c007042000c00843c03800307a6400250303004c101c1d54600000884100010038143c0b80400d00402010020605141003c04805000382003e2182080b654990786807081c01c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 263140746 1250 263139496 263139521
    0xe04180f021e1237230f07090c0c0320010e0a050a051c0e091909050a02280909020102070e070215010e06180a09050102070b010f0f031505090c04 64
    0x4040700034841540c985107900e000408080248882900c0040704d007048075001c101030195150400ca000488441004841a82c0b01213406d845460560700c0c105541c07886203000fa40080d5090002040c06180310b07040c1d4442e565056911203812030304407820b0b44184038400202000075500c43c803504101800401c408016540701e0001811641407500782075081881c0c4c2e03480034070076100c041581195680e00c4010500040412604140035440c3c031000c3c030302c1041e42c0c1940348990500b0032104005206000c1203004030700c0e0003582e900e81c0e0540b0280041d40007261480d0080c112040140b81441050110350000b00c60038818012030307120640300c031000d00c008402114040b0040c5d0200e0b40c03080180001c001c0460040c40741c61500011810030f88009030102a01c840303400c105000040c0020003100041d0085070480d034006008555810282c10508903800090041686925a10b000000c030700049035042401c59030845e850005800680e0f08041c050580903010121620072120030390001e030344504c03605030107210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 263141996 1250 263140746 263140753
    0x6060807140405040c0509070c122c0108013b04110130140705070b0108060c090103180c090203012c040f03020304090207030e04180f021e12 62
    0x24041c1000030341424506070030b000b5400c0800303000005400d00941000d864003216649180da43d107540403905519076005c050031100304440040d4166402c1801c03002580440080d1659911044802c40d001c001100505400510030900420a400c10310450300f039030150740040e1141d21302141500e01c940210110206000300c3c81c00c03090104000c035101d40e1450104003820b000300380e05c44000c02020104180b08401d2011501c02c02c070b052000c1a41c4e4082d0b08034104980985007107042c03a81d0020526013140c1c40840d41080f142002081408c8001400d52040e181e00074030300d142501d03050045000d805859141c4103110001880c0c4c000003410701c102c29018024082c4016100d600d818950005105a040400e60350081ea082501071b8400c1c40d13034002d40c040d420041045009080d491704910318401c6a003e01c80c02440803511200301135010030554111501102c050050f01140303980d8600b0b98505c410002c0000002a050100508200f400031031a20590450b9410a1003440c0103d484820400901c049642 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 263143246 1250 263141996 263141999
    0xf02060d0c18050f131d0102040b0d050f2a09061c05150108010b0f040e040c090c0e061e13060302130b040f030f020d0804030f020102070803130b030a0906060807 71
    0x10003410070800140f8044401119500c07900c0302050090116450a01d03007a0389880000000950060120400851385402103684a030b4039900002c07a500250030240301c403400c01011940c2c0d20074107a82d09015040c241450311203c1004c41c840640904020b01020414405200b003860365038418025007800340c00c05840030400740000e031404003150b03001000400c81c0600c0d020002490b0342e012a80c01c1c10f5030606003001d82d4414082c268019207020399070100b500013220710100420407804003203401c2101c8060f0418070044809040666800c515004c039140c0110b001e0080d41c900c50240f0408080084084200c54074010468509184102170b42d08950046034001517a1024076010004500080441d411f0180c1428240031502c00801d46620001e400600200c1078041917640c1d640d0b8000304d4030340c40b1003001d40e100e0744e9280c17055210000b120306134054001e8003000504418080129444020a660407100322410300720f4045031600060b02d0710070003039610448840054464401d07400540020f500409030035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 263144496 1250 263143246 263143277
    0x100606020313080d0e0d05071a0c0f01051504020a03090203061f090605060a050a090902031510020a0b13050705040e210705060402011b0605070f0e03010e06040f02060d0c 75
    0x1d034450700a0354442101c080c1100e03800100c440105e01c040f90700031400d07030850520783e1811b01c40e604180d00c810503403040500c00280a0f00242880031480c410394012458840c0d41c14201c6404440c80e5041310b2a01c080642c0624080e03000f0420032195040001c3c1a8001d500170070716050b02103865103141c21042d00101d070710464070320007800140401c4500380901800c100c0030980c42e000b5008184280000411400b00680c01590000090b1046c03400031034482c504101004021006450540d00a0381c61307402c801c20f1a071010451040d120340010207484540c90303201c1c0a401c201100941680c0b28081d488006c503140c0c1c0d4034069801e00c00718a000030312040b454101140d540740024103080c41001e0081000000181d4003082c06984190242004c45110545203102c041c00c5440910003000280303058100603c850300030444085c111101d64480030a01010303801e150807a020801c2a4055510840000d00041c12450210b03980a102406950600d5403003602401614101820b42005c02c401c202520f40c003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 263145746 1250 263144496 263144527
    0x50f030306180606090405041e060902040e15060915120303010501030b01020613110f040c1206061805060c030f0412050c0d030e010f020f0d030504020f0d02011b0201021006060203 79
    0x3000080c00c0d0240c16040080004140d8814607419602035a00c7d10300180034010740c00080d010460015030804903501c65840d00900034201d602040388220f185c00c81444080d41c00180040109122114203103494440d1380401600d0000103041c010442042140c06c402525141c203603800b1418480c00441c0c0f00c0d4140000034040d15181181681158860010450001d17866000008000e0f04100c16a00c10b490740004a41c01c100d0382c10040360003605240c030900748141d104130305044001d4281d0081103c0c036141c1c0001c0382d909041035549400d40c07298440134003142c07801c44000c0441072100411245444200c0100c030b03480340c00683c0450480102c421484040c000140702403002408201c2c0c200c850160565800b0303002c042202040c40c100b290000715a9901c41c02040302d0b5400980c8501228803441ca410402000f400080301c04a0180e803a540d250b00c0d60382460f0140300856a4161102d0010140c80d80080103015101d10f81a4110700c503e03c403550b9409a2485281c2c05042c00c1c0e409940d8030780d1000c02c1940c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 263146996 1250 263145746 263145769
    0xf080606060324010c0b0c0309010f0b030304060513030c080a03080603012306030703150f061401050f1e040b0304020910080d2102160201350c07050f030306 69
    0x80320704104022481009500c041d5010040354218124620030100480740c0b1804e4040c001c000200c1c1d202805074548064010310300c16040d100013402208100b11184040d2202c500342240c059000307001c180180e038024070181c0f4000d0490b2004d10355403541c07610340580f80801c503880109150447c5400d08241a0701280d21540143d094000740500d006243c08003200444151882e46840459000b04040307580a1180100541d08041926034030f400d88400e200081101c0000c0c10020b618142e80024054001c0710f6002c0696416140c1d0b6080c0107544124034019070201c1038003180352544820066100d01031a020b80080c14503039607030302c3d01c0c4d1410f44144180b101002d0040c0004001e082d0007001041c20000d401c0000a10524203050b02045019070301d601e450440c150048010b0010070120500340c1d03c2550340b25231500036a20400c1c141511504181200d400030300300c20340103460000032280d99515014464000610004040c40c000090b124103003800310083c1c4048040e007001040c001e0b1468a4000303040c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 263148246 1250 263146996 263146999
    0x30a060f061409060703021504060e010c080105060403230109080712080f06040b0f030a0b10051e06130b180111070b180109030f0f0308150907030e070f0f080606 71
    0x500b0800c1a40748030720b050249203183c13445400c0000b9031104141c17091000501086500303030443c9081c18685403078000b8190ba10540b0000350f01c0c0c1002c802c50b080c452101d0a04079140605810b241030309544a00540c42d02500c0b0b213003550141c002c40c1d43d00c1c01900344580801c59002d0708909c0d48039002403501d5140c404881071004208030b003803414080c0a2800070740d4150414401c842c00100f03070b0318903004110304004034003070300c4d5240c0500d820801c1440395482000e0302c0b84454185461406d40c07500f0401c8842d030b240d403054010030900500110700780e081c92401018691f20115804141d02e0796015080c00c65484040e0401030322200c10346030401542c121b03242c042628100350150854a05103540314015000ba441c1c1c901c4403040f01016800a40d02620101010b5a000565000115100d0502a016a5a002c000c6000a41d00000074444c02068118000c810b030000b40380700f001e6290074030304401500030b07182c0c0d15a82d40502c1724001840c0c4400040340c0c0080c4a101e40340100c952920702414204903005007010b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 263149496 1250 263148246 263148257
    0x140106120501060f23360103050606041b08091c0315230108130203010509061803190809070f060903031806020d08092404050c011706040c0311030a060f06 68
    0x10054400c14241e9400442400e40e1b0001555182600c107007140d900301070700c0041900d40102c20010b0a20702050680c1640d0084044547d180c81da1024081180e96401c01c003c40c000d881d015034030b51b00744680010750304510900110381e41122400e4142c1002402c103521030700440e658941c1e40c1013425206603040001c2014488041c1c2d90b0780800a80c001e101101003003141000b00220025050200305228018211b8005e0000c001c54a0114989951500190786d20300d0640030320f10401c0d001c100000100d5401840041d000404510902c9040d1450103025101404501440201060180c16003459030f00600c842e40d11440d549103541009008860440c044c000140302d16002400b14980000748400c0407545071910030b219a031903480d41e50410030046556002c981303061643c0c0e86100c00d00340015005034015810307140321450400054480e0818010350910b80003405000404034a040c0c0e00445182c00036080c0495001604003d0003600e0b4800c803070083ca05a40c404007032041808802c9c1c00303400383c222801c10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 263150746 1250 263149496 263149529
    0x30e07050604060f111204060206011205071829010f0c08040b0f0418060e010506030609010603020c010207051f050f0c27030318040f1107140106120501060f 69
    0x1c1071461046018540602560076038a0800c0b40c401c10500c900c1d601da007025100b04050030320001b5200d6200d80b040720f005202c1c2100104130743c00c2e01034884090960100040403101d15165010003a404030312510441966600040061481c0606412021800300348024036070b220090005040012040d000c0400c200c0c01c00054000540c0d07142c00c4400341c440325070025440f60706100300e5a00611458001c18407000d860400b84140d40191341054040d00d00d6842c10300707026a00c0300103000d02c03030004584c000e074080400d000401045001ea40102070000801c1c00142c9414131030307290b45240010f00300e80c6a40305507100f0b0f02194080864030580303410000751541c07810281002c05c4d4407138040c01500f0784c44080060303000342c0f400031503008100c07082c81800160a030380d15500c800c420264210340120803d805582088801c996000c483c1c8900480c000058440a090a001d600d81c00108145440d000c856503507180c202041540001e00c81da2080c034428000810800d00b0000100084003280d84000141000102c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 263151996 1250 263150746 263150749
    0x20d1b0f0801030609140a151a0f0f060405030a050c1207050d0312090606090519060b121017060405072312011508070509130305071b0302030102120403030e0705 71
    0x807181101d82041c804180c0700200e060400c00030981201c0e41c1020701c01c0c02030032000c00041c280d081500c45506d40e010090610100411100111005d040690240c4108032080e41450141004400c01502a01d204e0405071541c01103841c03c04158003e0710b01ea0b01262040c40d252500909042c160f401d0080900052464140441c0c540141c61000030140400e004001e01c140c1c0541c2e1006940a410403030070b01031b0035030b503983d42c20041105035111540b0017500c46094a1020b000e0141000321418844143c1c54403400c03442c40d0805010180c0f904034503145044000995501d07480d41c01510881c05005400703107060910b0705518003261980851200550005030801c03402407803144030100c00302522a52003440b40c1c1a802e0380149400c01e031f0051607280031a03021842d42000109001940d10940d007102e050b460301c6a400202480000380103001034410010140080c0048498116800c940140c4c4d4000f0b5403a58000307400d9801a00030742c2e0850108004100500d40c7c103008100c00b40f48118007a0203072a04100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 263153246 1250 263151996 263152007
    0x30309011202090603010e06010f020601060206070e06070b1e011e0603020a02010b030708071a0f09040e0a0c0902030a3b0a0b0f04060b0a120303050a060306020d1b0f 73
    0x24400d040c0211240021000000d41c1c0440c0d0304000d0003006240c0d60340e150b8103014080c090503600d00340003c01c0700d80754000c02400040c00606030766068000304019510154110b403007980f4403a02032b40183c1c080c081c0c1c8000070000310303030103004040d1820000d840850b0100e402401e076a0581c0a18405100881c50341110310589150001b41c8100d4030b40540c1d52500b0510503805004903800a43d0588140d00000a040001003042410b9441034000c0d0344400d00082c507401118040d01c00c09141001c3d00b04504680c0c1d14003980b10040b40c0030214140c2d04002019180c8801c1c0d004240d2105002e1a00041000640010391003140c000c448000d5024a050802000c0111401d18101d43c95890700d00701941c501420808101101c580c503441190b5808501e01040d040c43e41d054151022141d890820785541d1302840c2c04c04c02705d01a03c007103c0c014180040d564400b100075001c080d1916040340c0e030b41c080100105846000811459a00c0c5c3e6010403a6440b1039800050425441d100708204400d5010513240c05070b001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 263154496 1250 263153246 263153257
    0x302090c0c010e150a0c211a0301140105120109050607030501080c0604080307030c0804050409150506010206060616031404091a0402030c040b07080918040b15060301060302030901061a070b01140303 87
    0x742e4121b0490140c90ba0405031210002080112203800b007148082d0b0403241c004000211b07800f02160100303090500781c9000b00301d2510500c04900051005040c00c1c0121003090007004004540b0035a25250f05040090030b80b20721002075101d40c010300c14498104000c45120000755281460585070000c0a0b8036030241e000300900704040d1a07610030500c0400000e0720082e080090042019030140e01d0b207140070107c1920381019541c10b00000070b0b051342c0041b40c02d0344201809041c41d450030f90f1162a400d084944800100d0920020f0365000c07003070f0254540a0f1001e041c01880c00204805640c1c0c40d188081e100d185414890790040041004004500e01a82c040320b0710071828a4a0380c0d103030301c0e0400c02401a10b0285070884080ba1a030002c5003962500180118010a0350006a0f00d4850620002e101e0712900369401c408104010420103201e07500071540911b400000003591512016546071190700d8442c07685032032601013280000c0c000310b00356150061066141d03044808a82a0100f5201d0184 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 263155746 1250 263154496 263154511
    0x1b161a030702010f0c03060501090510020a0f0609060603030504051806151602040207080918011401052a010c0e01020a020a030b10030c0b0d06080604050618070302090c0c010e15 78
    0x8404101c0c024000d401c0150500a980c3c03007800904070412004000b00000d00c5018009059a680001c460400660041a003a00c07075002d0500c84100c0d46868418030074070941220019aa00c0843e40850082d2050307801030b512942e5400c1d41d461070101000b20f500010303415104684950001d100700f9035618441c11145544146005440300641e02c0764007650391803020080d4000c5c5c00042e0860401c0004030003088070103822211468420009070f582c500a00090203400c10a0007015910240c1d0f600620140c00880c850b103044500c0a008607180700804801e04078040e890380e444002a401c1a5046041605c01e81403e1000f89590815034000070125885840b0241a00207140045400c0400c5003000d20069a042549162500d0b610020100544d000701c4083e050b0358900032010030b40c200041107c0b4021501725000b0005a29884004041b5031a240e40c0f280042c42030140010052311034410071441403408030740d40e50b02c0309079207040b450a5800e4045840c40f00d400c5245407010181d003c0e50341c0342d0420711 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 263156996 1250 263155746 263155799
    0x50606180919060902040302150403110405150409150e0a1a0a02090a060f0e0607030507060b0a150e0f0303031e070c020d120e012a02151b16 62
    0x240c04000b0199940d01c6500c0e2000a4202003002c1100819500280103c034401ea40c003440081c8412282d240354011400014807403542010102c4d054549030300082d4010301216200711500c02044009001c4400a0070100d42c4450705807606240aa9148220346078020501d0241012540665a00690041e0303520030590011031900800e04032a02c0b541515580d110103068003001070744800000d0f00d6480c3c14480302000801e800503d241a00b002010b41301070941c15100c246c141800790742c840001d070000041464102c44140e00005400d4031782040441c00c80210740f1540390b0902c1100610134482503c21416000c4da2041061040c0000388070402c02d2a042c09044000c8a902c2c0c0c076008454000003400042c2d03001405440c04c10902c0010000d460000440788c40c0e4042200060005441d010145502c002c0e2418500100d026074124058103403c189100401c2c2d1200d01c016a541c05490307421010504404d103144451005204004100c850b604101c0031a24040300381c07030030038000e10b800b2244440503592031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 263158246 1250 263156996 263157001
    0x2c040e06070509131d15010b181c06051f08030301080a02010f110304060305011e050f12030f070803010312020109080a0f180b09030c121009080f03010e04060506061809 74
    0x41441e1700c511400c202100d4291104240c00d0003181e56040d032680b0780c01d24009201c0001500400320f600300c40c2e465549034240c20780c03810740f07104000041030f41e000940c0e1441c0c0541707189000251140720711032140c101d0341045803c00d9241c0805150b5000190443c0c40304d40c1c800c100500c400304001404aa00307a031b09207810035400e0214a002c80d0a60382511030310321944400701e40490225019040103050f181c401600d03020710301d418500e41040040c07038812544c00903003084c0d80503500d05080d2242420604082e044070b01c4e0480d030704e008800c561b01c98801914101c202000502c20403c40c0d40e0010340005051000340311502898580502c03a02c10040c5440501584c00c1c080801135000d1009452016000001c0100d1181e41e05003030700c04c4ac0e005406680c42402051405415868440c600c4001c016186001b010030710001014000204242402a200940d0030710030900c41d2508080110b001c3d00d00c1203050865814107191101c259800580998070442052112a000030866107200711703841c01c12070b200790494 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 263159496 1250 263158246 263158279
    0x50402060d020403030c02010e040c1e1107091a03150a020904060e1005040612080f030a18030201060e070518210712050d020703080d0203072c040e06070509 69
    0x5200703042055030624008a000411306801204c0b40c2d1645000780c80318034544150200b00000c644440e843e40c40414070781e2407090740a080030381100400f030b03401d814090300120540103190700e0a042ca6214504c5180c0394641e2250036101c2c12304401403028140c1c01000074500b00c080c0703036a1f400300041091441603404980c1c0d10596646400c0754000344000509252641803110414107c41100d00070540182e051030300004e95441050044176103160005030960a01d5100d0600740300b1030b03002810031f915181e291640c4161210b0b490300e00c508098403e0300000740a074542a03015015003002022042404010f00c400303003100e006c2480740d890b407100460300d4504a0000080b020300011400041400074032450320081031060304900802c00340c5004104440740340c4410202241e44070300500005092807020302405007114595000745400c00e0b05820309140c00500703048280071070fa005030085075074461900410f00c0300b4102072007140d83c0010307410058149480d01caa0003400340e00c10f5140b118050f121994955501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 263160746 1250 263159496 263159509
    0xe03030708030a0902100e060715090b0c0414030d050f03061909020414030325030c0f0b0a05060f0a050f010311040803030613050405120708070c0f080d08010302030c04050402 77
    0x100c0d58042100d6403a4244100440001c14144c0b100324002d0801c2041105154024000158080f41c02010b042c6012000d036141722566446400011409032100310030303000141d00e981451b01c280c0010184a441d2443c1071500c2c5201c1c4440390504d030198010840c18215558004210398455100d60301059880c3ca807200410306503540040b40c0da02c4150320300030200303000c00300707400170411984131100320002e401c0c1107010140c0b20304c12144900000c0c609031a031a20751000111140741140d0203401c0c625545412034407019000c1d661140115144804001013144603145845056008036040c0c0d03092046100e1600810610310040c091a440307210b5400c2c090410b6880b9410420300b1400c2d048a0300e440c1c550b544074039903980d0025545648148a55088041804207900c0341520613a0850000c2054000d110b090240c0c652000509480300c160400080c1c000c0350b0444c100a008101609400303c200f4544086a41840b0640d80804104a800b20040005d650002400c02101c0c0044400003856191071000480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 263161996 1250 263160746 263160757
    0x20f09030a05010b0102121c05090f03120403080c0a021e03070804030605070906050c0a060c121b200618210304060617030318190c0f0618060e0303 65
    0x40c18801c10300300008000b01904110708a41d8203030212400214141d000c211036000e203a45108481240200019152500d50405504001842c0903980c41e0001402d0365400c41c2e000d0600b07101e801c1d1a40043c04201a03000341282d90040c8500681810000b40da0002500d943c44051540486080a16001002241441154a040d03805031115580c0c0ba643e01d040b0019000890b1020040b0301c1c0c0c00e20005074a0300620480c0c8402031858041c25107130040e551032034000c003051030b4600204100550140c1e010082441081c072031040c0c1c107000291650408400504c1d03415031400c10094080c0103d4040054180020040d0b00300084a881c800000c0c0c000c0029450030004030100045900c0084114402c6c40d02c0c80011030003140280014050f541c1c43e02c3c21002c4058003280300c0e00300f41c0e0003000000c00d80a8207000d00e0002e03191840507600c42d042c5111100c003003120305150540c1d203800601d000300035554803202840c00815007414590b04528a4003829403920100c1d11500d0309002007030300c41159035503003401142d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 263163246 1250 263161996 263161999
    0xe070807020c0a0602010e10110a0518090c12090d0905040b062208060a0b010801140103150810050a0c08010b070c092d0603081b0f0616020706030c12020f09 69
    0x50b03c06603960030090103041c0002c0c009900b03006038880c16420b280c0500401d840301c29540b003030b030740b5100045600312072903032020040700b8084030070030384c408516a2054500c40c000d514808103035407640c0300ba04418150040140160106a0025201109181c1c00150080881d40f00301d40000794400b41070080340561289200e07680c0524205c0b0b0306c0a0034540c842d1125429202800101c580d6603031030241500880e14458001e5012550070340041000c06d00e80c481d4643d803154103140100c0c2202d00a9001d20800034103130460b110a410039032121280c2d40c8603225041d408a22000140015140324402824850041c0503080e04031400181440c01e104983c0d41100c000e298600f81044440c0c1e803011720340d521303c0040201800151465154840030f0426000c0c201c240d9400540b200e00e4560880c01c1c0c1c07413a648540c03401c8040782c01039500320070140c1003d02c1041c0c8640320364110b1452860002034000d040c4405500008181894180750f00b071340d19800311a20709072215444c4010f0380c807181d00844005900800c2000c6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 263164496 1250 263163246 263163259
    0x1406160605090106030b1501020601090506041b02061501031509020c1510030c090207050709020913110318161a0d150e0a180609060b03070e0108070608010e070807020c 74
    0x8014034105500c2130080740d0180000e0103003502e540c100c1a95400c08001c1c5140164071080061098581a80c426504100c00802c0040c1034006a14082c8000704012400c9000d604000b0800c40421151500c4120390300d400d00c1c04010352586800ca503200b22401c1e0243c02001580455003d240200800103080c000f0003002192440d45070403583d140c003002840c007040341d1010410000081034460390098070416075010002c1d00055050095520003500031341202688880700905520307801160344168111000c881c443c2590f41d1808100361914030380150845183c6601c100031075010712004000100945045030320700c0358000c1502e2200c0708140106075480e41040e20f0044600c030f0418480d07901500b1104043d1030501c182e5110720300b600c11502c03000300000e1342c0203c1203085d4000851640c8898400ca1140c0070000f854034140e4080307403070701e1141e4010401c0c060b0140d0040c004503000300f003004014083da1800503030560421407035841101c03020b429101448081c1011502c800c1c02408048403400c03001c1c104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 263165746 1250 263164496 263164501
    0x40e0a0b121609020c03030f070e0d050601050a0b0702090a090309052205060906010f0e06040308220506040605070f020f030d1205060a05010c021302090603100608070206011406160605 81
    0x11207484880d484140c054042c5403110009400442d07000b41c2d50800300c0103028504650390360520007659030000701020100100382580195981d0392140c40002d85010f1001000658100310501c0311510f45034004580c2480e0602450300161307074048641e075000c01c5d040004078601d8010301c0d094a06080c036401450f0312501601034030403454003101206120b203c6500c002e006507242c10702407210707000d02903607a18002451001d11400b01e0340509210100001c001e4200c1c1c0c44d050752a00d803044550801c0e840070060214091a260038404885040e4002d04401c8614a10f024603202019220f071060410080040d285501c00784150342d10130f2602c100110001d4140c45155400a400a002034020421000c1140c54200821514188099640d050711410784644080c54229001c20860000032100d81d94001e402300b048400b9500c03140041c501424070011021022400c007500604812001000d071011940003500420030030400e2125405420416920944d6035140f4100a09030200241001b9084a041c4401e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 263166996 1250 263165746 263165779
    0x204050a03060506030606091012030c0b0403090501122705010f05010312090b0906090103110c01110304021e0a050609010e0d1b120302060402130e0a06150605040803040e0a0b 77
    0x303e5072040d10100c0a8450350ba4541e010889000e00544000440015a220074007025425032442112180a8105004080f41664071072440e5401118101e001404103c81007000e941c00006080c02c90080c40000e00c130b080d14052070ba0503540c0896443d00e03510400340e16980c0a202d030a43c8104054500403c05100c2c0303607168102040c2c0380c004020348400040c000d400c00070f103288e89a000d486252100520952400c00007400441c05000303401c0c0e1030550050704000307445136000c0902c141c001210103109150345078500350041001d61200a003040c46001c14950b02090282c0d1603c03210400d89800b1112039880d0001000104d4440900421061b044180c400c11a014031030006007007c1c40341a040752a0140d5900d87d03202d081102d03600e4400401580c4800c010030014901a50003074080615440002000414001000d00d00700d800942611131a0b0749080e0800151040781444029054500f03240b80b40528080360655244624410001e0421200000c80e4044100303400003104180300138900c000202c00100c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 263168246 1250 263166996 263167001
    0xc060f010503070801060b040302090406060b180316060c030804140312090d0c03080415020910050a0306050f1014040812120108150a0207140f0f160312050d0204050a0306 75
    0x80e642c0b0034480c00f80300060701001400b810b001d1321388500715141440e14560902c115914050b0048034641d032100310203d4040c8100c0e01401d54001c11060f10301c7d41c0c0a005041c14142070303001c0d00c1200d140104c0034061003d1030300070003850078032681894a005e03995580c0c1019a401000403900d030102e80400a043c0e903903280d002c91624040d49204c010f56646112a12050340c103009000c8004010401c140c1c00900400c8441c50b01500e011f00e41e0340054035240e05d600000d01004900703052315000c40d01c00b1a40c1050140e040c801da03005040251909651807503030200042d06001105900170411a0400400b519869504292802080075104a03007660400000d042c140381c1007901c0f003ca068803032000000b850100000d0251081000c10f40c00320081e160055031f10040d600c201015109082d00104130b0030186000c01806070710304406405408146488448942850540181d000d50070690340c2062000c100201000390b410449030404541d80d0180072580301c00307405164460b030740c0b000d92800000309118a03034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 263169496 1250 263168246 263168249
    0x51f03080d090503210108150601050c010e070612200315010903140705011211090d03020c0325080601081e1603051b10020a02190e1801200a0804080c060f01 69
    0x106000522687c980d1016aa5005c2d202400d03960b140006001c02c415500400003007040300c002d0320011601ca500b005119151120030380c0410000b9440d040130510380f4402e032160384250004001030b0584068000ba8414450001800008021400182a1a287c2c1c02512141c00950340002c2414941103440f007120f481e444248102d5003c1204104148150003a5205005814405c810b00303505140000083c07015884c12500102e095104034500070119690400c00c803d0070903000c0c3c0c4545020744020508c0081002c96900000a503400040184090b15010800c01f1003003c1181c500c042d0b6614110b040b07894407410501165040c001e03504048140324000c28250702207203080d41491842d0b00041d081c4500c05540e80c042c00c0050700b000b1621801850f1100c3e0065a907005194001641601e072102a020380c181a100e0340c0c2c0c107c04120000da81890280551082c1b00c030b4102001011004070350750304070341348035a010580400150000003010000f003c415540c00c848480d0403a64a440e00404c0142c0d142030a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 263170746 1250 263169496 263169547
    0x922140106060206090303040b070c020105070618110a0803040905091903050a081509071d04020c03040e07090b04180f0f0b09010e010f030b09030714030706051f03080d090503 77
    0x203600c0005c80c810030020803240100da00c440620030300d40e1703008e1045031031001000b0207d0402208203d1500480e07803d016244420016051521503100e0034601001c440451080f402e001cac1e145200c0030020a2000b009070741c21900422000b04550f521503001c0c80c04e1080c81c8129208541e5060100014141c0c8540507241c1c0c40c4854640c00da00d030311200d074998401c501c1440115406030295002402c2d07a4818044140c0d148000b254540000500c6c00005042e80c00c2286032012a07840410304000c4802007550f2550004018100203690754101340581119100e00d000b042d07103404a0a50840312600c0e01e600c0305c0201e101030f140411005640b2000c0c0d0340500300c80704404d44a440c4a174008100c0c091104075a034122101e90080000301881c44d80c550401c0400248018150b020500a203804511354990081410783d11038080c598481d500d1500c90121039018040c4050085940d0420541c0002007550b401502c0d00030035074a80312010501003c020740302510f4014070500012809042d15034020807040f518291 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 263171996 1250 263170746 263170753
    0x60f0f1d010e071e0e131a0606180414070e1e1c03050d0c11010b03010506011b050c0a090518030a020d030218041103060a1202030319120e060a0b060909221401060602 73
    0x351381f80b2032010a04250342d420b9100b8020010700f036400106281c802c4100002420116603c01c18040c02c0c107420340121340e90804213403019032031a840c1c60100803000c0160000d0507295002e44403440419403510644030130903420500107141c03c05041c02881503030322052440380c051100403450346008002c103450b501076085940c2807005d91251890103020b001d200340b4060f524540001c01302100160f0203040950299011b0040800040258403880f1882000c0c00d00990041240d060001c1410302f0f110000317110580c2d0b600300703201c0d80880f035a001c00c0b80910341c50245400350300d8444510b40d00b20280c4502d41c520743d000c0d1602c40e41d03c840c074a44001a51160404441e900c1025a841420f4802c0e80e000f00300082d40354004003c2c08100c943c402c070b00c041c094030031460528145400c03089440110b400b1000a040b480c1d03c14400c11901540c5401600103c070000d50302c0782d050034450700c01301d00c803000d01801003c42030003011020120014400041c0880b5034001090451b80807240c405c9030300034500c83c05900010300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 263173246 1250 263171996 263172023
    0xb16020a060c050c0906190902030f01080a170a11060718090b010c0803180a11040b0f0105030735090606010c0f030507060f0f1d010e071e0e13 63
    0x140180844824543c1050141c464a6501410001900002880594050304080011405100ca024810082c0c070811000507503d0410010542c100101680032000650204c1503100c009850100407d0703040b00340300e40c8203464003405d1205988500d5003000d41c0b42c03a03210b0313102000401d50380141211242c840c01400d0000c600d0b200d003007080c1a1070000316414041002548034000250b20b48004542c8229030301100c544000304504c8642c01d00624405c256005400700f911180d0600d014880d244240d102180c2c0b122050846200180030380c04020032a00c144041c1302a4a15604034030300480340340c0d40e920101c2014503c000102c405250074103650000d01486903400082565015200c0c070303c446500003a418019040300e03031b000c50b001c2d40291011a40c1e41d440f80c0100c101c00101d4000c14451f002c1c102c0002c620540307d6012900715000e1034001c080560b04003140c9503184d2401044c25010750340f181480e040d03c0148007100000098003640100c54005081040080c92240070500c104401c0c45402e00c1d0a160 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 263174496 1250 263173246 263173259
    0xc041d06010915020d050c010b030105040b220b0a020a0c02030f0318030303040f02060711090a0b010e010201090b0106360501180302090106050a18030308190608070e060a0b16020a 79
    0x10122080000140c0e11240d40c1d174a44601a0024011015084001040d00c03d504408a4256242580d00b01c50a80751a000d1202d0b00c04802818070070650726894003032885081d5140c1426552025005400c8183d000401c48900c40c07180340f000d190036030060701725024400d00d46d003070325500e07804048090b841150b12400250f20703140c0401206e02480e00316008503158206602000a243d01150f41190303150554560100700ba21403d182c0c1d48a41419007000a41c100e200c1c0000d010394001c04401d5045900d400c040c500085c415401d101c1c1560450300d4101303a01420445c0c4442116800703800c0b50f175524049000203410501001e818015901c080c4c0e07607221000203001500d40444882d010095004010320b0041c09005d20074005410125102c0ca0b00f0090541c0c810340d009401081d07508240c00041c3c4190800409608400008101c400811420400603140050483e207958250003020500d007540000304101d641d0b40d080c1e1001815400c02440d55842c0368180c141100120114201d0061100d0000016023 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 263175746 1250 263174496 263174519
    0x30a0e060103050703081315200309011d0a09021201080c010801030507090218120a170c0a06020702040209030f0c010f17160504080709020d0e010203010503150c041d060109 76
    0x1200d03400703c01045258210f598450042c0c100410100e038100d410b050001d0406240d440d0358500da1a5910342c001070303e8407810040f50886601c020f01e01a54010070a040e8541d80c4820b800c40314003a490f15480b41e0300c07401c50000d52070f075090394021041e82c2d00115403004507405060b51641200c1c00e0000b210550190f0400642d03104800344000b0f071150b080b8213003c00110714035030024a2081c034800507001c1c010b04c1c0e03100041d10050304000c0031142980304c10855000c101c1140344203010301384045e0031141042c1c0d140101c141d41c1c0380c880ba40103043e030b078001c5074900071911190140c40c00b881004040d11088003402c0c1809a0b2003055859003800982c508c0500751449005031404d1030006002c00d00d0162642e50a0a44401d440b088611002084000c000015503108280003078001340184910240e51031f40c0c03d003109410366100d4440d41d01d040c1d10400040141da90002801c0b814800d041c0c1c0c4001d941d80d247e88070114103019941c0442d030148901034040810a0415089911550090b22658446615985907945 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 263176996 1250 263175746 263175749
    0x60f060201091a0601020106030b0106020319140d0e03040902070b0f0a05040804150c120f111203040b040311011404120e010e0d060f18020a0905060f010503090a0512030a0e0601 78
    0x4a00011032000f06081088160300794010410300020410503034940c1c40c1c1140349405d03848080140c1000c984007003510301917021400c020605190230118001c0d880943c1c50180f040f0101481450b55031411802c0c1140c080c419100240300c200070844d11034285007007425609508417400d890070001100007414a000d01e22440707000300e82004009080508103c96030186440b134854030070901c00c2d40c01010001480300c0307000f10513440e225501d10f10381810815014252020300e202c001126004454820508400038040c0d135400307034100d210070405031680d0400355090501d804032201d442d400d0400300e03602880c1e400b0312240a035100d02c521007800f11922a045455640002c00d01c6c1c00112500940d140741d18000c01900d003a02c0c021400005d41501041c6c020f41240c0d8040c4480750b421440c0c1c8a01030651800720780302c900400c170307070070341800140f5008001030a0f1124001280b0706104010000c622107400c20051100e5580e403010488402c4c1e200030040301035582044800014040c144031510403030b0403000c1000390 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 263178246 1250 263176996 263177003
    0x504030e0f031f0606170f0a1e02070503070b0a02091f02010f020705010b0f0306070210090309080a2303040f050402030901140f01050a14012001060f0603060f06020109 74
    0x10280d440c100281d80d100901116418458026100350701d0840002c08048541d80100000c0e02500d0810b0103000000a82c2c1411252503520b42048030510550b403005a00c403a08003000604400000441c0f07100e004141c0800001500c041000810044000700030b210060040c4441001651a0301441060b44140102c161f0011009142d003c0c03a852010881100200540008504581c240301440100c1e0040e04041d109a03442d00300c010f0701d40c00d00f60446241c074041500640398500e80030300081d64500811540500180c1d85001c408241071003900d0400242c0904030617101c54024a051420086c180300342c05c1605540f011940d0004400b00100310b5084603414030103035007524074040c200002908000c00a500035501c400107012140031044441388511240354607081a5414002444040e0541c0e801c509081e141086030128039a800060030110391098000c0701011401c501c12080c09001c01e5440010303100c0002c034002c2803880d010340140b000d983c0310745d151a1109549000c101d080e43c0c0c01a0018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 263179496 1250 263178246 263178257
    0x5070c02040b010207091e0507140a0c0305040b03010b03191a04091e0b04030e04180b1803040b040519050d1b1211100315051905040c0c02090901050403 67
    0x20040c14160001c860710300301401070322403e07691501c11000343ea08600641e010396401c80e40001c10201607102c2c0503000111454440641711440101c0c000500c07940184406011100215a04151060044502a0070140c0c40719490b0f523940c41094800341c000391a40d0610036582e00841201c00c1c007502c07411010850150b41082c0905002c01404000c02d445242070f203083c041d204034041d07a03800740003100c5221442180810014076182c10000e204108600303400388181d042154400d10210741e255461021500070541c1030390764849120041e2030413044982c1802d98080410002003600700714020700100c50b41915814200030b02050070101c1d0f180903019079688140c4885a01003c0f500c101100c0c0141d5202110b5000c0c4151500c5401d0310090400700c0440d445000d0001200d864284540400000005414140119401d4500701041100c05005d030f94054242d8005801501c40001100c0700107040140081144000e00c1400501c6240c40d1b85007a8001c59000c0b010503140e00c014466144581d030180d0307030f4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 263180746 1250 263179496 263179517
    0x20f030f0901050708120105190315020d14010f1e0e07110304030b04080a030f0507080414070302120c031203010608010b0d1413020406060c05100e0f030406050a0e040507 75
    0x180d50541e04008001c90400c00c091001800003004030000305012122030035050b4040d03140104100c100f00084404072036480a0b190101700242c0c900ba04010550030404000d07882e1009945508002d00c424082c0610102c00b43d800007456100249106050702c1d44402032400c10401400d103041503031110300c105200d2160700c00c0042c4c0f22031711a200001020140a0a5910b032955a446000180a050303c064500c000000f68400c01c060300340c880e803035408440314070a204510707000d01e01031310801c00280060a481c0b1070f000c03031003a40c5c0703814001d58001d50342c000c100030604145065074580d1841003620705800b17485141c1e400342c0a40d04c12800d50341213030b0349540e410303c042c1c1c00c014401005800100b00400c040e92528041c1d4000d03400480880d01c00c960240d04e0403151a000d00400c419240c0d0f0754400c2040c080c0ba031080001255000c0340c019440c02c0e104001054614401c41e14600d40030180d81076072036900001c1008280700ba8028001c009290f101e5440040704000b810811080f1603068500303001103850100e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 263181996 1250 263180746 263180767
    0x170702090f040215070804050307060903120c03030b180a0b060306090c0703020307120201020735071106040806090c03010606051204031206060f02060c0f1b071a070b07020f03 77
    0x250716a1240c0702038910020440b004000c54083e42200c001119a0789011909001505081061200900c40303031400c00b900c586161a045025000750710100c04101400c004041414000e03004100700900c050700a180066950107008544801070340c0801c54507040c813100b1100c0385049400e4074000c590091850600f5140c2c0f14001c5202e80c481141141503020a2000a001c114040000400c01e9265000940d44940903d000c400500d0501110b240160105481101002c0e5036a801d80c011030903d441c203a50f030800d904105d40e44840c6191502d1b8400b10000300411860004151180101c1e001d41c11107032803041110405082c0e5030540117010001c3c0d020f0107120b50000f1405c4000750044c4c0071382416010251301403e508140d4885030849400301c0c03685066015079680c100a001c1e0300424600345541007445044450140788220b100a610030030283e030380c4920820f0705200300c4000700007440168621000000f816055908030f80c42c20343c0d8403c03600307000910f00c03400855075110071111207000c2d520301400c081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 263183246 1250 263181996 263182021
    0xf0213150e03071205060a0915020c0708010501030f0308090d080604110705010c0f09090204151107120b0612150f10033002030a140706020909040f17070209 69
    0x2580c500800c0241e1120045544003071203400050102c80c5800e104814403418114506107001c1c0c6403081c0580b0b005176032004150441191a4500200321000d80c0c1c030810078142c00c1c44d02400360030000c0e0035403a1500003c1040401d0b5400380200340301e911901c0c8a641c80e0b00c1d0300c80c0c858480806030400f040709000001c0947c43c0036413041030300301c40b900c422508040e1b0300d4986a00710b0301103641031800710b00c11140600000750031407040d900900c1c80c1e69080d4a410f0138084540f404540c403030020004e01464030907400e01c100c020f218a4015101c6448800c00303541d00c504011612020688140380035200141100b006503001043c01c80d0706a0304c2101040f00740c0c0f03908100460f011002000007244c040f41c00e1010000485030000894012070205900c2e45005080c004044406540c00556003035600810001c1d000c941c120702030740310040e45295040d454103918240100070f0321075902440c1d800100d000400c010860302001c1244524094550100c1217000c0c400081014825840040e500c581402c000400300030582 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 263184496 1250 263183246 263183279
    0xe04020915130305060907030c0b03070908030a02031305100206041b1d0a0501060c02090106030903021603030f0f08071d0406050d140c03030901090b0306010c020a0b0702040f0213 79
    0x7038400041111044072181d01c0790003000001d14100b003215000c2040c800c00300004c9800c41d2440014004040c03565441119110385c1c0e20441d06444004000501524010300d0100020041d074010390747d41e0003004200070346a42c4403000410341d100700c854010405040101c640410f4280356001488035031920344800010400346104200100a15100400c00e0318040c500748010300009950018141072440030ba106490050304071030f041000800a00000d41d980d0301c80181121142e040006070151b250030300b02d0510440310200e0748000c04001c00041015400356403c4205001c075034030381d03d03856480c070001c885007601614910f00250116155851502081c81000c2c02040700400c00030340c40c0d81e101c02148445000b48820f03922404000d0091010200510100c1c0741507008030061440e02407140b0005c2e001540e140030304505400040001525a4003c91a8611080d0024407180c505035a811000160303500030001240681c0c18812105d0400c01c0d0303402542c07082108500c0c030001c80d9052980321409001d11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 263185746 1250 263184496 263184499
    0x5060124120e0304150908060c07020904031b0f03020609010e031801030e010c09260a0b15090c0d060e011a030615040e010311030f0a11011715090709060e040209 71
    0x240c070099420b03042e0402c01040105046188041c50041e000c1000e84000442c0e44405144d0304000d0030050303008d64007000c540328158105c401703185984a0341812601e1414a0048184000304890058140101c1c60b814641d528440e5080352450703910b5005041c00c0e519001c10340303241c9030720a01804401c041d031860401d11441c41850000755154011180b02e0035030b613500c00b01c03d0205030418014444030050660704841700c090141d42e210140100c44c401d42e0380359009400500003d83c50408a544444d041c040d214801d03c00404c0300e1958100303d1100c28072540012070410b1700c0782c9852070004d8000c03201041c5d103040b80e2071040001c1525138480c00000180d4001010303158062600c450900303401d24071b01c01600141243c40c80b0300d1001e41c15454100849003a0603401481b0341c0c03040c0c03c100261800042c12547c4241e0000c0c0790703500700813101d0058500900f5881c0a07104800103001700280e8500b10b481d0406207031001c98105030542c6030801c0995a000480c002c51000bc1d500310f00415440c20f00e50018801c0110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 263186996 1250 263185746 263185751
    0x30b3d030b150c06061003021201090903170403020c09041103030711011e05071b0b07150507030605090a0c02010219111b060d050c0405120c0114040b040302090916120506012412 78
    0x2541140810090001d80150501c80d64407163310050590021104a04e41d1f400e4100401c1402c2c2602c020f9600c0c010a4103180c0309906000004042100da40504840312001a04032070301e4450a2618009d00f8526000490004a6401d0391014211244014100340740e155103d2503e08a96900d64401c0404144c000c0080740c80c04242c002020414000180300c03590081d20100081941805c02c001034070f1001d03110b5020103040942c00d004990f10351003240e812051844000030051200d072816800ba010350803128800c12100d200e030481d02038025071a124118100003e50301141645515407000c40e0456180c1508590217001e4075100e071541d9441540c00115030710103a800d00760f03a2400141d806c107102c000e00c2c8550308200c140d1103955030490005c2030609006101f1505081c200141c20b42c481c0614407004c2c3c8100c1804010402161050100243c0103a000005020361a1142d49514440501a0703080310280328280002400b8283c080c903508011100016054042218100c12514098000d81c0c0104c100e6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 263188246 1250 263186996 263187007
    0x41a011211030f060403020604060c171317130807210209071e09030b061e060703030b0d050609070608040309060c053a030b3d030b150c0606100302 65
    0x5504221017413143e4800e900801c0c0d549054a003200a441c2c5442518047c008101d46111015090100701541300c2040305041080340400e040042120050300c5000b0540341c40081c05000707010b00c14020700141d50054048603481030341c0300c540a07094070800052810300e140302c40d504001441e08014068000290745060342140c08443c111070380d40c60419600501050141908100300309180d000c841d41b10b401162145120514403100c0600d410203401820300c1194001000400c1502a51150402910240c0003c4c01343d20140352442e40c443d004d41d0755494911801d5000150740d407155400700c2c03086605035695070300145010000d80b20398214800840b4940a1742c10154001c0110001c0440d0860801c204002c5200341401c88d8000c520f60305120104040c24483c070194107488003031640008404962800041d00780304800b030452a044683c01a80c214078034a0305a2410703500d504034103202e8104403410318810070410045589c6100c0c1041c600c14075048000014042d03e0469801e11154170b140c100503103441e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 263189496 1250 263188246 263188273
    0x51c0b01060e011d0d060e011d1e06040f06050705090d060c0801080304030f0b06010201020c160305060705040302100e0402090d060e0f060106080c031005060f03041a01121103 77
    0x1200240c0103500080e2991032840b40c1981d01c82e10503801841e081da0280305100d040404207034082044907020304011780303c0c5840103045809500c400030801c000c803501041001500c0480307454080c01e60b000010309011416500182d200030138250f02aa80c0844070320756101c02c0c0d0380e03448060080286100240a02400001e03180d881d1303101030440940c03007400005040d4492a80c064880a01030700141504d900034041480015078a481d0f4244080d00140ea00503180e49050040f4003a00c9240c0c0307003122500400c201658405100c50301141507038803801c1580c0f5166528801120300c1e0186120196102041c194044c8040303008022000361020060000f41c54100810003092800f02c0302c9200b00c0350242d07602400c016401f014850480890b40c818050074031540740c410300504808019100c003980e404000040313144d50350103807071070b4000740800f0b0422501c17290304408124803a00111810b540300c140040002c1c0d503040301610850b05031030000c0d0320404001d4031f035101c103000100341c40711194043c403c100ca0305402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 263190746 1250 263189496 263189513
    0x30c0803070509031002090f040203151507060c020109030e120a0c2303011a092a0901080a0902100507150617100e0606011b140105010618030b01051c 66
    0x500300c16198182d594803c0f5062500e0040b4584035251181d00c1030091290a549000c00d4a004c201c00310707000340e00c9882d078081005102c28040c0006a01482c840e000d0040311040d200070b046040e0044030200154540a03400368240c0312442d100400140000d00007404600d045010711320a48441c04c2240c48800203582c480402d00d0f101c2d00701c480040008644444814800d000d0b280b03052006030020700c64001c0881070350426440d1104002d00c10081e80c00014410000740e000e2920a00041c1d070b40c410454a101812540c0340c0c0211111350003c1c9100c00003460b1080d0902480c1c40c4039902903d0503480c15040c01003103802e0703001414120703040c100011044607581180d004940281c010741c1c080c1c40b041e19180c52082c1c40c2507084250415042c0c1000211260380b00c0c0030070890fa0184c07080c00c0611131026400d020a40190b40131030b00030a000314070307442265424030562041d4107841070741d1074081c42040102c0b133001400740c09110003409507042200601940c1402c2c8404a80d50400741442012a100d42da501c0d0003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 263191996 1250 263190746 263190751
    0x16050f0c2101201c02130b07080d0510030b0606070c0b0306030316060203090601061d04020d02070b07180f18020702030a0c0e060a0b0306310617010c0f0503070c030c0803 75
    0x407010010845100010313541850b07070303505a00a4400c52400301840e4401682c0701ea607100d200c00b0305801040300c5040c09000002c030b0303000c02c00b00842040345149c40c0c42c90b48000c0344240020754078444008001207550401c10200c0c7e40040e00f168404503044d241c515084c40d141c2c40200f105030540002e0000c50fa0103009606c03540000c901c51070015849142000101d85410016801b03207041185640035940b01010012000480400981d4003580d916040107a00300a41b041040042c003103051202000801d503404000141d0350103001115008580c0d454980218000090141d1090719000c00d05085501d440d550042c0002071016080d60071102c165151075045012a074030181031903101d2410070010b46010b440d804040c000c40c3d4040f0b0300394245140442c03040b20540342d103004064018104003a2010031050048200c600b058011b010081c2c403901c000e40c801d40c14400d04a4650f00f0100b0300c010782d0380206001d4071140b04035036031603013181d03115030b0211a94046514181c05010310708100a0104013004029271 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 263193246 1250 263191996 263192051
    0x1823060405090c100c1203050c0a1107050909030c01050106052113050d120f021c0b0d1b06110a02030c060f0d02030f0108240105040906020f16050f0c2101 68
    0x6402c0180c2d03003400f403405000b40e41e41400b05131912301004400c04c101e43c20f80f260200386240042c110710481c0c408a2510550350070166001c1440d404016400d00f00100410078440000024011a42ea801068426004040b06014598a03040018015501500000e83d00c10380d200503450021401c1c4d1038190500d540110044d0010310240041e0416030035a0040481c11101d02c3c07411440c00c104040043d8400c1c00300545a4851511100d092141c0c1e921400c028030346680081000d120512034954990307802c40706104880200746140300b0107122440205801010341c1e006005032001e07000090402542c0d0b0300082c8030801e854000d1103020303050301c454800ba6108070072022103410b865043c81d10b40d81c81c20502c3d07542103035238507000515440b0381090351800a044a50944002c50003080320314207080079001390080005100d07400300d480858459100340024465005000380c0e0341c280100078603543c036240743c00050354001c0310540704100c0040030144114040f01440c0000520282901c0c491100e02001c4500c11317 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 263194496 1250 263193246 263193257
    0x4020304050706140408071401030f11090a05041107060902130c0f0e030303070f080a090b101403070605030601140c1504060e070f09090503040503071823060405090c10 74
    0x1d1200940042d80340803130280311400107040c14500600641d4903c1d0038082c000007007004914010140e40a9004400075810190061020041c040f64030701003900b24030b400f180f0030a076030f44001035171b8102446401d00b00c0c080f5550b501d10707004213070312150b000d003420300c004030307040180140b00c003800c20924494003038902c43c2c0c0c4e55001c00c099150303040284900300d00b03100c6506c40e800410601030300d560010101c03039601b03400c1d08006c01195580c80c6940c004003440030019002102c00810001210703c4485a2019524542c1100c031039605480305050362035549009800208604101240c0306601801481d280c0c901e1054416190403588400b00703040001d0705070807620504800062008001c502d010701c0e800201840c0c010f21005140010400d5000c1c0944502000309039285020014400107200300e0f000713020041c049480780d41d600d19124415180304040900202d2070544260304000c2042d14410150088010904441d00d490003004000c4c03401600b0034195114200b045a040c0e125210683d01c3c1c1c201d1a00c0c1c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 263195746 1250 263194496 263194499
    0x1030c0e0606210705090a0803120a06030b010b03040c0f1203020f01020a020a080c030403170d060b070f02040209032b090e0606031306020405040614100807120f0902040203040507 79
    0x80d00480c050200c1d40710300c80070f105503c606a04160307040c4460035201d40c0e05400ea101d043c0180c84910484c000301d50405c1c03c6070000300b50100004020302c3d04c45d10f8400501c2c5681d4600705600c0440e50580802404040200010800c01c0d006030007451b0000c0c002c18119203203039034802101023500749a50100b0250803588040c0424190140100f482020820000750301d0007060110003500c1c1c03400a4001401e941e0003140700c42d030001d410002d44015503484903c100d87c103104035081c141c17907820200d0541e4a090810f280030540c46030010580d00c0f1160f21408555498059a0800001e500300c11401c40e0180b003001c0140740080740d0307603004525000c60014103072030003a2250001440300410350480c0f180c06291600b801096141d44007200d5004411020551071302280d4a0502c0281c0b2555014039071103410b0260114500c240c40004415071031084400345150a2082e5066030a010210340c17850200300392514581d030503020b80d000404122200030740050b000341954001012a00156000c1d07a103039004800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 263196996 1250 263195746 263195759
    0x60b04090606020c18190b0303072a0807050103020307050c070303030c0e040b090705090109120b010f0e2a041a03041704140f010318030804030201050106050c1002071a01030c 77
    0x1440c000c42c4241c1750412220200074010f0300c2002e0181c8410201080b13203000c1d0901280030342c06014500801820389907103000c142040c2e03400d00e01511855a481c0d0344080c1c0040f484003800b07282c008460403c4050072082d0310f00300045d00290801041c9a090041c1006980c0151609101441c0030b50301c00c0d1000550010f1020b8014080504800164003032480c00c94a03484a40d0b40c100c1c5968008040e2510741d0303850902000481784030a0580c81212a10310001e011800c2211106040d81a1011040d440c0401ba03503440c50602c40020681d5a220644090240041c07011110200070448102030204186081c0d903980040040c0300d00819200851300010080c00b0401c80f024079400c15904c0203245141c100f5003400b9880c0c3e000d51009043c0d42c82500360950108603a4000d812148010700113071058403c0a526040c0905001c1d011036045006501e0400040ba2240c051400e135103030491000300030111000300000180c025409910142c550007a640415010020006240e0303000e0740c032030340c0c2c1c0781200d0b403500c0c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 263198246 1250 263196996 263197003
    0xd0e0d051509060106030908041a04050d050102031b07021809160902070c0f030b0127090302011a0103060f050402032203051e27121204050a050f01080c0d060b0409060602 75
    0x30031100406041042807c0400c41c200151410b4501c5c020300040720380305480144602d44074076489150042142858030382070200641c0550b203e4006000951304071660b180c040500d0303200d400402035018000d1900390b02141c00541d4216072060005c5e0440390680c04d2501506803e1805038031520149400148502c00c1200c4420014020041980c0b0328107054103554131880346030014000e91000c000c40c6d805140741c607154002c01202640301004201722000d8075040c000d01921031a0365501c100b07a404e110303258040d44203102d117000b1100b003a00080032460a00c0d0802000c0c0d40050400c00b0074100710f903440755407040c2002d402c40880707202c1d0321500c0d86c03103180c000c0c4006a00708108080d501c8030018050710041415050342d00126120300201078020003e03810024031211035403008401a0305ca03120307800715082c07001e800600c103880e8115040e441080e520020481c0380d802c1050b5403030000d0703651400300e070040311208060900c550400601140c200c0d25105070100b99003266005443c803a0f221041081481c1d010b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 263199496 1250 263198246 263198249
    0x130609061e0e0708090c0402030a06170d14090604050307060e1203031303030903050d06030b150f0d06051003120807080c090f01081e090705100c03020d0e0d0515090601 74
    0x94040c1d658501200024694001483c0b941400610000503031650001c0c08140903034003005208546a09015160000801c802c0c003a07081c0c03000036420120031b103580000f101042500039941c0d600700c0c2c2d00c3c04200c0502d282c06c00655035420500521021030960340600c206006015165a0074884014003001c03c68420710a07420040386403c104240901080c0010fa00c00445405040c041002c00061800304c415210740b0420224a5280400200811510820803402116a41d6544881c1d004003020043d59201c2c0c00390007503012190040d9040080c6881e00602d501c12601401c0c1c0c40b4040e52500c5a5029010114403d03002511001c100884030381c010b00181d0700410280c10171803c1407102408186400d50040480d81442171910000d01e0404402031a0240d003e64599480900d00341803003801d54882c16400b445204000e00c0c0e8035804c0d51845110085800c40d0103500800d01e11504c03403016144184001401c80c0c0100d100c010600129a042140b840343c07841000c0210942c0c035003690300a0030400107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 263200746 1250 263199496 263199539
    0x6080c1624020315280b0a2a120908030d0b04060b070506071803051f0b0301021602040c140d02030a0b0607111807050a08090304030c0b030a050a0510031113060906 72
    0x110017004e29895200d1018400c2d207034118a03240d5101e03c068010f540c16080b8a2082c0d0000ca1700b1038181c1d060143c0d043c00c1005440c40f40c1c00311144848028004d0b540b280c403500074400594418070802c03503421420382000c0b404440c080c00000b100350715502c46000d40e50180d1016201a030100041c025807a51181d515071080000175a040034803800d583d0307001d84510214240c0d01d41402c2d00e0880075890034582d07110b441d44e03550040085540e4403003510080140c04803044160f114510b0001f40e002003d000da461100d8480304203105600d000010803034400290405004c0410f082e40e20f241c00c0c0110340f1000001c04965010f20452480d00da41d8004104803910401404012604004140b2280d19048000d0703e40300d0748542000207030f95031029140fa1139070085030300c050b044d403d18140c0001c42c1d0a1004c001e600503400c81c2c609021035a11400f030002a288155410001c0c0c00c41403000b000843c54502d003074001d080b8000d181d901d04808021381081600c0440e001024556590700e001c0040010008042920300d21 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 263201996 1250 263200746 263200789
    0x11e151a250c03060207050f0d090e0a0606091502030f03010f090c1d0d170403030302031e090c04050601030f05160f02010b06031b1603080106080c1624020315 70
    0x540c0e900c10b0310052521000709000d401003145c0c0204001400070615403020b000464070b521101c01c10062034800d0500c03c10001154a0000c0b41031031285005140503100c076500c030754001d585041c44205084c0d425003103110450000b0f1206491480040c0300a44c000c02c10040e81d8142c540c20050000c08640600300c840003840b2041011903580200c983c018408800c0482e6040c2103a2420704286d0001c00802034800303210a8000703008010982c06901444c000d03180e141854000702c42e00202c4000b1040c051b41c80440790740c042e00e2031400c54906604056801441890003180d00d5400f207041000395803080d030344407404400004e442c04030981d01c00031030304210700240b00030310191511001040483c8070103030030320310000198003811941c1c010250407034403a203000000150500f5a01c0c10000c207d01000e01070640040d0399040800c50072004402611404a040b440c0ca8641c59416941da08134110200d405034000390316440c0c0311001d500c807440591301c01c1414180605c1c01040d80810400f00c40c00f00302c0700c1914500d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 263203246 1250 263201996 263202067
    0xb0f03100b0306151b030c06070206060a14060a0302090607061a0f0604090209040216030201090605070915030c09050307030c0302040b010c050d11010207020405070e01020601050102011e151a 84
    0x81e110102404802250840f041c0d070303404c546002818528801d030035000175100009441d15043d800003015031140364a642581d106807688400c10110545a10030100300c0542580680300318a400c2c0001c200032aa90b05006140c0202d40d00802d8180c0c005801c160760b40c1b643d440303100281c910a8050012452030884100c2d01441000000500341e000d107008031100705502051010550f1956070440c0e99130384c0d800e01e40d504e19011a280090180504901c01c0714030900700390100d0240380c010410308003500e810070524aa40c7c0010702d004c800800789182c02c84200401c040c0e0004413502c05201c580042c0d402140b02500450560052100b0354003203803142410480d142c04018041200401c10b192444014682000d85075440402d8901a000d40500694400d00d0308041c490106d40006003031402010a8090700e415031707617a5006a0883ea8114540e0141d08040c90340410005000e038025081c6004010f011855a07440c3e0040c40c201c40c40d100c50444a1742400510340320807120419000b080c0f00c40900d4a92440c1c1c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 263204496 1250 263203246 263203249
    0x70218040302011413140102040b0304210815011d100f11030408071211040f020406020d1805010309140f160807061418031506010e01030e07050f0a0b0f03100b0306 72
    0x111202031001e006482c0302900601b40f60f01c00c2d0105c078000c0010302c4115849013003904220782c0222800a59504d80c1c000c0100340c081d50303030040f01c0d6548117002c00c2660280c1c111414005407441500301c0d18400000c48507041115665855040401e910002c540e10940100007081014014040411200241d41d20900c001c00410700d0000d864400d0300c80c9014542600072444c504581032501c1c4440300c0c0d07071003418211090605200c0c0c0d40640200c1e0a142c0c2158903900555405540703440b0311741200c000c02d021184c018040d65010740c029102241c070440318102c0d55411895503600f0422680b0845c68079822110b40021440e0314a060030f406422200060301025261980103170a8a0100c084100c548030085a1852902c11442d02d4100c000e00c0603080e00e813041180061591036010841d410340c042600e089441601d0351003481203644d4609808001c1809030b04100400444540200005600100c200400300d42040742c1c0014103600708070614440d46034100342024840c101e00d10381101c05066014410004503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 263205746 1250 263204496 263204521
    0x6040201110f0d03020901080f040317091e07090b09090a1b03061b031a0306060f04091e02090c0c1903051b0c0a050f1f03020702180403020114 63
    0x15424203101420064081d0524200310800900381401c0c000c2d4204040380b07940540041120030000d03a0f840d406e5070b40300b070002d10350f1f0f08082c0c90180c0080c410340070b21405800c100c42c1103a045103d80041700c0701450340c03c1000c6070f0005070807140f1080b900002000c014100081c014000003c070216a20300d01840d0001f11f0507580c42015201520000030010341900e00304898400c0f03006150407120a100ca40c11005c442c10340d850881c10704000007494000040d10309070155074000c0b051003000300034100381d86030720342041a1681c40c085130990140d0b5a44000c400160315640c0d14400c0505025940700075601801000491800203103106551013081255651620000c100c4d5400784108901d03039000319000f410100c5a82c0561007245601c4c903c180d80007400c00780c00145d080f55002c030459038900d4840e154014000d001c030265480b1600031003503100e401c9028211000c60f0070103501915005042c804180c000507503c40c80280803140340080700e428001030582c2802541a4142c0f51061080b040c280006013810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 263206996 1250 263205746 263205751
    0x20a0504050c0a03090201090b0d05070e030613060b0402040e180615010903020405090c032e1b0c1b15021501031e021f030b1e090a050402030a0209040303020c0705030f06 75
    0x1099a10030001c5c085a000d51094000f8054100b10180c468109030780f02c00c001c040a039041004142e034105042c0361498001401d81c0700d065660780c0380741c1c41c00ca280e0317903030340075002c419002070b84107400b880041107000c5240803461094000a0302c6100024420171040d080200140c803000e03144d803418100801e6641c101503c042100e905030740c001202e0750b50904071030610303180204c1d940d41401822821031100d0ba942c0303880503080f003c00c03002800d140d2441c148c3c0f804030340d4a0f00d00c08030904200d0a02e8406c060041d90040501401510090351900700240103d45043da250884c03000c03c10100030070040e46504000c6456180b503000d010f5002035056485d00206000301a04241c40046400c0e400c600f11745480c038540d508400b0740c1d02186c1c04151000f41c043c02900c000c1490b540582c0701c4850001420214485005207013002400c0704840380c45089086004d060300420a81e014070a101d00000143c41d19010548198025a8016202d0140d90345c0c42d41011850380c0194429804030340030060005000c14032030f4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 263208246 1250 263206996 263207017
    0xa03080f1905040302070501020f03033601090c03060c0e0d080a1202030f010816031a060103090f03021506040b090604020c07031704060201050a14040327060c020a0504050c 76
    0x10050381d2400c0c8144041090724091003070250600051104064000440a003607079000d8007520000d402d00c0ea10a42e0b00d0100f220b0f10000c2960842c01e400d8034441000008080c85c011101034240d10920010440c00e650075044100c40442d241802001805039510070015800e4852034074036204080ea5000551849d0441c0000d4010380700001c0c840c0e540d030300810380008140603001d4155241e103400700d03a0b000030b24024400c02c2d01600401c488000e102144d00700725025240e110044218500d0410014800100700400d206d042c1a5030354881d50201380d0040e1246516442540103000d054070588080c64490300284c07280c0d0081d800d000008450344c6e80d0b0305d041980038505940040c1c0700d811030942c0c903190843c40e40c4050200c00120106100a5104000400c2651410380091080e61032381004002100c0c1c11104c0c0010109180011400080c8030b03021501d1243c00780e03d050951100c40380038088aa0720f4030b620100c01700340c02000c001d0842c20400d028070000c10045070104064980b44100311654481c282d90310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 263209496 1250 263208246 263208271
    0x703120e01050d0e16090203060f01030b0a090b03100f1a03120702040504020406030f0b010812031b090d05060702012309120313050321060307140607080405040c0f0f020a0308 77
    0xe0144c003044460310203418001d41222607640d803c500070003980281c803a1401000030200c0716200d035000e8004d65807210340c064444120030b8506141c0c14001c22400001583c940034500e65003240101074020824a1015000f000038454500c40800400e9081c4c4003a00d4002d4200a807803603480881e03102501d0180d0b0701601c0208280d6554400240104520307040100701604130b00c0e1680078403030f030b03901918103880c103000880e440c5180740c5d1041d030810b00085a0300c04040d9515207031002c0784004031000c2d1407511800b034485001ea032420360b280d504104c0100c07a8031006070354640c071002c0c80c40781c03011030804c2881141180c0d012604007150700603192610060581541d08000000c20321000b40b10340110308598000041d682c07200541c0d5031f80c624204001d0340044140c045080400d800d440d02013821402c032081482601014100803040c017103d038108410581d656081400000b8250300e460003003242e0103503181d8a11000f440b0035080075016950032052041150f100d035950500282e04421a03039040304514805 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 263210746 1250 263209496 263209511
    0xf1d030723060a030e0d03020c060105120309030a060b1003110a11190b0a050c0315090a1515170705030a0f061203110607020102070b0f04020f030703050703120e01050d 74
    0x31658164208401ca5000200061003500080e85a40203a114240c001c06030340c280c0c0500d40d0300320240d00946040303283e0742c1c00c20b4004101c01e2406c180194404040802600c0c201803282002a0420f0a18001a83c006848002c11a1503243c14566004003e02d1814104007600c105000707800c076030007442c4041091210016030701c140c424042181e0b030000c81c1030500c000790b0401c6524000c503030b1100685450b140103042a020541070803151080d64842c00c400741d40e00c2c1140da01d2504004203c5809003c070b403001541c4a9052051340e020408100207045190802a080c0030b54a2000303280d010b491314160306584c0b04d00184143c281d48441180d4000040c11000301e601001c40301d0782001002294450a030328400c140c20207003019040f00010b0702d0040c460050300d500c1e503106041a401e0380b1400e0340040c41e152030800060a40d1000104d115006030010f0200d00d44144444003007854410150016030f8a0b0340960820001c0020000b0807400c0d866484c5001030400c800b040001e0094002d02c00280f0005446000c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 263211996 1250 263210746 263210789
    0x100f0219020d080721050403050d08180d09031104090f0b07210c0e0609240d060b0714010c081611060a060503010501140a030f03050d09030f1d0307 65
    0x8441c0046400000f0030b0350342c5000e4030b00000d4200c0200c0c814840f0f0b0010035112207a450142082d60200c07500304014002c0324401c03400488419000610000b00081d5000b003140075001c007003107000c04003240d82d00c44451035429820b1003007280042001c0184a0f40c200540d281c0040d10550074520070303561004a029680d242c036503041e103210f5900ea03000d0404900303401c2000c2440050350030061691131141c42f84014429003a0030700c0100d00c680e03c0301a4108504a5513002100c01b4003201503100080300c000e603030034075002c0c142c0c07141a90055800b5444041c0003140c008144600c5180c0810848400c100802940d1002d4a01070070120f00240f080b40305c03024580102c1c242038003643c0c010b09000310500a454041c68101c807242d000340514043c2e14080d602c1c01e4008503c0d00000d040c0105004802452240c0c01840d5544000b5100940075003141005020f00446401900e28091845064400e44500c444000c000e0002001d00455401c1c900803001c0418001000b601e0210380302c405d0311420507801c0d800312003848 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 263213246 1250 263211996 263212009
    0x90203160f051c090b06030a120c050c060406030903090b04121401090c0b1306030b060f0c030c030a09150c0f0305030a060f1511032503031415100f021902 68
    0xe072000346580c20300c4030f40d101ca50901d920005a0500c40c4210198039103440c4140750340d440e254280200342220912151508500410a0100c800d1241040360201c0031510003086030383d00154010780c042500e07040d41e0b104040d04544600c1c050404074103090f0403e031925000007202140510090811088039100004100c401c1d00060902d0350022a40142d0301d6807101d2041a551021807001c400d00400d0f0400f0034140d200e4007401c0e0900300001d1405051030a0a1014800d66000c0603d04481e40310800144442580c01c1c4040e1203407034115210310403c0340c40c00c0c5610081262034003450003044114003040c0b001900446020216030341603e031494503a51000c00c0c040080c0607540054140d08500709000074100243c011b403078541502d580e1456101e0400b0b00c00107599000b01d005a40440c4000d5503090481c02136610b2140902d40249000302e810385000c05010b1094106807244139000211520780701140c1410500d0040e12060741c504546a0b0a078907038020340307402e903903030490a41ea24460342d031805640d81c02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 263214496 1250 263213246 263213257
    0x18180c0809031c150305030c07050f0a0503071a0c07090902040f0902010c11040e01020f091f0c17090d14011104050120010912020304030b0c0301050907051b0304080a0203010501090203160f05 84
    0x28100e980d5110344008070b49d130720b41b928030034640b00c0c180c24600d031000ba05200301d2000844402030001c0900ca4142004113420035049807a000b40038500b4403400346042000c0041900a041c038080c0080c2c03000d25030040c04191a0380c04110240103041a17000c10050341d212164010464001e1000f00400961400103000f4101e01c0e28021220341c004900224211052401010903802c115801803141ca0583c034407621a0404048140100b00d4010500000c1001c1e0744003c0c00c080c0046054074585018800040e502154081055034528011952008590b80c240b1801c110100301c446068145480d00d0002449072046e490794a0103881400300100c2580d509400c5080700c1c40e4005a270b4450207031035040c000d54a410030b2200343c5401c552040803d40342815802181d060300c01c050046132071a6112107090350340394480e079a00307802c50380c8142525108403020300190001d000c15401400f0006000d004060948106030440e02c00f0070310400c2404401400c0c0520b00308204128205109405010342d000d81d41805079 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 263215746 1250 263214496 263214503
    0x80613110c030d0f090c21170a021b090a020d060806040b06031b010804080c0a020a1514030105101103120c040303110c010c0318180c0809031c1503 65
    0x20404a4100002001505100143c203008009040840343c015043d640602e101401d0580440d105000c44030070365040031081c5050300384034020500941e9800045001d0304500d15810040803585c0c03007000d681405421801160ba10215108d40e00701000104d0100002d0269105154001030040c010005a006a40180140700c29980c02e40741c241071070389040348201e5070507129010b03030b0305080060b60030b0b0042c14407d030b8010b035602102c40e500e0341d80b40007050b4080c0c1c076640000c0c40b540030180016903900c5204400707003c4081c0c3c0e04080c4000e80c1b40140461039070102c00c1103120014030040c07100d51a0010746000682c03481c50480e02c203040c0d030350307040381903108021124401c210070400b00030104200744002c10480c0e01c25500d17a0702c51005004043e4944003040b6a1500042d4802c0d4444003003441558114088040d50140c0c0d40001d50300d0083d0301025042c811420f01e81034036184982c0109400070f0501e68072007d0140a1864801c0300300701c03c0400f28003071001c40091540c61726040000e00c40c864004029552 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 263216996 1250 263215746 263215781
    0x71101060f0806070e06030c03010e060d0b070e030f0109030e13020912010902030c010e0d14071d01030b0601090e01060503071202070305031902040b070605040510050f1015080613 79
    0x22544001e540f2002c04407180000b00d86900f100907034504040040703d101d64000300d90f09013035034200f40211002420181800d0307480056445040041400343ca4164041d691581302c0c3c1d40340b0700541e024503007007100e421354000d804c0e45032005043c08281c0085034092008400c580003070340125819080002401121000342d0807090165004296650541c88041c080307008138100d80c0359080080046410041c03802d052034201c0301d00d000c0365001510206a688200315160280e86440ea1101d10000c00107149000d5407500d60b01d1000104207010798900c000f50071500a181c540b1078107003404c00614402c241807190b24100100000000d00c0107116900c10481d41c2070f9110150740c1c6c1c010501340200b02d500300359030800b02095001520701160780c42d44201c90440b01082480c50802c0181e0301c1d82c20052600400a548602400344526010345146c2306062054500141c0d00482c3e040c0180269580681500804401d04580300c003400c031660816862948584215102c10410000c0c03035100380a0319520382c45885255 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 263218246 1250 263216996 263216999
    0x50604060c32010e0303060a050d021201181a010605070b0a0b0303031608090604120f030f02041508011401091a09090106030203160504030b0601030504081b010606030b040c08071101060f 82
    0xe5402442d245100c541400910041d02e89004213626440107440541d80400c880c101000b06040405400301400e000070071340307090044080003140c01c0d41c1d440c404459140c840c1031006002c01c0907400510500c0018002d10180f198103050700603186200e58000030745942d203507100040e102c20082d080540201c2002c0c003502d840b42000200740c040c0012000100010400010004640e050001b421503c5550001c0c000c40001d100c03580305540420408000e081010380baa2914a040200e9000500041554030104c00e031481c0c3c000d00044c04840c0c1038010b401013001070b401592860303030f000c042c040036280310f685180c028840201c6a04c10f04e2050340348482d0000c4005000082258140e409180b1a01070b60691030407140742d1040842d0248190b0000401c00c5c0c011401142255103ea0700c0f41e0b42c490300c1112200d181489408002c07007007200054a000741607460346014450b00e94113008000182c98107441c00c0c011080c1e690005404200024104c900b045074202e15907803c800250401d070001c00140725040c000a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 263219496 1250 263218246 263218313
    0x30b06060c0a0501020d0513030c0308090106050a1701060f0f030b180118050f0a15021e040f0911090904060c1214010e0106020303010602060106050a09031e110a050604060c 76
    0xc0d04403046c011209850080007650130100542e03000d003844d0303055036840103085c5580e0741511148409800d100326507594000102d503d0b102c0b113520801418403142000c5003100180c0400742525503940060a00c201c00c80c00400c0105410540744c400e880e84007200540d1781d42d4040c085821280348542442d41582003800700c041201070010103200311401841070300d03641507940c0c98060f51461314450007820503a158916502034219940a4141000c25240c03c501c1c00a04101c001c0c5250001d4003e030301400c502d983d08009a072602e1043c4900c00c0d01c0141d0720790800002c440014035a220042001d02203c0c0c650710348580040c8245020303042901d1548080001c100700c1e042000c1c00d803109008010382c801c14200089142c50000081d0790484081d54014421030b801c2c114111060f4000c4070018041c000d0526006c80044d09504008020080c80109016a203030b090902c0c09045c1d010030041c40c061035490a003807186480e070004071030a44010b42408500c02020f0b26009a0002441c60004d00680d07403295a840310b03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 263220746 1250 263219496 263219501
    0x4030309020a0509070e0105090301060b0714010c020111090418140109030e0303072303070204110c0c0a0806070f1e02030406170609071202070b07050c011107020a030b06060c0a0501 80
    0x44074026914494070980303070400e1010114054480c1c20108880405210043d80328000400c14080c1c00b030300100c1c00030380c2c81014085641086004a41128003030126450b158002d214151070a00248000e0010064580014800740f044041860180e80c03100098460104141e404490141d408032506c05100c901002c0d5600070802e514046000810b500301030140d0f4500042a6a8116000722580e41c0c0b601111901000145401400a129000511140c00965034a101e003550410a02d40d18503034560f00100e000341000c03000d103507451041c140c4400a0101420009029510041c541080390245501a074141e07400c510010302c003882d190000300c0180d46280d01001400c100e45e2281c8503818011402c003544020b0700801c444072508010708600149403d03110303800d403c2260380400750061501d40c00c0e0b11170007080c00d0104c0f00340d07000c01e8000464901a800c2440390808041c05107444508000c61035001508410b00e40c84003905000305c501c013042050799000e0071140c0320300c880f070212541d804561802502 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 263221996 1250 263220746 263220761
    0x909060219030e2a0904050a0506040302030d0c111b0d02031902040b060c060f07031b021501050103290a0e0a0609051005060a03110d0603301b020105070803040303 72
    0xc45001c1c0c2d802d10305400d24014040c0e0201d410351100320850f1311000051101400008006407018481c180c0c3c0701d0301150007446058000d42c0244c2c05141d0b240260388542056494400e050001c225034410852940b620200d110a00d20320005a00080d86502c20000b6141854454001e5450701802d0605181442854085200e4500c296024402440070100f00416805072501e540c010390081d03400910420b4095010507400b5141e420005110b08513a25851740324564850a200580d000b200703040c44004600310414010f050910b803d009120070310350342c001454082c0d0316540300305840501c002103c0d6608010803000d4841030300050070a203810140320740a0140c80c40b030034542d80d19010128032654903c034404001d982018015a01d0195610000ca0080400c0305029060341010f102088190449004000042d40a080030901d00d915400404100001c411951200e2608407103580d0469a04004c84513200c41f006c01d0600c541c10002d000688161180715001041c0d807a00004100c20103030160311604 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 263223246 1250 263221996 263222021
    0x50f16080610350f0903120718150909020a09050d11121b0301180b06010c06020a020d110102040812030c13262107050708071d0703090b01090906021903 67
    0x60715902c1c0d620001c04c0302e150548103603980f50010403510146450010a041d003000c640d02c1c0880307a418030000e0b4072041c0314903901300d00314401c0501280361600f580441c1c00c60142c80031080840c90701d80d6410317010302420105e22442e40900900c2000d5024070920038000d044100d400b03400c10b1b8203841039034000c540740c88500900100102c45100d08901a0905200d411142e80f0400340380b000c101e046480790711030b080c0010310843c10089e20118000c0060240d0002c0c000f0100c0c1500100b041c1146038902401700b00c1006110b0b41c4907071050104001d482c0c1d0006010f652007182c580307159580c0d2514900d443d1544100b810070324130104026000507002c200403007030054441131081303510701c0a039581d544036850301c0090328075064101c0001c146200b4030845030700030030000d40700340101e841c6d65680da04041c2c1000c3c0141d000b02003089010080f0789001c00d202e12101c1c3c0c0002e10303280c100841c0b0b020b642c41034150030041c060040c41c1a0742b9a001ea040240640c1100d609640114001480c00041d10000307020380300098100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 263224496 1250 263223246 263223347
    0x50a15090b1303020913170313020301090b0108070e06060906030603100603050a143c0f060103020103050f09030d020f1b0705032802040b03011509050f16080610 71
    0xa0f100082050411b118a648481c001c0d110030401041040d40303402c05000580c3d42d014a40c484801681c092240414540c80740d44500c415600d002e0800e8181001036102602480c01d05081084a655100441e29102c40494095482c0c6d11900d010034a040c070341c0e050400c2250b29240c8048103011000a640503403501c81d1600020101f10303c0041c40c0c9031310584c540c02041e0392408100d1050b41707900c96003c03685075400110f800040500014a6890311020320503003c081c0e0441c000500a5591600503035601400120090515041c800da0060b582e104000d44152003036400704a2390b040001403421104080b40c1403089008ac0043d820510fa200c080900c1424407901c80c0300000e903d051884007800c03400c0721504d03112902100c0d850302403002400505040303990655a2b0f401e94000c00806100070f4002c0c1809404c0098985880059014503801c0904011800040400310810700d07940044107941c01001564510f69031010303134401390781e01400350f036006507558090404440952199812101c40c0c591440c0b00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 263225746 1250 263224496 263224501
    0xb0105040207052a100504090605010203040506221502010b010f02011b1404080102030c0a02070f150c0c0b180916050406050a050d09080c010e07050a15090b13030209 73
    0x10081207202d0100020003982220782003a040c2070b000198440100c0700101400c02d201800360000d00e80380e003640701c40c1c80410008501882084803500c1030102070031003800203524150815000070580e001d903042001080c0010450b6001c01000c0c6d42e0035100a2003002c9540750710341c4940784c02038041c0c03c10001c0039001500c442c1c240300d0264814082d045440200301d400c0da9000b0905a0704440c8105000444021000b040000207200d40c82440218401d40640a03869208c4c842200002e040c43d11990000140ca00d8940043c003ca4030400000303c2c1a00b16402e000eaa100042d02e4070b43c0b1810391a030311900d42d031000403074110030203041c603a0382c1401c000d000c540d280c10719514150070280b0f091001084600042003440107002c07540c020001060303080043d081c00c40c20420449080c0b400e484c14588202c036010004180016000310901440c0986218030019002c0720f0f08040c04110310015900c45d450390410708091821400f4099504000a0000740b800146d50700302c0d2034100c00e1510542c0c40103e002c0c1505000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 263226996 1250 263225746 263225749
    0x513061d04060b03150f03032209020c06060105030a0b1201060609080a0b0c03070923120f1c0504080a060504210819140717010f060c06021303020604030c030b0105 72
    0x14150541d070710f2010490940d00c070300400300b03020460a00816008540700410b8a5503a50400203451580d0084014070003421484a0280c2d0101041d4000483e25006211a07602c9503000f1804a510180a107015520b99841200403000b41001980c01500104410044802d05806401040a681541d142c4005e00d5554220140c0d4a01c5099005000c510800300411040c2a09000440d0801d000d891320341821034941d120100c13807524524400000c1c041584643e241800c20b00c0481d8400c0c0f481802400440d00da4109517a241d00184240c0c01d403581915081c204564001c1e01500e000d0014202141d40303450040c40c0500003440161402d45030801040c40414052a0244560040500c5540d03500740303a8072180c800c0b0038843c002e183c00c00300441e1034038013040504040c0003d9500c680707070701d580305805462101800f00c00c005040e0004421008007843c00c0c01070b80d81000801c4800c80d80301d400180d841d0742c1c20f40171054144090304000e521036000a4004140f00340a0084000e4900a40040c901e590380c410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 263228246 1250 263226996 263227001
    0xc0816120207170a0209070509030706112803080a1b02060108070504060605040303030b061e0d050106081b0c031603110c0a05010c0206030405070306020f040602121e03070513061d04 80
    0x10f03882c0c6180c0c8610700d05030050400c00b0325503803c40780030b0400b5030030201e0f408002420007105030070440008101151044081c0020070071150710a940e0700c4468260810b2842c0805c0c010f6a02030302400b0f02c02c07414041756800d4456402400300124000151216620034903009480c0c0c81c4c01c1c03003a00e4180c03040344000b0902d89000d10841d41140c406071070315480c180c6150380903000b5045000c01c5603445081400016210404101d40260341250004070a64403002515842c0803500103810031070400c81c80030204645541c10040828141c6c5c00c68180c2c54888501ca69490724500c603861a00081402c51000001015040301f0188814520780c4103036042c865441044c44440030251040d81d000a0807940e000c005414404019500a03001c0c005071360301c1d66202d89844087c2d0f4001d1200c0c0203068030000c0c0800100d98144041c5040415001429160403564556000705140c26807401d40d90076400000f2401c0c1e60700420840344065042d196004950340d40e40000761058a0600700c440007104604644011481c3c03d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 263229496 1250 263228246 263228279
    0x7020f061e06060c150a0902060f0702010314010503070603020d060503070b12070f0e010c020102011b05030a0e01140705091801091a040b030d05030714070b0403020123070c0816120207 81
    0xc8014040d011812107449001172000c1c080c8041c0590390340660015881d44001407200ca0011907080d40d0314070561000400325142625110f0ba00c2740c00303100600c4165000715000080b205c10b03240140c0c880d00f282d4401e800401c0154400c0703525110b00000020310300300700310150629a400da402d210303199807041c00a50f281d03001100981e001409801c0d80711075560040c01103d6003a4010f100001d000202a8129440341400c101d612002c00c41c08010081c400140380610320008500400074410714030103004610b8800d5000c2c00341001d00801003101e0185840300c0c069022a00c40c02e60914005507500d0488400800d101d0414640002c0b4495000d155030401d40030300c1d4000b1038042d0040036030740b281d4542211260005040402002020041c0c4ca2498201c030010f01b8125010358200d08580c140b520307000c1e00315020030001c00c0c081703a40041c5201c112007240c14015400100f03030806031018481c034500250540308900f02c18100300d0702c00c00c00009102160208045410780b94084407e80c0d9100c0d0b1381540c142404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 263230746 1250 263229496 263229517
    0x60405010c0c0f03140408030a0c0203070807030c0306022b1407090302031f0f060602100f180f050c040c02010903020f0c0a330f03110403020906010807020f061e0606 73
    0x100c081500080d10400001c4182589070b175505d03092580b21814241150b01500280300060887c001020540c502032107030b84001d05140c0300500459166035100ca0603440c0d103110251401e9804a0030060f0001c014803001141252a404d0500030302c0301d002c0d00313070042440c8900c076000d118010380040c00941c01400071070256a0010014a22003407481203482c61082031a00c201d4030306441d05010b400d122468081c1d80058000f6801914403401c1404484046501100f101c00da21400d02840f19403800050018841c1c05400070280c9894100b00e0814918003241980b0030360304140341c40c0b02c001019070f042d4405405644a50309a41c4d071042d0114000b41d54250301c5400952101a000041000248441d4001502c48120740d07801e1880c150000c036107512900c071340d60b9000401d16a5410740342d8664140304041098a4040c0301c9411301e821500032944c11000206041c4c10b0194240100d034010380208840a444070780325080310a2841c240204034014040d01c050300c24184032a00104003980b130040c05a601c40b40c0d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 263231996 1250 263230746 263230763
    0x605060a091215052805101a040e01030c051207050f04020c160b1e040f03020f0f04060b0c070b0304120c0c0305060103241811061308060405010c0c 65
    0x1070000c10682e08251000407680601d403030034503990607490360003100d01c100080c50303035072400d031042a101c00000e01d214090400418540702c201300c2c2e112074a9011005907481c1c00e0304020441400c1d017400b2240c0c0b00d1500410103682d4118000420440c09a14400075110162030140c0d48049c3e03003a506603142000d014980d0b0140002000d00c030141050b42c041c0074821a81411103480300c0401014511090054026009107440011131a00d040c121100100d4148008200035182030315203100300082d0310050000034464250018440c019a88504a06684072002002040100e950380c16810f281e81c00064005250300603490000749600c1041c0036603219503040011505078641d8018100e58074034203c078084490740300312200400401e0301044490b028521aa80e140151001400102500c40c584141c01d4000790804880d51a2140384524040c0d489610041c2003c542d007880000652a000d40c65252940c0091404000364440f80018850f0040303029030020400d000740d000045074560300f182005841101d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 263233246 1250 263231996 263231999
    0x10203100b1606020c060708060102060403080a0c090e09010b0109050d03051c1b030509060c040302100806030c0301020d0b130e0607110a08030a231e04050309060c0d030605060a09 79
    0x1001c1100400070450350503401c1c8103010741507851030200e0700140140c030084d81c028010020a40d800c40700341d50300040240002c00c0386180658005000d064014440c542c0c0c261591060100741d401035042002902a0554100c910301c0e0842d0340900801c9800e50340c50000341091800139981c1480c8001030136154042e0349562800310407560868900da40e408000800aa8482c990358486540103000c8900c40c03960b84d0042500e0501d503414602c1c0c100301400207503201100f08010001030f92101090503001c4120b0a0801c807550f00c800000307081003140303142c00780c149d40001100d070141c03401a4440c482c4450221041e05815020901100441c1c0d40303c04440765540c004000301e55198040ca030091061940714088403c104410381e5a110309030020350b0801e245c142c6548101251086100c3c007820040d04561090302c0c02e1400f004485110001c03060400320031000312000c5014010280204d070a4030f00e0151030395680f0080c10842c1c0b03030b41e1819543d47c1030010b454100302284d10f161450464021802d5940c0d0004400d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 263234496 1250 263233246 263233259
    0x1006080a031b0218090609010606080f060a08070801020703120b0123071e0209130210030e0a0203011104050a080a030c1211060f0a0c0503010e0423071202040b0301020310 75
    0x9609146400388841002e51803400181e41d5034000220306041078a40e00514241241e0161400700c01400d03808040c1d05041003844000c2d440b41840e64820707000c180030313840c503280c0034007040070300c4d50940180205001e41c10001c030701e9010540042c450035210340d5031421145285a079100403682c00c04c5880f07001816503581600d841c0d0f141c6a100e1000c4008100c120b00c0c100196071040c070002142142d4800260189481e2419071500391822588608a4000c14064840a42c0041e60500c1c1e03103441c401c103140c3d881d400c1c032880341c03002c020b10000107074007400800102c015064900400e405c40d00c100362250150340710220301309101203a45504564992a42039401216a0b103a105002c2c0001c0f007081008001c0d1500845504100a898010741100b1002c0040c0d04141031020155040c401408060240c10001044140c03801049980d06c103810900702c004500c804050801d20411100200f1b56a214800000c00e40110145034038840c6071080301c4c20040b181c0400107060907808204e9010407020101c3c0c908000d0b4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 263235746 1250 263234496 263234507
    0x705010e0a0e041a010612050627070903061401051f021002090f03100e0d0c020913050c0618010215040327051206060a1a0a05070c0306050403050703021006080a03 72
    0x20300c6840c86901507134000f2210000e1038400d901403c00a00c1a0b00300d080740e041a4806c064000a068980703800c06c407542a40501400b5084d01e005459840e030b84005001c640c03290b5180d0000d1940b102050282d0105441120500542802110302c102080300701b0820006841b9040210b9842580140201c0c07924032403a04000d400443d0441d03000000c020344004280d909112540720444414400201c00d0442c0c01002c1c5000070408110301407022240d480300240c1c0c0c44071a9603072700c4904041c1035415808186012820190346680c2d8642104000c180e81d400010010001d0501c60310a900300d070000341d10302c0008010900b042e2000fa0116052110303000c0a485001d5240020041d0781c42c03005a569616804100e440e101d0340d4070028907400078801d00c000b6160014100b402400c0804184049042c0000a04168800c0f03050003c240100001c80d9070800c642d0100a400841e0070620811a030310303040c1005045d503407001d0b804038018010805504161500ca00c00e8509030340b0800c1c002c051201ea90307a8142c40713 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 263236996 1250 263235746 263235751
    0x302060f060f061c060504020301062001090c03050703050607050315040b030c030f0c01030506060403050c061602030d05250b061c05030f040302030f06090d031a030a060b01020705010e0a0e 83
    0x1c100300c19024424060711803000900303103002850402c4c071511030b03038a0b610000c5404503000340d84564010030040103c2a40f014103001514800245039005541c2c62410600600c2400030042c80400103d1000040c0040400c000040360b0160b810b8500554440744100c810b803100b201e914940c0b10f05011075644606090380865100300018041fa803201e0049000a0700e07005550400e00455800380440500c1540d1501440c0d4101006540c080c0c2840d045a542c603481e84581290240119008116840c150013810b00b01e180e081c1e00601516808804100c004100d0340c052031420219010700915011101076800f07034140310b69044828510240c0b00e94040200c07641108100c0c09010300c6500640b00410b00c280001c0024442034800c042d651840c40c81403600f02503c00d0300c403401d07a0b08034808000c00000089220705d000c011301d141c00200214070040945454200070131294045c81400c080c4030801803680d00c6141007e60076000c5843e1503135103000458502403400c80c1d0941286c0811810410240324061854 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 263238246 1250 263236996 263236999
    0xb07120c0c0b0703111506010f0c08041e1701330605030604090c170601050a0311010804030309050d02070509180a02091509040b07090f051f03061a0904050703090302060f06 76
    0x71101e1740e0400101d00d4000e00200d21100c9041c1700092103455a0050618007200101e410045005401519040382c2800f65110b01c115415850170444100062013200c0c101500d00d0000c40080f101c10302c54414002d1600c40501643c04100f001506c00c1c94002111a403050200d41036440307615401d040003210300340c001424080d006901c074404000054104034415000d007000e00302e5882d4100303078420818075040b03040c0e2005004501d40c14080c0042580a05480c105803020f0810080315122407508800600e450880905180100802e41100c250701088840c201c0c0d004845d10405500e44608420702c48030803240d4540d055100000c03150050500b94019503010f00e042200310345098008020a0000604481c1150f5100b811410019101c2c0c100b00c8490161000d40300c0c02a8003414400412000324102c0813107450340c01404600090700b4441d4001c4400383ca07080c1b10741e562a111810b0b16a841c0c1c0c005061451045013414005030709140300744108809c2c80d07003544c010f1075a40c0300c0300183e121582000c0c201c103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 263239496 1250 263238246 263238257
    0x30b0d020409021309050c0f090910090201020a0818041a010c110604080613060f090c030f020411040b04050301180c1a0906030117060a0902010e060a020f070b07120c0c0b0703 77
    0x104135108580c401e0203102402000540740714014102042040070000c280365116401d80018001482c5002420801e2408507200c00140d6080500050b841c0c03513043e0800a180c00343c001480e25440004600c1220803d0781514148114007884c100b501100a0b8000c106000501e20183c2c0f0740842d0001c00444040b44010704194a4191910129410200c003100c02201c00c800110752202007050500c00c0140e0041c0d007540c02c110a25082c0c1c1c40341284809403201174118002b540740501990307215031110ba0302c400c2da032900a954070b071f545007907030b8058101d44601131081d407070400344580640b80e03217500c080c0890b0312120b02421030f820200c544030102c0d201c5140780d0101c8000d0100b800c1a850710802103000e40422610f44d29038880115005240080041101005508007825100180d80200503c00c031114125880c68a807803414004924003040c58085141d248126100000c500c3c0740c41000f013100b64082c246103c0001100c04007681c000c01700810080c80c03010012010400400c65401034000d4030f110f072070300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 263240746 1250 263239496 263239519
    0x31f03060c0c020a0e01030206040312050d090506060f1503060d0302121c0e0c0108041101020102160c030614090703021e0603240f03030d090c12080415030b0d02040902 74
    0xc2008540d80300301c1d00c0d40410b00c1c0e003410800794601510410300034907021952603d20340c10769020900b40c1c099880002d201e01120b03c42188082d0044054a8040c80d0311b0a041107901098240207546000075110300d8007940c04510000c00a06100350b1a8890342241c0e4102e9103144ca031102405043c001c050003c0e4118041c510200b581d0440440c010090208403168180e580d02100400204a071032182c59021903a012900508059801c56040b075801900301c40c42860340d49a820060f80607104000c00c05090b880d107009940d0420626042c0c1509890044e64100401005c0c052a01300a24080c1c45d0f0340309a07070046c0c0040005203065440c04090302041481c803800c900498011038041d800664a091500801d400c9080118000035102d94603030604030380401c1e5140300000420b882c3d2089083c0310024030f80f981066001e114104039820018103a4138081150142e01c0d04010440b60043d0003403213012480782041c81140c1c0d1003401f8184540000400c940141810341e0b0801000b041100d604a030408500c100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 263241996 1250 263240746 263240753
    0x2030c030c03040609170c010309140f010e0c03060f280f02071103070609180e0a05030a09051503010504021b01110c01270803070e060a090501180b031f03 68
    0x504402003800c0001c0d43c40d075003042c101400c07030119504040d12204851111000104e00000d003090508003e00380050030361804e0a001a81d446c2c00d50242e03489200f204c0200914040560012040000a030191050781e180380c010141c03100d0b02644c1d03501c00c0c0307844a00480c145e43c0030310600c584e506142c0d074121a07115980c004c140058070683d02002000396401718106041c40011500344018110440151525508100e4007906041090140d2031010840094202842d40d00e075000c010300180041c1200d001810034500199254081d042610000d661410001114240403184000c0380001c1082e880c10350b82000240030003904071000c4400808401d5244102c40d00b000c0c4580d456002c9105012035640c1039440c0e049081d00c0002c80041c0780c00250a0711200c40b68441071003000c14641c800c0c3ea003035a94a4110040f10031a0500034a260320000c001a0010982d401504407001c132002030321403480904019032081d00c00705052081404078441040042e160400a21003540071199800301d4a00d400c1e1640c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 263243246 1250 263241996 263242003
    0x10312020a05010f2309030a050a050408101d120a110102090a0806061005030f01271109100507051002030a1e0212060613050108062121070b1602030c 66
    0x1d000c05111175845010403441c40c00d001d000480003558a100355a60305003044019624800c0c01108002c03c10701055032299540703d01c0846004005800403540d0170070000c0c00c48001041c41c014000e205104800710440344200100d2144448520b0004d01410304000300700c242c4a0140c80c1c00740c0d00503550308000445a0f59035102c407107005804000010304903842d0041c24000c200d070401d100b0170140501442001106113000c0311940c152500251802d10040740060b00030700e4000b003401284d03020b5040c00802e40a865020024101d0254210746600c0a502d2404042d140c034814680d020700a60401d001004984605800841d0401038503e40000c5405000030b42d01d442551102e941054160001034000740f5198008840c0e800000403507a051601d842c40401e0b600e880d84c140b00b91414406440d00152039030b5510740e0382025038904076004581c200c412003185604d03920040c44100781c00d900401220001d1101c0d41c240e60040341d0020250b80c503503d442c035a50480203014100d080440c80100710086d070005013030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 263244496 1250 263243246 263243261
    0x70f0c02061b012a110703022701061d060406080604110c01060306050901063302151501031109010c1509050f071706040f060c020708070b040e1509010312020a0501 72
    0x341800b406810050302081c0c0c0018001300d20404020074151007540c241d1000c2103680844e9030448800d40000801030011040310001051524121141000058100e8100c5001d50380e0300040b042a0b200310005408221090141c0d019550024500740300045417418503a0020700d04a6251403400d05101d003803030b03c207030942d01c9582049512540b01d8061041603442406030304060442410b962108800d13040800b0704142c9100750784030503c22056251541c0034000d1056000c00803060308200401d150019202290705520845140000d20300300d51010240e4400c4295000c00d10705a540096540c0e207a01d4000012003002d0f10001865a21405c032400600c00300807038400100c0102c0903000440c0341c0741803100c1a8820140c069056001441000005550720016158407940080001000704a5000480c905201d1303810032940c600c16001c001c51102c00c481c0c0504116000046506070555403140000040624036a446400000c02c40c010700008621115260145190380304403400101d03181c880c0c50030340d03420 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 263245746 1250 263244496 263244521
    0x20721020d1b03020405010b0a170c0d1401030317010602030a031a0a06030b1915121407080a0f06030f0b0c07060204091506170708060a0306090506090105070f0c02061b01 75
    0xb000041003141440d00415004010040d0f4050030f151031988040c0c001c150840c0200500d034012000108161040000c1d501012100c03401041603040c2441e00710b66540b001c1c0400d90200d01c0d500045060324100c0f000e241d040c1c5d905680611300f05007130b0110030b80180c07400c403030b00000185520f0000301007610b07030f2400d1074000e02c0f00f07680200380c5c0d41101050105500c00d519440311610034041c01032000020305035410040380d50616150000086100744480181741400702c90f1000344042e010721140b1940000181d0050001110802c80c80c447d809115080304c0d40352100800e100c1c4d1100300400450f00c0c1c406e6071035000c901c0002a03450b1602691780e6200b2640990000c01003260340701d0311441c81c1e1511104140c09004e182c01c01d6041c3d0010b85001e00e00071040104400d080206030000521251551181180150b40c400700601072034a107481e147c6c2e22520110380e00385c80ea62070b06c00003e41c080d1048448450b0100580ca03100300c284196004d001c00c0794018003a4035290003080094240001e0b0900c600e8108848 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 263246996 1250 263245746 263245793
    0x409020c07030c0e010303020304122d03200a02042a03020406091a0d0506061c0e06061512150a030b19050610030203151801060e01020721020d 63
    0x114900140c1c107443c5500602c0821140c08014800282c00000711070a171031080500d02e101c9801071030215008540740d0314a5241103da20f020300c0e85031050541d10401d080c465100d0401c80c01c6664103140c2d440c5400c103a003448650088060300050b082641c040c1c2465070b07068258219401c050102a00204c6181c2c03200c2c00000d5002404020b03550703102030600c001e07150803072003000d07401c1c65010120414014282800340480e80d41c400305440b0383c2c0741d104450880c61000c146044400300e052031030300100743c8260b111460340220740006d40185000314010b400803d019284030300300760140c3e04940840c04001d011101d05024a10344186070750fa8804d800008502c0307010444440d10700140c880b01c001c0890600f40c9802070600c82070101d02e07138070000582a60140b500c1c0040e181e51b9a41c40e0300500d81d004641e00c94020755240c01c180481c0222905180c1a144140c881640c00341c1c0316401242e90b13000d0351250421010314840c5582d2180d08605d0f034029a640000c00605c0303503601903200d40400c00c40c6890790104058 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 263248246 1250 263246996 263246999
    0x12021314010911030f012303100b1503010b07140c090c0304050d09050a0504020a090f0305060621031e27010e04060e040605040201170c030a1404021e0102030409020c07 74
    0x3a41c061414003e5400140c5420740c2807000d070040e01d03402c06009041002c4281c441450362007031700a10640403010001e0481c0c0071081c461910100404001001d14041e5060040900341000100100d070b0403101c0c003d103100e24040c440c1c2c959846502c1c01e50805081801814846030036562070105d4980100290078645540e82090b107001d074038101d00c10005200b03100d00d048080013070b603482070f030402c00310f500644d0f000d6507641ca042001c0300c20600ea40c0094040340718401d07001c001d0010000320340d440ba80041c2c03400d80e001c0d1403a81c000c984034844c0c2c8081602940c01002010900440c082103a402141345450140c104650030203035480e04454000385a1030003403e540558815070340038140e400210010b98040201500344803005150400040000e0900b42e01c1707901003030441e4405c880c145646003071103411000e03500340f9031000e8850b68400c0e42c5071b82986091581440d80d0b01034002d400c1d03006603401401c1d04150720f01001c41e03500b122100001c4d42d040d404140000501e0181500040c80c8041e4614068600706 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 263249496 1250 263248246 263248259
    0x14040308161b03050d1b0201080703020c0c03060a0f0e03040b0412060e010e0c010305070c0f061116080304050c01051204021e06121006051e0d1104080604150509071202131401 77
    0x8101011603081e444817440806d0016076002952682c10064901d4091381da410440003480c0340000c1c144415405202c1c000c03c200c00700040c2d9206481805640b00181f2030079044c043c03240ea0b01c0c00b076801034002c0c0040c2004200400042030b403c0c00540c070b204000200b016440c00c2100f80c2103ca1316200c8001503081492081010740e8144141d130b50228190405e02180c0c4000d84401030350840d4108020016592990b91202c26280714044e140c1001e2041d10002540d02d580c030f00f84d9039a80060f101105d40f84a0781520024642c001c2c0203845c4003005201007240c160741c41d0b4081200d010081c1030481c07000c00c4071100c04c46080d103804005040c2c144080f0740240f49070402c0c01a2044001e00780e4041300800105010056103140085031100b0000300440301651035800d6445080f000b04038501042c20440c0d00005c00040c694408a0784601c03171409540c414030925450041081030340c1003220f007000141c100802c10310841d2318403585a0311190020f002020440501541081262816100420161040e10040112 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 263250746 1250 263249496 263249507
    0xf20071703150a170c010c17041e060503130605040f0206191d06040509090f100f3c1803080613090209150310150614040308161b03050d 60
    0x6001c2022040070160400301185c1d1124034050406040020314082d60081c031652031034602e020182c0006003076913141e498824032022800a100701c8035070b8041040010348a409201030341d100d00c021604110700500300c0d41d6600c0081600420407141e060300e07480d4403c0580c5412015000c081e034402070070a00e102046001a040814200d05540d11201c02030b545c401540794401070b1422034000350703030400e030b84c0e00c85005050600140146280161041c3c192100e02c00002c0c1d00000c001010314802000442d451050210301c2000240392202081d40d40108148030000044592038200364946000a10703804a200312020003807182c0042e8006040c1405018052034000000364084802d407104100c804113540c0854814003004080d00748a00c100d10140809490a00045203441c4842100300074850b04050132840303401841c018000005c00700801355007042c5a08084500756500300e402d0310306041e003488080079161071155080701c2d030111303c40c0c3c20081d84030000700207805184200060160030300c048500414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 263251996 1250 263250746 263250749
    0x310b040303242c010b040b031801090b0a06060f0c0b0709080318010318050c0f011b03020f0601050301090b010e06060702030a030504031b0302300d0507060f20071703150a 75
    0x1010901ea6004001c00300501c1700700e4044481902c01a0b07129691028112605810000c9042d895401c088010b410442080d5003144030700798a00080180c552145000c9600311100b00b801004581401400b00200300c080301e141d0b82c081020f15045200c20341350b540380350071500601440c10820f1a040740c0c0d00d050790303018010408041498120702005120035200c09035100e54410500e40140d41070621180f13142d11a82d90f81c3d6129074009541c0658050a1500a540303a440002e903010a0244100119180c5018064807a6098000e12007091903400d001600c0c6503010040c00c02039009004001400060f00c06026130031041d402070715815101d034079508008285001c04607805460707170105082400180d81c0c001ea00100302740920340c01101001c0b02e0020b030241d010309046260141c850b0b16640183d40f58054010411903103d00020b024400d0244e905105803401c55428003168140b80070b00b91044c980c400c0c0a0000035000c0c100c00300c035070440c0c0fa2a0624940c4180ca0030007800d2401d407240005030415010b83c40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 263253246 1250 263251996 263252069
    0x26040305010e0f250b041401031b0c020f180702030c060a020f0304120903060e0109020f060301031211070f0e040210020706050a0302160605310b04030324 68
    0x8080420300306079440e0008002c0e60400c0c00030f801c13010001041503440c01d001501a11011310782d61a1504807a2181444540070f40740083e0501c0405c5160a0003008c0901c0c0c1c281c115200c901d034640d000c1d0f0070868a40000e0940a0f042008070750031141c0d1001c1c14144a000c0d0840d07401071503a031840d03a0100303814500c008003019100c41c01007206051500058080720f6000e508070606500f192012034080303804240551001e0061410080f0300038140342d0642c00b00340c070a8800c44134000418108424441c1c80d000c2440051f03c00d0901044d42ca41c100c1c06a040446024442c1040d100d2440d214603010100d0403054009500c24500302c0c08004c210b003000c10300000c808501c0e0009142061603c907008210307124240c0448101600400c03000700c12002e44c240200da6590001e004d028611f04040c0188051003100b007069911007c4000700c03c0e0a88200440c82c00054005440410641c5d903511f05a002d081d03210300e1081040e100c4821045148503c00740800a0802500d05040c02c5503a070424103240329801c1e5109 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 263254496 1250 263253246 263253253
    0x271905071208120702030d110409060f0b090609061309140901050f070e06210403141e0702460506270303030703050105130c020a03080426040305010e 66
    0x21008030b260001650954101124200c1d001d81c0e030034400f01c2c294059002c01c20403c80c10610141905414000030700142c81c1c00700d0080029030780d00c03040c01e40100303407030300c42e8002c11001040200310302d04004c0010400c80e400540720a01e06018200002c551084583c06102e2541e501c1d01001a0320050106564111ba007080082c010381c1404107003951031078000350000c001e010380c0054561941d111030040c1c581c00c0152038251481c2c400c2d108090001c0341801c07901200047d0800c8810031142e014501a5480003000c1405124501c800c1c0302c40145c0365101003426a400144240110140c50004580710003540344c2c01541d18200b00c0a0458140d4400d51204500f215042c1000600041d15a00140c40740302080804a40030340341c5c805004812000404c100f2500340c00000304021007950544c000c1c904848050f00c6403581e200980300c0a204031511001b000e030041e00950100000709100d01105500140219103506801004480200d240c103584c4401105290020404200b40700d0203210301500a48910042c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 263255746 1250 263254496 263254529
    0x4060b120d02010b0409032708030408070512070308030c0d1e1b05030601020a02061308060705030106020f010c090608040507050301021c06120809060706060504050c27060327190507 80
    0xa000c1829410440200c081c00c0b080e401c96022803c8c5c610700040c107802064a54488d111864280ca901950050310302a10701030701c121051101c0014820b040305d400504550543d01c4480382c0034420f84c0169001003c95465045645021002c501c90f83e0950b88001c4000a0402d2200956004d5164200c80103041c0501402040f44c01e0b40c01080424174590b04558403581d0340c084900082080f1000e8000e0303001e510a803c104904150171500550582d03001e40c0840d840c1e01000310425003651b410003c0000021031840042024a000d1005d964000f40702c0d0381036442507612040400d0884c2c10506c41c803202c08611520000c60095280300710310241c8414004044204142e4441c0b4211f84624001c85014010005080301440f4456100001622000740b05004504040701d62040f9034000140321040d0b50402521a503440074841c100b002c1e1940c01805c40c5055990f100040c482100b42c400d040c82a40900644410b40510244004407120481209500c04030031103003070051800049420448166004040c0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 263256996 1250 263255746 263255753
    0x2010b040516050703020307150c08011a0a12020c0f07091503020d020f12060108061b03190c030f0906060305070806010303141303150608010b0f150304060b120d02010b0409 76
    0x160300012035803810110380d40c40c020700e4220f25520a02d07201818040705000340034800c1c0c409d9040002c208c581661018050307625016074402c440b0b0340d0340c0301030101a02000150b003003038001c890007050b104240d2401400c0036000d229603410300707401400c1d0603c1500b190a0a001407141132241c0e0b000b03c608580240c18580c00c6034045001d008800c503001e0310403611215800c0c001e035181d1038420442110901643d000d940d43d08421691601c003580c114030b0318030203000310f1420b540c4500182e0b4421400c1651601043c07980d8134142c0000c1c10907842080c109900d40091121000490203005101881494000b0340d2610350b00708035040c680c01d90848081504100c0040001c00da0011180340240c0310040490382d40c89030b41d00841054801980000c19460708507500034840e00e06944000119586c02c1e0003441503507600410800000d031064451903001da08250000030402030708000e0341e0b22510a40d000103040084100240d0440c84200e4881d07955408040301c6040c4c680c1c2800342e11041130050f10140810b040e1641c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 263258246 1250 263256996 263257021
    0x3070f060206061903020d030507050105130b0f0c0c010204080a020f031501091505040509031b160e0a1d0318030106140d0611130e101d25030b0102010b0405 69
    0x240304130301ca0809000d850380300490030402d003c0190b600421036216800c131860043c00d1034101321341c05da40342d5180c81c1c005500032510102d0200c0640c1d00208403022603403031800001101902905c03052031030380184070785801030742c3c248002e001524030720004241440e882e1041000c201556085107000748c00c4035100205404003000651705540d00944089640c1a107040900c04e4507409a00031541300d401d18050082802c0048020040521825038400b920a06043d1b26a6261080340362460358005004080242c0f0107040c0700c0303a82008a825010611134a40420440c020302c11500c2043d19400006092035440c85145400f2802c00c0e06400a0000900d010904681e0382410203105028452042c1090108140d90f8004044441c0d10f120036911000b00300d01140184007140036201c4804140740100d600d0702001c414210880e11214880d0050107501d00114141034800b821103410031810310002d044442ca0314407440c01446071550001542c0a00500081c25a0300042c1d0250090785010f0a00041400c43e8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 263259496 1250 263258246 263258251
    0x30f030f120408090409032f1c0c0605040c05030d02010612031d0a0308030912120601200d020d03061202010906051c020d0902090714030f0c0409150503070f060206 72
    0x51280041c242d40d6420246514440d00f004194014034099440081581003580840780225801b101c51960145404510f102000c503480e04281c0c1d400495045104040f40c0304002c41e1001c0c5107003481c509461a074a04054030b0302603a044882d600032240610071424200b00700e041415540c4000c0c45114508140c2001c1c40c0706110000d0200142d40c1c0041485200301e12044060b400040c1040342041d40c6c0b4180929a0f400698102140e0b014000d00440d0a00b040c1e8103480f108502c040c1d21800ba901c0307500054030038840007915120140b0040381002804802803100c080c3c0c0e0101500a04101080304c5801011070340540c000c0b0003002c450005034000760341e1021488003610500c0c01c0c41580d41c4040d444000c40140811040c0750058000501702002c181e403900120b80d164030943d000b407019200e90800341d8039003181d60188910440180009821000200d44117a046400035140c185003580b240380c44001d5480350038569a9a075a4103e04001506080100000900011581e0a815810854020b4079180302 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 263260746 1250 263259496 263259517
    0xe010204030b160f080709151d01020f070e1003150c02010f0c020307061a03010606030e011404170306010c0b090606010e0f0604061d031e010b0612070807180f05030f030f 75
    0xa03240000c0856010360005c0014146803a4948042c442c42240108042c032124689e8103140b40b02840b41d841940000340c80000301c080b100c0507040d52820100c0000c08401c0040c40c006403400e0040c000008201044000804160300910100f140510200081e0941d000018000c05162901d003400003400d03800300a45404e50382c80b082c045524240200300316045101001758543c19440c1080c0001c84036050751064080340403001c02400006c1d00c0c01c6240400103800c07a0007410710041d401d890f540140d0083c000750b50010050500e2600e105054545400008040358146090303845441800015a00615010480da400301d4040200154044c0490b11500651103120309003c0040d001410046c0010703141080c0e21b1001d011214038a80c1c01c1c104070403004002290900c0e40d441c21b1015052402c11700111580800411002c24041d03d41110441c0d00440c001e00202c02c22600790665038100201c11300a00081501072100c2d02468102810181440c05408520300164070070841080b0780c0d0070000c00d442c8504d40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 263261996 1250 263260746 263260757
    0xf0f060509060112021e09070c0314030114210a0c05030606100f0e03120705030301060801060816110309090f0709060201090b0a0504170a0327051b0d060e010204030b160f 75
    0x800f0030720780c1b03c504081c8001c503621100000800c200c0a5000700308103e150f00a581e2005803800309840602544002e00529080c41c95800c0d264455040c075140c44003c058110080c0f00d51411842015420901e13441c05c119600c200c0040c0c02c02c4189801c000e481e800190440e06426400c13203910002e441c20101070786d40014400c1c80308024070590303014401c48003110701c00402140d84804624009480e54001d0080102242000b0004074802c0e01c244182441460300718021464216000400e41c1e40300d440781d4800c8518801003240c100d0710344668a40e50b0040f6001c042c481c80f103040c204005024890150800000c6a00d005024404641e160100580201e801c00000030240c50b981401c510800301c491803180300c41d000051000129925034040e100c50399000b011203151700106001038446000414001d001ca6010311801e01010141c0c0380e56952181c13006220010940c1c3d00c5ea180030594013031650561342c9075408036003002400540c0011341c2d44801e0700c040480241038035090141c400300144000d00d0401c81c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 263263246 1250 263261996 263262019
    0x80105011809050112140d050d020325021f0c0914040e0a1a13031e11010e03040504140c0301030609020102100509010c0f020304080d1107030f0f06050906011202 71
    0xa10185412002e01001201401550384820340207440e28503003842220300301c000c8000c400e513610307022412900d490015913803549400140d0030288065000a00a54400e0b002c1c0d940380010204044921032405c0c203107401a19072a2209101c2000120642c200803d10900744240701d00032660000500050750241203418180c00d20120201d0014000c10415003818800c240b82d0000788811610780c0358440e0b016011941c0e01d1707038403215651180204440004c010032039403e16001c5142001200d1200880f0500c1c1400c2c440e04c0c00041c050a603643c9100c2d25140d6040054140b01c0c42c00c09006085c4007030341d010100c00c040c3c10320b0041801d0328441407001403c0320350744894150031a031080c0828410300f440c2c200180500c1c20030101040c020b21016030703414045030039917000e80b40c0c850000c03044d142201c69010140680c804158825940070401040d604041e0003148404400210300070010031000d8040c50301c0d6528511280b404804840010304020070b55449440100501d81a90713003106002c42e4141c6a194408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 263264496 1250 263263246 263263277
    0x40b0a120908030117011a01050304141f06091107021804030201060906030605150306091903170405151302102106080c03190f0f02010c051501061103030708010501 72
    0xc1103801401040b00500000005101211900000e6503040250081003100d900340c1040c14420795406246020030b0381400003401048a4240e101d1200300b81d10107940100c0d11940201c00940d00201a10481d030782d4459051000c2011403060700c0c40d0700005101caa144c16102d40005142c41344110503490001c0c0d89000050415100307410400042c0500702c0c062001607100e00c0c1030b00281c141121403070a0300c030040f050400d9610f8000741c600d0151070104094024501c80109001030080c00c000140c003440010010a0400009503440520440c09000078140d45040f0306901c0100031806858004c070080301004000269562400104120202e0b003881904035207081d48802c0907506855110003803528141000502e00e00c0842c3c00700d9885802c03801d50b500c208000703d58624406580c0b4014005032080c1e00040300299800000004141c01410518442025a620300d0702e0316400c119080e1000c4c016200401040350082001c0c6080d00b80c040146040d4604000c0003000300e01c0c14403865040115141040055 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 263265746 1250 263264496 263264501
    0x60902030a1410090b0f040510050127021201090506010c080316090b1c0f230a110f0304080a020111220501111009082214060c0307031425050601060302040b0a12 71
    0x114227540103100540c5d46540301c1d161f00ba04c6606038020355807035500302513009003588221a11440d00001c3c0d40e0450b404d046846000b0100200b0545c10701889056000101e8211000f462245800c11a90b281040880000411038141d0340e210216000f000e00a0522a800084544240d41c8d08540000703000101c002c040c0c0c1c080c218580031540e008210034603542400b1600e0000c1c911a00c507002c1c1c103000341034071240c804825209003814101140c50070b201260008150310001c0c1001c80b42c901c00030410090b54150b55095610520080c2c2c81d81840c030005800070340341c5a0806000708000d00744240e469180c0501580c035510312804014415640300710510802c00309405031410300141003603102c07000600100c8040c03902c249004000401c5108007c14929181c900c00300e0394003990031070195003003081c1d5580a0741c42c252000030941c10b6580611010071030340c4400009000059003400452104801c500740581000d5041c0c000400b01801080203101244c1d1800842c0c1f4044a60f140c101076110007404ae8100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 263266996 1250 263265746 263265763
    0x4031205060312040909350903071e0306050f130f0f060501090e19121b0f080702010e01020f0d0c1401050a05041b050a06050304060902030a1410090b0f0405 69
    0x269010302280104110b441580720045041c4600302445075410072480e41d00860034240014903640300d0101d49440701a2400002e00081070001d8100c1c0c0c0c64ae03031940c9100300045c0350041c0c41b291b050048481082484020700447d078020750f0403c0e0080450900c15083c0080c0840c90a000e040705100003003034410850720440000441390002c00821095031a4403111005d4580c2e4202c2920a05c96007242940e031b00e40c2c81e0b000c0840c19a01100c000b16410000d9400d5401c600a104520318202a80001d000811a00314040c0580c0e441404101c0d41e030419440090020084d11401504540c07200501c0302c102c210000700e0380020021420b2a19001c41d4510300342428503081a41c1d907030703a5403c5c0014401c010910380c101d0b43c01240700391103210503800f1000701228443d00500c40c1c0c0d80d21101d0b208042000c2805180290780083c02010081512205074001c40d00e444800002202c0d10400d542c80c415079041c090000c0880c0280c44a0140030604403078648081d04070024041249940282d00840c04201c01000341c0f0783c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 263268246 1250 263266996 263267023
    0x311060d050405030c07050111060a110f04031b0e0906220503070b09070501080f010e041401140406051b09060307031b020c01021501060f0309030201020d020708030402130203040312050603 83
    0x4858500383c42c0058480d08001444d002611950340c010a0540c0640000c00e0042400c01c002c108607510100114058540000c008201503820440031403145840d9004002550090b000d040145007620390503207086c8400c1c0e1250141410b150107102190340007103141500001d0b0164810300001d00d160809032008a1140002e109100c0081c540c001c00070340d50744482c03040b980031040c3d0f04c01d6603540b8010350f00807a040b0b50003402c405e400c1c0014442059001c00190700701c1d01810003a822a030b140080c6608403074198010941c81004941004104020390240650081c0c00c100403155554108440c900940600d99009105403804000551824426403040d543d040d00e40072050b402c5003035413101a49403082d125001d130044c0603800c08000146c94040100f0f04860241da5104078034060224201c0c014240c5003400c6045540800240407250342134006420780303902920030b00b9034a0802e80304020790b006002410204d954010710070080401d80151031110004015440801d01d9621140000d040c4802e002d80d02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 263269496 1250 263268246 263268251
    0xb06090604080105010f151b050a0b0a1b020705150d11040b03070f02060412050a1202031006020f0a0b07140403051207060b0d020a09020d11030112030f0801030c0311060d 75
    0x540c1503815044a8101c502c100f428005542c0c07651f440304a03042110300c41c0030110f80007851698503586c2320050340b01424010400c0d1140254281d80f41c1d00b2000007681e034141c1e15a1604058403007200c201c548803900b006540003e055280c135002c0847c45840844880124141c0085017078900041c942c0c01c04441081d5000380b1658450304c03142d40f00401c0d0802d651840019041c4010b13103184500001f15580900d410644c9071440039081031003111694401500d8404001e041000600880c07903a00155020720403015490603414200036000380b0300104c000c0400f05a90240c0100303808100d035034419641090443c500700c48007024044e11841248520390009180c1e1166051919041149001500c22903215a005014000407481005100021100b02030f5100c403560004124241d803660041082129031100454a0307241b40c4905103050304264842c04000e240d18900b1810964010114103903203482d0b041010f581e5055031101c4801c0e0115000c014054030045881d1440c50343c91b1000e4900300545120107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 263270746 1250 263269496 263269499
    0xa05090a0803030405071a180d150b10080f0601030203040305070506040b041e0c0e0910051e09070b190c0807141905030702061b1006030c23040b06090604 68
    0x180e50b032940111410307075080c00b5501d0f003c0740d078a1000400211200c4002c40c43c034140640c010100401d6500e5484071a4040404401100040c0103010325194092000b400060300343c080f101848640c0004440107010800b40b0340411904129140100350040c03400e20303005032a90383e0352070152032502c1404d0016005218030010001045044400644a20301c1000072403050551103040c0c100d8214548801170080100340000d200c0c031850402090b41c040082012039043c8150345038181c2c210b03007094580b203402c041320120325411255064425038000850800400e200340c03030802034500703a02500503000d0066a140c00340c50340d41446200700c0001c040d00600842d540e1085490b281d8220310440f6100041b9024a00280b010f210b08080e91480d066080f0001c4c501e819069802c2000d1580a05680301107141070080340b0410f1001004298000d28564200042160640c00c00000c0e410f460f038401c0002000010a5440780130b00b800c0541d070350160a981c0400c200e420b0a000410a001d01c0100740c1c1c120a02080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 263271996 1250 263270746 263270759
    0x190c0804091a151903060902070b0114010801080717100e0a0303110406120504050708030714060609070c240f1a040203011d04081c090201111507050a05090a 69
    0x141d1440d40d00044000c0da010149001d001d881e00082c1c0c1d00e01840f50381806641441300c05044464040f070154070f80003514680310240c500480c1c00407001a10804916001485005809001c1488201003420008083d41c501600c02c1e03640d070020f00903000350400c41c10512060040400615112901c0d2400a00c40580a1072100e07548400c4443c050740000d08100e10340406c1d61010048409039400c960716803c150848000100c0600030140c0100c40034400e8201c0012412402e02c081c00314076201c0d925a1114607004c1140303500c1c02d140580814030401e602414880d246812000c2d0032249a800806802404001c2d01c40c1d0344550b01101d0030015890030300c0c040c040c0e140c1440c1d00085244c6034480320095044024410700c0224042401140f10b01c7d000d072aa549000030820038025813291044614030701e0300301440f01c0403a000355008d242001454407002880308540c0c01200d98070300076652000030a800c10045600c030200340c402800250601c8000100803008910a100b141c203d45400381c22816025501c80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 263273246 1250 263271996 263272001
    0x80a020c06040e060906090f0c0702011403070e1813020d02030115030302030316050c030711150a050405151c0f090b103204020d0209090a14090c0105190c080409 71
    0x5410314405d09001001900c6842c058100c2030217901d0703c1041060382e079a10201c02c2c5c9079501c107100aa050250020800074150000c40055114010720381c2c81c0000007908005000b1500e444c0c600311440262418200100e6900c408040600107404540504c0910301c68004070340106003101200b40700750750170040802850b8002000b035000300c12500404040c1a444d0a044500d80030700065188550003c105241c04190340b14054141c440008003012102501103151500a07840030030f00704003050b4041003c00c00c2d85010700c3e1847d11078114203842890b00b54419065020983e0185042c0102640e80c3c2c940b25408400c3d42c46040c030140e01c80754848283c2401c041c0410342919520501d510121081440011800b0540c02012158280e14035440079034040000c000c0a5040500c041c0040c41c1d0074420802c550f5a402070090064200d400c00055110741d56940e20805a40140365004a600c40000c160702c07664402c0c00c5503130074260044a00000082c60204940384280c040300605825000320703000c1000d01c42607 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 263274496 1250 263273246 263273251
    0x4060c08070c0302070509060613230d022416081305010f09120302031347090a03081b07080a030804060b03010f020c0a02012604080a020c06040e 64
    0x1a140e001855840e00300c2100ca100c207101c0014016004103c00304964141500160b800c4a0001e265a0a201d0700251038668640c1d164071038009030310080da002004641541d8140c00104058035281601348464002c030380040620f204218040180d18036591009004a054402c201244014241d10884a003015005600261403a00d9100c95032100040c0944c01629180d100c4186616800503552500b4501d800c10807040341c0036401d40c041000091000d000c0041c406c0e0207880c800c80d11440c140082c2d00061310070045120764aa00102e8145125002041000c0d07180c01c0044115200e43c4d5a580310300421030301031840c0c0c40101805004101c03544070042d45202004070b0b011207000c0303a072680d954001c3c041d030715501a80040c1c04203846402103004a1500c1e00400380c3c2090280000c1040001985040101c4c0d00c201102e10164200a03202411036034444d0b403845030103103180d540d1450b030101d0f01356035040403501510042c00d803400012420720700ba00070f01404a0317416000701001d440d159079494403003848408 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 263275746 1250 263274496 263274521
    0x4020409151a04090506011205010603121e0e01020309130204030f0803160e130c0201240f051f03091a04060504110d0c03060e07050306041202010b12030904050c040e0406 75
    0xb814032040c2c940c1000d11901c0411608040100040d07442c211144d081c02c2c00f400c0058400f55229000400490100c0070030703c505125617a40c00074240955054010400c070707100b0912007000200c200c640030603070313000040d21a0104219480014086c03c1c2d229200240b0450388002c260740b480c0d40300030040c020641d01862107500c2145100c0c15101015000b01d554100b1a04410b511000c1c003111a881c0184650004500c4031071400000ba8480e0703240b018007912103095281c50202c40e0804e109101d0384803110305000040c0b0341603078105c015045030b20202c00e2440395100110101603a078100352052001c6103801d1841000540032180c087d0a00e814154040d03c411070f001e441e00f514080112000342050250b840c043c6800070300e00c00b00e00b815656042c0243c01100d000c02d0151042c1d4401203019582030000c1c9004620034001c01c494028107c1c0041e0030344040395043e0344600034040314402c18000100441e00f401004880014841e41c0300100d4000c1d0f8022038100702c400840306000c00c001c1000070340c841141c1c0d800303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 263276996 1250 263275746 263275781
    0x7050307080a03050711060d051302030706090e0414031b070f151d01020f1905010b0a0f090f020f040305061e100b1c0203040b160203031506030402040915 68
    0x84074000260b032803241c1d4200a000481c100000303400b18412200f0350034a91401400d080c03030002003940070416500103a0b81602030055020f4100c0451800304401d030f008124a040440e0340341d1802d0940c00e2206001003028003c5a5440d00d101702248003482124012400810036450322100c002089030b403120382e4096604201c2d9080702c04522900d000c0400b8446c40c22596a90000b8480e411841d00e80c03201a296050540c4221820389550700001d001c5025800280400380001c82c1c0349040a80c25500025115030160b030410340c040c88115100742e607003000c1e1034810001040305064030075400000c0c03080c040c14100e840d03004200802000408245c15014100142000d0000c174040380b5003080003030341510003003d40fa42d4500100824580b00c1d000d022503904924080c44a0b10018140d407050b41e004490840f40100b104080001c82101a49840701030181440114103614026410354009103c174566180701d0400400081d04640c0e40c2c3e000964803e40c03142c88500c07051440122203000c4c0c9030314082840b182c40d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 263278246 1250 263276996 263276999
    0x2211030709060915050711090a02070501110322050c0901330f111011070c080a050705090c090a0303090504180f02151303080301051521130b0907050307 67
    0x180300f6143c80d02030b62031600e01c490030819155010385171544012021110303100f84070b80c00310440c0d9a1180413481140d0040000d0b070349000c01d280a41c01c44400708400440307100140103001a4681440c02810000902c400b102d039000d42c142815481c2034030305940c06902c401c11500110340d52454a089080c40300081003100121101c4800d050042d50034000d070301002803041a0001d072868070a07082c20490002440036210b2403d0301c01e581105454170270f40c11110030003000501c01c0030480c200052400400a550107021402d00301d03030760140c03580020b00c038a92040c1094008500002064012a015031100900c1880540d95a29002e88000c0f03140c464180f042c3d1402c000640d43d080200c52111065600c2860740a682d00107900b00708080f00d8012407000a98000e0040d1100c10346007101d400081c1d40200d801940340c0d071424041004071100e6031054007600000b030089003640c00c40c0c0313418100034003030303400e0008800d6451410366000d00d40d88000203005020781200307210748600c0c0405c003002507903400e030191001607 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 263279496 1250 263278246 263278259
    0x311091008190b091b04110405060f091f08190e100501031103030901020303041403070f1b0906080604032d0c0b07020f030307051602131e0c0207052211030709 70
    0x1844005064514042d00400c1005d103442d0641c09071042044042100d81003544034030114660390440f044110070303c0b03000543d444483c07070542043c100a88907500340034134554002400803e1a100600200036030307803443c0c521030444074164000000700c81c8032004903503030305248404107000340c4000e1000ba1403c81e0314400c3c11600303003070210491b100c00c2c80c107030011407031a215561030817990b940c01d410480350f6000c18460b0300d0008480c4d500d854040c5009019039404c48200c114075844101a650207180740a2410341e04000100020988550058050904517105541031800801c01d214010804040a08280c251068580c0001c102c05580b40240030540d03140d65000c1c410baa07110030040031030304103910034400507070307082d1007400100820030424140d000036140c294080750781c1004480c410000c4544070707011541c5c0034030040000c07c8a509200001d01140c1c04070900a07455007190300070b0078000e880c0d0302c00001c20881e600d40710004039040c082c3c0421060350040150119030304155402030004007441d80c005401c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 263280746 1250 263279496 263279503
    0x3160306260f03040609030b090604030903240e0f100e030922020f0a020d09050a050d031e080403020f01060501090e1801050c0901090b040311091008190b09 69
    0x19200910302084400740e801201903a980c100c010500c03540d1103550a0010820300a00141004107026150a0f104509614010520340802000034043d9801481000082607100f005502120381020317140142d410203402501005049001b00420700f800e109448203e940c002074444400d40c82c2c2d0081e21607080d1000d20a10540f00e40302c203806400d600a01c2a030041d45030108042c2d4003c01c0081502c0d1603441103804d400c003660050400c2c0300c0048000f00e003c8000d643c0500c4480601e445c3d5141014043c1d08107400164005402d0042038090880b424981d0f04141c007400c0759210100d0520f004601c2c4182040c00103203c44001c980480060054000d841d0705100c05001c0c031b00c159041611081e103510b0420903030441e0b43d070004110303814449074422050b200210a20540e0700481000c0701e019514444000090155545070340100c2100a0801041000c10f144803c0c00c949040c0c216250a501d49992004029804450b00440302d83e0140742e2811004104407007103c042680b140141e8040c80d550460402c5d103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 263281996 1250 263280746 263280749
    0xc030f1e060402130c020f06100f14030d050309010e120d0b09010f05010c021813110d0b0604020d15060507020906040207050a0215041e03050105090f0d0c0809100503160306 76
    0x41142130005001a801101d800400d100d031000c0c8100d5440c605540140d5140c01415a0308181c031900d030710001c0c081010380100c59400342c807012402021207000c48000c1707540d40c40700c1c4244008202c40803002c15178004083d0008240d150b540b1007160081040c02c00e0040c8103034452454480040d01d456410281401c143c481c50f4100d41c002a00b107001540380074015250901c030340104a9020881228540001c0801c0510b24001c91f06082040c00822062610303841c8850750140c400e1184640741034100003e0141402150300c13920507078026841d20a40c02c2e804014110170103507400324900e560030126640d03600401a01c030080c005c817490300550f200c034000d0004a2080c82000382291f005034503401c001d03042c40c040b4140070b891030801080c0fa140d071f104130406020020900719490104030500030424403000740a1141c0114049025100007111550f405e9621100703003203940c05021603204824244840d4a064414204014024025451503400000c0c01d943c0120b8040410705002c413082d40c1c00c3c40c8203125460 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 263283246 1250 263281996 263281999
    0xf281403161203090306140405060601030e030d18080f0307032007110a08010c2f06010509070909050a060501030c03110301050607060f0f0c0f0e210c030f1e060402 72
    0x1000c1824910b408680d01d80d400c0003602800005000003000510902c1269a140c548511441075810f140ca005820100090205810581084a01d408082d40402111105086014001500b01080700d01100400094001030000380f0b02040941c0001742500007188102041e940404c4a0074858022102c4415a000306165000c0188075120005204400702e0b100e03604010401e041e00d940d100c6000b401e42d42d0650040c1d0000300e009803010702c0c05221003500b80742c10a0081c50b640541d40f990152503600c800c1485003600c184c5070700002c10461409000c40102a000f01a400e00141c60003000b440b000d01000d1141c81d00103440c064084264034442c1c420b00c412100030a48152850b440e02003000096040050305840860742c1d078420320f104590030b00c50f0f018081e04c1c034000402c0c201c0440318080c00313200c1c3c40e204050900c400442c0c0c28099541d05da84c00d2004030100b038002081b2445d120ba445107040b410100f05030b014440d006d80c05101078070004880d400c00d0078407020810001c40c0314100d240c0310842900c1c0203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 263284496 1250 263283246 263283283
    0x9150c030108031b0a0c03060605014e0e0d2706050a030b19052e0503150d050c041a06040b07020d0804030b0a0b01050702030307020f281403 62
    0xc0c43c8100300d9800b0051050300c1c0c88100d801394421780e01c5441036511654401c407041c0741e0b1404100000e58001c0e0030045440490400da8141c0382089400c0c0b504c0d400c4a0480154000c00d18003055001c82d82d0380a81e19542201740010048000114030031981c80c0580780003c0081482a807501030001000804803c514003c812036400140ca4504140c03101d4002008030400c0c140ca40b0720440640c0c480c0707409421805046101c941840f40350101342710240070741ca4075545007403148c15084050b41c404040c050f02c030300710146049543d03507451102c4e2800c00d041040781c07640d020024202800c01c0c800e0024804481c540d04640402000d0f810003041e03160900d20b501c1c950b0f009842408204082c000c0301e4041c112032400584040c0c000e800f660b40da640c0c03903072007a041122043e040303d003407281040540c030454010000a0a00d503103020840d8001a03030b00c0c02582c3e0002d22454220030001016296480c455040034540d80124041ca12840403000545c082c50041d0412480226614945860700054104d00b107a41c1c5c0890 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 263285746 1250 263284496 263284507
    0x21209010512061c0507050405150d0f02040f060b07031d0f01080907150207060207050d1a1e0703021c09080307050d0b1005040801050603210714010509150c03010803 73
    0x422040c1c2034014840e99100568a0001010207005210200b09510a134080e1240e1b44c00c01c0c04100c00c41714080d0522804090000d0702c1075058844500d4040c03801d0308242c00740000e902a00c0094068020050a54041c1d41080d00000d05107002c040076100a51183d281e2070b4034000031181180f40c0100c022002c1341d00004a603402001940281d4190b0380080e50103040d10100c940780c06991000300300c4401070780d0059011200c02c001c1c9a50500010000e460b0407104145491800d03110248140503559504546009980114078442e030b0004a0440304004490328141a160a180180c020341040c0d008001d0090120050005c00c04d80b88079511100b0ba000ca40b403170442d140c02c40115030940000b00c41001940d618418600180d44000100100350702ca6a200c0d99510706101e505425964082d0840d8002c0e4810506110145898201185400052500c5503156451402e0145030048805003c00780d5520307000520200300c0d4041303680d80d140360f440e078400b030120b896094020045200c24490060140c006005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 263286996 1250 263285746 263285767
    0xf080f0f16050c070303020c0102070e0421030f09050d030b1206040b130606080706091403100c03060504020d0f4a061303090807050f040e01021312030212090105 71
    0x20350820700c0206241080c1040c0c81c491070545000481d41084c0c0c05a8050340700d0822969041142c68083d05600352400701d5400c00355034400b6100105120701e04550585c104007032030140300b948403582c2d480030404203002000c2d8a044c00c42d22212100a400c00113810202003240358100b0403038030081c40c1003010013014641d980d030b2580007420101a00039001c0046410f1810049a02ea000c1c16000e000d00601502403140b03040406001d07500541c0c011721404007201ca0040ca07580d070214160707d014030940404211042903134000c400502ca180c000c50b9106e031000c02d180d04000480da01580759180707401d20810140740c2c50720001008034045440b11810101c842c05000300595511030395021020351080800810102d00c20b4181880340072140d608044801500c10310078954001501001403803214064001036041202154480100380704050040ea110030f000c0e41c0000095045a165a209210000581e5120007107160130721140300c0c0c1600148210322044078804450021902c0e040342c140c4600c2d2800301e42c100c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 263288246 1250 263286996 263287021
    0x4120807030c050f01051609140d050721060605011e030e07031514180304050d1401091b09020301240210110a091205060103080c07050d030f080f0f 65
    0x4100710200710709100a50700290b42000b110058000c4000003007081d1034503500144411102c002080c0030806035510409c50704003540070140b0106000d0f24020070703403a41400c0c614036150450b4000c1c00c0b80c08800165481c0035110340041e0103c5403161034144080b40d43c88004440b0340c2c90103140161a01c510006d0400d01c40c1c040c1d44611a0015000c00350b403241035494444441030701d40d200c0c2c0d180505454003a08602c903c00c0c000c02c942d010341f11019080c4943d05180c841c642d0b038001e50180314025135181c000700c1c0621440007100150320000100901c07060110346402001c001940340e03e80c0340e611080c1401704000465000303580c1030303402e94441c9050150405400c456a0010700904609500614220905007a01c50050b042031060a141507a50360140c02c000400400960b403100590300d001c1ca107054005013020614504580d045050725859802600b2250300f800110740c0042d030b024242c507520340c040541203010012458201d4503152030742e5403100c482102c00d08080301d034200c40000740400500c06240c0704 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 263289496 1250 263288246 263288257
    0x21224040312020a050414150a030f06030b010303020c03062206090204091713050a080c01030b18040b0a0c0c051218060d05010503010506101d0607050a030f14041208 73
    0x24909400b146010b44a180d04a0340f0000407807001600c0000d0521a000c1e400b11502c8034500d055070349140102c400d0400c400a4054901010201078503015079030b141100540181000e140c01c03142404041d6581d2802943c0c4070700d15400d4500034001c100010301c1b0965110310240c0040c06c41c02809005042e207503074002c0140070f513003422a0b10554800c2c0e0080801e031021008090302406100195540c5881d80c0011900002c03030740024800c2000410502113103070f01048003c50100c00707017000300d00d40717071414009481d01c0d19040442c1d41f1a40140100428050500500381c000c90500108101094040c4012030300d400c020040030703100d41d0010f681443c801071220020924684612580800b6148610000714a5407080c2d500c040031030349541c01030109183c01c0c45080c1d00903604541d012500844284090701c0c40c0d00e4520625220841c1c00f15807080394451200300e40179203600005076204074142d03150140c01420164131a8001401101c404400310910104031000d80750b5803100c6074216040c982c0d40d040380e503101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 263290746 1250 263289496 263289503
    0x60e060912010513030e0d02011407060603021c02040c0e030d0c0c1208041802040e150301180b0a11090109230414012d0612110c010902122404 63
    0x52040c0d900703107034020b210301c1d40a181541015040700e409400c0081810b054110340510400a260750400140e800825060040c8194081d0329190303860f60401c07100501031940083d4114409000304030400c2ea008400c0030b000e0344225010013007514030311000c40b000342c1c2004505400d40e22861180b00b07841e000f80c03511800d15102d40480300c3e0365034441c0048100c42c014020116503840003c1000d200d40c20904070808801050002e04500b00b074540714411258850107000c0c14051111034034040c0d05070303c080d00490800d0780c04844040880800d880c182c21010005c4807552461480c00034006450317440e2104564000005a5400b031003181441d03003403030740324101d900e040c0041101e004440e82e654489004071200c0300f041c2c13071507180b89616007001482c00e80c00d40a80d41c0310186003652051601081c0c00150b030240d6411f4604080034401c05800e90740203200341038159403103120100b80320328081415000480664420f4403003005402505c484180e40d1880440407c6440961803150007a02008680c0b1a81c001e01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 263291996 1250 263290746 263290759
    0x1e07080105120c121e01020f0901050c100c0504320f0a121208090102090a090b2103041706060d020d080f030a0506040c0f080406020f070c08010c080f01060e0609 71
    0x1080e50000313120007094000464142c00546400c8108503d10036005070048240b0002e500d4040102024045c9100e4034048506100c001301d02005014000c000128513000e00e1501003115411104019010f80c1143c40388601c8060359001300c0125140207000c020b000c800e940320550441424000b080711800700800d032142c01500700000000c0303d4000d0641041100c0c00380141a0841d140004000c22160f0b004160503140da004021000302500c0c0c0b45009003c54030f19150003c0c801046e00000350403591241c0700c3c510304040d0784121000d40f4102000900c1101c00036203040e80240c003000791490b2510300840c0d280f584840c6100e0502d000d81022030080d2800c0e072203003422901c1c05940101515041c0c00c1a10085160382e52001041040d0820740b050050703806150815803880c0701804401003154000400040440da00403032020508103c040565440e150b1200c88034862584a0f4074460023022162464800a00000c000c01d00c9804c03001c0010f810384807103980e44e0305641400c40a026543d0b0045006980204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 263293246 1250 263291996 263292013
    0x6120b03060c070210020708120a052206090911030c03040f020d05011a010507230f030a0806030105010e090d05031f030308090c010801180f09060204030b1e0708010512 74
    0x36420302205100340741140e0055203c05150051208800000d00b214095600c5464240514940014010082901d1680427603556521050483d03031401506ea81012007690b0050044130003001258010603900340d84d4a403c5002d584642810a07604039281d04800b401081010070940314100c8019540903014010240c0c920308030340d01141010700320a00940d0b403a551076071002070a0002c3d0007848004c88003403034940d08290b03403915484500d114001110145000740c018801000d13400740071a4030760490307440036251140c07031040c0041c049050460310b4503c607520b42000405d0001101024038050b15101c8003e004c02e080b2540141c449a00c05004440340b0030800403060503030804000c0c9035002d10710030703580d500c034074100600607519003008041c207141031000500041c4040c40310141b0708000281690380104401c032aa1135060020040c080c000b5140600000f400f00c24055131180c024000c4000e4200c000c80102c50f400c8080c0440400d41e0101e000602c55030041084d4640002c010306a441e0782400e079203200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 263294496 1250 263293246 263293249
    0x7061d06010605190801060f050a0917150637090513030e012a0f12090e010b120a1a0306043e0d031808211306120b 51
    0x20302680a000003a100041011100d0b500c0e205035a6010881e0900c4481541400400390400e800c0754148c50801c1004140e900100c0d00ca50051801852030488110170300300e524050380d460350f03481c01c0e88031745062038030000c40c4d80c80c2400646202003202004540310b0581d80398041340a10b0000480300c0300c03580000180820010898420103005403000c0018200ca1400d031b2401a0080c038030020341c41d040c42160003903800c07680304e10172008c3c3e0f22002d0807642101c40007003840c01032140344418001604140c0030802c1c17102c03e15040704131b500036070f0700d00034160050381c0c2e070786c000c0101d10302c40c007910700e80a003020b040400d0345070300d441d00980300f1280a100000b048841010100c6c3c64501d04507015100951012140c6c02e403100c207100b080c00380c54850483d42e0b032207540e0303041418000500402c180740900d000310540c4003070500c50b50101d59144c15041d01200019925a20240e8507007100700c001012070110310404e0803a041140440303240c120007030700c017400a501e844c005a48600c7c50901d01d00c1c84c0c54031280c005005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 263295746 1250 263294496 263294503
    0x4060806060a060f14130f0e040309031b230109080a05030403060c1b0b010504050c070c031103030906070b090607050a08150307090221060904030504031205040f0315110f07061d 78
    0x400d82d1000b0006c286a03d468184c0340a100a540a90500d01c3d2182c28440400c0d0300c00000015240c0200048122440000c404800c404080e400342c05812010031402c100d1001081d601210300000b40c0e01d00c401d0540302e401c01a03c40d05da034800209950320802007040003d0703058000c010800c030075007001ca0b450800b4003002401180501e07012110075080c04c006010f1860035100b810381007d40101c11130305000c241d41d100c107010280c900010380304178016905c43d49240e504000329031842d41c0140c0340c00e0320359450f450801c0407954140c900300128019903001403401d5105100b616040c20440c1c2d10000349449840040500301c0c4200c0041d074050051034004103c400c410f00052442066404070401e101c0c03d0780c5281c160b40301014000a109524981c24000440d40c0031043c1c030305480d08140100024600c030901a2070a11850780400c03802c410107200082400311002c0c20b2101034014940610a91034090207040781c500c2002e01509400d801841594040341142e40a4042c21511619000c0807501d0308203070307078603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 263296996 1250 263295746 263295757
    0xe0903180411030901090c060f020a0201030504020301020d020f0c0d0215270607020c0a08010e0703080f1210030201020615100c060e12190c03050901210509010b04060806060a060f14 80
    0x3613580d1502d4030001042120820400140700b28682081000000c240c0251640c00351040681015254400320f01075540079030481e00341250145d821035480c402044a40d4450f004402036030064019040c8a00d0900d0022643d04d075442c2c1141540b2500e0743d251500600044448030036128011902c1400d2581c0c4402040010702500182d0000c0054100e0b035010800183c0702030308010142d90418000b0800c00b107001806505a0350300400b61070f110b072000c10074081d10340980c040348480010380c00140108031508018180a80307000703034250f408560382c0101d1807101100d41d12043d43c2000c4504003645900b4443c104054100e403203410080341603155061402d160100d0400d601a8043c2e001601031100e032040314190035180703e03a0801c000d980f04c041d24003805502890201506100e0341c2010100300f400c2c40f5100100c01401c0d2402040f1508105101500034207031504002e000e903180c910042119280041c100703100c0d410040040e0f802e40d0412604403110305184844506200c94541500d080c409100058070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 263298246 1250 263296996 263297011
    0x309041a0a05010e0a0e13060603060b0a3311030c1e0703081e190c0326060d050f0d0503070305010f0608180f03120f010e090318041103 60
    0xe18000503201004107144003540030324180000700c5002c1d10152260b6074040100c40181050b02240d6a0303400e43c803035074202d083c07a00900c52458400b0200030086603606c920070130001a035401d6120741e01c0c0ca1103c0c400b642050400104154103054400c108000c0c0c2602d144134116a2520700c800014451101c0c0c5903403c265070400d216045103100c070b00d065081142400d11001003a0061401c240745888004051154045001040001c143c0541e1555074010844075609a1503800c280e017044414001800245c105d00200d002508075014481100130509500708900e0f0041d281b55040d40b284410400344a100440c102c9140c010b00c8000080c140080c4200305090302d09446441d56071502c0d240080454070305810031030140d0076030001449059800300045912000740d03132340e4803051008000307210b1a1442080b09803078140301c00124010503070452490240501e070300134030024090740c88480c00c0c241e211044842c44619030003403010320743c101580400b4401202c2c01810016864018040e602e005510443e42e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 263299496 1250 263298246 263298281
    0x6040f0227010806010801030f110a09020d05090c0a05011d06040303080a05130c0e070c06050a06080c153f1503010e0d030c1701060315120b0103020d05030904 70
    0x407248280c8110801c44490000d280c10841c81c40d0510001e0711200c010300010300f1031007500400c2e404003c1c00743c0780e07206646002030854040c0d41d91044008040c1d40151418101c05007850042010b00c0400680e0407192400204243d100c1814900115448045803c3c030030b21254034130b10a0505a10344500500155000750b445c005140703031424400f0203442000c1e03d0303603c601034003403445004a00c4490421040d11014003803a1255220210110741b0b202120034060017441c6004144215880d01d03074852411540c868060300d101003681010450344400216130307142200002c025020100006843d00c503288003461209545002c0c0c210f00b094500360b4180c0d9020104520182404955608144200d082501c00c40080c403042001d84800d649640301100307100280b50b11402000700303042c0036a02d0207011070148015006903681d5010010050825820384440415004401141c5610380d0283d0900d0385801c47c2510165904c1d55080c410140d00b0076078291081d010070720008903160703514080c00c03004122001d40c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 263300746 1250 263299496 263299537
    0x10f0f09030c090522201207080718060b19020a06020705010f0b06070c0b0a0201060306051009150e150109080604151d0a0209060a03080d020c06010605180906040f02 73
    0x84480c10a1140d0405c84034948003140080081c421181014040f078803c5150100c840c00c22000c40e801c0c0714102d200c0b2045000e40c0e0740104400d000000c4180407075000d00462052200d0309101401110b0b89402000c80d801c100b0045054010300f5030540d00c1c81e1078400d00c1180c503942c00e19107400e41241c000100803942039451f180820188900d601440d40760640072686580740040d1a03a800b45126864424040f41440100c1c00b40b0409000b1751080d4003d5804c044140070310b1802400c4080d002c01d085c02040481c515280c0c03001e50f03101e50b04142c001640c1d8500b00c1e1398843c1e2521f03021148403400b1003102504000e210507003c0b8603980d041c41502d0145100784507400c007200c03400048500b500e1400c000d0740d101c03444107446a4450300d4006507902100f0307010b031042d40c16905c0b2000070071424010394101a02c1100002982844510241d00900284845206855459880307020480741d0784074609003455020034001108010f8a00741c6ca0403504504000e00000341d07100400c0484080e40c1240740c8035400d120b89200da = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 263301996 1250 263300746 263300761
    0x61501050c2b0f050306090a060504060801050906070903170702030a0804061e03050c1b0c030106060f030b01020a0305120717131e170304030c02031c0f020a02010f0f09030c0905 78
    0x22610111541c18012143c1c8180300c0c004000f07010041c0014403800d0301e0000b01d10f001051b40d204501400c00600203214081e03c400e00305000e00416241180b152164000003440e1602c41c03684034050380c2c1c2c403240700d01040484000c2e0081e147c0195005031b03854040d0000030303000a01690001c02c02448952128200e5406907000b20100d840d00724040c03c00d041c10a410011394100c1035007100c0901030130902d00021038550a000c01d18204140c0e4010b50950b20301503002c146507820440f01600c80c00b1a40c2d040c400c84460000490711003881e030f413004011450620400c0c400921090100c2c0d485109071820700142c03001340c0c1d5038081005040d1800610504550254020b01c5104c600340c82d941d40f04011280b8040c2080da81300106011032801c20408204c021010600b010b00c25486c03203000769001002c03605c0041920100b003900c0c0d80e0186a08010034042c112844c005070010420440344c84c3c05031590a04594026019900c168210744401700b04400d216000c8001900f500c4000003600740d411002885140601 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 263303246 1250 263301996 263302063
    0x2040303030b091014040207150f2a090603020a05070221070b0313030c0201091805010e06030a050a2315041b080d1202040b0c060703060b0c061501050c 67
    0x10000c03103050903061010303c0ba10340c0300031001032004011b43d00140e55034441e003005441ea0325940c03008503e05040c01c02036006203015400c01e5203602038410f14610314004981030310005088807540303000031480018013080079070300a5000c0c1052400038202203103000170540c0010341d8109180304001c078100a03121030380e062440c02c1125202804103440003d2450805081c06c0d0480c445814004040060151256003107911911440c0c0081404245001441c40074090900207030409001c0c4900d41c0520328000f914a1400180012031707190080041c1c414212586c642c41d80c0c040710104480c103606500e054203840d1202c20000040420b1401c40440407a003082d00d402e0900003040e1204005483c02480141b01d071f5500450b00c520589441d041c2440310004005082000c1e0080d0381c0720a8060401040c103c1e071081c00400d035180b0401081e5010803226890380800c0e40c0d54005c03000c2c01003440d0300403800509030f00300c1c100e0f02c0030900105040250420708400021441e00050320080040f040d05c0b084443c800c40d0700781d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 263304496 1250 263303246 263303251
    0x30207030b07030920060408060f041709010804140f19050f0607020601060809070e090d0f08100b1605030f0712050331051b0f0607020d0f060f02040303030b09 70
    0x42c5002d10000d04191510141181740841804c0c0e80901c400540001ea5148802c1310300030b2540c10b040d600380f49890705124004201c11103050742c1c00903c0402c041c050081000440701840d005850b081c4240d1269220080c03601e2800744400e80d00e02c076004010310310250400120707100b43e2100300324200c5841d1914010742002e050720030140441c1d009500f4080d9281e0046402c40c10b460503417805680940e28410f501d0706e0030a080e4040d60000002100b031204149000c02c01c1c000040f0f9640385d0318400c8102e4002280c00703080480e1031081042885070180311041030000205051105039000841580302525114203507801200034105000c0006112400c109054000e00704032185820031604500d0042002c0350241031042d094a080020012490341000c210f42201400c01c2d0058100c0305c11070300c960f402c42500c80700011440d2044510190340c520320b24003c01128091540a004074104030015520010303107404050b812240c8070344415124065520510107040214002d079004640d0741c00b0b0005016481b4800b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 263305746 1250 263304496 263304511
    0x20903010f050a02091903020612091c1e0806010203090f03010b13052202090a050403180f1802160803040302072c01050f0924130203010807121e0c030b04030207030b 73
    0x241d43c401c002507a0303410b0a8604441c45007001c1442940c4841481d801c2c11501018031250740c030052030a07002c0c41d378031909010304c550780118811000941d20380700352114001104d03110f0060784208040c000320705102681031049000540081642e208110001329441d1003001130a25581d0344408101c03003480b08000e43d400359603000400301c01030310310350b008254a03030001400c0a2105484602003400c05116410306020740b0111000c4500042c1c490380269034018582c0b040f004103040c0341c2e024064104e1a0710865280c11400d610a614118990b502d000303c0b6040100207030258050101c2c0010404209482908104c00c411198000c042134031110b00c0d8001c1042e00050700412182010030380320380303400804d5a0003460f030514806200f42e0090751940100100c1d038030360f1303046110603c455076045aa130300614140c450390300980e601c55440303101c04d41c40e80240c030201500120000c10140b030303a940107070010b511081c02000f000560b503841c0d07243e95a08803416101100184c2c8010300070400c6c80681e81c00306401544 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 263306996 1250 263305746 263305789
    0x112031704050d0c020d050102031807171e0312010f050a270504110409050a1403030402010504060e0411192309010503090f06070f080610050d020903010f050a0209 72
    0x7420b4031010381e0b0755024074100081c0034005400000390342d03482e442075070359a038004008d640c1c91510030161004800e2404a2030000c1c400d0400204016024048184003403207100028922918050a07200b10030b180c0140d03480701c501042009601a45a24031031303d0184c0403050001c5600da00e0201400400081644106400c4e41d500c004805020480710640e514111510310200301504d0f0740c1070a11081e25400900740d07206d032900074400c0400a0100d01040c1150049000928540c89486503584900c01101c0c001d0009808000601401e406902c00c1000703900090000074480d0440010484964000c08013410700e5112005011901a440805100c800d4525104403260030802da0b2080e51900540b403419040c4080800042c004103c01c200d104036100c021000c0342e03081d0a2000b40504000c810319800c80004000e64001081428041d14802c020b101e590340d524508101e9444207030080d049460080e625548030204092114114000e240c0100c0c0590001a50b9040c120308201c80b02207214141011020f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 263308246 1250 263306996 263307001
    0x6110d03050c091e101d0906010e09040303090503030f0a0b030d05190c02060f121b03010302040504210806120a051903050403050106140111010e0a0305091801120317 73
    0x1e1042a50300d6183c0941d00445245990100c620500081c1340d056a0003112075095920302ca035200e00312003404010003604142002c030b202c09209402c40200c90150200e00240c0421855040001003950b00070301a203000202d10505a03261811a403003901c003000414246814030408803140c1c85411589501140103003820005d1030405021800381c41c05002103001c0140c502c042d118080c05454200ca0b0380100300640c0d4040d0020b2076101d981001c00c421761600c62490010310419103240102c01b03071070010701806046038a10742c200005408000e000310b4048400d0f19910101c2007010b0031a04002c4c0c0d40d611a150340c0e242c0b58050240860310b00c26a004c2541c401040480440c001240844600c880030880341614074403401c0550319440b550384010820b40c41e0080c0041e807601c4203c505e80e01c2c003400f642d9000d0b01c0380d04c0c3d421480c2694051171880c141604100f41d0307840021f01850040002c0e02c2d0281c1000c8000100001e4418400f00980c0100c500c0c0d40440f01080030154010b548840101da8100300030000d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 263309352 1106 263308246 263308261
    0x406050a1518050c120402190305060708010531020a020a0206040801020418060b09040506130f06051207081216080c100f020406050d150306050106110d0305 69
    0x510f440d022511403d0f0030411102c1a0b1044815000c1a0f02d40c1d400700544442d8044440c849103540d0180000080c2c000e101c614891030168490038441e40c07500050001034010b2403a00c0e002e07801000c10244640030351174035600031000366075001030b00ca5641c4207080e4904540700d1400ba600c4100401d0010f016641500100705652030030101c0300905982100e0754041c1c440030b004000a004081c040c80c0c90a04003544201d510400080080341d07074032400f91400c07007241d040140398502542c4900081c03100d81480300d03441f902c6d024598010002507152910341500d400000001810324000003a0191088441d00d18521006030000411382c2c0d180b107a941d00743d07502c550041d04920083d060120440502c0502d20030742d003c0300c00700e4540f1031910075072000b000010710854022100104450002101041c1e95109041c0a0241c03620340c3e40f111030400310a246825807110707006040508000400805 = true := by decide +kernel

theorem cover : BRFrame.Cov 263129496 263309352 := by
  have h0 := BRFrame.cov_init 263129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 263129496 ≤ n) (h2 : n < 263309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
